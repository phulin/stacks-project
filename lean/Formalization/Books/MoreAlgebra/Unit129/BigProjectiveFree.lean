/-
# More on Algebra, Chapter 129: Big projective modules are free
-/

import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Formalization.Books.Algebra.Unit85.ProjectiveModulesLocalRing
import Formalization.Books.Algebra.Unit19.Radical
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Finsupp.Fin
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.TensorProduct.Finite

namespace Formalization.Books.MoreAlgebra.Unit129

open scoped TensorProduct

noncomputable section

universe u v

/-! ## Source-facing predicates -/

/- The source's `P_𝔪` is the canonical module localization at a maximal ideal.
   Its rank is a cardinal, so `aleph0 ≤ rank` expresses infinite rank without
   choosing a finite-rank encoding. -/

/-- Every maximal localization of `M` has infinite module rank. -/
def HasInfiniteMaximalRank
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ m : MaximalSpectrum R,
    Cardinal.aleph0 ≤
      Module.rank (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl M)

private theorem free_equiv_finsupp_nat
    {R F : Type*} [CommRing R]
    [AddCommGroup F] [Module R F] [Module.Free R F]
    (hF : ¬ Module.Finite R F) :
    Nonempty (F ≃ₗ[R] ℕ →₀ F) := by
  classical
  let b := Module.Free.chooseBasis R F
  have hι : ¬ Finite (Module.Free.ChooseBasisIndex R F) := by
    intro hι
    let _ := hι
    exact hF (Module.Finite.of_basis b)
  have hι' : Infinite (Module.Free.ChooseBasisIndex R F) :=
    not_finite_iff_infinite.mp hι
  let _ := hι'
  let c := Finsupp.basis (fun _ : ℕ => b)
  have hcard :
      Cardinal.mk (Σ _ : ℕ, Module.Free.ChooseBasisIndex R F) =
        Cardinal.mk (Module.Free.ChooseBasisIndex R F) := by
    rw [Cardinal.mk_sigma, Cardinal.sum_const]
    simp
  exact ⟨b.equiv c (Cardinal.eq.mp hcard.symm).some⟩

private def finsupp_prod_equiv
    {R X Y : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] :
    (ℕ →₀ (X × Y)) ≃ₗ[R] (ℕ →₀ X) × (ℕ →₀ Y) :=
  { toFun := fun f =>
      (Finsupp.mapRange.linearMap (LinearMap.fst R X Y) f,
        Finsupp.mapRange.linearMap (LinearMap.snd R X Y) f)
    invFun := fun fg =>
      { toFun := fun n => (fg.1 n, fg.2 n)
        support := fg.1.support ∪ fg.2.support
        mem_support_toFun := by
          intro n
          by_cases h₁ : fg.1 n = 0 <;> by_cases h₂ : fg.2 n = 0 <;>
            simp [h₁, h₂] }
    left_inv := by
      intro f
      ext n <;> simp
    right_inv := by
      intro fg
      apply Prod.ext
      · ext n
        simp
      · ext n
        simp
    map_add' := by
      intro f g
      ext n <;> simp
    map_smul' := by
      intro a f
      ext n <;> simp }

private def finsupp_head_tail
    {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X] :
    (ℕ →₀ X) ≃ₗ[R] X × (ℕ →₀ X) := by
  let eDomain : Option ℕ ≃ ℕ :=
    (Equiv.optionEquivSumPUnit.{0, 0} ℕ).trans Equiv.natSumPUnitEquivNat.{0}
  let eOption : (Option ℕ →₀ X) ≃ₗ[R] X × (ℕ →₀ X) :=
    { Finsupp.optionEquiv with
      map_add' := by
        intro f g
        ext <;> simp
      map_smul' := by
        intro a f
        ext <;> simp }
  exact (Finsupp.mapDomain.linearEquiv X R eDomain).symm.trans eOption

private def finsupp_shift_equiv
    {R X Y : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] :
    (X × (ℕ →₀ (X × Y))) ≃ₗ[R] ℕ →₀ (X × Y) := by
  let split := finsupp_prod_equiv (R := R) (X := X) (Y := Y)
  let head := finsupp_head_tail (R := R) (X := X)
  let e₁ := (LinearEquiv.refl R X).prodCongr split
  let e₂ := (LinearEquiv.prodAssoc R X (ℕ →₀ X) (ℕ →₀ Y)).symm
  let e₃ := head.symm.prodCongr (LinearEquiv.refl R (ℕ →₀ Y))
  exact
    e₁.trans (e₂.trans (e₃.trans split.symm))

/-! ## Eilenberg's lemma and its first consequence -/

/-- Eilenberg's swindle: a non-finitely generated free module absorbs a summand. -/
theorem eilenberg_swindle
    {R : Type u} {P Q F : Type v} [CommRing R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup F] [Module R F] [Module.Free R F]
    (hF : ¬ Module.Finite R F)
    (hPQ : Nonempty ((P × Q) ≃ₗ[R] F)) :
    Nonempty ((P × F) ≃ₗ[R] F) := by
  classical
  obtain ⟨eF⟩ := free_equiv_finsupp_nat hF
  obtain ⟨ePQ⟩ := hPQ
  let eMap : (ℕ →₀ F) ≃ₗ[R] (ℕ →₀ (P × Q)) :=
    Finsupp.mapRange.linearEquiv ePQ.symm
  let e0 : (P × F) ≃ₗ[R] P × (ℕ →₀ (P × Q)) :=
    (LinearEquiv.refl R P).prodCongr (eF.trans eMap)
  let eShift := finsupp_shift_equiv (R := R) (X := P) (Y := Q)
  exact ⟨e0.trans (eShift.trans (eMap.symm.trans eF.symm))⟩

/-- A projective module becomes free after adjoining a suitable free module. -/
theorem projective_plus_free_is_free
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P] :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F),
      Module.Free R F ∧ Module.Free R (P × F) := by
  classical
  let F₀ : Type (max u v) := P →₀ R
  let j : F₀ →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R P).out
  have hji : ∀ p : P, j (i p) = p := hi
  have hi_inj : Function.Injective i := by
    intro p q hpq
    have := congrArg j hpq
    simpa [hji] using this
  let Q : Submodule R F₀ := LinearMap.ker j
  let iQ : P →ₗ[R] LinearMap.range i :=
    i.codRestrict _ (fun p => ⟨p, rfl⟩)
  have hiQ : Function.Injective iQ := by
    intro p q hpq
    apply hi_inj
    exact congrArg Subtype.val hpq
  have hiQ_surj : Function.Surjective iQ := by
    intro x
    rcases x.property with ⟨p, hp⟩
    exact ⟨p, Subtype.ext hp⟩
  let f : F₀ →ₗ[R] LinearMap.range i := iQ.comp j
  have hf : ∀ x : LinearMap.range i, f x = x := by
    intro x
    rcases x.property with ⟨p, hp⟩
    apply Subtype.ext
    change i (j (x : F₀)) = (x : F₀)
    rw [← hp, hji]
  have hker : LinearMap.ker f = Q := by
    ext x
    change iQ (j x) = 0 ↔ j x = 0
    constructor
    · intro hx
      apply hiQ
      simpa using hx
    · intro hx
      simp [hx]
  have hcomp : IsCompl (LinearMap.range i) Q := by
    rw [← hker]
    exact LinearMap.isCompl_of_proj hf
  let eI : P ≃ₗ[R] LinearMap.range i :=
    LinearEquiv.ofBijective iQ ⟨hiQ, hiQ_surj⟩
  let ePQ : (P × Q) ≃ₗ[R] F₀ :=
    (eI.prodCongr (LinearEquiv.refl R Q)).trans
      (Submodule.prodEquivOfIsCompl _ _ hcomp)
  let F : Type (max u v) := ℕ →₀ F₀
  let eMap : (ℕ →₀ (P × Q)) ≃ₗ[R] F :=
    Finsupp.mapRange.linearEquiv ePQ
  let e : (P × F) ≃ₗ[R] F :=
    ((LinearEquiv.refl R P).prodCongr eMap.symm).trans
      ((finsupp_shift_equiv (R := R) (X := P) (Y := Q)).trans eMap)
  refine ⟨F, inferInstance, inferInstance, inferInstance, ?_⟩
  let _ : Module.Free R F := by
    dsimp [F]
    infer_instance
  exact Module.Free.of_equiv e.symm
/-
  classical
  let F₀ : Type (max u v) := P →₀ R
  let j : F₀ →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R P).out
  have hji : ∀ p : P, j (i p) = p := hi
  have hi_inj : Function.Injective i := by
    intro p q hpq
    have := congrArg j hpq
    simpa [hji] using this
  let Q : Submodule R F₀ := LinearMap.ker j
  let iQ : P →ₗ[R] LinearMap.range i :=
    i.codRestrict _ (fun p => ⟨p, rfl⟩)
  have hiQ : Function.Injective iQ := by
    intro p q hpq
    apply hi_inj
    exact congrArg Subtype.val hpq
  have hiQ_surj : Function.Surjective iQ := by
    intro x
    rcases x.property with ⟨p, hp⟩
    exact ⟨p, Subtype.ext hp⟩
  let f : F₀ →ₗ[R] LinearMap.range i := iQ.comp j
  have hf : ∀ x : LinearMap.range i, f x = x := by
    intro x
    rcases x.property with ⟨p, hp⟩
    apply Subtype.ext
    change i (j (x : F₀)) = (x : F₀)
    rw [← hp, hji]
  have hker : LinearMap.ker f = Q := by
    ext x
    change iQ (j x) = 0 ↔ j x = 0
    constructor
    · intro hx
      apply hiQ
      simpa using hx
    · intro hx
      simp [hx]
  have hcomp : IsCompl (LinearMap.range i) Q := by
    rw [← hker]
    exact LinearMap.isCompl_of_proj hf
  let eI : P ≃ₗ[R] LinearMap.range i :=
    LinearEquiv.ofBijective iQ ⟨hiQ, hiQ_surj⟩
  let ePQ : (P × Q) ≃ₗ[R] F₀ :=
    (eI.prodCongr (LinearEquiv.refl R Q)).trans
      (Submodule.prodEquivOfIsCompl _ _ hcomp)
  let F : Type (max u v) := ℕ →₀ F₀
  let eMap : (ℕ →₀ (P × Q)) ≃ₗ[R] F :=
    Finsupp.mapRange.linearEquiv ePQ
  let e : (P × F) ≃ₗ[R] F :=
    ((LinearEquiv.refl R P).prodCongr eMap.symm).trans
      ((finsupp_shift_equiv (R := R) (X := P) (Y := Q)).trans eMap)
  refine ⟨F, inferInstance, inferInstance, inferInstance, ?_⟩
  letI : Module.Free R F := by
    dsimp [F]
    infer_instance
  exact Module.Free.of_equiv e.symm
-/

/-! ## Finite free pieces containing elements -/

/-- An element of a projective module is contained in a finite free direct summand
of a finite-free enlargement.  Finite free modules are written canonically as
`Fin n →₀ R`. -/
theorem element_projective
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (s : P) :
    ∃ n : ℕ, ∃ K : Submodule R ((Fin n →₀ R) × P),
      (0, s) ∈ K ∧ IsComplemented K ∧
        Module.Finite R K ∧ Module.Free R K := by
  classical
  let L : Type (max u v) := P →₀ R
  let j : L →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R P).out
  have hji : ∀ p : P, j (i p) = p := hi
  let b : Module.Basis P R L := Finsupp.basisSingleOne
  let c : L := i s
  let d : P →₀ R := b.repr c
  let S : Set P := d.support
  letI : Finite S := Finite.of_injective
    (fun x : S => (⟨x.1, x.2⟩ : d.support))
    (by intro x y hxy; exact Subtype.ext (congrArg Subtype.val hxy))
  letI : Fintype S := Fintype.ofFinite S
  let A : Submodule R L := Submodule.span R (b '' S)
  let B : Submodule R L := Submodule.span R (b '' Sᶜ)
  have hAB : IsCompl A B := by
    exact b.linearIndependent.isCompl_span_image (Module.Basis.span_eq b)
      isCompl_compl
  let v : S → A := fun x =>
    ⟨b x, Submodule.subset_span ⟨x, x.2, rfl⟩⟩
  let bA : Module.Basis S R A := Module.Basis.mk (v := v) (by
    apply LinearIndependent.of_comp A.subtype
    change LinearIndependent R (fun x : S => b (x : P))
    exact b.linearIndependent.comp (fun x : S => (x : P)) Subtype.val_injective) (by
    intro y hy
    have hy' : (y : L) ∈ Submodule.span R (b '' S) := y.property
    refine Submodule.span_induction (p := fun z hz =>
      (⟨z, hz⟩ : A) ∈ Submodule.span R (Set.range v)) ?_ ?_ ?_ ?_ hy'
    · rintro z ⟨x, hx, rfl⟩
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    · exact Submodule.zero_mem _
    · intro z w hz hw hz' hw'
      exact Submodule.add_mem _ hz' hw'
    · intro a z hz hz'
      exact Submodule.smul_mem _ a hz')
  have hcA : c ∈ A := by
    have hc : d.sum (fun k a => a • b k) = c := by
      simpa only [d, Finsupp.linearCombination_apply] using b.linearCombination_repr c
    rw [← hc]
    change d.sum (fun k a => a • b k) ∈ A
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem A (d k)
      (Submodule.subset_span ⟨k, hk, rfl⟩)
  let eFin : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let eA : A ≃ₗ[R] (Fin (Fintype.card S) →₀ R) :=
    bA.repr.trans (Finsupp.mapDomain.linearEquiv R R eFin)
  let pA : L →ₗ[R] A := A.projectionOnto B hAB
  let u : A →ₗ[R] A := pA.comp (i.comp (j.comp A.subtype))
  let T : A →ₗ[R] A × P :=
    { toFun := fun a => (a - u a, j a)
      map_add' := by
        intro a a'
        apply Prod.ext
        · change (a + a') - u (a + a') = (a - u a) + (a' - u a')
          rw [map_add]
          abel
        · simp
      map_smul' := by
        intro r a
        ext x <;> simp [u, smul_sub] }
  let r : (A × P) →ₗ[R] A :=
    LinearMap.fst R A P + pA.comp (i.comp (LinearMap.snd R A P))
  have hrT : r.comp T = LinearMap.id := by
    apply LinearMap.ext
    intro a
    change (a - pA (i (j a))) + pA (i (j a)) = a
    abel
  let eAmbient : (A × P) ≃ₗ[R] (Fin (Fintype.card S) →₀ R) × P :=
    eA.prodCongr (LinearEquiv.refl R P)
  let T' : A →ₗ[R] ((Fin (Fintype.card S) →₀ R) × P) :=
    eAmbient.toLinearMap.comp T
  let r' : ((Fin (Fintype.card S) →₀ R) × P) →ₗ[R] A :=
    r.comp eAmbient.symm.toLinearMap
  have hrT' : r'.comp T' = LinearMap.id := by
    apply LinearMap.ext
    intro a
    simpa [r', T', eAmbient] using LinearMap.congr_fun hrT a
  let K : Submodule R ((Fin (Fintype.card S) →₀ R) × P) := LinearMap.range T'
  let T'K : A →ₗ[R] K := T'.codRestrict K (fun a => ⟨a, rfl⟩)
  have hT'inj : Function.Injective T' := by
    intro a a' haa'
    have h₁ := congrArg r' haa'
    have h₂ : r' (T' a) = a := LinearMap.congr_fun hrT' a
    have h₃ : r' (T' a') = a' := LinearMap.congr_fun hrT' a'
    exact h₂.symm.trans (h₁.trans h₃)
  have hT'Ksurj : Function.Surjective T'K := by
    intro x
    rcases x.property with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  have hT'Kinj : Function.Injective T'K := by
    intro a a' haa'
    apply hT'inj
    exact congrArg Subtype.val haa'
  let eK : A ≃ₗ[R] K := LinearEquiv.ofBijective T'K ⟨hT'Kinj, hT'Ksurj⟩
  let fK : ((Fin (Fintype.card S) →₀ R) × P) →ₗ[R] K :=
    (T'.comp r').codRestrict K (fun x => ⟨r' x, rfl⟩)
  have hfK : ∀ x : K, fK x = x := by
    intro x
    rcases x.property with ⟨a, ha⟩
    apply Subtype.ext
    change T' (r' (x : (Fin (Fintype.card S) →₀ R) × P)) = x
    rw [← ha]
    have ha' : r' (T' a) = a := LinearMap.congr_fun hrT' a
    rw [ha']
  have hKcomp : IsComplemented K :=
    ⟨LinearMap.ker fK, LinearMap.isCompl_of_proj hfK⟩
  letI : Module.Finite R A := Module.Finite.of_basis bA
  letI : Module.Free R A := Module.Free.of_basis bA
  have hKfin : Module.Finite R K := Module.Finite.equiv eK
  have hKfree : Module.Free R K := Module.Free.of_equiv eK
  have hTa : T' ⟨c, hcA⟩ = (0, s) := by
    let a0 : A := ⟨c, hcA⟩
    change eAmbient (T ⟨c, hcA⟩) = (0, s)
    rw [← eAmbient.apply_symm_apply (0, s)]
    apply congrArg eAmbient
    apply Prod.ext
    · apply Subtype.ext
      change c - pA (i (j (a0 : L))) = 0
      rw [hji, Submodule.projectionOnto_apply_of_mem_left hAB hcA]
      simp
    · change j (a0 : L) = s
      exact hji s
  refine ⟨Fintype.card S, K, ?_, hKcomp, hKfin, hKfree⟩
  exact ⟨⟨c, hcA⟩, hTa⟩

/-
private theorem element_projective_aux
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (s : P) :
    ∃ n : ℕ, ∃ K : Submodule R ((Fin n →₀ R) × P),
      (0, s) ∈ K ∧ IsComplemented K ∧
        Module.Finite R K ∧ Module.Free R K := by
  classical
  let L : Type (max u v) := P →₀ R
  let j : L →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R P).out
  have hji : ∀ p : P, j (i p) = p := hi
  let b : Module.Basis P R L := Finsupp.basisSingleOne
  let c : L := i s
  let d : P →₀ R := b.repr c
  let S : Set P := d.support
  letI : Finite S := Finite.of_injective
    (fun x : S => (⟨x.1, x.2⟩ : d.support))
    (by intro x y hxy; exact Subtype.ext (congrArg Subtype.val hxy))
  letI : Fintype S := Fintype.ofFinite S
  let A : Submodule R L := Submodule.span R (b '' S)
  let B : Submodule R L := Submodule.span R (b '' Sᶜ)
  have hAB : IsCompl A B := by
    exact b.linearIndependent.isCompl_span_image (Module.Basis.span_eq b)
      isCompl_compl
  let v : S → A := fun x =>
    ⟨b x, Submodule.subset_span ⟨x, x.2, rfl⟩⟩
  let bA : Module.Basis S R A := Module.Basis.mk (v := v) (by
    apply LinearIndependent.of_comp A.subtype
    change LinearIndependent R (fun x : S => b (x : P))
    exact b.linearIndependent.comp (fun x : S => (x : P)) Subtype.val_injective) (by
    intro y hy
    have hy' : (y : L) ∈ Submodule.span R (b '' S) := y.property
    refine Submodule.span_induction (p := fun z hz =>
      (⟨z, hz⟩ : A) ∈ Submodule.span R (Set.range v)) ?_ ?_ ?_ ?_ hy'
    · rintro z ⟨x, hx, rfl⟩
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    · exact Submodule.zero_mem _
    · intro z w hz hw hz' hw'
      exact Submodule.add_mem _ hz' hw'
    · intro a z hz hz'
      exact Submodule.smul_mem _ a hz')
  have hcA : c ∈ A := by
    have hc : d.sum (fun k a => a • b k) = c := by
      simpa only [d, Finsupp.linearCombination_apply] using b.linearCombination_repr c
    rw [← hc]
    change d.sum (fun k a => a • b k) ∈ A
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem A (d k)
      (Submodule.subset_span ⟨k, hk, rfl⟩)
  let eFin : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let eA : A ≃ₗ[R] (Fin (Fintype.card S) →₀ R) :=
    bA.repr.trans (Finsupp.mapDomain.linearEquiv R R eFin)
  let pA : L →ₗ[R] A := A.projectionOnto B hAB
  let u : A →ₗ[R] A := pA.comp (i.comp (j.comp A.subtype))
  let T : A →ₗ[R] A × P :=
    { toFun := fun a => (a - u a, j a)
      map_add' := by
        intro a a'
        ext x <;> simp [u] <;> abel
      map_smul' := by
        intro r a
        ext x <;> simp [u, smul_sub] }
  let r : (A × P) →ₗ[R] A :=
    LinearMap.fst R A P + pA.comp (i.comp (LinearMap.snd R A P))
  have hrT : r.comp T = LinearMap.id := by
    apply LinearMap.ext
    intro a
    change (a - pA (i (j a))) + pA (i (j a)) = a
    abel
  let eAmbient : (A × P) ≃ₗ[R] (Fin (Fintype.card S) →₀ R) × P :=
    eA.prodCongr (LinearEquiv.refl R P)
  let T' : A →ₗ[R] ((Fin (Fintype.card S) →₀ R) × P) :=
    eAmbient.toLinearMap.comp T
  let r' : ((Fin (Fintype.card S) →₀ R) × P) →ₗ[R] A :=
    r.comp eAmbient.symm.toLinearMap
  have hrT' : r'.comp T' = LinearMap.id := by
    apply LinearMap.ext
    intro a
    simpa [r', T', eAmbient] using LinearMap.congr_fun hrT a
  let K : Submodule R ((Fin (Fintype.card S) →₀ R) × P) := LinearMap.range T'
  let T'K : A →ₗ[R] K := T'.codRestrict K (fun a => ⟨a, rfl⟩)
  have hT'inj : Function.Injective T' := by
    intro a a' haa'
    have h₁ := congrArg r' haa'
    have h₂ : r' (T' a) = a := LinearMap.congr_fun hrT' a
    have h₃ : r' (T' a') = a' := LinearMap.congr_fun hrT' a'
    exact h₂.symm.trans (h₁.trans h₃)
  have hT'Ksurj : Function.Surjective T'K := by
    intro x
    rcases x.property with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  have hT'Kinj : Function.Injective T'K := by
    intro a a' haa'
    apply hT'inj
    exact congrArg Subtype.val haa'
  let eK : A ≃ₗ[R] K := LinearEquiv.ofBijective T'K ⟨hT'Kinj, hT'Ksurj⟩
  let fK : ((Fin (Fintype.card S) →₀ R) × P) →ₗ[R] K :=
    (T'.comp r').codRestrict K (fun x => ⟨r' x, rfl⟩)
  have hfK : ∀ x : K, fK x = x := by
    intro x
    rcases x.property with ⟨a, ha⟩
    apply Subtype.ext
    change T' (r' (x : (Fin (Fintype.card S) →₀ R) × P)) = x
    rw [← ha]
    rw [LinearMap.congr_fun hrT' a]
  have hKcomp : IsComplemented K :=
    ⟨LinearMap.ker fK, LinearMap.isCompl_of_proj hfK⟩
  letI : Module.Finite R A := Module.Finite.of_basis bA
  letI : Module.Free R A := Module.Free.of_basis bA
  have hKfin : Module.Finite R K := Module.Finite.equiv eK
  have hKfree : Module.Free R K := Module.Free.of_equiv eK
  have hTa : T' ⟨c, hcA⟩ = (0, s) := by
    apply eAmbient.injective
    apply Prod.ext
    · apply Subtype.ext
      change (⟨c, hcA⟩ - pA (i (j ⟨c, hcA⟩)) : L) = 0
      rw [hji, Submodule.projectionOnto_apply_of_mem_left hAB hcA]
      simp
    · change j ⟨c, hcA⟩ = s
      exact hji s
  refine ⟨Fintype.card S, K, ?_, hKcomp, hKfin, hKfree⟩
  exact ⟨⟨c, hcA⟩, hTa⟩
 -/

/-! ## Finding a unimodular element -/

private theorem bass_functional
    {k : Type*} {Q : Type*} [Field k]
    [AddCommGroup Q] [Module k Q] (x y : Q)
    (hy : y ∉ Submodule.span k ({x} : Set Q)) :
    ∃ f : Q →ₗ[k] k, f y = 1 ∧ f x = 0 := by
  let W : Submodule k Q := Submodule.span k ({x} : Set Q)
  obtain ⟨f, hf, hfy⟩ :=
    LinearMap.exists_extend_of_notMem (0 : W →ₗ[k] k) hy 1
  refine ⟨f, hfy, ?_⟩
  have hxW : x ∈ W := Submodule.subset_span (by simp)
  have hfx := congrArg (fun g => g ⟨x, hxW⟩) hf
  simpa using hfx

private theorem bass_basechange_projective
    {R A P : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module R P] [Module.Projective R P] :
    Module.Projective A (TensorProduct R A P) := by
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R P).out
  let F : Type _ := P →₀ R
  let j : F →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  let i' : TensorProduct R A P →ₗ[A] TensorProduct R A F :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) i
  let j' : TensorProduct R A F →ₗ[A] TensorProduct R A P :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) j
  apply Module.Projective.of_split i' j'
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => simp [i', j', j, hi p]
  | add z z' hz hz' => rw [map_add, hz, hz']; simp

private theorem bass_basechange_span
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P]
    (M : Submodule R P) (s : P)
    (hgen : Submodule.span R ({s} : Set P) ⊔ M = ⊤) :
    let A := R ⧸ Ring.jacobson R
    let PB := TensorProduct R A P
    let q : P →ₗ[R] PB := TensorProduct.mk R A P 1
    let N : Submodule A PB := Submodule.span A (q '' (M : Set P))
    Submodule.span A ({q s} : Set PB) ⊔ N = ⊤ := by
  dsimp
  let A := R ⧸ Ring.jacobson R
  let PB := TensorProduct R A P
  let q : P →ₗ[R] PB := TensorProduct.mk R A P 1
  let N : Submodule A PB := Submodule.span A (q '' (M : Set P))
  let W : Submodule A PB := Submodule.span A ({q s} : Set PB) ⊔ N
  apply top_unique
  intro z _
  have hall : ∀ z : PB, z ∈ W := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact W.zero_mem
    | tmul a p =>
        have hp : p ∈ Submodule.span R (({s} : Set P) ∪ (M : Set P)) := by
          rw [Submodule.span_union]
          simpa [hgen]
        have hqp : q p ∈ W := by
          refine Submodule.span_induction
            (p := fun x _ => q x ∈ W) ?_ ?_ ?_ ?_ hp
          · rintro x (rfl | hx)
            · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
            · exact Submodule.mem_sup_right (Submodule.subset_span ⟨x, hx, rfl⟩)
          · simpa [q] using W.zero_mem
          · intro x y _ _ hx hy
            simpa only [map_add] using W.add_mem hx hy
          · intro r x _ hx
            rw [map_smul]
            exact W.smul_mem (Ideal.Quotient.mk (Ring.jacobson R) r) hx
        have htmul : a ⊗ₜ[R] p = a • q p := by
          calc
            a ⊗ₜ[R] p = a • (1 ⊗ₜ[R] p) :=
              TensorProduct.tmul_eq_smul_one_tmul a p
            _ = a • q p := by rfl
        rw [htmul]
        exact W.smul_mem a hqp
    | add z z' hz hz' => exact W.add_mem hz hz'
  exact hall z

private theorem bass_basechange_span_lift
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P]
    (M : Submodule R P) (s : P) (z : TensorProduct R (R ⧸ Ring.jacobson R) P)
    (hz : z ∈ Submodule.span (R ⧸ Ring.jacobson R)
      ((TensorProduct.mk R (R ⧸ Ring.jacobson R) P 1) '' (M : Set P))) :
    ∃ m : P, m ∈ M ∧ TensorProduct.mk R (R ⧸ Ring.jacobson R) P 1 m = z := by
  let A := R ⧸ Ring.jacobson R
  let PB := TensorProduct R A P
  let q : P →ₗ[R] PB := TensorProduct.mk R A P 1
  refine Submodule.span_induction (p := fun z _ => ∃ m : P, m ∈ M ∧ q m = z)
    ?_ ?_ ?_ ?_ hz
  · rintro z ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · exact ⟨0, M.zero_mem, by simp [q]⟩
  · rintro x y _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', M.add_mem hm hm', by simp [q]⟩
  · intro a z _ hz'
    rcases hz' with ⟨m, hm, hzm⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨r • m, M.smul_mem r hm, by
      rw [map_smul, hzm]
      exact (IsScalarTower.algebraMap_smul A r z).symm⟩

private theorem bass_basechange_rank
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) :
    HasInfiniteMaximalRank (R ⧸ Ring.jacobson R)
      (TensorProduct R (R ⧸ Ring.jacobson R) P) := by
  intro m
  let A := R ⧸ Ring.jacobson R
  let PB := TensorProduct R A P
  let q := m.asIdeal.comap (algebraMap R A)
  letI : q.IsMaximal := Ideal.comap_isMaximal_of_surjective
      (Ideal.Quotient.mk (Ring.jacobson R)) Ideal.Quotient.mk_surjective
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime m.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver q m.asIdeal
  let LA := Localization.AtPrime m.asIdeal
  let LR := Localization.AtPrime q
  let e : LocalizedModule m.asIdeal.primeCompl PB ≃ₗ[LA]
      LA ⊗[LR] LocalizedModule q.primeCompl P :=
    LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A _ _ P) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R _ _ _ P).symm ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (LocalizedModule.equivTensorProduct _ P).symm)
  letI : Module.Projective LR (LocalizedModule q.primeCompl P) := inferInstance
  letI : Module.Free LR (LocalizedModule q.primeCompl P) :=
    Formalization.Books.Algebra.Unit85.projective_free_over_local_ring inferInstance
  have hbase := Module.rank_baseChange (R := LA) (S := LR)
      (M' := LocalizedModule q.primeCompl P)
  have hq : Cardinal.aleph0 ≤
      Module.rank LR (LocalizedModule q.primeCompl P) :=
    hP ⟨q, inferInstance⟩
  rw [e.rank_eq, hbase]
  exact Cardinal.aleph0_le_lift.mpr hq

private theorem bass_finite_kernel
    {R : Type u} {P : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P]
    (M : Submodule R P) (x : P) {n : ℕ}
    (fs : Fin n → P →ₗ[R] R)
    (hgen : Submodule.span R ({x} : Set P) ⊔ M = ⊤) :
    Module.Finite R
      (P ⧸ (M ⊓ ⨅ i : Fin n, LinearMap.ker (fs i))) := by
  let K : Submodule R P := M ⊓ ⨅ i : Fin n, LinearMap.ker (fs i)
  have hqtop : Submodule.span R ({M.mkQ x} : Set (P ⧸ M)) = ⊤ := by
    have hmap : Submodule.map M.mkQ (Submodule.span R ({x} : Set P)) = ⊤ := by
      apply (Submodule.map_mkQ_eq_top M (Submodule.span R ({x} : Set P))).mpr
      simpa [sup_comm] using hgen
    simpa only [Submodule.map_span, Set.image_singleton] using hmap
  let q : R →ₗ[R] (P ⧸ M) :=
    LinearMap.toSpanSingleton R (P ⧸ M) (M.mkQ x)
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective M z
    have hy : y ∈ Submodule.span R (({x} : Set P) ∪ (M : Set P)) := by
      rw [Submodule.span_union]
      simpa [hgen]
    refine Submodule.span_induction
      (p := fun z _ => ∃ r, q r = M.mkQ z) ?_ ?_ ?_ ?_ hy
    · rintro z (rfl | hz)
      · exact ⟨1, by simp [q]⟩
      · refine ⟨0, ?_⟩
        simpa [q] using ((Submodule.Quotient.mk_eq_zero M).mpr hz).symm
    · exact ⟨0, by simp [q]⟩
    · rintro z z' _ _ ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simp only [q, map_add, ha, hb]
    · intro a z _ ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        (q (a * b)) = a • q b := by simp [q, smul_smul]
        _ = a • M.mkQ z := by rw [hb]
  letI : Module.Finite R (P ⧸ M) := Module.Finite.of_surjective q hqsurj
  letI : Module.Finite R (Fin n → R) := inferInstance
  let f : P →ₗ[R] (P ⧸ M) × (Fin n → R) :=
    (M.mkQ).prod (LinearMap.pi fs)
  have hfK : LinearMap.ker f = K := by
    ext y
    change y ∈ LinearMap.ker ((M.mkQ).prod (LinearMap.pi fs)) ↔
      y ∈ (M ⊓ ⨅ i : Fin n, LinearMap.ker (fs i))
    constructor
    · intro h
      have h' : M.mkQ y = 0 ∧ (LinearMap.pi fs) y = 0 := by
        simpa [LinearMap.mem_ker, LinearMap.prod_apply] using h
      apply Submodule.mem_inf.mpr
      refine ⟨(Submodule.Quotient.mk_eq_zero M).mp h'.1, ?_⟩
      rw [Submodule.mem_iInf]
      intro i
      have hi := congrFun h'.2 i
      simpa using hi
    · intro h
      rcases (Submodule.mem_inf.mp h) with ⟨hy, hi⟩
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · exact (Submodule.Quotient.mk_eq_zero M).mpr hy
      · ext i
        exact (Submodule.mem_iInf _).mp hi i
  let fQ : (P ⧸ K) →ₗ[R] (P ⧸ M) × (Fin n → R) :=
    K.liftQ f (by rw [hfK])
  have hfQinj : Function.Injective fQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_liftQ_eq_bot' K f hfK.symm]
  exact Module.Finite.of_injective fQ hfQinj

private theorem bass_localized_exact_finite
    {A : Type u} {P : Type v} [CommRing A]
    [AddCommGroup P] [Module A P] (K : Submodule A P)
    [Module.Finite A (P ⧸ K)] (p : Ideal A) [p.IsPrime] :
    let L := Localization.AtPrime p
    let Ploc := LocalizedModule p.primeCompl P
    let Hloc := LocalizedModule p.primeCompl (P ⧸ K)
    let k := p.ResidueField
    let q : Ploc →ₗ[L] TensorProduct L k Ploc :=
      TensorProduct.mk L k Ploc 1
    let f : LocalizedModule p.primeCompl K →ₗ[L] Ploc :=
      LocalizedModule.map p.primeCompl K.subtype
    let g : Ploc →ₗ[L] Hloc :=
      LocalizedModule.map p.primeCompl K.mkQ
    Module.Finite k
      ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) := by
  dsimp
  let L := Localization.AtPrime p
  let Ploc := LocalizedModule p.primeCompl P
  let Hloc := LocalizedModule p.primeCompl (P ⧸ K)
  let k := p.ResidueField
  let f : LocalizedModule p.primeCompl K →ₗ[L] Ploc :=
    LocalizedModule.map p.primeCompl K.subtype
  let g : Ploc →ₗ[L] Hloc :=
    LocalizedModule.map p.primeCompl K.mkQ
  have hfg : Function.Exact f g :=
    LocalizedModule.map_exact p.primeCompl K.subtype K.mkQ
      (LinearMap.exact_subtype_mkQ K)
  have hgs : Function.Surjective g :=
    LocalizedModule.map_surjective p.primeCompl K.mkQ
      (Submodule.mkQ_surjective K)
  have hfg' : Function.Exact (f.baseChange k) (g.baseChange k) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact k hfg hgs
  have hgs' : Function.Surjective (g.baseChange k) :=
    LinearMap.baseChange_surjective k hgs
  letI : Module.Finite L Hloc := Module.Finite.of_isLocalizedModule
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl (P ⧸ K))
  letI : Module.Finite k (TensorProduct L k Hloc) := Module.Finite.base_change L k Hloc
  let q : TensorProduct L k Ploc →ₗ[k] TensorProduct L k Hloc := g.baseChange k
  have hqker : LinearMap.ker q = LinearMap.range (f.baseChange k) :=
    hfg'.linearMap_ker_eq
  let qbar : ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) →ₗ[k]
      TensorProduct L k Hloc :=
    (LinearMap.range (f.baseChange k)).liftQ q (by rw [hqker])
  have hqbar_surj : Function.Surjective qbar := by
    intro z
    obtain ⟨y, rfl⟩ := hgs' z
    exact ⟨Submodule.mkQ (LinearMap.range (f.baseChange k)) y, by simp [qbar, q]⟩
  have hqbar_inj : Function.Injective qbar := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (f.baseChange k)) x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (f.baseChange k)) y
    apply (Submodule.Quotient.eq (LinearMap.range (f.baseChange k))).mpr
    have hz : q (x - y) = 0 := by
      rw [map_sub, sub_eq_zero]
      simpa [qbar] using hxy
    obtain ⟨z, hz⟩ := (hfg' (x - y)).mp hz
    exact ⟨z, by simpa [map_sub] using hz⟩
  let e : ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) ≃ₗ[k]
      TensorProduct L k Hloc := LinearEquiv.ofBijective qbar ⟨hqbar_inj, hqbar_surj⟩
  exact Module.Finite.equiv e.symm

set_option maxHeartbeats 1000000 in
private theorem bass_localized_range_le
    {A : Type u} {P : Type v} [CommRing A]
    [AddCommGroup P] [Module A P] (K : Submodule A P)
    (p : Ideal A) [p.IsPrime]
    (s : P) (m : P)
    (hnot : ∀ y : P, y ∈ K →
      (TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1)
          (LocalizedModule.mkLinearMap p.primeCompl P y) ∈
        Submodule.span p.ResidueField
          ({(TensorProduct.mk (Localization.AtPrime p) p.ResidueField
            (LocalizedModule p.primeCompl P) 1)
            (LocalizedModule.mkLinearMap p.primeCompl P (s + m))} :
            Set (TensorProduct (Localization.AtPrime p) p.ResidueField
              (LocalizedModule p.primeCompl P)))) :
    LinearMap.range ((LocalizedModule.map p.primeCompl K.subtype).baseChange
      p.ResidueField) ≤
      Submodule.span p.ResidueField
        ({(TensorProduct.mk (Localization.AtPrime p) p.ResidueField
          (LocalizedModule p.primeCompl P) 1)
          (LocalizedModule.mkLinearMap p.primeCompl P (s + m))} :
          Set (TensorProduct (Localization.AtPrime p) p.ResidueField
            (LocalizedModule p.primeCompl P))) := by
  let L := Localization.AtPrime p
  let Ploc := LocalizedModule p.primeCompl P
  let k := p.ResidueField
  let f : LocalizedModule p.primeCompl K →ₗ[L] Ploc :=
    LocalizedModule.map p.primeCompl K.subtype
  let q : Ploc →ₗ[L] TensorProduct L k Ploc := TensorProduct.mk L k Ploc 1
  let v : TensorProduct L k Ploc := q (LocalizedModule.mkLinearMap p.primeCompl P (s + m))
  let W : Submodule k (TensorProduct L k Ploc) := Submodule.span k ({v} : Set _)
  have hu (u : LocalizedModule p.primeCompl K) : q (f u) ∈ W := by
    obtain ⟨⟨y, d⟩, rfl⟩ := IsLocalizedModule.mk'_surjective
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl K) u
    have hmk' :
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl P) (y : P) d =
          IsLocalization.mk' (Localization.AtPrime p) (1 : A) d •
            IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl P)
              (y : P) (1 : p.primeCompl) := by
      simpa using (IsLocalizedModule.mk'_smul_mk'
        (f := LocalizedModule.mkLinearMap p.primeCompl P)
        (Localization.AtPrime p) 1 (y : P) d 1).symm
    have hy : q (LocalizedModule.mkLinearMap p.primeCompl P (y : P)) ∈ W :=
      hnot (y : P) y.property
    change q (f (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap
      p.primeCompl K) y d)) ∈ W
    have hf : f (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap
        p.primeCompl K) y d) =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl P)
          (y : P) d := by
      change IsLocalizedModule.map p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl K)
        (LocalizedModule.mkLinearMap p.primeCompl P) K.subtype
          (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl K) y d) = _
      exact IsLocalizedModule.map_mk' _ _ _ _ _ _
    rw [hf]
    rw [hmk', map_smul]
    rw [← algebraMap_smul k]
    exact Submodule.smul_mem W _ (by simpa using hy)
  rintro z ⟨w, rfl⟩
  change (f.baseChange k) w ∈ W
  induction w using TensorProduct.induction_on with
  | zero => exact W.zero_mem
  | tmul a u =>
      rw [LinearMap.baseChange_tmul, TensorProduct.tmul_eq_smul_one_tmul]
      exact Submodule.smul_mem W a (hu u)
  | add z z' hz hz' => rw [map_add]; exact W.add_mem hz hz'

private theorem bass_exists_global_element
    {A : Type u} {P : Type v} [CommRing A]
    [AddCommGroup P] [Module A P] (K : Submodule A P)
    (p : Ideal A) [p.IsPrime]
    (s m : P)
    (hQ : Cardinal.aleph0 ≤ Module.rank p.ResidueField
      (TensorProduct (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P)))
    (hfin : Module.Finite p.ResidueField
      ((TensorProduct (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P)) ⧸
        LinearMap.range ((LocalizedModule.map p.primeCompl K.subtype).baseChange
          p.ResidueField))) :
    ∃ y : P, y ∈ K ∧
      (TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1)
          (LocalizedModule.mkLinearMap p.primeCompl P y) ∉
        Submodule.span p.ResidueField
          ({(TensorProduct.mk (Localization.AtPrime p) p.ResidueField
            (LocalizedModule p.primeCompl P) 1)
            (LocalizedModule.mkLinearMap p.primeCompl P (s + m))} :
            Set (TensorProduct (Localization.AtPrime p) p.ResidueField
              (LocalizedModule p.primeCompl P))) := by
  let L := Localization.AtPrime p
  let Ploc := LocalizedModule p.primeCompl P
  let k := p.ResidueField
  let f : LocalizedModule p.primeCompl K →ₗ[L] Ploc :=
    LocalizedModule.map p.primeCompl K.subtype
  let qglobal : P →ₗ[A] TensorProduct L k Ploc :=
    (TensorProduct.mk L k Ploc 1).restrictScalars A |>.comp
      (LocalizedModule.mkLinearMap p.primeCompl P)
  let v := qglobal (s + m)
  let W : Submodule k (TensorProduct L k Ploc) := Submodule.span k ({v} : Set _)
  by_contra h
  push_neg at h
  have hle : LinearMap.range (f.baseChange k) ≤ W := by
    apply bass_localized_range_le K p s m
    intro y hy
    simpa [qglobal, v, W] using h y hy
  let qbar : ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) →ₗ[k]
      (TensorProduct L k Ploc) ⧸ W :=
    (LinearMap.range (f.baseChange k)).liftQ W.mkQ (by
      rw [LinearMap.range_le_iff_comap]
      apply top_unique
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero W).mpr (hle ⟨x, rfl⟩))
  letI : Module.Finite k
      ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) := hfin
  have hqbar_surj : Function.Surjective qbar := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W z
    exact ⟨Submodule.mkQ (LinearMap.range (f.baseChange k)) x, rfl⟩
  letI : Module.Finite k ((TensorProduct L k Ploc) ⧸ W) :=
    Module.Finite.of_surjective qbar hqbar_surj
  letI : Module.Finite k W := inferInstance
  letI : Module.Finite k (TensorProduct L k Ploc) :=
    Module.Finite.of_submodule_quotient W
  exact (not_lt_of_ge hQ) (Module.rank_lt_aleph0 k (TensorProduct L k Ploc))

private theorem bass_good_element_noetherian
    {A : Type u} {P : Type v} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup P] [Module A P] [Module.Projective A P]
    (hP : HasInfiniteMaximalRank A P) (s : P) (M : Submodule A P)
    (hgen : Submodule.span A ({s} : Set P) ⊔ M = ⊤) :
    ∃ m : P, m ∈ M ∧ ∃ φ : P →ₗ[A] A, φ (s + m) = 1 := by
  let states : Set (Ideal A) := {I |
    ∃ n : ℕ, ∃ m : P, m ∈ M ∧ ∃ fs : Fin n → P →ₗ[A] A,
      I = Ideal.span (Set.range (fun i => fs i (s + m)))}
  have hstates : states.Nonempty := by
    refine ⟨⊥, ?_⟩
    refine ⟨0, 0, Submodule.zero_mem M, (fun i : Fin 0 => Fin.elim0 i), ?_⟩
    simp [states]
  obtain ⟨I, hI, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := A) (M := A)).mpr inferInstance
      states hstates
  rcases hI with ⟨n, m, hm, fs, rfl⟩
  by_contra htopGood
  have hnotop : Ideal.span (Set.range (fun i => fs i (s + m))) ≠ ⊤ := by
    intro htop
    have hone : (1 : A) ∈ Ideal.span (Set.range (fun i => fs i (s + m))) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
    apply htopGood
    refine ⟨m, hm, ∑ i, c i • fs i, ?_⟩
    simpa [LinearMap.sum_apply, smul_eq_mul] using hc
  obtain ⟨p, hp, hIp⟩ := Ideal.ne_top_iff_exists_maximal.mp hnotop
  letI : p.IsMaximal := hp
  let K : Submodule A P := M ⊓ ⨅ i : Fin n, LinearMap.ker (fs i)
  letI : Module.Finite A (P ⧸ K) := by
    simpa [K] using bass_finite_kernel M s fs hgen
  have hQ : Cardinal.aleph0 ≤ Module.rank p.ResidueField
      (TensorProduct (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P)) := by
    letI : Module.Projective (Localization.AtPrime p)
        (LocalizedModule p.primeCompl P) := inferInstance
    letI : Module.Free (Localization.AtPrime p)
        (LocalizedModule p.primeCompl P) :=
      Formalization.Books.Algebra.Unit85.projective_free_over_local_ring inferInstance
    have hr := Module.rank_baseChange (R := p.ResidueField)
      (S := Localization.AtPrime p) (M' := LocalizedModule p.primeCompl P)
    rw [hr]
    simpa using hP ⟨p, hp⟩
  have hfin := bass_localized_exact_finite K p
  obtain ⟨y, hyK, hyind⟩ := bass_exists_global_element K p s m hQ hfin
  obtain ⟨fres, hfres_y, hfres_sm⟩ :=
    bass_functional
      ((TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1)
        (LocalizedModule.mkLinearMap p.primeCompl P (s + m)))
      ((TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1)
        (LocalizedModule.mkLinearMap p.primeCompl P y)) hyind
  let qglobal : P →ₗ[A] p.ResidueField :=
    fres.restrictScalars A |>.comp
      ((TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1).restrictScalars A |>.comp
        (LocalizedModule.mkLinearMap p.primeCompl P))
  have hqglobal_y : qglobal y = 1 := by
    simpa [qglobal] using hfres_y
  have hqglobal_sm : qglobal (s + m) = 0 := by
    simpa [qglobal] using hfres_sm
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property
    (Algebra.linearMap A p.ResidueField) qglobal
    p.algebraMap_residueField_surjective
  have hφ_y : algebraMap A p.ResidueField (φ y) = 1 := by
    have h := congrArg (fun g : P →ₗ[A] p.ResidueField => g y) hφ
    simpa [qglobal, LinearMap.comp_apply] using h.trans hqglobal_y
  have hφ_sm : algebraMap A p.ResidueField (φ (s + m)) = 0 := by
    have h := congrArg (fun g : P →ₗ[A] p.ResidueField => g (s + m)) hφ
    simpa [qglobal, LinearMap.comp_apply] using h.trans hqglobal_sm
  have hφ_sum : algebraMap A p.ResidueField (φ (s + m + y)) = 1 := by
    rw [map_add, map_add, hφ_sm, hφ_y]
    abel
  have hsum_not_mem : φ (s + m + y) ∉ p := by
    intro hmem
    have hz := Ideal.algebraMap_residueField_eq_zero.mpr hmem
    rw [hφ_sum] at hz
    exact one_ne_zero hz
  let fs' : Fin (n + 1) → P →ₗ[A] A := Fin.cases φ (fun i => fs i)
  let I' : Ideal A := Ideal.span (Set.range (fun i => fs' i (s + (m + y))))
  have hI'state : I' ∈ states := by
    refine ⟨n + 1, m + y, M.add_mem hm (Submodule.mem_inf.mp hyK).1, fs', rfl⟩
  have hker_y : ∀ i : Fin n, fs i y = 0 := by
    intro i
    exact LinearMap.mem_ker.mp
      ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hyK).2 i)
  have hle : Ideal.span (Set.range (fun i => fs i (s + m))) ≤ I' := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.subset_span
    refine ⟨Fin.succ i, ?_⟩
    simp [fs', hker_y, add_assoc, add_left_comm, add_comm]
  have hnle : ¬ I' ≤ Ideal.span (Set.range (fun i => fs i (s + m))) := by
    intro hle'
    have hmemp : φ (s + m + y) ∈ I' := by
      apply Ideal.subset_span
      exact ⟨0, by simp [fs', add_assoc]⟩
    exact hsum_not_mem (hIp (hle' hmemp))
  have hlt : Ideal.span (Set.range (fun i => fs i (s + m))) < I' := by
    exact lt_of_le_of_ne hle (by
      intro heq
      apply hnle
      rw [← heq])
  exact (hmax I' hI'state) hlt

/-- If `s` together with a submodule `M` generates `P`, one can adjust `s` by
an element of `M` to obtain a rank-one free direct summand. -/
theorem trick_to_find_good_element
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) (s : P) (M : Submodule R P)
    (hgen : Submodule.span R ({s} : Set P) ⊔ M = ⊤) :
    ∃ m : P, m ∈ M ∧
        IsComplemented (Submodule.span R ({s + m} : Set P)) ∧
        Nonempty (R ≃ₗ[R] Submodule.span R ({s + m} : Set P)) := by
  let A := R ⧸ Ring.jacobson R
  let PB := TensorProduct R A P
  let q : P →ₗ[R] PB := TensorProduct.mk R A P 1
  let N : Submodule A PB := Submodule.span A (q '' (M : Set P))
  letI : IsNoetherianRing A := hR
  letI : Module.Projective A PB :=
    bass_basechange_projective (R := R) (A := A) (P := P)
  have hgenPB : Submodule.span A ({q s} : Set PB) ⊔ N = ⊤ := by
    change Submodule.span A ({q s} : Set PB) ⊔
      Submodule.span A (q '' (M : Set P)) = ⊤
    simpa [A, PB, q] using bass_basechange_span M s hgen
  obtain ⟨z, hz, φ, hφ⟩ := bass_good_element_noetherian
    (A := A) (P := PB) (bass_basechange_rank hP) (q s) N hgenPB
  obtain ⟨m, hm, hqm⟩ := bass_basechange_span_lift M s z (by
    simpa [N] using hz)
  have hqm' : q m = z := by
    change (1 ⊗ₜ[R] m) = z
    exact hqm
  let φR : P →ₗ[R] A := φ.restrictScalars R |>.comp q
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property
    (Algebra.linearMap R A) φR Ideal.Quotient.mk_surjective
  let x : P := s + m
  have hφx : φR x = 1 := by
    have hqsm : q x = q s + z := by
      dsimp [x]
      rw [map_add, hqm']
    have hφq : φ (q x) = 1 := by rw [hqsm]; exact hφ
    simpa [φR, LinearMap.comp_apply] using hφq
  have hψxmod : algebraMap R A (ψ x) = 1 := by
    have hh := congrArg (fun g : P →ₗ[R] A => g x) hψ
    simpa [φR, x, LinearMap.comp_apply] using hh.trans hφx
  have hψxquot : Ideal.Quotient.mk (Ring.jacobson R) (ψ x) = 1 := by
    simpa [A] using hψxmod
  have hunit_quot : IsUnit (Ideal.Quotient.mk (Ring.jacobson R) (ψ x)) := by
    rw [hψxquot]
    exact isUnit_one
  have hunit : IsUnit (ψ x) :=
    Formalization.Books.Algebra.Unit19.isUnit_of_isUnit_quotient_of_le_jacobson
      (Ring.jacobson R) le_rfl hunit_quot
  let χ : P →ₗ[R] R := (↑(IsUnit.unit hunit).inv : R) • ψ
  have hχx : χ x = 1 := by
    simpa [χ, LinearMap.smul_apply, mul_comm] using hunit.val_inv_mul
  let S : Submodule R P := Submodule.span R ({x} : Set P)
  let ix0 : R →ₗ[R] P := LinearMap.toSpanSingleton R P x
  let ix : R →ₗ[R] S := ix0.codRestrict S (by
    intro r
    exact Submodule.smul_mem S r (Submodule.subset_span (by simp)))
  have hχix (r : R) : χ (ix r : P) = r := by
    change χ (r • x) = r
    rw [map_smul, hχx]
    simp [smul_eq_mul]
  let pr : P →ₗ[R] S := ix.comp χ
  have hpr : ∀ y : S, pr y = y := by
    intro y
    apply Subtype.ext
    change (ix (χ (y : P)) : P) = (y : P)
    refine Submodule.span_induction
      (p := fun z _ => (ix (χ z) : P) = z) ?_ ?_ ?_ ?_ y.property
    · intro z hz
      have hz' : z = x := Set.mem_singleton_iff.mp hz
      subst z
      rw [hχx]
      change (1 : R) • x = x
      simp
    · simp
    · intro z z' _ _ hz hz'
      change (ix (χ (z + z')) : P) = z + z'
      rw [map_add, map_add]
      change (ix (χ z) : P) + (ix (χ z') : P) = z + z'
      exact congrArg₂ (· + ·) hz hz'
    · intro r z _ hz
      change (ix (χ (r • z)) : P) = r • z
      rw [map_smul, map_smul]
      change r • (ix (χ z) : P) = r • z
      exact congrArg (fun w : P => r • w) hz
  have hcomp : IsComplemented S :=
    ⟨LinearMap.ker pr, LinearMap.isCompl_of_proj hpr⟩
  have hix_inj : Function.Injective ix := by
    intro a b hab
    have h := congrArg (fun y : S => χ (y : P)) hab
    simpa [hχix] using h
  have hix_surj : Function.Surjective ix := by
    intro y
    refine ⟨χ (y : P), ?_⟩
    simpa [pr] using hpr y
  refine ⟨m, hm, hcomp, ?_⟩
  exact ⟨LinearEquiv.ofBijective ix ⟨hix_inj, hix_surj⟩⟩

private theorem bass_hasInfinite_product
    {R : Type u} {P : Type v} {F : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup F] [Module R F] [Module.Finite R F]
    (hP : HasInfiniteMaximalRank R P) :
    HasInfiniteMaximalRank R (F × P) := by
  intro m
  let L := Localization.AtPrime m.asIdeal
  let S := m.asIdeal.primeCompl
  let e : LocalizedModule S (F × P) ≃ₗ[L]
      LocalizedModule S F × LocalizedModule S P :=
    IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (F × P))
      ((LocalizedModule.mkLinearMap S F).prodMap
        (LocalizedModule.mkLinearMap S P)) |>.extendScalarsOfIsLocalization S L
  let i : LocalizedModule S P →ₗ[L] LocalizedModule S (F × P) :=
    e.symm.toLinearMap.comp (LinearMap.inr L
      (LocalizedModule S F) (LocalizedModule S P))
  have hi : Function.Injective i := by
    intro x y hxy
    simpa [i] using congrArg e hxy
  have hr := i.lift_rank_le_of_injective hi
  have hq := hP m
  have hr' : Module.rank L (LocalizedModule S P) ≤
      Module.rank L (LocalizedModule S (F × P)) :=
    Cardinal.lift_le.mp hr
  exact hq.trans hr'

private theorem bass_complement_infinite
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P)
    (K C : Submodule R (R × P)) (hKC : IsCompl K C)
    [Module.Finite R K] :
    HasInfiniteMaximalRank R C := by
  intro m
  by_contra hC
  have hlt : Module.rank (Localization.AtPrime m.asIdeal)
      (LocalizedModule m.asIdeal.primeCompl C) < Cardinal.aleph0 :=
    lt_of_not_ge hC
  let L := Localization.AtPrime m.asIdeal
  let S := m.asIdeal.primeCompl
  let projC : (R × P) →ₗ[R] C := C.projectionOnto K hKC.symm
  letI : Module.Projective R C := Module.Projective.of_split C.subtype projC (by
    apply LinearMap.ext
    intro c
    exact C.projectionOnto_apply_left hKC.symm c)
  letI : Module.Projective L (LocalizedModule S C) := inferInstance
  letI : Module.Free L (LocalizedModule S C) :=
    Formalization.Books.Algebra.Unit85.projective_free_over_local_ring
      (R := L) (P := LocalizedModule S C) inferInstance
  letI : Module.Finite L (LocalizedModule S C) :=
    Module.rank_lt_aleph0_iff.mp hlt
  letI : Module.Finite L (LocalizedModule S K) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S K)
  let eProd : LocalizedModule S (K × C) ≃ₗ[L]
      LocalizedModule S K × LocalizedModule S C :=
    IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (K × C))
      ((LocalizedModule.mkLinearMap S K).prodMap
        (LocalizedModule.mkLinearMap S C)) |>.extendScalarsOfIsLocalization S L
  letI : Module.Finite L (LocalizedModule S (K × C)) :=
    Module.Finite.equiv eProd.symm
  let eKC : (K × C) ≃ₗ[R] (R × P) :=
    Submodule.prodEquivOfIsCompl K C hKC
  let eLoc : LocalizedModule S (K × C) ≃ₗ[L]
      LocalizedModule S (R × P) :=
    IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S (K × C))
      (LocalizedModule.mkLinearMap S (R × P)) L eKC
  letI : Module.Finite L (LocalizedModule S (R × P)) :=
    Module.Finite.equiv eLoc
  exact (not_lt_of_ge (bass_hasInfinite_product (F := R) hP m))
    (Module.rank_lt_aleph0 L (LocalizedModule S (R × P)))

set_option maxHeartbeats 1000000 in
private theorem bass_rank_one_step
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    (hP : HasInfiniteMaximalRank R P)
    (K : Submodule R (R × P)) (hKcomp : IsComplemented K)
    (hKfin : Module.Finite R K) (hKstable : Module.IsStablyFree R K)
    (s : P) (hs : (0, s) ∈ K) :
    ∃ L : Submodule R P, s ∈ L ∧ IsComplemented L ∧
      Module.Finite R L ∧ Module.IsStablyFree R L := by
  letI : Module.Finite R K := hKfin
  letI : Module.IsStablyFree R K := hKstable
  obtain ⟨C, hKC⟩ := hKcomp
  let projC : (R × P) →ₗ[R] C := C.projectionOnto K hKC.symm
  letI : Module.Projective R C := Module.Projective.of_split C.subtype projC (by
    apply LinearMap.ext
    intro c
    exact C.projectionOnto_apply_left hKC.symm c)
  have hCP : HasInfiniteMaximalRank R C :=
    bass_complement_infinite hP K C hKC
  let eKC : (K × C) ≃ₗ[R] (R × P) :=
    Submodule.prodEquivOfIsCompl K C hKC
  let π : (R × P) →ₗ[R] C :=
    (LinearMap.snd R K C).comp eKC.symm.toLinearMap
  let inrP : P →ₗ[R] (R × P) := LinearMap.inr R R P
  let t : C := π (1, 0)
  let MC : Submodule R C := LinearMap.range (π.comp inrP)
  have hπsurj : Function.Surjective π := by
    intro c
    refine ⟨eKC (0, c), ?_⟩
    simp [π, eKC]
  have hgenC : Submodule.span R ({t} : Set C) ⊔ MC = ⊤ := by
    apply top_unique
    intro c _
    obtain ⟨⟨a, p⟩, hp⟩ := hπsurj c
    have hsplit (a : R) (p : P) :
        π (a, p) = a • t + π (0, p) := by
      rw [show (a, p) = a • ((1 : R), (0 : P)) + ((0 : R), p) by ext <;> simp,
        map_add, map_smul]
    rw [← hp, hsplit]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ a
        (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton t)))
    · apply Submodule.mem_sup_right
      exact ⟨p, by simp [MC, inrP]⟩
  obtain ⟨mc, hmc, hU, ⟨eU⟩⟩ :=
    trick_to_find_good_element hR hCP t MC hgenC
  obtain ⟨p, hp⟩ := hmc
  let y : C := t + mc
  let U : Submodule R C := Submodule.span R ({y} : Set C)
  have hU' : IsComplemented U := by simpa [U, y] using hU
  have hπone : π (1, p) = y := by
    have hp' : π (0, p) = mc := by simpa [inrP] using hp
    calc
      π (1, p) = π ((1, 0) + (0, p)) := by congr 1 <;> ext <;> simp
      _ = π (1, 0) + π (0, p) := map_add π (1, 0) (0, p)
      _ = t + mc := by rw [hp']
      _ = y := rfl
  obtain ⟨C₂, hUC₂⟩ := hU'
  let proj₂ : C →ₗ[R] C₂ := C₂.projectionOnto U hUC₂.symm
  let π' : P →ₗ[R] C₂ := proj₂.comp (π.comp inrP)
  have hπ'surj : Function.Surjective π' := by
    intro z
    obtain ⟨⟨a, p₀⟩, hp₀⟩ := hπsurj (z : C)
    have hsplit (a : R) (p : P) :
        π (a, p) = a • t + π (0, p) := by
      rw [show (a, p) = a • ((1 : R), (0 : P)) + ((0 : R), p) by ext <;> simp,
        map_add, map_smul]
    have heq : (z : C) = a • y + π (0, p₀ - a • p) := by
      have hp' : π (0, p) = mc := by simpa [inrP] using hp
      rw [← hp₀, hsplit]
      dsimp [y]
      have hpairs : ((0 : R), p₀ - a • p) = ((0 : R), p₀) - a • ((0 : R), p) := by
        ext <;> simp
      have hdiff := congrArg π hpairs
      rw [map_sub, map_smul, hp'] at hdiff
      rw [hdiff]
      simp only [smul_add, smul_neg, neg_smul, neg_one_smul, one_smul]
      abel
    have hy0 : proj₂ y = 0 :=
      C₂.projectionOnto_apply_of_mem_right hUC₂.symm
        (Submodule.subset_span (Set.mem_singleton y))
    have hproj2 (z : C₂) : proj₂ (z : C) = z :=
      C₂.projectionOnto_apply_left hUC₂.symm z
    refine ⟨p₀ - a • p, ?_⟩
    change proj₂ (π (0, p₀ - a • p)) = z
    rw [← hproj2 z, heq, map_add, map_smul, hy0]
    simp
  letI : Module.Projective R C₂ := Module.Projective.of_split C₂.subtype proj₂ (by
    apply LinearMap.ext
    intro z
    exact C₂.projectionOnto_apply_left hUC₂.symm z)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    π' (LinearMap.id : C₂ →ₗ[R] C₂) hπ'surj
  let L : Submodule R P := LinearMap.ker π'
  let fL : P →ₗ[R] L :=
    (LinearMap.id - g.comp π').codRestrict L (by
      intro q
      apply LinearMap.mem_ker.mpr
      simp only [LinearMap.id_apply, LinearMap.sub_apply, LinearMap.comp_apply]
      rw [map_sub]
      have hh : π' (g (π' q)) = π' q := by
        have hh0 := congrArg (fun f : C₂ →ₗ[R] C₂ => f (π' q)) hg
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hh0
      rw [hh]
      simp)
  have hfL : ∀ z : L, fL z = z := by
    intro z
    apply Subtype.ext
    change (z : P) - g (π' z) = (z : P)
    rw [LinearMap.mem_ker.mp z.property]
    simp
  have hLcomp : IsComplemented L :=
    ⟨LinearMap.ker fL, LinearMap.isCompl_of_proj hfL⟩
  have hsL : s ∈ L := by
    apply LinearMap.mem_ker.mpr
    have hπs : π (0, s) = 0 := by
      change (eKC.symm (0, s)).2 = 0
      exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero K C hKC).mpr hs
    simp [π', inrP, hπs]
  
  let eCU : (U × C₂) ≃ₗ[R] C :=
    Submodule.prodEquivOfIsCompl U C₂ hUC₂
  let eDec : ((K × U) × C₂) ≃ₗ[R] (R × P) :=
    (LinearEquiv.prodAssoc R K U C₂).trans
      ((LinearEquiv.refl R K).prodCongr eCU) |>.trans eKC
  let inL : (R × L) →ₗ[R] (R × P) :=
    { toFun := fun z => (z.1, (z.2 : P) + z.1 • p)
      map_add' := by
        intro z z'
        ext <;> simp [add_smul, smul_add, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro r z
        ext <;> simp [smul_add, mul_smul] }
  let alpha : (R × L) →ₗ[R] K × U :=
    (LinearMap.fst R (K × U) C₂).comp
      (eDec.symm.toLinearMap.comp inL)
  have hproj2_pi (r : R) (l : L) :
      proj₂ (π (r, (l : P) + r • p)) = 0 := by
    have hsplit (a : R) (p : P) :
        π (a, p) = a • t + π (0, p) := by
      rw [show (a, p) = a • ((1 : R), (0 : P)) + ((0 : R), p) by ext <;> simp,
        map_add, map_smul]
    have hl : proj₂ (π (0, (l : P))) = 0 := by
      exact LinearMap.mem_ker.mp l.property
    have hy0 : proj₂ y = 0 :=
      C₂.projectionOnto_apply_of_mem_right hUC₂.symm
        (Submodule.subset_span (Set.mem_singleton y))
    have hp' : π (0, p) = mc := by simpa [inrP] using hp
    have hpair : π ((0, (l : P)) + r • ((0 : R), p)) =
        π (0, (l : P)) + r • π (0, p) := by
      rw [map_add, map_smul]
    rw [hsplit]
    rw [show (0, (l : P) + r • p) = (0, (l : P)) + r • ((0 : R), p) by
      ext <;> simp, hpair]
    simp only [map_add, map_smul, map_zero, hl, hp']
    rw [zero_add, ← smul_add, ← map_add, hy0]
    exact smul_zero r
  have hzero (r : R) (l : L) :
      (eDec.symm (r, (l : P) + r • p)).2 = 0 := by
    have h := hproj2_pi r l
    change (eCU.symm (π (r, (l : P) + r • p))).2 = 0
    apply (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U C₂ hUC₂).mpr
    exact (Submodule.projectionOnto_apply_eq_zero_iff hUC₂.symm).mp h
  let betaX : (K × U) →ₗ[R] (R × P) :=
    eDec.toLinearMap.comp (LinearMap.inl R (K × U) C₂)
  have hproj2_betaX (z : K × U) : proj₂ (π (betaX z)) = 0 := by
    have hz : eDec.symm (betaX z) = (z, 0) := by
      simp [betaX]
    have hz' : (eCU.symm (π (betaX z))).2 = 0 := by
      change (eDec.symm (betaX z)).2 = 0
      exact congrArg Prod.snd hz
    apply C₂.projectionOnto_apply_of_mem_right hUC₂.symm
    exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U C₂ hUC₂).mp hz'
  have hbetaL (z : K × U) :
      (betaX z).2 - (betaX z).1 • p ∈ L := by
    apply LinearMap.mem_ker.mpr
    have hsplit (a : R) (q : P) :
        π (a, q) = a • t + π (0, q) := by
      rw [show (a, q) = a • ((1 : R), (0 : P)) + ((0 : R), q) by ext <;> simp,
        map_add, map_smul]
    have hy0 : proj₂ y = 0 :=
      C₂.projectionOnto_apply_of_mem_right hUC₂.symm
        (Submodule.subset_span (Set.mem_singleton y))
    change proj₂ (π (0, (betaX z).2 - (betaX z).1 • p)) = 0
    rw [show (0, (betaX z).2 - (betaX z).1 • p) =
      (betaX z) - (betaX z).1 • ((1 : R), p) by ext <;> simp,
      map_sub, map_smul, map_sub, hproj2_betaX]
    rw [map_smul, hπone, hy0, smul_zero]
    simp
  let betaR : (K × U) →ₗ[R] R :=
    (LinearMap.fst R R P).comp betaX
  let betaP : (K × U) →ₗ[R] P :=
    (LinearMap.snd R R P).comp betaX - betaR.smulRight p
  let beta : (K × U) →ₗ[R] R × L :=
    betaR.prod (betaP.codRestrict L hbetaL)
  have hdec (x : R × L) : eDec (alpha x, 0) = inL x := by
    rw [← eDec.apply_symm_apply (inL x)]
    apply congrArg eDec
    apply Prod.ext
    · rfl
    · exact (hzero x.1 x.2).symm
  have hxβ (x : R × L) : betaX (alpha x) = inL x := by
    simpa [betaX] using hdec x
  have hβα (x : R × L) : beta (alpha x) = x := by
    apply Prod.ext
    · change (betaX (alpha x)).1 = x.1
      rw [hxβ x]
      rfl
    · apply Subtype.ext
      change (betaX (alpha x)).2 - (betaX (alpha x)).1 • p = (x.2 : P)
      rw [hxβ x]
      simp [inL]
  have hαβ (z : K × U) : alpha (beta z) = z := by
    have hz : inL (beta z) = betaX z := by
      apply Prod.ext
      · change betaR z = (betaX z).1
        rfl
      · change betaP z + betaR z • p = (betaX z).2
        simp [betaP, betaR]
    change (eDec.symm (inL (beta z))).1 = z
    rw [hz]
    simp [betaX]
  have hab : Function.Bijective alpha := by
    refine ⟨?_, ?_⟩
    · intro x x' hxx'
      have h := congrArg beta hxx'
      rw [hβα x, hβα x'] at h
      exact h
    · intro z
      exact ⟨beta z, hαβ z⟩
  let eα : (R × L) ≃ₗ[R] K × U := LinearEquiv.ofBijective alpha hab
  let eU' : R ≃ₗ[R] U := by simpa [U, y] using eU
  letI : Module.Finite R U := Module.Finite.equiv eU'
  letI : Module.Free R U := Module.Free.of_equiv eU'
  letI : Module.Finite R (K × U) := inferInstance
  letI : Module.Finite R (R × L) := Module.Finite.equiv eα.symm
  have hKUstable : Module.IsStablyFree R (K × U) := by
    obtain ⟨N, hNadd, hNmod, hNfin, hNfree, hKNfree⟩ :=
      Module.IsStablyFree.exist_free_prod R K
    letI : AddCommGroup N := hNadd
    letI : Module R N := hNmod
    letI : Module.Finite R N := hNfin
    letI : Module.Free R N := hNfree
    letI : Module.Free R (K × N) := hKNfree
    let eKU : ((K × U) × N) ≃ₗ[R] (K × N) × U :=
      ((LinearEquiv.prodAssoc R K U N).trans
        ((LinearEquiv.refl R K).prodCongr (LinearEquiv.prodComm R U N))).trans
        (LinearEquiv.prodAssoc R K N U).symm
    letI : Module.Free R ((K × U) × N) := Module.Free.of_equiv eKU.symm
    exact Module.IsStablyFree.of_free_prod R (K × U) N
  letI : Module.IsStablyFree R (K × U) := hKUstable
  have hRLstable : Module.IsStablyFree R (R × L) := by
    obtain ⟨N, hNadd, hNmod, hNfin, hNfree, hKUNfree⟩ :=
      Module.IsStablyFree.exist_free_prod R (K × U)
    letI : AddCommGroup N := hNadd
    letI : Module R N := hNmod
    letI : Module.Finite R N := hNfin
    letI : Module.Free R N := hNfree
    letI : Module.Free R ((K × U) × N) := hKUNfree
    letI : Module.Free R ((R × L) × N) := Module.Free.of_equiv
      (eα.symm.prodCongr (LinearEquiv.refl R N))
    exact Module.IsStablyFree.of_free_prod R (R × L) N
  letI : Module.IsStablyFree R (R × L) := hRLstable
  have hLfin : Module.Finite R L := by
    exact Module.Finite.of_surjective (LinearMap.snd R R L) (by
      intro l
      change ∃ x : R × L, x.2 = l
      exact ⟨(0, l), rfl⟩)
  have hLstable : Module.IsStablyFree R L := by
    obtain ⟨N, hNadd, hNmod, hNfin, hNfree, hRLNfree⟩ :=
      Module.IsStablyFree.exist_free_prod R (R × L)
    letI : AddCommGroup N := hNadd
    letI : Module R N := hNmod
    letI : Module.Finite R N := hNfin
    letI : Module.Free R N := hNfree
    letI : Module.Free R ((R × L) × N) := hRLNfree
    let eL : ((R × L) × N) ≃ₗ[R] L × (R × N) :=
      (((LinearEquiv.prodAssoc R R L N).trans
        ((LinearEquiv.refl R R).prodCongr (LinearEquiv.prodComm R L N))).trans
        (LinearEquiv.prodAssoc R R N L).symm).trans
        (LinearEquiv.prodComm R (R × N) L)
    letI : Module.Free R (L × (R × N)) := Module.Free.of_equiv eL
    exact Module.IsStablyFree.of_free_prod R L (R × N)
  exact ⟨L, hsL, hLcomp, hLfin, hLstable⟩

/-! ## Finite stably free summands -/

private theorem bass_stably_free_equiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : Module.IsStablyFree R M) (e : M ≃ₗ[R] N) :
    Module.IsStablyFree R N := by
  obtain ⟨T, hTadd, hTmod, hTfin, hTfree, hMTfree⟩ :=
    Module.IsStablyFree.exist_free_prod R M
  letI : AddCommGroup T := hTadd
  letI : Module R T := hTmod
  letI : Module.Finite R T := hTfin
  letI : Module.Free R T := hTfree
  letI : Module.Free R (M × T) := hMTfree
  letI : Module.Free R (N × T) :=
    Module.Free.of_equiv (e.prodCongr (LinearEquiv.refl R T))
  exact Module.IsStablyFree.of_free_prod R N T

private theorem bass_finite_summand
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) (n : ℕ)
    (K : Submodule R ((Fin n →₀ R) × P)) (hKcomp : IsComplemented K)
    (hKfin : Module.Finite R K) (hKstable : Module.IsStablyFree R K)
    (s : P) (hs : (0, s) ∈ K) :
    ∃ L : Submodule R P, s ∈ L ∧ IsComplemented L ∧
      Module.Finite R L ∧ Module.IsStablyFree R L := by
  induction n with
  | zero =>
      let e0 : ((Fin 0 →₀ R) × P) ≃ₗ[R] P :=
        LinearEquiv.uniqueProd (R := R) (M := P) (M₂ := (Fin 0 →₀ R))
      obtain ⟨C, hKC⟩ := hKcomp
      let fK : K →ₗ[R] P := e0.toLinearMap.comp K.subtype
      let L : Submodule R P := LinearMap.range fK
      let projK : ((Fin 0 →₀ R) × P) →ₗ[R] K := K.projectionOnto C hKC
      let projL : P →ₗ[R] L :=
        (fK.codRestrict L (by intro x; exact ⟨x, rfl⟩)).comp
          (projK.comp e0.symm.toLinearMap)
      have hprojL : ∀ z : L, projL z = z := by
        intro z
        rcases z.property with ⟨k, hk⟩
        apply Subtype.ext
        rw [← hk]
        simp [projL, fK, projK, hKC.1]
        rfl
      have hLcomp : IsComplemented L :=
        ⟨LinearMap.ker projL, LinearMap.isCompl_of_proj hprojL⟩
      have hsL : s ∈ L := by
        refine ⟨⟨(0, s), hs⟩, ?_⟩
        simp [fK, e0]
      let fK' : K →ₗ[R] L :=
        fK.codRestrict L (by intro x; exact ⟨x, rfl⟩)
      have hfK'inj : Function.Injective fK' := by
        intro x y hxy
        apply Subtype.ext
        apply e0.injective
        exact congrArg (fun z : L => (z : P)) hxy
      have hfK'surj : Function.Surjective fK' := by
        intro z
        rcases z.property with ⟨k, hk⟩
        exact ⟨k, Subtype.ext hk⟩
      let eK : K ≃ₗ[R] L := LinearEquiv.ofBijective fK' ⟨hfK'inj, hfK'surj⟩
      letI : Module.Finite R K := hKfin
      have hLfin : Module.Finite R L := Module.Finite.equiv eK
      have hLstable : Module.IsStablyFree R L :=
        bass_stably_free_equiv hKstable eK
      exact ⟨L, hsL, hLcomp, hLfin, hLstable⟩
  | succ n ih =>
      let econs : (R × (Fin n →₀ R)) ≃ₗ[R] (Fin (n + 1) →₀ R) :=
        { toFun := fun z => Finsupp.cons z.1 z.2
          invFun := fun f => (f 0, Finsupp.tail f)
          left_inv := by
            intro z
            apply Prod.ext
            · simp
            · ext i
              simp
          right_inv := by
            intro f
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          map_add' := by
            intro x y
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          map_smul' := by
            intro r x
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp }
      let eAmbient : (R × ((Fin n →₀ R) × P)) ≃ₗ[R]
          ((Fin (n + 1) →₀ R) × P) :=
        (LinearEquiv.prodAssoc R R (Fin n →₀ R) P).symm.trans
          (econs.prodCongr (LinearEquiv.refl R P))
      obtain ⟨C, hKC⟩ := hKcomp
      let K' : Submodule R (R × ((Fin n →₀ R) × P)) :=
        K.map eAmbient.symm.toLinearMap
      let C' : Submodule R (R × ((Fin n →₀ R) × P)) :=
        C.map eAmbient.symm.toLinearMap
      have hK'comp : IsComplemented K' := by
        refine ⟨C', ?_⟩
        constructor
        · exact Submodule.disjoint_map eAmbient.symm.injective hKC.disjoint
        · exact Submodule.codisjoint_map eAmbient.symm.surjective hKC.codisjoint
      have hsK' : (0, (0, s)) ∈ K' := by
        refine ⟨(0, s), hs, ?_⟩
        simp [K', eAmbient, econs]
        ext i
        simp [Finsupp.tail_apply]
      let eK : K ≃ₗ[R] K' :=
        Submodule.equivMapOfInjective eAmbient.symm.toLinearMap
          eAmbient.symm.injective K
      letI : Module.Finite R K := hKfin
      have hK'fin : Module.Finite R K' := Module.Finite.equiv eK
      have hK'stable : Module.IsStablyFree R K' :=
        bass_stably_free_equiv hKstable eK
      obtain ⟨L', hsL', hL'comp, hL'fin, hL'stable⟩ :=
        bass_rank_one_step (R := R) (P := (Fin n →₀ R) × P) hR
          (bass_hasInfinite_product (F := Fin n →₀ R) hP) K' hK'comp
          hK'fin hK'stable (0, s) hsK'
      exact ih L' hL'comp hL'fin hL'stable hsL'

/-- Every element of a projective module satisfying the Jacobson and rank
hypotheses lies in a finite stably-free direct summand. -/
theorem element_in_free_summand
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) (s : P) :
    ∃ M : Submodule R P, s ∈ M ∧ IsComplemented M ∧
      Module.Finite R M ∧ Module.IsStablyFree R M := by
  obtain ⟨n, K, hsK, hKcomp, hKfin, hKfree⟩ :=
    element_projective (R := R) (P := P) s
  letI : Module.Free R K := hKfree
  exact bass_finite_summand hR hP n K hKcomp hKfin
    (inferInstance : Module.IsStablyFree R K) s hsK

/-! ## Countably generated projective modules -/

/-- A countably generated projective module of infinite rank at every maximal
localization is free. -/
theorem countable_free
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hPgen : Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated R P)
    (hP : HasInfiniteMaximalRank R P) :
    Module.Free R P := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit129
