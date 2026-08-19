/-
# More on Algebra, Chapter 129: Big projective modules are free
-/

import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs

namespace Formalization.Books.MoreAlgebra.Unit129

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

/-! ## Finding a unimodular element -/

/-- If `s` together with a submodule `M` generates `P`, one can adjust `s` by
an element of `M` to obtain a rank-one free direct summand. -/
 -/
theorem trick_to_find_good_element
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) (s : P) (M : Submodule R P)
    (hgen : Submodule.span R ({s} : Set P) ⊔ M = ⊤) :
    ∃ m : P, m ∈ M ∧
      IsComplemented (Submodule.span R ({s + m} : Set P)) ∧
        Nonempty (R ≃ₗ[R] Submodule.span R ({s + m} : Set P)) := by
  sorry

/-! ## Finite stably free summands -/

/-- Every element of a projective module satisfying the Jacobson and rank
hypotheses lies in a finite stably-free direct summand. -/
theorem element_in_free_summand
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) (s : P) :
    ∃ M : Submodule R P, s ∈ M ∧ IsComplemented M ∧
      Module.Finite R M ∧ Module.IsStablyFree R M := by
  sorry

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
