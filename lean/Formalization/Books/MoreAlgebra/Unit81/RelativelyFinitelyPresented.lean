import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.BaseChange
import Formalization.Books.Algebra.Unit06.FiniteType
import Formalization.Books.Algebra.Unit14.BaseChange

/-!
# More on Algebra, Chapter 81: Relatively finitely presented modules

The source section is formalized using Mathlib's canonical finiteness
predicates.  A presentation by `R[x₁, ..., xₙ]` is represented by a
surjective map from `MvPolynomial (Fin n) R`, and the induced module action is
made explicit with `Module.compHom`.
-/

namespace Formalization.Books.MoreAlgebra.Unit81

open scoped TensorProduct

noncomputable section

universe u v w

/-! ## The relative finite-presentation predicate -/

/--
An `A`-module is finitely presented relative to the ring map `f : R →+* A`
when it is finitely presented after restricting scalars along one finite
polynomial presentation of `A` over `R`.

This is condition (1) of the source lemma; the later equivalence theorem
records the source's conditions (2) and (3).
-/
def RelativelyFinitelyPresented
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)
    (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  letI : Algebra R A := f.toAlgebra
  ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
    Function.Surjective α ∧
      letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
      Module.FinitePresentation (MvPolynomial (Fin n) R) M

private theorem moduleFinitePresentation_of_surjective
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (q : R →+* S) (hq : Function.Surjective q)
    (hM : letI : Module R M := Module.compHom M q
      Module.FinitePresentation R M) :
    Module.FinitePresentation S M := by
  let : Module R M := Module.compHom M q
  obtain ⟨s, hs, hker⟩ := hM.out
  let fR : (s →₀ R) →ₗ[R] M := Finsupp.linearCombination R ((↑) : s → M)
  let fS : (s →₀ S) →ₗ[S] M := Finsupp.linearCombination S ((↑) : s → M)
  have hfR : Function.Surjective fR := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa using hs
  let fRq : (s →₀ R) →ₛₗ[q] M :=
    { toFun := fR
      map_add' := fR.map_add
      map_smul' := by
        intro r x
        exact fR.map_smul r x }
  let map : (s →₀ R) →ₛₗ[q] (s →₀ S) :=
    Finsupp.mapRange.linearMap q.toSemilinearMap
  have hmap : Function.Surjective map := by
    intro x
    obtain ⟨y, hy⟩ := Finsupp.mapRange_surjective q q.map_zero hq x
    exact ⟨y, by simpa [map] using hy⟩
  have hcomm : fS.comp map = fRq := by
    ext x
    simp [fR, fS, map, fRq, Finsupp.linearCombination_apply]
  have hkerR : (LinearMap.ker fR).FG := by
    simpa [fR] using hker
  let mapKer : LinearMap.ker fR →ₛₗ[q] LinearMap.ker fS :=
    { toFun := fun x =>
        ⟨map x, by
          change (fS.comp map) x = 0
          rw [hcomm]
          exact x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map.map_add x y
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact map.map_smul' r x }
  have hmapKer : Function.Surjective mapKer := by
    intro x
    obtain ⟨y, hy⟩ := hmap x
    have hyker : fRq y = 0 := by
      rw [← hcomm]
      change fS (map y) = 0
      rw [hy]
      exact x.property
    exact ⟨⟨y, by exact hyker⟩, Subtype.ext hy⟩
  let : Module.Finite R (LinearMap.ker fR) := Module.Finite.of_fg hkerR
  have hkerSfin : Module.Finite S (LinearMap.ker fS) :=
    Module.Finite.of_surjective mapKer hmapKer
  have hkerS : (LinearMap.ker fS).FG := Module.Finite.iff_fg.mp hkerSfin
  have hfS : Function.Surjective fS := by
    intro x
    obtain ⟨y, hy⟩ := hfR x
    refine ⟨map y, ?_⟩
    change (fS.comp map) y = x
    rw [hcomm]
    simpa [fRq] using hy
  exact Module.finitePresentation_of_surjective fS hfS hkerS

private theorem moduleFinitePresentation_of_surjective_of_fg_ker
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (q : R →+* S) (hq : Function.Surjective q)
    (hker : (RingHom.ker q).FG) (hM : Module.FinitePresentation S M) :
    letI : Module R M := Module.compHom M q
    Module.FinitePresentation R M := by
  let : Algebra R S := q.toAlgebra
  let : Module R M := Module.compHom M q
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨s, hs, hs'⟩ := hM.out
  let fR : (s →₀ R) →ₗ[R] M := Finsupp.linearCombination R ((↑) : s → M)
  let fS : (s →₀ S) →ₗ[S] M := Finsupp.linearCombination S ((↑) : s → M)
  let map : (s →₀ R) →ₗ[R] (s →₀ S) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap R S)
  have hmap : Function.Surjective map := by
    have hq' : Function.Surjective (Algebra.linearMap R S) := by
      intro x
      obtain ⟨y, hy⟩ := hq x
      refine ⟨y, ?_⟩
      change q y = x
      exact hy
    intro x
    obtain ⟨y, hy⟩ := Finsupp.mapRange_surjective
      (Algebra.linearMap R S) (Algebra.linearMap R S).map_zero hq' x
    exact ⟨y, by simpa [map] using hy⟩
  have hcomm : (fS.restrictScalars R).comp map = fR := by
    ext x
    simp [fR, fS, map, Finsupp.linearCombination_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.sum_mapRange_index]
  have hker_map : (LinearMap.ker map).FG := by
    dsimp [map]
    rw [Finsupp.ker_mapRange]
    rw [Finsupp.submodule_eq_iSup]
    apply Submodule.fg_iSup
    intro i
    exact Submodule.FG.map (Finsupp.lsingle i) hker
  have hkerS : (LinearMap.ker (fS.restrictScalars R)).FG := by
    let N : Submodule S (s →₀ S) := LinearMap.ker fS
    have hN : (N.restrictScalars R).FG :=
      Submodule.FG.restrictScalars_of_surjective hs' hq
    simpa [N] using hN
  have hmapker : (LinearMap.ker fR).map map =
      LinearMap.ker (fS.restrictScalars R) := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hxy := LinearMap.congr_fun hcomm x
      calc
        (fS.restrictScalars R) (map x) = fR x := hxy
        _ = 0 := hx
    · intro y hy
      obtain ⟨x, hx⟩ := hmap y
      refine ⟨x, ?_, hx⟩
      have hxy := LinearMap.congr_fun hcomm x
      calc
        fR x = (fS.restrictScalars R) (map x) := hxy.symm
        _ = (fS.restrictScalars R) y := by rw [hx]
        _ = 0 := hy
  have hker_le : LinearMap.ker map ≤ LinearMap.ker fR := by
    intro x hx
    have hxy := LinearMap.congr_fun hcomm x
    change map x = 0 at hx
    calc
      fR x = (fS.restrictScalars R) (map x) := hxy.symm
      _ = 0 := by simpa using congrArg (fS.restrictScalars R) hx
  have hkerR : (LinearMap.ker fR).FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker map
    · rw [hmapker]
      exact hkerS
    · rw [inf_of_le_right hker_le]
      exact hker_map
  have hfS : Function.Surjective fS := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa using hs
  have hfR : Function.Surjective fR := by
    intro m
    obtain ⟨x, hx⟩ := hfS m
    obtain ⟨y, hy⟩ := hmap x
    refine ⟨y, ?_⟩
    have hxy := LinearMap.congr_fun hcomm y
    calc
      fR y = (fS.restrictScalars R) (map y) := hxy.symm
      _ = fS x := by rw [hy]; rfl
      _ = m := hx
  refine ⟨s, ?_, hkerR⟩
  have hrange : LinearMap.range fR = ⊤ := LinearMap.range_eq_top.mpr hfR
  simpa [fR, Finsupp.range_linearCombination] using hrange

private theorem moduleFinitePresentation_of_finite
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (q : R →+* S) (hfinite : RingHom.Finite q)
    (hM : letI : Module R M := Module.compHom M q
      Module.FinitePresentation R M) :
    Module.FinitePresentation S M := by
  let : Algebra R S := q.toAlgebra
  letI : Module.Finite R S := hfinite
  let : Module R M := Module.compHom M q
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : Module.FinitePresentation R M := hM
  let fS : (s : Finset M) → (s →₀ S) →ₗ[S] M :=
    fun s => Finsupp.linearCombination S ((↑) : s → M)
  let fR : (s : Finset M) → (s →₀ S) →ₗ[R] M :=
    fun s => (fS s).restrictScalars R
  obtain ⟨s, hs, _⟩ := hM
  have hsurjR : Function.Surjective
      (Finsupp.linearCombination R ((↑) : s → M)) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa using hs
  have hsurj : Function.Surjective (fR s) := by
    intro m
    obtain ⟨x, hx⟩ := hsurjR m
    let y : s →₀ S := x.mapRange (algebraMap R S) (by simp)
    refine ⟨y, ?_⟩
    change Finsupp.linearCombination S ((↑) : s → M) y = m
    simp only [Finsupp.linearCombination_apply, y]
    rw [Finsupp.sum_mapRange_index (fun _ => by simp)]
    simpa only [Finsupp.linearCombination_apply, algebraMap_smul] using hx
  have hkerR : (LinearMap.ker (fR s)).FG := by
    apply Module.FinitePresentation.fg_ker (fR s)
    · exact hsurj
  have hkerS : (LinearMap.ker (fS s)).FG := by
    apply Submodule.FG.of_restrictScalars R
    simpa [fR] using hkerR
  apply Module.finitePresentation_of_surjective (fS s)
  · exact hsurj
  · exact hkerS

private theorem moduleFinitePresentation_finite_iff
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (q : R →+* S)
    (hfinite : RingHom.Finite q) (hfp : RingHom.FinitePresentation q) :
    (letI : Module R M := Module.compHom M q;
      Module.FinitePresentation R M) ↔
      Module.FinitePresentation S M := by
  let : Algebra R S := q.toAlgebra
  letI : Module.Finite R S := hfinite
  let : Module R M := Module.compHom M q
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  constructor
  · intro hM
    exact moduleFinitePresentation_of_finite q hfinite hM
  · intro hM
    letI : Algebra.FinitePresentation R S := hfp
    letI : Module.FinitePresentation R S :=
      Module.FinitePresentation.of_finite_of_finitePresentation R S
    exact Module.FinitePresentation.trans R M S

/-- The counterexample in the introduction: finite presentation over the
quotient does not imply finite presentation over the original polynomial
ring. -/
theorem intro_counterexample
    {k : Type u} [Field k] :
    let R := MvPolynomial ℕ k
    let I : Ideal R := Ideal.span (Set.range (MvPolynomial.X : ℕ → R))
    let q : R →+* (R ⧸ I) := Ideal.Quotient.mk I
    RingHom.Finite q ∧
      RingHom.FiniteType (RingHom.id R) ∧
        RingHom.FiniteType q ∧
          Module.Finite (R ⧸ I) (R ⧸ I) ∧
            Module.FinitePresentation (R ⧸ I) (R ⧸ I) ∧
              ¬ (letI : Module R (R ⧸ I) := Module.compHom (R ⧸ I) q
                Module.FinitePresentation R (R ⧸ I)) := by
  let R := MvPolynomial ℕ k
  let I : Ideal R := Ideal.span (Set.range (MvPolynomial.X : ℕ → R))
  let q : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  change RingHom.Finite q ∧ RingHom.FiniteType (RingHom.id R) ∧
    RingHom.FiniteType q ∧ Module.Finite (R ⧸ I) (R ⧸ I) ∧
      Module.FinitePresentation (R ⧸ I) (R ⧸ I) ∧
        ¬ (letI : Module R (R ⧸ I) := Module.compHom (R ⧸ I) q
          Module.FinitePresentation R (R ⧸ I))
  refine ⟨?_, RingHom.FiniteType.id _, RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective,
    inferInstance, inferInstance, ?_⟩
  · exact Module.Finite.of_surjective
      (Module.compHom.toLinearMap (Ideal.Quotient.mk _))
      Ideal.Quotient.mk_surjective
  · intro h
    let : Module R (R ⧸ I) := Module.compHom (R ⧸ I) q
    let l : R →ₗ[R] (R ⧸ I) := Module.compHom.toLinearMap q
    let : Module.FinitePresentation R (R ⧸ I) := h
    have hker : (LinearMap.ker l).FG :=
      Module.FinitePresentation.fg_ker l q.surjective
    have hI : I.FG := by
      have heq : LinearMap.ker l = I := by
        ext x
        change q x = 0 ↔ x ∈ I
        exact Ideal.Quotient.eq_zero_iff_mem
      rw [← heq]
      exact hker
    obtain ⟨S, hS⟩ := hI
    have hT : (⋃ p : (S : Set R), (p.1.vars : Set ℕ)).Finite := by
      exact Set.finite_iUnion fun p => p.1.vars.finite_toSet
    have hne : (⋃ p : (S : Set R), (p.1.vars : Set ℕ)) ≠ Set.univ := by
      intro htop
      have : (Set.univ : Set ℕ).Finite := by simpa [← htop] using hT
      exact (Set.not_finite.mpr (Set.infinite_univ (α := ℕ))) this
    obtain ⟨n, hn⟩ :=
      (Set.ne_univ_iff_exists_notMem _).mp hne
    let ev0 : R →ₐ[k] k := MvPolynomial.aeval (fun _ : ℕ => 0)
    have hI0 : I ≤ RingHom.ker ev0.toRingHom := by
      change Ideal.span (Set.range (MvPolynomial.X : ℕ → R)) ≤ RingHom.ker ev0.toRingHom
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change MvPolynomial.aeval (fun _ : ℕ => 0) (MvPolynomial.X i) = 0
      simp
    have hS0 : ∀ p : S, ev0 p.1 = 0 := by
      intro p
      have hpI : p.1 ∈ I := by
        rw [← hS]
        exact Ideal.subset_span p.2
      exact hI0 hpI
    have hconst : ∀ p : S, MvPolynomial.constantCoeff p.1 = 0 := by
      intro p
      have heval : ev0 p.1 = algebraMap k k (MvPolynomial.constantCoeff p.1) := by
        change MvPolynomial.aeval (fun _ : ℕ => 0) p.1 =
          algebraMap k k (MvPolynomial.constantCoeff p.1)
        exact MvPolynomial.aeval_eq_constantCoeff_of_vars
          (g := fun _ : ℕ => 0) (p := p.1) (by simp)
      rw [hS0 p] at heval
      simpa using heval.symm
    let evn : R →ₐ[k] k :=
      MvPolynomial.aeval (fun i : ℕ => if i = n then 1 else 0)
    have hSn : ∀ p : S, evn p.1 = 0 := by
      intro p
      have heval : evn p.1 = algebraMap k k (MvPolynomial.constantCoeff p.1) := by
        apply MvPolynomial.aeval_eq_constantCoeff_of_vars
        intro i hi
        by_cases hin : i = n
        · exfalso
          apply hn
          rw [← hin]
          exact Set.mem_iUnion.mpr ⟨p, hi⟩
        · simp [hin]
      rw [hconst p] at heval
      simpa using heval
    have hspan : Ideal.span (S : Set R) ≤ RingHom.ker evn.toRingHom := by
      rw [Ideal.span_le]
      intro p hp
      exact hSn ⟨p, hp⟩
    have hX : MvPolynomial.X n ∈ Ideal.span (S : Set R) := by
      rw [hS]
      exact Ideal.subset_span ⟨n, rfl⟩
    have hz : evn (MvPolynomial.X n) = 0 := hspan hX
    change MvPolynomial.aeval (fun i : ℕ => if i = n then 1 else 0)
      (MvPolynomial.X n) = 0 at hz
    rw [MvPolynomial.aeval_X] at hz
    simp at hz

/-! ## The three equivalent presentations -/

/-- Relative finite presentation is independent of the chosen polynomial
presentation of the finite-type algebra. -/
theorem relativelyFinitelyPresented_iff_all_presentations
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) :
    letI : Algebra R A := f.toAlgebra
    RelativelyFinitelyPresented f M ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α →
          letI : Module (MvPolynomial (Fin n) R) M :=
            Module.compHom M α.toRingHom
          Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  let : Algebra R A := f.toAlgebra
  dsimp [RelativelyFinitelyPresented]
  constructor
  · rintro ⟨n, α, hα, hM⟩ m β hβ
    let C := MvPolynomial (Fin n ⊕ Fin m) R
    let pToC : MvPolynomial (Fin n) R →ₐ[R] C :=
      MvPolynomial.aeval (fun i => (MvPolynomial.X (Sum.inl i) : C))
    let qToC : MvPolynomial (Fin m) R →ₐ[R] C :=
      MvPolynomial.aeval (fun i => (MvPolynomial.X (Sum.inr i) : C))
    let lift : Fin n → MvPolynomial (Fin m) R :=
      fun i => Classical.choose (hβ (α (MvPolynomial.X i)))
    have hlift (i : Fin n) : β (lift i) = α (MvPolynomial.X i) :=
      Classical.choose_spec (hβ (α (MvPolynomial.X i)))
    let cToQ : C →ₐ[R] MvPolynomial (Fin m) R :=
      MvPolynomial.aeval (Sum.elim lift MvPolynomial.X)
    let cToA : C →ₐ[R] A := β.comp cToQ
    have hcq : cToQ.comp qToC = AlgHom.id R _ := by
      apply MvPolynomial.algHom_ext
      intro i
      change cToQ (qToC (MvPolynomial.X i)) = MvPolynomial.X i
      change cToQ (MvPolynomial.aeval
        (fun i => (MvPolynomial.X (Sum.inr i) : C)) (MvPolynomial.X i)) =
        MvPolynomial.X i
      rw [MvPolynomial.aeval_X]
      change MvPolynomial.aeval (Sum.elim lift MvPolynomial.X)
        (MvPolynomial.X (Sum.inr i)) = MvPolynomial.X i
      rw [MvPolynomial.aeval_X]
      rfl
    have hcq_surj : Function.Surjective cToQ := by
      intro x
      refine ⟨qToC x, ?_⟩
      exact AlgHom.congr_fun hcq x
    have hpcA : cToA.comp pToC = α := by
      apply MvPolynomial.algHom_ext
      intro i
      have hpC : pToC (MvPolynomial.X i) = MvPolynomial.X (Sum.inl i) := by
        change MvPolynomial.aeval (fun i => (MvPolynomial.X (Sum.inl i) : C))
          (MvPolynomial.X i) = MvPolynomial.X (Sum.inl i)
        rw [MvPolynomial.aeval_X]
      have hcA' : cToA (MvPolynomial.X (Sum.inl i)) = α (MvPolynomial.X i) := by
        change β (cToQ (MvPolynomial.X (Sum.inl i))) = α (MvPolynomial.X i)
        have hcQ : cToQ (MvPolynomial.X (Sum.inl i)) = lift i := by
          change MvPolynomial.aeval (Sum.elim lift MvPolynomial.X)
            (MvPolynomial.X (Sum.inl i)) = lift i
          rw [MvPolynomial.aeval_X]
          rfl
        rw [hcQ]
        exact hlift i
      have hcase : cToA (pToC (MvPolynomial.X i)) = α (MvPolynomial.X i) := by
        rw [hpC, hcA']
      simpa only [AlgHom.comp_apply] using hcase
    have hpC : RingHom.FiniteType pToC.toRingHom := by
      let : Algebra (MvPolynomial (Fin n) R) C := pToC.toAlgebra
      let : IsScalarTower R (MvPolynomial (Fin n) R) C :=
        IsScalarTower.of_algebraMap_eq' (by
          apply RingHom.ext
          intro r
          exact (pToC.commutes r).symm)
      change Algebra.FiniteType (MvPolynomial (Fin n) R) C
      exact Algebra.FiniteType.of_restrictScalars_finiteType R _ _
    let : Module C M := Module.compHom M cToA.toRingHom
    let modP : Module (MvPolynomial (Fin n) R) M :=
      Module.compHom M pToC.toRingHom
    let modPα : Module (MvPolynomial (Fin n) R) M :=
      Module.compHom M α.toRingHom
    have hmodP : modP = modPα := by
      apply Module.ext' _ _
      intro r x
      change cToA (pToC r) • x = α r • x
      rw [show cToA (pToC r) = α r from congrArg (fun g => g r) hpcA]
    let : Module (MvPolynomial (Fin n) R) M := modP
    have hpcM : @Module.FinitePresentation (MvPolynomial (Fin n) R) M _ _ modP := by
      rw [hmodP]
      exact hM
    have hC : Module.FinitePresentation C M :=
      Formalization.Books.Algebra.Unit06.finitePresentation_module_over_finiteType
        pToC.toRingHom hpC hpcM
    let : Module (MvPolynomial (Fin m) R) M :=
      Module.compHom M β.toRingHom
    exact moduleFinitePresentation_of_surjective cToQ.toRingHom hcq_surj (by
      exact hC)
  · intro hAll
    obtain ⟨n, α, hα⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hf
    exact ⟨n, α, hα, hAll n α hα⟩

/-- The quotient-algebra formulation of relative finite presentation. -/
theorem relativelyFinitelyPresented_iff_surjective_from_finitelyPresented
    {R : Type u} {A : Type v} {M : Type w} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) :
    letI : Algebra R A := f.toAlgebra
    RelativelyFinitelyPresented f M ↔
      ∀ {A' : Type u} [CommRing A'] [Algebra R A']
        (q : A' →ₐ[R] A),
        Function.Surjective q →
          RingHom.FinitePresentation (algebraMap R A') →
            letI : Module A' M := Module.compHom M q.toRingHom
            Module.FinitePresentation A' M := by
  let : Algebra R A := f.toAlgebra
  dsimp [RelativelyFinitelyPresented]
  constructor
  · intro hrel A' _ _ q hq hfp
    have hfp' : Algebra.FinitePresentation R A' :=
      (RingHom.finitePresentation_algebraMap).mp hfp
    obtain ⟨n', β, hβ, _⟩ := hfp'.out
    let β' : MvPolynomial (Fin n') R →ₐ[R] A' := β
    have hβ' : Function.Surjective β' := by
      simpa [β'] using hβ
    have hcomp : Function.Surjective (q.comp β') := by
      exact hq.comp hβ'
    let : Module A' M := Module.compHom M q.toRingHom
    have hall :=
      (relativelyFinitelyPresented_iff_all_presentations f hf).mp hrel
        n' (q.comp β') hcomp
    let modPcomp : Module (MvPolynomial (Fin n') R) M :=
      Module.compHom M (q.comp β').toRingHom
    let modPβ : Module (MvPolynomial (Fin n') R) M :=
      Module.compHom M β'.toRingHom
    have hmodP : modPcomp = modPβ := by
      apply Module.ext' _ _
      intro r x
      change q (β' r) • x = q (β' r) • x
      rfl
    let : Module (MvPolynomial (Fin n') R) M := modPβ
    have hall' : @Module.FinitePresentation
        (MvPolynomial (Fin n') R) M _ _ modPβ := by
      rw [← hmodP]
      exact hall
    exact moduleFinitePresentation_of_surjective β'.toRingHom hβ' (by
      exact hall')
  · intro hAll
    obtain ⟨n, α, hα⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hf
    have hfp : RingHom.FinitePresentation (algebraMap R (MvPolynomial (Fin n) R)) := by
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance
    exact ⟨n, α, hα, hAll α hα hfp⟩

/-- A relatively finitely presented module is finitely presented over `A`. -/
theorem relativelyFinitelyPresented.finitePresentation
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hM : RelativelyFinitelyPresented f M) :
    Module.FinitePresentation A M := by
  let : Algebra R A := f.toAlgebra
  dsimp [RelativelyFinitelyPresented] at hM
  obtain ⟨n, α, hα, hPM⟩ := hM
  exact moduleFinitePresentation_of_surjective α.toRingHom hα hPM

/-! ## The remarks following the definition -/

/-- If `R → A` is finitely presented, relative and absolute finite
presentation of an `A`-module coincide. -/
theorem relativelyFinitelyPresented_iff_finitePresentation
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FinitePresentation f) :
    RelativelyFinitelyPresented f M ↔ Module.FinitePresentation A M := by
  let : Algebra R A := f.toAlgebra
  constructor
  · intro hM
    exact relativelyFinitelyPresented.finitePresentation f hM
  · intro hM
    have hfp : Algebra.FinitePresentation R A := hf
    obtain ⟨n, α, hα, hker⟩ := hfp.out
    refine ⟨n, α, hα, ?_⟩
    exact moduleFinitePresentation_of_surjective_of_fg_ker
      α.toRingHom hα hker hM

/-- `A` is relatively finitely presented over `R` exactly when the algebra
map `R → A` is finitely presented. -/
theorem relativelyFinitelyPresented_self_iff
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) :
    RelativelyFinitelyPresented f A ↔ RingHom.FinitePresentation f := by
  let : Algebra R A := f.toAlgebra
  constructor
  · intro hrel
    dsimp [RelativelyFinitelyPresented] at hrel
    obtain ⟨n, α, hα, hPA⟩ := hrel
    let P := MvPolynomial (Fin n) R
    let : Algebra P A := α.toAlgebra
    let : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      exact (α.commutes r).symm)
    letI : Module.FinitePresentation P A := hPA
    have hPfp : Algebra.FinitePresentation P A := inferInstance
    have hRfp : Algebra.FinitePresentation R A :=
      Algebra.FinitePresentation.trans R P A
    exact hRfp
  · intro hf
    exact (relativelyFinitelyPresented_iff_finitePresentation f hf).mpr inferInstance

/-- Over a Noetherian base, relative finite presentation reduces to finite
generation over the finite-type algebra. -/
theorem relativelyFinitelyPresented_iff_finite
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) [IsNoetherianRing R] :
    RelativelyFinitelyPresented f M ↔ Module.Finite A M := by
  let : Algebra R A := f.toAlgebra
  letI : Algebra.FiniteType R A := hf
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hfp : RingHom.FinitePresentation f :=
    (RingHom.FinitePresentation.of_finiteType).mp hf
  constructor
  · intro hrel
    letI : Module.FinitePresentation A M :=
      relativelyFinitelyPresented.finitePresentation f hrel
    infer_instance
  · intro hfinite
    apply (relativelyFinitelyPresented_iff_finitePresentation f hfp).mpr
    exact Module.finitePresentation_of_finite A M

/-! ## Stability under finite maps -/

/-- Relative finite presentation is unchanged on passing across a finite map
between finite-type `R`-algebras. -/
theorem relativelyFinitelyPresented_finite_extension_iff
    {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] (f : R →+* A) (g : A →+* B)
    (hf : RingHom.FiniteType f) (hg : RingHom.FiniteType (g.comp f))
    (hfinite : RingHom.Finite g) :
    (letI : Module A M := Module.compHom M g;
      RelativelyFinitelyPresented f M) ↔
      RelativelyFinitelyPresented (g.comp f) M := by
  let : Algebra R A := f.toAlgebra
  let : Algebra R B := (g.comp f).toAlgebra
  letI : Module A M := Module.compHom M g
  change RelativelyFinitelyPresented f M ↔
    RelativelyFinitelyPresented (g.comp f) M
  constructor
  · intro hrel
    dsimp [RelativelyFinitelyPresented] at hrel
    obtain ⟨n, α, hα, hPM⟩ := hrel
    let P := MvPolynomial (Fin n) R
    let pB : P →+* B := g.comp α.toRingHom
    let : Algebra P B := pB.toAlgebra
    have hfiniteP : RingHom.Finite pB := by
      exact RingHom.Finite.comp hfinite
        (RingHom.Finite.of_surjective α.toRingHom hα)
    letI : Module.Finite P B := hfiniteP
    letI : Module P M := Module.compHom M pB
    have hPM' : Module.FinitePresentation P M := by
      simpa [pB, P] using hPM
    obtain ⟨S, _, _, _, _, _, q, hq⟩ :=
      Module.Finite.exists_free_surjective P B
    let : Algebra R S :=
      ((algebraMap P S).comp (algebraMap R P)).toAlgebra
    let : IsScalarTower R P S :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro r
        rfl)
    let : IsScalarTower R P B :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro r
        rw [show algebraMap P B = pB from rfl]
        change (g.comp f) r = g (α (algebraMap R P r))
        rw [α.commutes]
        rfl)
    letI : Module S M := Module.compHom M q.toRingHom
    have hmap : q.toRingHom.comp (algebraMap P S) = pB := by
      apply RingHom.ext
      intro x
      change q (algebraMap P S x) = g (α x)
      rw [q.commutes]
      rfl
    have hPSM :
        (letI : Module P M := Module.compHom M (algebraMap P S);
          Module.FinitePresentation P M) := by
      have hmod : Module.compHom M
          (q.toRingHom.comp (algebraMap P S)) = Module.compHom M pB := by
        apply Module.ext'
        intro x m
        change (q.toRingHom.comp (algebraMap P S)) x • m = pB x • m
        have hx := congrArg (fun k : P →+* B => k x) hmap
        rw [hx]
      change @Module.FinitePresentation P M _ _
        (Module.compHom M (q.toRingHom.comp (algebraMap P S)))
      rw [hmod]
      exact hPM'
    have hSM : Module.FinitePresentation S M :=
      moduleFinitePresentation_of_finite (algebraMap P S) (by
        rw [RingHom.finite_algebraMap]
        infer_instance) hPSM
    let qR : S →ₐ[R] B := q.restrictScalars R
    have hmap : q.toRingHom.comp (algebraMap P S) = pB := by
      apply RingHom.ext
      intro x
      change q (algebraMap P S x) = g (α x)
      rw [q.commutes]
      rfl
    letI : Algebra.FinitePresentation R S :=
      Algebra.FinitePresentation.trans R P S
    obtain ⟨m, β, hβ, hkerβ⟩ :=
      (inferInstance : Algebra.FinitePresentation R S).out
    refine ⟨m, qR.comp β, hq.comp hβ, ?_⟩
    exact moduleFinitePresentation_of_surjective_of_fg_ker
      β.toRingHom hβ hkerβ hSM
  · intro hrel
    obtain ⟨n, α, hα⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hf
    let P := MvPolynomial (Fin n) R
    let pB : P →+* B := g.comp α.toRingHom
    let : Algebra P B := pB.toAlgebra
    have hfiniteP : RingHom.Finite pB := by
      exact RingHom.Finite.comp hfinite
        (RingHom.Finite.of_surjective α.toRingHom hα)
    letI : Module.Finite P B := hfiniteP
    obtain ⟨S, _, _, _, _, _, q, hq⟩ :=
      Module.Finite.exists_free_surjective P B
    let : Algebra R S :=
      ((algebraMap P S).comp (algebraMap R P)).toAlgebra
    let : IsScalarTower R P S :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro r
        rfl)
    let : IsScalarTower R P B :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro r
        rw [show algebraMap P B = pB from rfl]
        change (g.comp f) r = g (α (algebraMap R P r))
        rw [α.commutes]
        rfl)
    let qR : S →ₐ[R] B := q.restrictScalars R
    have hmap : q.toRingHom.comp (algebraMap P S) = pB := by
      apply RingHom.ext
      intro x
      change q (algebraMap P S x) = g (α x)
      rw [q.commutes]
      rfl
    letI : Algebra.FinitePresentation R S :=
      Algebra.FinitePresentation.trans R P S
    letI : Module S M := Module.compHom M qR.toRingHom
    have hfpRC : RingHom.FinitePresentation (algebraMap R S) := by
      rw [RingHom.finitePresentation_algebraMap]
      infer_instance
    have hSM : Module.FinitePresentation S M := by
      exact (relativelyFinitelyPresented_iff_surjective_from_finitelyPresented
        (g.comp f) hg).mp hrel qR hq hfpRC
    have hPM :
        (letI : Module P M := Module.compHom M (algebraMap P S);
          Module.FinitePresentation P M) := by
      apply (moduleFinitePresentation_finite_iff (algebraMap P S) (by
        rw [RingHom.finite_algebraMap]
        infer_instance) (by
        rw [RingHom.finitePresentation_algebraMap]
        infer_instance)).mpr hSM
    refine ⟨n, α, hα, ?_⟩
    have hmod : Module.compHom M (algebraMap P S) =
        Module.compHom M α.toRingHom := by
      apply Module.ext'
      intro x m
      change (q.toRingHom.comp (algebraMap P S)) x • m = g (α x) • m
      have hx := congrArg (fun k : P →+* B => k x) hmap
      rw [hx]
      rfl
    change @Module.FinitePresentation P M _ _ (Module.compHom M α.toRingHom)
    rw [← hmod]
    exact hPM

/-! ## Localization, base change, pullback, and composition -/

/-- Localizing an `A`-module at `g` carries relative finite presentation from
`R_f` to `R`.  The target module is Mathlib's canonical `LocalizedModule`. -/
theorem relativelyFinitelyPresented_localize
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R)
    (h : Localization.Away f →+* A)
    (hh : RingHom.FiniteType h) (g : A)
    (hM : RelativelyFinitelyPresented h M) :
    RelativelyFinitelyPresented
      (((algebraMap A (Localization.Away g)).comp h).comp
        (algebraMap R (Localization.Away f)))
      (LocalizedModule.Away g M) := by
  let Rf := Localization.Away f
  let N := Localization.Away g
  let L := LocalizedModule.Away g M
  let : Algebra R Rf := (algebraMap R Rf).toAlgebra
  let : Algebra Rf A := h.toAlgebra
  let target : R →+* N :=
    ((algebraMap A N).comp h).comp (algebraMap R Rf)
  let : Algebra R N := target.toAlgebra
  dsimp [RelativelyFinitelyPresented] at hM
  obtain ⟨n, α, hα, hPM⟩ := hM
  let : Algebra Rf (MvPolynomial (Fin n) Rf) := inferInstance
  let : Algebra (MvPolynomial (Fin n) Rf) A := α.toAlgebra
  let : IsScalarTower Rf (MvPolynomial (Fin n) Rf) A :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (α.commutes x).symm)
  let g' : MvPolynomial (Fin n) Rf := Classical.choose (hα g)
  have hg' : α g' = g := Classical.choose_spec (hα g)
  let pN : MvPolynomial (Fin n) Rf →+* N :=
    (algebraMap A N).comp α.toRingHom
  have hunit : IsUnit (pN g') := by
    change IsUnit ((algebraMap A N) (α g'))
    rw [hg']
    exact IsLocalization.Away.algebraMap_isUnit g
  let q : Localization.Away g' →+* N :=
    IsLocalization.Away.lift g' hunit
  have hqinv : q (IsLocalization.Away.invSelf g') * pN g' = 1 := by
    calc
      q (IsLocalization.Away.invSelf g') * pN g' =
          q (IsLocalization.Away.invSelf g') *
            q (algebraMap (MvPolynomial (Fin n) Rf) (Localization.Away g') g') := by
        rw [IsLocalization.Away.lift_eq]
      _ = q (IsLocalization.Away.invSelf g' *
          algebraMap (MvPolynomial (Fin n) Rf) (Localization.Away g') g') := by
        rw [q.map_mul]
      _ = 1 := by
        rw [mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  have hqinv' : q (IsLocalization.Away.invSelf g') *
      (algebraMap A N) g = 1 := by
    simpa [pN, hg'] using hqinv
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj g z
    obtain ⟨p, hp⟩ := hα a
    let x : Localization.Away g' :=
      algebraMap (MvPolynomial (Fin n) Rf) (Localization.Away g') p *
        IsLocalization.Away.invSelf g' ^ k
    refine ⟨x, ?_⟩
    apply (IsLocalization.Away.algebraMap_isUnit g).pow k |>.mul_right_cancel
    simp only [x, map_mul, IsLocalization.Away.lift_eq, map_pow]
    rw [IsLocalization.Away.lift_eq]
    change ((algebraMap A N) (α p) * q (IsLocalization.Away.invSelf g') ^ k) *
      (algebraMap A N) g ^ k = z * (algebraMap A N) g ^ k
    rw [hp, mul_assoc, ← mul_pow, hqinv', one_pow, mul_one]
    exact ha.symm
  let : Algebra (MvPolynomial (Fin n) Rf) N := pN.toAlgebra
  let : Module (MvPolynomial (Fin n) Rf) M := Module.compHom M α.toRingHom
  let : Module (MvPolynomial (Fin n) Rf) L := Module.compHom L α.toRingHom
  let : IsScalarTower (MvPolynomial (Fin n) Rf) A M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower (MvPolynomial (Fin n) Rf) A L :=
    IsScalarTower.of_compHom _ _
  let f0 : M →ₗ[A] L := LocalizedModule.mkLinearMap (.powers g) M
  let f1 : M →ₗ[MvPolynomial (Fin n) Rf] L :=
    f0.restrictScalars (MvPolynomial (Fin n) Rf)
  letI : IsLocalizedModule (.powers (α g')) f0 := by
    simpa only [hg'] using
      (inferInstance : IsLocalizedModule (.powers g) f0)
  have hloc : IsLocalizedModule (.powers g') f1 := by
    exact IsLocalizedModule.restrictScalars_powers g' f0
  let : Module (Localization.Away g') L := Module.compHom L q
  let : IsScalarTower (MvPolynomial (Fin n) Rf) (Localization.Away g') L :=
    IsScalarTower.of_algebraMap_smul (by
      intro x y
      have hx := congrArg (fun k :
          MvPolynomial (Fin n) Rf →+* N => k x)
        (IsLocalization.Away.lift_comp g' hunit)
      simpa [Module.compHom, pN, q] using
        (show (algebraMap A N) (α x) • y = α x • y by
          rw [← IsScalarTower.algebraMap_smul A N]))
  letI : Module.FinitePresentation (MvPolynomial (Fin n) Rf) M := hPM
  have hSN : Module.FinitePresentation (Localization.Away g') L := by
    apply FinitePresentation.of_isBaseChange f1
    exact IsLocalizedModule.isBaseChange _ _ f1
  let : Algebra R (MvPolynomial (Fin n) Rf) :=
    ((algebraMap Rf (MvPolynomial (Fin n) Rf)).comp (algebraMap R Rf)).toAlgebra
  let : Module R (MvPolynomial (Fin n) Rf) :=
    Module.compHom (MvPolynomial (Fin n) Rf)
      ((algebraMap Rf (MvPolynomial (Fin n) Rf)).comp (algebraMap R Rf))
  let : IsScalarTower R Rf (MvPolynomial (Fin n) Rf) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      change ((algebraMap Rf (MvPolynomial (Fin n) Rf)).comp
          (algebraMap R Rf)) r =
        ((algebraMap Rf (MvPolynomial (Fin n) Rf)).comp
          (algebraMap R Rf)) r
      rfl)
  let : IsScalarTower R (MvPolynomial (Fin n) Rf) (Localization.Away g') :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      rfl)
  letI : Algebra.FinitePresentation Rf (MvPolynomial (Fin n) Rf) := inferInstance
  letI : Algebra.FinitePresentation R Rf :=
    IsLocalization.Away.finitePresentation f
  letI : Algebra.FinitePresentation R (MvPolynomial (Fin n) Rf) :=
    Algebra.FinitePresentation.trans R Rf (MvPolynomial (Fin n) Rf)
  letI : Algebra.FinitePresentation R (Localization.Away g') :=
    Algebra.FinitePresentation.of_isLocalizationAway g'
  obtain ⟨m, β, hβ, hker⟩ :=
    (inferInstance : Algebra.FinitePresentation R (Localization.Away g')).out
  let qR : Localization.Away g' →ₐ[R] N :=
    { q with
      commutes' := by
        intro r
        change q (algebraMap R (Localization.Away g') r) =
          algebraMap R N r
        rw [← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) Rf)
          (Localization.Away g')]
        rw [IsLocalization.Away.lift_eq]
        rfl }
  dsimp [RelativelyFinitelyPresented]
  refine ⟨m, qR.comp β, hq.comp hβ, ?_⟩
  exact moduleFinitePresentation_of_surjective_of_fg_ker
    β.toRingHom hβ hker hSN

/-- Relative finite presentation is preserved by arbitrary base change.  The
module is expressed with the earlier chapter's canonical extension-of-scalars
model for the source's `M ⊗[R] R'`. -/
theorem relativelyFinitelyPresented_baseChange
    {R A R' M : Type*} [CommRing R] [CommRing A] [CommRing R']
    [AddCommGroup M] [Module A M] (f : R →+* A) (g : R →+* R')
    (hf : RingHom.FiniteType f)
    (hM : RelativelyFinitelyPresented f M) :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    letI : Algebra R' (A ⊗[R] R') :=
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).toAlgebra
    RelativelyFinitelyPresented
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
      (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g) := by
  sorry

/-- Pulling an `A`-module along a finitely presented map `A → A'` preserves
relative finite presentation. -/
theorem relativelyFinitelyPresented_pull
    {R A A' M : Type*} [CommRing R] [CommRing A] [CommRing A']
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) (g : A →+* A')
    (hg : RingHom.FinitePresentation g)
    (hM : RelativelyFinitelyPresented f M) :
    RelativelyFinitelyPresented (g.comp f)
      ((ModuleCat.extendScalars g).obj (ModuleCat.of A M) : Type _) := by
  sorry

/-- Relative finite presentation composes with a finitely presented first
map. -/
theorem relativelyFinitelyPresented_comp
    {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] (f : R →+* A) (g : A →+* B)
    (hf : RingHom.FiniteType f) (hg : RingHom.FiniteType g)
    (hfp : RingHom.FinitePresentation f)
    (hM : RelativelyFinitelyPresented g M) :
    RelativelyFinitelyPresented (g.comp f) M := by
  sorry

/-! ## Gluing and exact sequences -/

/-- Relative finite presentation is local on a finite standard-open cover of
the target algebra. -/
theorem relativelyFinitelyPresented_glue_iff
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) (s : Finset A)
    (hs : Ideal.span (s : Set A) = ⊤) :
    (∀ x : s,
      RelativelyFinitelyPresented
        ((algebraMap A (Localization.Away (x : A))).comp f)
        (LocalizedModule.Away (x : A) M)) ↔
      RelativelyFinitelyPresented f M := by
  sorry

/-- The middle term of a short exact sequence is relatively finitely
presented when the ends are. -/
theorem relativelyFinitelyPresented_middle_of_shortExact
    {R A M' M M'' : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
    [AddCommGroup M''] [Module A M''] (f : R →+* A)
    (hf : RingHom.FiniteType f) (i : M' →ₗ[A] M) (p : M →ₗ[A] M'')
    (hi : Function.Injective i) (hex : Function.Exact i p)
    (hp : Function.Surjective p)
    (hM' : RelativelyFinitelyPresented f M')
    (hM'' : RelativelyFinitelyPresented f M'') :
    RelativelyFinitelyPresented f M := by
  sorry

/-- In a short exact sequence, a relatively finitely presented middle term
and a finite left term give a relatively finitely presented quotient. -/
theorem relativelyFinitelyPresented_right_of_shortExact
    {R A M' M M'' : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
    [AddCommGroup M''] [Module A M''] (f : R →+* A)
    (hf : RingHom.FiniteType f) (i : M' →ₗ[A] M) (p : M →ₗ[A] M'')
    (hi : Function.Injective i) (hex : Function.Exact i p)
    (hp : Function.Surjective p) (hM'finite : Module.Finite A M')
    (hM : RelativelyFinitelyPresented f M) :
    RelativelyFinitelyPresented f M'' := by
  sorry

/-- Relative finite presentation passes to the two summands of a finite
direct sum. -/
theorem relativelyFinitelyPresented_of_prod
    {R A M M' : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (f : R →+* A) (hf : RingHom.FiniteType f)
    (h : RelativelyFinitelyPresented f (M × M')) :
    RelativelyFinitelyPresented f M ∧
      RelativelyFinitelyPresented f M' := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit81
