import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType

/-!
# Commutative Algebra, Chapter 6: Ring maps of finite type and of finite presentation

The source's two finiteness notions are represented by Mathlib's canonical
`RingHom.FiniteType` and `RingHom.FinitePresentation` predicates.  Polynomial
rings in the source are represented by `MvPolynomial (Fin n) R`, and finitely
generated ideals by `Ideal.FG`.
-/

namespace Formalization.Books.Algebra.Unit06

universe u v w

/-! ## Finite type and finite presentation -/

/- The definition of finite type is `RingHom.FiniteType f`: the target is a
   finitely generated algebra over the source.  The definition of finite
   presentation is `RingHom.FinitePresentation f`: the target is a finitely
   presented algebra over the source.  These are the source definitions, so
   no parallel predicates are introduced here. -/

/-! ## Composition and change of base -/

/-- Finite type ring maps are stable under composition. -/
theorem finiteType_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.FiniteType f) (hg : RingHom.FiniteType g) :
    RingHom.FiniteType (g.comp f) := by
  exact RingHom.FiniteType.comp hg hf

/- The source's finite-presentation composition assertion. -/
/-- Finitely presented ring maps are stable under composition. -/
theorem finitePresentation_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.FinitePresentation f)
    (hg : RingHom.FinitePresentation g) :
    RingHom.FinitePresentation (g.comp f) := by
  exact RingHom.FinitePresentation.comp hg hf

/- The source's third assertion says that a factor of a finite-type composite
   is finite type.  This is the standard `of_comp_finiteType` interface. -/
/-- If a composite is of finite type, then its second map is of finite type. -/
theorem finiteType_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (h : RingHom.FiniteType (g.comp f)) :
    RingHom.FiniteType g := by
  exact RingHom.FiniteType.of_comp_finiteType h

/- The source's fourth assertion is the finite-presentation version of the
   preceding factor statement. -/
/-- If the composite is finitely presented and the first map is of finite type,
then the second map is finitely presented. -/
theorem finitePresentation_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hcomp : RingHom.FinitePresentation (g.comp f))
    (hf : RingHom.FiniteType f) :
    RingHom.FinitePresentation g := by
  exact RingHom.FinitePresentation.of_comp_finiteType f hcomp hf

/-! ## Independence of a finite presentation -/

/- In the source, `R[x₁, ..., xₙ]` is the finite-variable polynomial ring
   `MvPolynomial (Fin n) R`. -/
/-- A surjection from a finite-variable polynomial ring onto a finitely
presented algebra has finitely generated kernel. -/
theorem finitePresentation_kernel_fg_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hS : RingHom.FinitePresentation f) (n : ℕ)
    (α : letI : Algebra R S := f.toAlgebra
      MvPolynomial (Fin n) R →ₐ[R] S)
    (hα : Function.Surjective α) :
    letI : Algebra R S := f.toAlgebra
    (RingHom.ker α.toRingHom).FG := by
  let hfp : @Algebra.FinitePresentation R S _ _ f.toAlgebra := hS
  exact @Algebra.FinitePresentation.ker_fG_of_surjective
    R (MvPolynomial (Fin n) R) S _ _ inferInstance _ f.toAlgebra α hα _ hfp

/-! ## Finitely presented modules over a finite-type subring -/

/- The R-module structure in the source is the one induced by the ring map.
   The `letI` binders make that choice explicit and prevent an unrelated
   pre-existing R-module structure from being used. -/

private theorem moduleFinitePresentation_of_finiteType_aux
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hS : Algebra.FiniteType R S)
    (hM : Module.FinitePresentation R M) :
    Module.FinitePresentation S M := by
  classical
  obtain ⟨s, hs, hk⟩ := hM.out
  obtain ⟨t, ht⟩ := hS.out
  obtain ⟨v, hv⟩ := hk
  let pR : (s →₀ R) →ₗ[R] M :=
    Finsupp.linearCombination R ((↑) : s → M)
  let pS : (s →₀ S) →ₗ[S] M :=
    Finsupp.linearCombination S ((↑) : s → M)
  have hpR : Function.Surjective pR := by
    change Function.Surjective (Finsupp.linearCombination R ((↑) : s → M))
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination,
      Subtype.range_val, hs]
  let coeffMap : (s →₀ R) →ₗ[R] (s →₀ S) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap R S)
  have hp_coeff (y : s →₀ R) : pS (coeffMap y) = pR y := by
    simp [pS, pR, coeffMap, Finsupp.linearCombination_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.sum_mapRange_index]
  choose ys hys using fun a : t => fun j : s => hpR ((a : S) • (j : M))
  let relations : Finset (s →₀ S) :=
    (t.attach.product s.attach).image
      (fun q => Finsupp.single q.2 (q.1 : S) - coeffMap (ys q.1 q.2))
  let generators : Finset (s →₀ S) := v.image coeffMap ∪ relations
  let K : Submodule S (s →₀ S) := Submodule.span S (generators : Set (s →₀ S))
  have hKker : K ≤ LinearMap.ker pS := by
    apply Submodule.span_le.2
    intro z hz
    simp only [generators, Finset.mem_coe, Finset.mem_union] at hz
    rcases hz with hz | hz
    · rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
      change pS (coeffMap y) = 0
      rw [hp_coeff]
      exact LinearMap.mem_ker.mp (by rw [← hv]; exact Submodule.subset_span hy)
    · rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
      change pS (Finsupp.single q.2 (q.1 : S) - coeffMap (ys q.1 q.2)) = 0
      rw [map_sub, hp_coeff]
      simp [pS, hys]
  let Q := (s →₀ S) ⧸ K
  let q : (s →₀ S) →ₗ[S] Q := K.mkQ
  let basis : s → Q := fun j => q (Finsupp.single j (1 : S))
  let aLin : (s →₀ R) →ₗ[R] Q := Finsupp.linearCombination R basis
  let W : Submodule R Q := LinearMap.range aLin
  have hWspan : W = Submodule.span R (Set.range basis) := by
    simpa [W, aLin] using
      (Finsupp.range_linearCombination (R := R) (v := basis))
  have hq_coeff_map : (q.restrictScalars R).comp coeffMap = aLin := by
    apply Finsupp.lhom_ext
    intro j r
    simp only [LinearMap.comp_apply, aLin, Finsupp.linearCombination_single,
      basis, coeffMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
    calc
      q (Finsupp.single j ((algebraMap R S) r)) =
          q ((algebraMap R S r) • Finsupp.single j (1 : S)) := by
            congr 1
            simp [Algebra.smul_def]
      _ = (algebraMap R S r) • q (Finsupp.single j (1 : S)) := q.map_smul _ _
      _ = r • q (Finsupp.single j (1 : S)) := IsScalarTower.algebraMap_smul S r _
  have hq_coeff (y : s →₀ R) : q (coeffMap y) = aLin y := by
    exact LinearMap.congr_fun hq_coeff_map y
  have hgen (a : t) (j : s) : (a : S) • basis j ∈ W := by
    have hrel : Finsupp.single j (a : S) - coeffMap (ys a j) ∈ K := by
      apply Submodule.subset_span
      simp only [generators, Finset.mem_coe, Finset.mem_union]
      exact Or.inr (by
        simp only [relations, Finset.mem_image]
        exact ⟨(a, j), Finset.mem_product.mpr
          ⟨Finset.mem_attach t a, Finset.mem_attach s j⟩, rfl⟩)
    have hqeq : q (Finsupp.single j (a : S)) = q (coeffMap (ys a j)) := by
      apply sub_eq_zero.mp
      rw [← q.map_sub]
      exact (Submodule.Quotient.mk_eq_zero K).mpr hrel
    rw [show (a : S) • basis j = q (Finsupp.single j (a : S)) by
        simp [basis, ← q.map_smul],
      hqeq, hq_coeff]
    exact ⟨ys a j, rfl⟩
  have hstable_gen (a : t) : ∀ z, z ∈ W → (a : S) • z ∈ W := by
    intro z hz
    rw [hWspan] at hz ⊢
    induction hz using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨j, rfl⟩
        simpa [hWspan] using hgen a j
    | zero => simp
    | add x y _ _ hx hy =>
        rw [smul_add]
        exact add_mem hx hy
    | smul r x _ hx =>
        rw [smul_comm]
        exact Submodule.smul_mem _ r hx
  have hstable (a : S) : ∀ z, z ∈ W → a • z ∈ W := by
    have ha : a ∈ Algebra.adjoin R (t : Set S) := by
      rw [ht]
      exact Algebra.mem_top
    refine Algebra.adjoin_induction
      (p := fun a _ => ∀ z, z ∈ W → a • z ∈ W) ?_ ?_ ?_ ?_ ha
    · intro a ha z hz
      exact hstable_gen ⟨a, ha⟩ z hz
    · intro r z hz
      simpa [Algebra.smul_def] using W.smul_mem r hz
    · intro x y hx hy ihx ihy z hz
      rw [add_smul]
      exact add_mem (ihx z hz) (ihy z hz)
    · intro x y hx hy ihx ihy z hz
      rw [mul_smul]
      exact ihx (y • z) (ihy z hz)
  have hWtop : W = (⊤ : Submodule R Q) := by
    apply top_unique
    intro z hz
    obtain ⟨x, rfl⟩ := K.mkQ_surjective z
    rw [← Finsupp.sum_single x]
    rw [Finsupp.sum, map_sum]
    apply W.sum_mem
    intro j hj
    have hbW : basis j ∈ W := by
      rw [hWspan]
      exact Submodule.subset_span (Set.mem_range_self j)
    change q (Finsupp.single j (x j)) ∈ W
    have hsingle : q (Finsupp.single j (x j)) = (x j) • basis j := by
      calc
        q (Finsupp.single j (x j)) =
            q ((x j) • Finsupp.single j (1 : S)) := by
              congr 1
              simp
        _ = (x j) • q (Finsupp.single j (1 : S)) := q.map_smul _ _
        _ = (x j) • basis j := rfl
    rw [hsingle]
    exact hstable (x j) (basis j) hbW
  have hmap :
      Submodule.map coeffMap (Submodule.span R (v : Set (s →₀ R))) ≤ K.restrictScalars R := by
    rw [Submodule.map_span]
    apply Submodule.span_le.2
    intro y hy
    change y ∈ K
    rcases hy with ⟨x, hx, rfl⟩
    apply Submodule.subset_span
    simp only [generators, Finset.mem_coe, Finset.mem_union, Finset.mem_image]
    exact Or.inl ⟨x, hx, rfl⟩
  have hker : LinearMap.ker pS ≤ K := by
    intro x hx
    have hxW : q x ∈ W := by
      rw [hWtop]
      exact Submodule.mem_top
    obtain ⟨y, hy⟩ := hxW
    have hqeq : q x = q (coeffMap y) := by
      rw [← hy, hq_coeff]
    have hmem : x - coeffMap y ∈ K := by
      have hzero : q (x - coeffMap y) = 0 := by
        rw [q.map_sub, hqeq, sub_self]
      have hqker : x - coeffMap y ∈ LinearMap.ker q := LinearMap.mem_ker.mpr hzero
      change x - coeffMap y ∈ (K.mkQ).ker at hqker
      rw [Submodule.ker_mkQ] at hqker
      exact hqker
    have hpy : pR y = 0 := by
      have hzero : pS (x - coeffMap y) = 0 :=
        LinearMap.mem_ker.mp (hKker hmem)
      rw [map_sub, hp_coeff] at hzero
      rw [LinearMap.mem_ker.mp hx] at hzero
      simpa using hzero
    have hyspan : y ∈ Submodule.span R (v : Set (s →₀ R)) := by
      rw [hv]
      exact hpy
    have hcoeff : coeffMap y ∈ K := hmap ⟨y, hyspan, rfl⟩
    have := K.add_mem hmem hcoeff
    simpa [sub_add_cancel] using this
  have hsS : Submodule.span S (s : Set M) = ⊤ :=
    Submodule.span_eq_top_of_span_eq_top R S (s : Set M) hs
  refine ⟨s, hsS, ?_⟩
  have hEq : LinearMap.ker pS = K := le_antisymm hker hKker
  rw [hEq]
  exact ⟨generators, rfl⟩

/-- An S-module finitely presented over R remains finitely presented over S when
the map R → S is of finite type. -/
theorem finitePresentation_module_over_finiteType
    {R S M : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) [AddCommGroup M] [Module S M]
    (hS : RingHom.FiniteType f)
    (hM : letI : Module R M := Module.compHom M f
      Module.FinitePresentation R M) :
    letI : Module R M := Module.compHom M f
    Module.FinitePresentation S M := by
  let alg : Algebra R S := f.toAlgebra
  let modR : Module R M := Module.compHom M f
  let tower : @IsScalarTower R S M alg.toSMul (inferInstance : SMul S M) modR.toSMul :=
    IsScalarTower.of_algebraMap_smul (fun r m => rfl)
  let hS' : @Algebra.FiniteType R S _ _ alg := hS
  let hM' : @Module.FinitePresentation R M _ _ modR := hM
  exact @moduleFinitePresentation_of_finiteType_aux
    R S M _ _ alg _ modR _ tower hS' hM'

end Formalization.Books.Algebra.Unit06
