import Formalization.Books.Exercises.Unit27.Core
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Exercises, Chapter 27: statements

This file records the source-facing assertions in their chapter order.  The
canonical Mathlib constructions and the small interfaces needed for the
blowup examples live in `Core.lean`.
-/

noncomputable section

universe u v

open CategoryTheory
open TopologicalSpace
open _root_.Topology
open AlgebraicGeometry

namespace Formalization.Books.Exercises.Unit27

private def reesGradedPieces {A : Type u} [CommRing A] (I : Ideal A) (d : ℕ) :
    Submodule ℤ (blowupAlgebra I) :=
  Submodule.comap
    (((Polynomial.toFinsuppIsoLinear A).toLinearMap.restrictScalars ℤ).comp
      ((reesAlgebra I).val.toLinearMap.restrictScalars ℤ))
    ((AddMonoidAlgebra.grade A d).restrictScalars ℤ)

private lemma reesGradedPieces_mem_iff {A : Type u} [CommRing A] (I : Ideal A)
    (d : ℕ) (x : blowupAlgebra I) :
    x ∈ reesGradedPieces I d ↔
      ∃ a : A, ∃ _ha : a ∈ I ^ d, x.1 = Polynomial.monomial d a := by
  constructor
  · intro hx
    have hs : (x.1.support : Set ℕ) ⊆ ({d} : Set ℕ) := by
      exact hx
    refine ⟨x.1.coeff d, ?_, ?_⟩
    · by_cases hd : d ∈ x.1.support
      · exact x.2 d
      · have hzero : x.1.coeff d = 0 := by
          apply Classical.not_not.mp
          intro hn
          exact hd (Finsupp.mem_support_iff.mpr hn)
        rw [hzero]
        exact (I ^ d).zero_mem
    · apply Polynomial.ext
      intro n
      by_cases hnd : n = d
      · subst hnd
        simp
      · have hzero : x.1.coeff n = 0 := by
          apply Classical.not_not.mp
          intro hn
          exact hnd (hs (Finsupp.mem_support_iff.mpr hn))
        have hdn : d ≠ n := by
          intro h
          exact hnd (Eq.symm h)
        rw [Polynomial.coeff_monomial]
        simp [hzero, hnd, hdn]
  · rintro ⟨a, ha, hxa⟩
    simpa [reesGradedPieces, hxa] using
      (AddMonoidAlgebra.single_mem_grade (R := A) d a)

private def reesGradedMonoid {A : Type u} [CommRing A] (I : Ideal A) :
    SetLike.GradedMonoid (reesGradedPieces I) where
  one_mem := by
    rw [reesGradedPieces_mem_iff]
    exact ⟨1, by simp, by simp⟩
  mul_mem := by
    intro i j x y hx hy
    rw [reesGradedPieces_mem_iff] at hx hy ⊢
    rcases hx with ⟨a, ha, hxa⟩
    rcases hy with ⟨b, hb, hya⟩
    refine ⟨a * b, ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul ha hb
    · change x.1 * y.1 = _
      rw [hxa, hya]
      simp [Polynomial.monomial_mul_monomial]

private lemma polynomial_monomial_add {A : Type u} [CommRing A]
    (d : ℕ) (a b : A) :
    Polynomial.monomial d (a + b) =
      Polynomial.monomial d a + Polynomial.monomial d b := by
  apply Polynomial.ext
  intro n
  by_cases hnd : n = d
  · subst hnd
    simp
  · have hdn : d ≠ n := by
      intro h
      exact hnd h.symm
    simp [Polynomial.coeff_add, hnd, hdn]

private def reesHomogeneousComponent {A : Type u} [CommRing A] (I : Ideal A)
    (x : blowupAlgebra I) (d : ℕ) : reesGradedPieces I d :=
  ⟨reesHomogeneousElement I d (x.2 d),
    (reesGradedPieces_mem_iff I d _).2 ⟨x.1.coeff d, x.2 d, rfl⟩⟩

private def reesDecompose {A : Type u} [CommRing A] (I : Ideal A) :
    blowupAlgebra I →+ DirectSum ℕ (fun d => reesGradedPieces I d) :=
  { toFun := fun x =>
      DirectSum.mk (fun d : ℕ => reesGradedPieces I d) x.1.support
        (fun d => reesHomogeneousComponent I x d.1)
    map_zero' := by
      classical
      apply DirectSum.ext
      intro d
      rw [DirectSum.mk_apply_of_notMem (by simp)]
      rfl
    map_add' := by
      classical
      intro x y
      apply DirectSum.ext
      intro d
      by_cases hx0 : x.1.coeff d = 0
      · by_cases hy0 : y.1.coeff d = 0
        · simp [DirectSum.add_apply, DirectSum.mk, reesHomogeneousComponent,
            reesHomogeneousElement, Polynomial.coeff_add, Finsupp.mem_support_iff,
            hx0, hy0]
        · simp [DirectSum.add_apply, DirectSum.mk, reesHomogeneousComponent,
            reesHomogeneousElement, Polynomial.coeff_add, Finsupp.mem_support_iff,
            hx0, hy0]
      · by_cases hy0 : y.1.coeff d = 0
        · simp [DirectSum.add_apply, DirectSum.mk, reesHomogeneousComponent,
            reesHomogeneousElement, Polynomial.coeff_add, Finsupp.mem_support_iff,
            hx0, hy0]
        · by_cases hsum : x.1.coeff d + y.1.coeff d = 0
          · rw [DirectSum.mk_apply_of_notMem]
            · rw [DirectSum.add_apply]
              have hxmem : d ∈ x.1.support := by
                simp [Finsupp.mem_support_iff, hx0]
              have hymem : d ∈ y.1.support := by
                simp [Finsupp.mem_support_iff, hy0]
              rw [DirectSum.mk_apply_of_mem hxmem,
                DirectSum.mk_apply_of_mem hymem]
              apply Subtype.ext
              apply Subtype.ext
              change (0 : Polynomial A) =
                Polynomial.monomial d (x.1.coeff d) +
                  Polynomial.monomial d (y.1.coeff d)
              rw [← polynomial_monomial_add, hsum]
              simp
            · simp [Finsupp.mem_support_iff, hsum]
          · simp [DirectSum.add_apply, DirectSum.mk, reesHomogeneousComponent,
              reesHomogeneousElement, Polynomial.coeff_add, Finsupp.mem_support_iff,
              polynomial_monomial_add, hsum, hx0, hy0]
  }

private def reesGradedRing {A : Type u} [CommRing A] (I : Ideal A) :
    GradedRing (reesGradedPieces I) :=
  { reesGradedMonoid I with
    decompose' := reesDecompose I
    left_inv := by
      classical
      intro x
      apply Subtype.ext
      rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
      change DFinsupp.sum (reesDecompose I x)
          (fun _ z => (z : blowupAlgebra I)) = x.1
      have hsupport : (reesDecompose I x).support = x.1.support := by
        ext i
        rw [DFinsupp.mem_support_iff, Polynomial.mem_support_iff]
        change
          (DirectSum.mk (fun d : ℕ => reesGradedPieces I d) x.1.support
            (fun d : (x.1.support : Set ℕ) =>
              (reesHomogeneousComponent I x d.1 :
                reesGradedPieces I d.1)) i ≠ 0) ↔
            x.1.coeff i ≠ 0
        constructor
        · intro h
          by_contra hi
          have hi0 : x.1.coeff i = 0 := hi
          have hnot : i ∉ x.1.support := by
            intro hi'
            exact ((Finsupp.mem_support_iff).1 hi' hi0).elim
          have : (DirectSum.mk (fun d : ℕ => reesGradedPieces I d)
              x.1.support
              (fun d : (x.1.support : Set ℕ) =>
                (reesHomogeneousComponent I x d.1 : reesGradedPieces I d.1)) i) = 0 := by
            simp [DirectSum.mk, hnot]
          exact h this
        · intro h
          simp only [DirectSum.mk, DFinsupp.mk_apply,
            dif_pos (Finsupp.mem_support_iff.2 h)]
          intro hz
          apply h
          have hz' := congrArg
            (fun z : reesGradedPieces I i =>
              (z : blowupAlgebra I).1.coeff i) hz
          simpa [DirectSum.mk, h, reesHomogeneousComponent,
            reesHomogeneousElement] using hz'
      simp only [DFinsupp.sum, hsupport]
      have hsum : (∑ i ∈ x.1.support,
          ((reesDecompose I x) i : blowupAlgebra I)) = x := by
        apply Subtype.ext
        change (reesAlgebra I).val (∑ i ∈ x.1.support,
          ((reesDecompose I x) i : blowupAlgebra I)) = x.1
        rw [map_sum]
        calc
          (∑ i ∈ x.1.support,
              (reesAlgebra I).val ((reesDecompose I x) i)) =
              ∑ i ∈ x.1.support, Polynomial.monomial i (x.1.coeff i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [reesDecompose, DirectSum.mk, hi, reesHomogeneousComponent,
              reesHomogeneousElement]
          _ = x.1 := (Polynomial.as_sum_support x.1).symm
      exact congrArg Subtype.val hsum
    right_inv := by
      classical
      intro x
      induction x using DirectSum.induction_on with
      | zero =>
          apply DirectSum.ext
          intro i
          simp [reesDecompose, DirectSum.mk]
      | of i y =>
          apply DirectSum.ext
          intro j
          simp only [DirectSum.coeAddMonoidHom_of]
          change
            (DirectSum.mk (fun d : ℕ => reesGradedPieces I d) y.1.1.support
              (fun d => reesHomogeneousComponent I (y : blowupAlgebra I) d.1)) j = _
          have hy : (y : blowupAlgebra I).1 =
              Polynomial.monomial i ((y : blowupAlgebra I).1.coeff i) := by
            obtain ⟨a, ha, hya⟩ :=
              (reesGradedPieces_mem_iff I i (y : blowupAlgebra I)).1 y.property
            rw [hya]
            simp
          by_cases hij : i = j
          · subst hij
            by_cases hmem : i ∈ y.1.1.support
            · rw [DirectSum.mk_apply_of_mem hmem, DirectSum.of_eq_same]
              apply Subtype.ext
              apply Subtype.ext
              change Polynomial.monomial i ((y : blowupAlgebra I).1.coeff i) =
                (y : blowupAlgebra I).1
              exact hy.symm
            · rw [DirectSum.mk_apply_of_notMem hmem, DirectSum.of_eq_same]
              apply Subtype.ext
              apply Subtype.ext
              have hi0 : (y : blowupAlgebra I).1.coeff i = 0 := by
                by_contra hi0
                exact hmem ((Finsupp.mem_support_iff).2 hi0)
              change (0 : Polynomial A) = (y : blowupAlgebra I).1
              rw [hy, hi0]
              rw [Polynomial.monomial_zero_right]
          · by_cases hmem : j ∈ (y : blowupAlgebra I).1.support
            · have hjne : (y : blowupAlgebra I).1.coeff j ≠ 0 :=
                (Finsupp.mem_support_iff).1 hmem
              have hj0 : (y : blowupAlgebra I).1.coeff j = 0 := by
                rw [hy]
                simpa [Polynomial.coeff_monomial, hij]
              exact (hjne hj0).elim
            · rw [DirectSum.mk_apply_of_notMem hmem]
              have hji : j ≠ i := by
                intro h
                exact hij h.symm
              rw [DirectSum.of_eq_of_ne (β := fun i => reesGradedPieces I i)
                i j y hji]
      | add x y hx hy =>
          simp only [map_add, hx, hy] }

variable {R : Type u} [CommRing R]

/-! ## 27.1. Homogeneous ideals -/

theorem homogeneousIdeal_iff_homogeneous_generators
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (I : Ideal R) :
    IsHomogeneousIdeal 𝒜 I ↔
      ∃ S : Set (SetLike.homogeneousSubmonoid 𝒜),
        I = Ideal.span ((↑) '' S) := by
  simpa using (Ideal.IsHomogeneous.iff_exists (𝒜 := 𝒜) (I := I))
theorem homogeneousIdeal_iff_components
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (I : Ideal R) :
    IsHomogeneousIdeal 𝒜 I ↔
      ∀ r, r ∈ I → ∀ n, GradedRing.proj 𝒜 n r ∈ I := by
  constructor
  · intro h r hr n
    exact h.mem_iff.mp hr n
  · intro h
    change Ideal.IsHomogeneous 𝒜 I
    rw [Ideal.isHomogeneous_iff_forall_subset]
    intro n r hr
    exact h r hr n
theorem homogeneousIdeal_components_mem_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {I : Ideal R} (hI : IsHomogeneousIdeal 𝒜 I) (r : R) :
    r ∈ I ↔ ∀ n, GradedRing.proj 𝒜 n r ∈ I := by
  simpa only [GradedRing.proj_apply] using hI.mem_iff
theorem projToPrimeSpectrum_injective
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    Function.Injective (projToPrimeSpectrum 𝒜) := by
  intro x y h
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  simpa only [projToPrimeSpectrum] using congrArg PrimeSpectrum.asIdeal h
theorem projToPrimeSpectrum_inducing
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsInducing (projToPrimeSpectrum 𝒜) := by
  refine ⟨TopologicalSpace.ext_isClosed fun Z ↦ ?_⟩
  rw [isClosed_induced_iff, ProjectiveSpectrum.isClosed_iff_zeroLocus]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨PrimeSpectrum.zeroLocus s, ?_, ?_⟩
    · exact (PrimeSpectrum.isClosed_iff_zeroLocus _).2 ⟨s, rfl⟩
    ext x
    rfl
  · rintro ⟨t, ht, h⟩
    obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).1 ht
    exact ⟨s, h.symm⟩
theorem projToPrimeSpectrum_isEmbedding
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsEmbedding (projToPrimeSpectrum 𝒜) :=
  ⟨projToPrimeSpectrum_inducing 𝒜, projToPrimeSpectrum_injective 𝒜⟩
theorem mem_dPlus_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (f : R) (x : ProjPoints 𝒜) :
    x ∈ dPlus 𝒜 f ↔ f ∉ x.asHomogeneousIdeal := by rfl
theorem mem_vPlus_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) (x : ProjPoints 𝒜) :
    x ∈ vPlus 𝒜 I ↔ (I : Set R) ⊆ x.asHomogeneousIdeal := by rfl
theorem isOpen_dPlus
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (f : R) :
    IsOpen (dPlus 𝒜 f) := by
  exact ProjectiveSpectrum.isOpen_basicOpen (𝒜 := 𝒜)
theorem isOpen_dPlus_of_positive_homogeneous
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {m : ℕ} {f : R} (_hf : f ∈ 𝒜 m) (_hm : 0 < m) :
    IsOpen (dPlus 𝒜 f) := by
  exact ProjectiveSpectrum.isOpen_basicOpen (𝒜 := 𝒜)
theorem dPlus_mul
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (f f' : R) :
    dPlus 𝒜 (f * f') = dPlus 𝒜 f ∩ dPlus 𝒜 f' := by
  change (ProjectiveSpectrum.basicOpen 𝒜 (f * f') : Set (ProjectiveSpectrum 𝒜)) =
    (ProjectiveSpectrum.basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜)) ∩
      (ProjectiveSpectrum.basicOpen 𝒜 f' : Set (ProjectiveSpectrum 𝒜))
  rw [ProjectiveSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf]
theorem dOnProj_eq_iUnion_projections
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (g : R) :
    dOnProj 𝒜 g =
      ⋃ n : ℕ, dPlus 𝒜 (GradedRing.proj 𝒜 n g) := by
  change (ProjectiveSpectrum.basicOpen 𝒜 g : Set (ProjectiveSpectrum 𝒜)) =
    ⋃ n : ℕ, (ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 n g) :
      Set (ProjectiveSpectrum 𝒜))
  rw [ProjectiveSpectrum.basicOpen_eq_union_of_projection,
    TopologicalSpace.Opens.coe_iSup]
theorem dOnProj_eq_zero_component_union_positive
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (g : R) :
    dOnProj 𝒜 g =
      dOnProj 𝒜 (GradedRing.proj 𝒜 0 g) ∪
        ⋃ n : {n : ℕ // 0 < n},
          dPlus 𝒜 (GradedRing.proj 𝒜 n.1 g) := by
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, mem_dPlus_iff]
  change g ∉ x.asHomogeneousIdeal.toIdeal ↔
    (GradedRing.proj 𝒜 0 g) ∉ x.asHomogeneousIdeal.toIdeal ∨
      ∃ n : {n : ℕ // 0 < n},
        GradedRing.proj 𝒜 n.1 g ∉ x.asHomogeneousIdeal.toIdeal
  have hx : x.asHomogeneousIdeal.toIdeal.IsHomogeneous 𝒜 :=
    x.asHomogeneousIdeal.isHomogeneous
  have hcomp : g ∈ x.asHomogeneousIdeal.toIdeal ↔
      ∀ n : ℕ, GradedRing.proj 𝒜 n g ∈ x.asHomogeneousIdeal.toIdeal := by
    simpa only [GradedRing.proj_apply] using hx.mem_iff
  constructor
  · intro hg
    by_cases h0 : GradedRing.proj 𝒜 0 g ∈ x.asHomogeneousIdeal.toIdeal
    · right
      by_contra hnone
      apply hg
      apply hcomp.mpr
      intro n
      cases n with
      | zero => exact h0
      | succ n =>
          by_contra hn
          exact hnone ⟨⟨n + 1, Nat.zero_lt_succ n⟩, hn⟩
    · exact Or.inl h0
  · rintro (h0 | ⟨n, hn⟩) hg
    · apply h0
      exact (hcomp.mp hg) 0
    · have hnm : GradedRing.proj 𝒜 n.1 g ∈ x.asHomogeneousIdeal.toIdeal :=
        (hcomp.mp hg) n.1
      exact hn hnm
theorem dOnProj_degree_zero_eq_iUnion_mul
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {g : R} (_hg : g ∈ 𝒜 0) {ι : Type v} (f : ι → R)
    (_hf : ∀ i, ∃ n : ℕ, 0 < n ∧ f i ∈ 𝒜 n)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range f)) :
    dOnProj 𝒜 g = ⋃ i, dPlus 𝒜 (g * f i) := by
  ext x
  simp only [Set.mem_iUnion, mem_dPlus_iff]
  change g ∉ x.asHomogeneousIdeal.toIdeal ↔
    ∃ i, g * f i ∉ x.asHomogeneousIdeal.toIdeal
  have hex : ∃ i, f i ∉ x.asHomogeneousIdeal.toIdeal := by
    by_contra h
    have hfi : ∀ i, f i ∈ x.asHomogeneousIdeal.toIdeal := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    apply x.not_irrelevant_le
    intro y hy
    have hy' : y ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := hy
    have hyspan : y ∈ Ideal.span (Set.range f) := hspan hy'
    have hspanP : Ideal.span (Set.range f) ≤ x.asHomogeneousIdeal.toIdeal := by
      apply Ideal.span_le.2
      rintro _ ⟨i, rfl⟩
      exact hfi i
    exact hspanP hyspan
  constructor
  · intro hg
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    intro hprod
    exact (x.isPrime.2 hprod).elim hg hi
  · rintro ⟨i, hi⟩ hg
    apply hi
    exact x.asHomogeneousIdeal.toIdeal.mul_mem_right (f i) hg
theorem dPlus_isTopologicalBasis
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsTopologicalBasis
      {U : Set (ProjPoints 𝒜) |
        ∃ (n : ℕ) (_hn : 0 < n) (f : R), f ∈ 𝒜 n ∧ U = dPlus 𝒜 f} := by
  let B : Set (Set (ProjPoints 𝒜)) :=
    Set.range (fun x : Σ n : {n : ℕ // 0 < n}, 𝒜 n.1 => dPlus 𝒜 (x.2 : R))
  have hB : IsTopologicalBasis B := by
    apply TopologicalSpace.IsTopologicalBasis.isTopologicalBasis_of_exists_subset
      (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜)
    · rintro _ ⟨x, rfl⟩
      exact isOpen_dPlus_of_positive_homogeneous 𝒜 x.2.2 x.1.2
    · rintro U ⟨g, rfl⟩ p hp
      change g ∉ p.asHomogeneousIdeal.toIdeal at hp
      have hp' : p ∈ dOnProj 𝒜 g := hp
      rw [dOnProj_eq_zero_component_union_positive] at hp'
      simp only [Set.mem_union, Set.mem_iUnion] at hp'
      rcases hp' with hp0 | ⟨i, hi⟩
      · have hp0' : p ∈ dOnProj 𝒜 (GradedRing.proj 𝒜 0 g) := hp0
        let ι : Type u := Σ n : {n : ℕ // 0 < n}, 𝒜 n.1
        let f : ι → R := fun x => x.2
        have hf : ∀ x, ∃ n : ℕ, 0 < n ∧ f x ∈ 𝒜 n := by
          intro x
          exact ⟨x.1.1, x.1.2, x.2.2⟩
        have hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
            Ideal.span (Set.range f) := by
          rw [HomogeneousIdeal.toIdeal_irrelevant_le]
          intro n hn y hy
          apply Ideal.subset_span
          exact ⟨⟨⟨n, hn⟩, ⟨y, hy⟩⟩, rfl⟩
        rw [dOnProj_degree_zero_eq_iUnion_mul (𝒜 := 𝒜)
          (g := GradedRing.proj 𝒜 0 g) (SetLike.coe_mem _)
          f hf hspan] at hp0'
        simp only [Set.mem_iUnion] at hp0'
        obtain ⟨x, hx⟩ := hp0'
        have hproj0 : GradedRing.proj 𝒜 0 g ∈ 𝒜 0 := SetLike.coe_mem _
        let y : Σ n : {n : ℕ // 0 < n}, 𝒜 n.1 :=
          ⟨x.1, ⟨GradedRing.proj 𝒜 0 g * (x.2 : R),
            by
              convert SetLike.mul_mem_graded hproj0 x.2.2 using 1
              simp⟩⟩
        refine ⟨dPlus 𝒜 (y.2 : R), ⟨y, rfl⟩, ?_, ?_⟩
        · simpa [y, f] using hx
        · intro q hq
          change g ∉ q.asHomogeneousIdeal.toIdeal
          intro hg
          apply hq
          exact q.asHomogeneousIdeal.toIdeal.mul_mem_right (x.2 : R)
            ((q.asHomogeneousIdeal.isHomogeneous.mem_iff.mp hg) 0)
      · let x : Σ n : {n : ℕ // 0 < n}, 𝒜 n.1 :=
          ⟨i, ⟨GradedRing.proj 𝒜 i.1 g, SetLike.coe_mem _⟩⟩
        refine ⟨dPlus 𝒜 (x.2 : R), ⟨x, rfl⟩, hi, ?_⟩
        intro q hq
        change g ∉ q.asHomogeneousIdeal.toIdeal
        intro hg
        apply hq
        exact (q.asHomogeneousIdeal.isHomogeneous.mem_iff.mp hg) i.1
  have hEq : B =
      {U : Set (ProjPoints 𝒜) |
        ∃ (n : ℕ) (_hn : 0 < n) (f : R), f ∈ 𝒜 n ∧ U = dPlus 𝒜 f} := by
    ext U
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1.1, x.1.2, x.2, x.2.2, rfl⟩
    · rintro ⟨n, hn, f, hf, rfl⟩
      exact ⟨⟨⟨n, hn⟩, ⟨f, hf⟩⟩, rfl⟩
  rw [← hEq]
  exact hB
noncomputable def dPlusHomeomorph
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {m : ℕ} {f : R} (_hf : f ∈ 𝒜 m) (_hm : 0 < m) :
    {x : ProjPoints 𝒜 // x ∈ dPlus 𝒜 f} ≃ₜ
      PrimeSpectrum (degreeZeroLocalization 𝒜 f) :=
  TopCat.homeoOfIso
    (AlgebraicGeometry.projIsoSpecTopComponent _hf _hm)

theorem dPlus_chart_bijective
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {m : ℕ} {f : R} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Bijective (dPlusHomeomorph 𝒜 hf hm) := by
  exact (dPlusHomeomorph 𝒜 hf hm).bijective
abbrev InfinitePolynomialGrading (k : Type u) [CommRing k] :
    ℕ → Submodule k (MvPolynomial ℕ k) :=
  MvPolynomial.homogeneousSubmodule ℕ k

noncomputable def infinitePolynomialProj (k : Type u) [CommRing k] : Type u :=
  letI : GradedAlgebra (InfinitePolynomialGrading k) := MvPolynomial.gradedAlgebra
  ProjectiveSpectrum (InfinitePolynomialGrading k)

private theorem infinitePolynomialProj_not_quasiCompact_aux (k : Type u) [Field k]
    [GradedAlgebra (InfinitePolynomialGrading k)] :
    ¬ CompactSpace (ProjectiveSpectrum (InfinitePolynomialGrading k)) := by
  have hcover :
      (Set.univ : Set (ProjectiveSpectrum (InfinitePolynomialGrading k))) =
        ⋃ i : ℕ, (ProjectiveSpectrum.basicOpen (InfinitePolynomialGrading k)
          (MvPolynomial.X i : MvPolynomial ℕ k) :
            Set (ProjectiveSpectrum (InfinitePolynomialGrading k))) := by
    ext x
    constructor
    · intro _
      by_contra hx
      have hX : ∀ i : ℕ, MvPolynomial.X i ∈ x.asHomogeneousIdeal := by
        intro i
        by_contra hi
        apply hx
        exact Set.mem_iUnion.mpr ⟨i,
          (ProjectiveSpectrum.mem_basicOpen (InfinitePolynomialGrading k)
            (MvPolynomial.X i) x).2 hi⟩
      apply x.not_irrelevant_le
      rw [HomogeneousIdeal.irrelevant_le]
      intro n hn y hy
      have hyspan : y ∈
          Ideal.span (MvPolynomial.X '' (Set.univ : Set ℕ)) := by
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        have hhom : MvPolynomial.IsHomogeneous y n :=
          (MvPolynomial.mem_homogeneousSubmodule n y).mp hy
        have hmne : m ≠ 0 := by
          intro hmzero
          have hdeg := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hhom hm
          have : n = 0 := by simpa [hmzero] using hdeg
          exact (Nat.ne_of_gt hn) this
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hmne
        exact ⟨i, Set.mem_univ i, Finsupp.mem_support_iff.mp hi⟩
      apply (Ideal.span_le.2 ?_) hyspan
      rintro _ ⟨i, -, rfl⟩
      exact hX i
    · intro _
      exact Set.mem_univ _
  intro hcompact
  have hfinite : ∃ t : Finset ℕ,
      (Set.univ : Set (ProjectiveSpectrum (InfinitePolynomialGrading k))) ⊆
        ⋃ i ∈ t, (ProjectiveSpectrum.basicOpen (InfinitePolynomialGrading k)
          (MvPolynomial.X i) : Set (ProjectiveSpectrum (InfinitePolynomialGrading k))) := by
    exact (@isCompact_univ _ _ hcompact).elim_finite_subcover
      (fun i : ℕ => (ProjectiveSpectrum.basicOpen (InfinitePolynomialGrading k)
        (MvPolynomial.X i) : Set (ProjectiveSpectrum (InfinitePolynomialGrading k))))
      (fun i => ProjectiveSpectrum.isOpen_basicOpen (InfinitePolynomialGrading k))
      (by rw [hcover])
  obtain ⟨t, ht⟩ := hfinite
  obtain ⟨j, hj⟩ := t.exists_notMem
  let J : Ideal (MvPolynomial ℕ k) :=
    Ideal.span (MvPolynomial.X '' (t : Set ℕ))
  have hdisj : Disjoint (J : Set (MvPolynomial ℕ k))
      (Submonoid.powers (MvPolynomial.X j : MvPolynomial ℕ k) : Set (MvPolynomial ℕ k)) := by
    refine Set.disjoint_right.mpr ?_
    intro q hq hqpow
    rcases (Submonoid.mem_powers_iff q (MvPolynomial.X j : MvPolynomial ℕ k)).mp hq with
      ⟨n, rfl⟩
    change MvPolynomial.X j ^ n ∈
      Ideal.span (MvPolynomial.X '' (t : Set ℕ)) at hqpow
    rw [MvPolynomial.mem_ideal_span_X_image] at hqpow
    have hqpow' : ∃ i ∈ t, ¬ (Finsupp.single j n) i = 0 := by
      simpa [MvPolynomial.support_X_pow] using hqpow
    rcases hqpow' with ⟨i, hi, hsingle⟩
    exact hj ((Finsupp.single_apply_ne_zero.mp hsingle).1 ▸ hi)
  obtain ⟨p, hp, hJp, hpdisj⟩ :=
    Ideal.exists_le_prime_disjoint (I := J)
      (Submonoid.powers (MvPolynomial.X j : MvPolynomial ℕ k)) hdisj
  let Q : HomogeneousIdeal (InfinitePolynomialGrading k) :=
    p.homogeneousCore (InfinitePolynomialGrading k)
  have hQp : Q.toIdeal.IsPrime := hp.homogeneousCore
  have hQJ : ∀ i ∈ t, MvPolynomial.X i ∈ Q := by
    intro i hi
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    · exact ⟨1, (MvPolynomial.mem_homogeneousSubmodule 1 _).2
        (MvPolynomial.isHomogeneous_X k i)⟩
    · exact hJp (Ideal.subset_span ⟨i, hi, rfl⟩)
  have hQj : MvPolynomial.X j ∉ Q := by
    intro h
    exact Set.disjoint_left.mp hpdisj
      (Ideal.toIdeal_homogeneousCore_le (InfinitePolynomialGrading k) p h)
      (Submonoid.mem_powers _)
  let x : ProjectiveSpectrum (InfinitePolynomialGrading k) :=
    ⟨Q, hQp, by
      intro hIr
      apply hQj
      exact hIr (HomogeneousIdeal.mem_irrelevant_of_mem (InfinitePolynomialGrading k)
        (by simp : 0 < (1 : ℕ))
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).2
          (MvPolynomial.isHomogeneous_X k j)))⟩
  have hxcover := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion] at hxcover
  rcases hxcover with ⟨i, hi, hxi⟩
  exact (ProjectiveSpectrum.mem_basicOpen (InfinitePolynomialGrading k)
    (MvPolynomial.X i) x).1 hxi
    (hQJ i hi)
theorem infinitePolynomialProj_not_quasiCompact (k : Type u) [Field k] :
    letI : GradedAlgebra (InfinitePolynomialGrading k) := MvPolynomial.gradedAlgebra
    ¬ CompactSpace (ProjectiveSpectrum (InfinitePolynomialGrading k)) := by
  exact @infinitePolynomialProj_not_quasiCompact_aux k _ MvPolynomial.gradedAlgebra
theorem exists_homogeneousIdeal_eq_vPlus
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (T : Set (ProjPoints 𝒜)) (hT : IsClosed T) :
    ∃ I : HomogeneousIdeal 𝒜, T = vPlus 𝒜 I := by
  refine ⟨ProjectiveSpectrum.vanishingIdeal T, ?_⟩
  change T = ProjectiveSpectrum.zeroLocus 𝒜
    (ProjectiveSpectrum.vanishingIdeal T : Set R)
  rw [ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hT.closure_eq]
noncomputable def projToSpecZeroPointMap
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    ProjPoints 𝒜 → PrimeSpectrum (𝒜 0) :=
  (projToSpecZeroScheme 𝒜).base

theorem projToSpecZeroPointMap_continuous
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    Continuous (projToSpecZeroPointMap 𝒜) := by
  exact (projToSpecZeroScheme 𝒜).continuous
abbrev oneVariablePolynomialRing (A : Type u) [CommRing A] :=
  MvPolynomial (Fin 1) A

noncomputable def oneVariablePolynomialEquiv (A : Type u) [CommRing A] :
    oneVariablePolynomialRing A ≃ₐ[A] Polynomial A :=
  MvPolynomial.uniqueAlgEquiv A (Fin 1)

abbrev oneVariablePolynomialGrading (A : Type u) [CommRing A] :
    ℕ → Submodule A (oneVariablePolynomialRing A) :=
  MvPolynomial.homogeneousSubmodule (Fin 1) A

theorem oneVariableDegreeZeroEquiv_exists (A : Type u) [CommRing A] :
    Nonempty {
      e : (oneVariablePolynomialGrading A 0) ≃+* A //
      ∀ a : A,
          ((e.symm a : oneVariablePolynomialGrading A 0) :
              oneVariablePolynomialRing A) = MvPolynomial.C a } := by
  let φ : oneVariablePolynomialGrading A 0 →+* A :=
    { toFun := fun p => MvPolynomial.constantCoeff (p : oneVariablePolynomialRing A)
      map_one' := by simp
      map_mul' := by intro p q; simp
      map_zero' := by simp
      map_add' := by intro p q; simp }
  have hzero (p : oneVariablePolynomialGrading A 0) :
      (p : oneVariablePolynomialRing A) = MvPolynomial.C (φ p) := by
    have hp : MvPolynomial.IsHomogeneous
        (p : oneVariablePolynomialRing A) 0 := p.property
    have hdeg : (p : oneVariablePolynomialRing A).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 1)).mpr hp
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg]
    congr 1
  have hφ : Function.Bijective φ := by
    constructor
    · intro p q hpq
      apply Subtype.ext
      rw [hzero p, hzero q, hpq]
    · intro a
      refine ⟨⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin 1) a⟩, ?_⟩
      simp [φ]
  let e : (oneVariablePolynomialGrading A 0) ≃+* A := RingEquiv.ofBijective φ hφ
  refine ⟨⟨e, ?_⟩⟩
  intro a
  rw [hzero (e.symm a)]
  change MvPolynomial.C (φ (e.symm a)) = MvPolynomial.C a
  have hea : φ (e.symm a) = a := e.apply_symm_apply a
  rw [hea]
noncomputable def oneVariableDegreeZeroEquivData (A : Type u) [CommRing A] :
    {e : (oneVariablePolynomialGrading A 0) ≃+* A //
      ∀ a : A,
        ((e.symm a : oneVariablePolynomialGrading A 0) :
            oneVariablePolynomialRing A) = MvPolynomial.C a} :=
  Classical.choice (oneVariableDegreeZeroEquiv_exists A)

noncomputable def oneVariableDegreeZeroEquiv (A : Type u) [CommRing A] :
    (oneVariablePolynomialGrading A 0) ≃+* A :=
  (oneVariableDegreeZeroEquivData A).1

private lemma oneVariable_adjoin_X (A : Type u) [CommRing A] :
    Algebra.adjoin (oneVariablePolynomialGrading A 0)
        ({MvPolynomial.X 0} : Set (oneVariablePolynomialRing A)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
      change (algebraMap (oneVariablePolynomialGrading A 0)
        (oneVariablePolynomialRing A) ⟨MvPolynomial.C a,
          MvPolynomial.isHomogeneous_C _ _⟩) ∈ _
      exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq =>
      exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
      apply Subalgebra.mul_mem _ hp
      exact Algebra.subset_adjoin (by simpa using congrArg MvPolynomial.X (Fin.eq_zero i))

private lemma oneVariable_homogeneous_one_mem_span_X
    (A : Type u) [CommRing A] {p : oneVariablePolynomialRing A}
    (hp : p ∈ oneVariablePolynomialGrading A 1) :
    p ∈ Ideal.span ({MvPolynomial.X 0} : Set (oneVariablePolynomialRing A)) := by
  change p ∈ MvPolynomial.homogeneousSubmodule (Fin 1) A 1 at hp
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, rfl⟩
      exact Ideal.subset_span (by simpa using congrArg MvPolynomial.X (Fin.eq_zero i))
  | zero => exact (Ideal.span ({MvPolynomial.X 0} : Set (oneVariablePolynomialRing A))).zero_mem
  | add p q hp hq hpp hqq =>
      exact (Ideal.span ({MvPolynomial.X 0} : Set (oneVariablePolynomialRing A))).add_mem hpp hqq
  | smul r p hp hpp =>
      simpa [Algebra.smul_def] using
        (Ideal.mul_mem_left (Ideal.span ({MvPolynomial.X 0} : Set (oneVariablePolynomialRing A)))
          (MvPolynomial.C r) hpp)

private lemma oneVariable_irrelevant_le_span_X (A : Type u) [CommRing A]
    [GradedRing (oneVariablePolynomialGrading A)] :
    (HomogeneousIdeal.irrelevant (oneVariablePolynomialGrading A)).toIdeal ≤
      Ideal.span ({MvPolynomial.X 0} : Set (oneVariablePolynomialRing A)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  cases n with
  | zero => omega
  | succ n =>
      have hp' : p ∈
          (MvPolynomial.homogeneousSubmodule (Fin 1) A 1) ^ (n + 1) := by
        rw [MvPolynomial.homogeneousSubmodule_one_pow]
        exact hp
      rw [pow_succ] at hp'
      refine Submodule.mul_induction_on hp' ?_ ?_
      · intro q hq r hr
        exact (Ideal.span ({MvPolynomial.X 0} : Set (oneVariablePolynomialRing A))).mul_mem_left
          q (oneVariable_homogeneous_one_mem_span_X A hr)
      · intro x y hx hy
        exact (Ideal.span ({MvPolynomial.X 0} : Set (oneVariablePolynomialRing A))).add_mem hx hy

private lemma oneVariable_fromZeroRingHom_bijective (A : Type u) [CommRing A]
    [GradedRing (oneVariablePolynomialGrading A)] :
    Function.Bijective
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers (MvPolynomial.X 0))) := by
  classical
  constructor
  · intro p q hpq
    apply Subtype.ext
    have hloc := congrArg HomogeneousLocalization.val hpq
    change Localization.mk (p : oneVariablePolynomialRing A) (1 : Submonoid.powers
      (MvPolynomial.X (R := A) (σ := Fin 1) 0)) =
        Localization.mk (q : oneVariablePolynomialRing A) (1 : Submonoid.powers
          (MvPolynomial.X (R := A) (σ := Fin 1) 0)) at hloc
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hloc
    rcases hloc with ⟨c, hc⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : oneVariablePolynomialRing A)
      (MvPolynomial.X (R := A) (σ := Fin 1) 0)).mp c.property
    apply (MvPolynomial.isRegular_X_pow n).left
    simpa [← hn] using hc
  · intro z
    let v : Unit → oneVariablePolynomialRing A := fun _ => MvPolynomial.X 0
    let hf : v Unit.unit ∈ oneVariablePolynomialGrading A 1 :=
      MvPolynomial.isHomogeneous_X A 0
    have hadj : Algebra.adjoin (oneVariablePolynomialGrading A 0) (Set.range v) = ⊤ := by
      simpa [v] using oneVariable_adjoin_X A
    have hspan :
        Submodule.span (oneVariablePolynomialGrading A 0)
            { (HomogeneousLocalization.Away.mk (oneVariablePolynomialGrading A)
                hf a (∏ i : Unit, v i ^ ai i)
                (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun _ _ ↦ hf)) |
                (a : ℕ) (ai : Unit → ℕ)
                  (hai : ∑ i, ai i • 1 = a • 1) } = ⊤ := by
      exact HomogeneousLocalization.Away.span_mk_prod_pow_eq_top hf v hadj
        (fun _ : Unit ↦ 1) (fun _ ↦ hf)
    have hz : z ∈
        Submodule.span (oneVariablePolynomialGrading A 0)
            { (HomogeneousLocalization.Away.mk (oneVariablePolynomialGrading A)
                hf a (∏ i : Unit, v i ^ ai i)
                (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun _ _ ↦ hf)) |
                (a : ℕ) (ai : Unit → ℕ)
                  (hai : ∑ i, ai i • 1 = a • 1) } := by
      rw [hspan]
      trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨a, ai, hai, rfl⟩
        have hai' : ai Unit.unit = a := by simpa using hai
        refine ⟨1, ?_⟩
        apply HomogeneousLocalization.val_injective
        simp [HomogeneousLocalization.fromZeroRingHom,
          HomogeneousLocalization.Away.val_mk, v, hai']
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy hxp hyp =>
        rcases hxp with ⟨p, rfl⟩
        rcases hyp with ⟨q, rfl⟩
        exact ⟨p + q, map_add _ _ _⟩
    | smul r x hx hxp =>
        rcases hxp with ⟨p, rfl⟩
        exact ⟨r * p, by simp [Algebra.smul_def, HomogeneousLocalization.algebraMap_eq,
          HomogeneousLocalization.fromZeroRingHom]⟩

theorem oneVariableDegreeZeroEquiv_spec (A : Type u) [CommRing A] (a : A) :
    (((oneVariableDegreeZeroEquiv A).symm a : oneVariablePolynomialGrading A 0) :
        oneVariablePolynomialRing A) =
      MvPolynomial.C a := by
  exact (oneVariableDegreeZeroEquivData A).2 a
noncomputable def oneVariableProjScheme (A : Type u) [CommRing A] : Scheme :=
  letI : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  AlgebraicGeometry.«Proj» (oneVariablePolynomialGrading A)

noncomputable def oneVariableProjToSpec (A : Type u) [CommRing A] :
    oneVariableProjScheme A ⟶ Spec (CommRingCat.of A) :=
  letI : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A) ≫
    Spec.map (CommRingCat.ofHom (oneVariableDegreeZeroEquiv A).symm.toRingHom)

private theorem oneVariable_projToSpec_isHomeomorph (A : Type u) [CommRing A] :
    IsHomeomorph (oneVariableProjToSpec A).base := by
  letI : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  change IsHomeomorph
    ((AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A) ≫
      Spec.map (CommRingCat.ofHom (oneVariableDegreeZeroEquiv A).symm.toRingHom)).base)
  let f : oneVariablePolynomialRing A := MvPolynomial.X 0
  have hf : f ∈ oneVariablePolynomialGrading A 1 := MvPolynomial.isHomogeneous_X A 0
  have hirr :
      (HomogeneousIdeal.irrelevant (oneVariablePolynomialGrading A)).toIdeal ≤
        Ideal.span ({f} : Set (oneVariablePolynomialRing A)) := by
    simpa [f] using oneVariable_irrelevant_le_span_X A
  have htop : AlgebraicGeometry.Proj.basicOpen
      (oneVariablePolynomialGrading A) f = ⊤ := by
    have h := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
      (𝒜 := oneVariablePolynomialGrading A) (fun _ : Unit => f) (by
        simpa using hirr)
    simpa using h
  let hm : (0 : ℕ) < 1 := by omega
  let away := AlgebraicGeometry.Proj.awayι
      (oneVariablePolynomialGrading A) f hf hm
  have haway_range : away.opensRange = ⊤ := by
    dsimp [away]
    rw [AlgebraicGeometry.Proj.opensRange_awayι, htop]
  have haway_surj : Function.Surjective away.base := by
    intro x
    have hx : x ∈ (away.opensRange : Set _) := by
      rw [haway_range]
      trivial
    rw [Scheme.Hom.coe_opensRange] at hx
    exact hx
  letI : IsIso away :=
    (isIso_iff_isOpenImmersion_and_surjective away).2
      ⟨inferInstance, ⟨haway_surj⟩⟩
  have haway : IsHomeomorph away.base := by
    exact away.homeomorph.isHomeomorph
  have hmap0 : IsHomeomorph
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
          (Submonoid.powers f)))).base := by
    change IsHomeomorph (PrimeSpectrum.comap
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers f)))
    simpa [f] using
      (PrimeSpectrum.isHomeomorph_comap_of_bijective
        (oneVariable_fromZeroRingHom_bijective A))
  have hcomp : IsHomeomorph
      ((away ≫ AlgebraicGeometry.Proj.toSpecZero
        (oneVariablePolynomialGrading A)).base) := by
    rw [show away = AlgebraicGeometry.Proj.awayι
        (oneVariablePolynomialGrading A) f hf hm from rfl]
    rw [AlgebraicGeometry.Proj.awayι_toSpecZero]
    exact hmap0
  have hto : IsHomeomorph
      (AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A)).base := by
    apply (isHomeomorph_iff_exists_homeomorph).2
    refine ⟨haway.homeomorph.symm.trans hcomp.homeomorph, ?_⟩
    funext x
    change (AlgebraicGeometry.Proj.toSpecZero
        (oneVariablePolynomialGrading A)).base
      (away.base (haway.homeomorph.symm x)) = _
    congr 1
    exact haway.homeomorph.apply_symm_apply x
  have hmap : IsHomeomorph
      (Spec.map (CommRingCat.ofHom
        (oneVariableDegreeZeroEquiv A).symm.toRingHom)).base := by
    change IsHomeomorph (PrimeSpectrum.comap
      (oneVariableDegreeZeroEquiv A).symm.toRingHom)
    exact
      (PrimeSpectrum.homeomorphOfRingEquiv
        (oneVariableDegreeZeroEquiv A).symm).symm.isHomeomorph
  simpa only [Scheme.Hom.comp_base, TopCat.coe_comp] using IsHomeomorph.comp hmap hto

theorem oneVariableProjToSpec_bijective (A : Type u) [CommRing A] :
    Function.Bijective (oneVariableProjToSpec A).base := by
  exact (oneVariable_projToSpec_isHomeomorph A).bijective
theorem oneVariableProjToSpec_isHomeomorph (A : Type u) [CommRing A] :
    IsHomeomorph (oneVariableProjToSpec A).base := by
  simpa [oneVariableProjToSpec] using oneVariable_projToSpec_isHomeomorph A
theorem blowupBaseOpen_isOpen {A : Type u} [CommRing A] (I : Ideal A) :
    IsOpen (blowupBaseOpen I) := by
  change IsOpen ((PrimeSpectrum.zeroLocus (I : Set A))ᶜ)
  exact ((PrimeSpectrum.isClosed_iff_zeroLocus _).2 ⟨(I : Set A), rfl⟩).isOpen_compl

private lemma localizationAwayComapSubtype_isHomeomorph
    {R : Type u} [CommRing R] (r : R) :
    IsHomeomorph (fun q : PrimeSpectrum (Localization.Away r) =>
      (⟨PrimeSpectrum.comap (algebraMap R (Localization.Away r)) q,
        by
          change PrimeSpectrum.comap (algebraMap R (Localization.Away r)) q ∈
            (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
          rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
          exact ⟨q, rfl⟩⟩ :
        {p : PrimeSpectrum R // p ∈ PrimeSpectrum.basicOpen r})) := by
  apply isHomeomorph_iff_isEmbedding_surjective.2
  constructor
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding
      (Localization.Away r) r).toIsEmbedding.codRestrict _ _
  · intro p
    have hp : p.1 ∈ Set.range
        (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact p.2
    obtain ⟨q, hq⟩ := hp
    exact ⟨q, Subtype.ext hq⟩

private lemma subtypeSubtype_isHomeomorph
    {X : Type u} [TopologicalSpace X] [T0Space X] {s t : Set X} (hst : s ⊆ t) :
    IsHomeomorph (fun x : {x : X // x ∈ s} =>
      (⟨⟨x.1, hst x.2⟩, x.2⟩ : {x : {x : X // x ∈ t} // x.1 ∈ s})) := by
  apply isHomeomorph_iff_isEmbedding_surjective.2
  constructor
  · rw [isEmbedding_iff_isInducing]
    have houter : IsInducing
        (fun y : {x : X // x ∈ t} => (y.1 : X)) :=
      Topology.IsInducing.subtypeVal
    have hinner : IsInducing
        (fun x : {x : X // x ∈ s} => (x.1 : X)) :=
      Topology.IsInducing.subtypeVal
    have hcomp : IsInducing
        (fun x : {x : X // x ∈ s} =>
          ((⟨x.1, hst x.2⟩ : {x : X // x ∈ t}) : X)) := by
      simpa using hinner
    have hcontg : Continuous
        (fun x : {x : X // x ∈ s} =>
          (⟨⟨x.1, hst x.2⟩, x.2⟩ :
            {x : {x : X // x ∈ t} // x.1 ∈ s})) := by
      exact (continuous_subtype_val.subtype_mk (fun x => hst x.2)).subtype_mk
        (fun x => x.2)
    have hcomp' : IsInducing
        (fun x : {x : X // x ∈ s} =>
          (((⟨⟨x.1, hst x.2⟩, x.2⟩ :
            {x : {x : X // x ∈ t} // x.1 ∈ s}).1 : {x : X // x ∈ t}) : X)) := by
      simpa using hcomp
    have hcomp'' : IsInducing
        ((fun z : {x : {x : X // x ∈ t} // x.1 ∈ s} => (z.1.1 : X)) ∘
          (fun x : {x : X // x ∈ s} =>
          (⟨⟨x.1, hst x.2⟩, x.2⟩ :
            {x : {x : X // x ∈ t} // x.1 ∈ s}))) := by
      simpa [Function.comp_def] using hcomp'
    have houtercont : Continuous
        (fun z : {x : {x : X // x ∈ t} // x.1 ∈ s} => (z.1.1 : X)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact Topology.IsInducing.of_comp
      hcontg houtercont hcomp''
  · intro y
    exact ⟨⟨y.1.1, y.2⟩, Subtype.ext rfl⟩

private lemma homeomorphSubtypePreimage_isHomeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T0Space X]
    (e : X ≃ₜ Y) (s : Set X) :
    IsHomeomorph (fun x : {x : X // x ∈ s} =>
      (⟨e x.1, by simpa using x.2⟩ : {y : Y // e.symm y ∈ s})) := by
  apply isHomeomorph_iff_isEmbedding_surjective.2
  constructor
  · rw [isEmbedding_iff_isInducing]
    have hcomp : IsInducing
        (fun x : {x : X // x ∈ s} => e x.1) :=
      e.isInducing.comp Topology.IsInducing.subtypeVal
    have hcontg : Continuous
        (fun x : {x : X // x ∈ s} =>
          (⟨e x.1, by simpa using x.2⟩ : {y : Y // e.symm y ∈ s})) := by
      exact (e.continuous.comp continuous_subtype_val).subtype_mk
        (fun x => by simpa using x.2)
    have hcomp' : IsInducing
        (fun x : {x : X // x ∈ s} =>
          ((⟨e x.1, by simpa using x.2⟩ :
            {y : Y // e.symm y ∈ s}) : Y)) := by
      simpa using hcomp
    have houtercont : Continuous
        (fun y : {y : Y // e.symm y ∈ s} => (y.1 : Y)) :=
      continuous_subtype_val
    exact Topology.IsInducing.of_comp hcontg houtercont hcomp'
  · intro y
    exact ⟨⟨e.symm y.1, y.2⟩, by simp⟩

private lemma blowup_chart_awayMap_bijective
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} {d : ℕ} {f : blowupAlgebra I}
    (hf : f ∈ P.gradedPieces d) (hd : 0 < d) (a : A) (ha : a ∈ I ^ d)
    (hfa : f.1 = Polynomial.monomial d a) :
    (letI : GradedRing P.gradedPieces := P.graded;
      Function.Bijective
        (Localization.awayMap
          (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
            (Submonoid.powers f))
          (P.degreeZeroEquiv.symm a))) := by
  letI : GradedRing P.gradedPieces := P.graded
  let R₀ := P.gradedPieces 0
  let S := HomogeneousLocalization.Away P.gradedPieces f
  let g : R₀ →+* S :=
    HomogeneousLocalization.fromZeroRingHom P.gradedPieces (Submonoid.powers f)
  let r := P.degreeZeroEquiv.symm a
  have hr : (r : blowupAlgebra I) = algebraMap A (blowupAlgebra I) a :=
    P.degreeZeroEquiv_spec a
  have hx0 (x : R₀) : (x : blowupAlgebra I) =
      algebraMap A (blowupAlgebra I) (P.degreeZeroEquiv x) := by
    simpa using P.degreeZeroEquiv_spec (P.degreeZeroEquiv x)
  constructor
  · rw [Localization.awayMap_injective_iff]
    intro x hx
    have hxval :
        Localization.mk (x : blowupAlgebra I)
          (⟨1, one_mem _⟩ : Submonoid.powers f) = 0 := by
      have hx' := congrArg HomogeneousLocalization.val hx
      change HomogeneousLocalization.val
          (HomogeneousLocalization.mk
            (⟨0, x, 1, one_mem _⟩ :
              HomogeneousLocalization.NumDenSameDeg P.gradedPieces
                (Submonoid.powers f))) =
        HomogeneousLocalization.val 0 at hx'
      rw [HomogeneousLocalization.val_mk] at hx'
      simpa [Submonoid.coe_one] using hx'
    rw [Localization.mk_eq_mk'] at hxval
    obtain ⟨m, hm⟩ := (IsLocalization.mk'_eq_zero_iff _ _).1 hxval
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff (m : blowupAlgebra I) f).1 m.property
    have hm' : f ^ j * x = 0 := by
      rw [hj]
      exact hm
    refine ⟨j, ?_⟩
    apply Subtype.ext
    have hcoeff := congrArg
      (fun z : blowupAlgebra I => z.1.coeff (j * d)) hm'
    have hax : a ^ j * P.degreeZeroEquiv x = 0 := by
      simpa [hfa, hx0 x, hr, Polynomial.coeff_mul, Polynomial.coeff_monomial,
        Polynomial.coeff_zero, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcoeff
    calc
      ((r ^ j * x : R₀) : blowupAlgebra I) =
          (r : blowupAlgebra I) ^ j * (x : blowupAlgebra I) := rfl
      _ = algebraMap A (blowupAlgebra I) (a ^ j * P.degreeZeroEquiv x) := by
        rw [hr, hx0]
        simp
      _ = 0 := by rw [hax]; simp
  · rw [Localization.awayMap_surjective_iff]
    intro s
    obtain ⟨n, c, hc, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      P.gradedPieces hf s
    obtain ⟨b, hb, hcb⟩ :=
      (P.gradedPieces_spec (n • d) c).1 hc
    refine ⟨P.degreeZeroEquiv.symm b, n, ?_⟩
    apply HomogeneousLocalization.val_injective
    have hpoly :
        (algebraMap A (blowupAlgebra I) b) * f ^ n =
          (algebraMap A (blowupAlgebra I) a) ^ n * c := by
      apply Subtype.ext
      change
        Polynomial.C b * f.1 ^ n = Polynomial.C a ^ n * c.1
      rw [hcb, hfa]
      rw [Polynomial.monomial_pow, Polynomial.C_mul_monomial,
        ← Polynomial.C_pow, Polynomial.C_mul_monomial]
      congr 1
      · simp [Nat.mul_comm]
      · exact mul_comm _ _
    have hbval :
        (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
          (Submonoid.powers f) (P.degreeZeroEquiv.symm b)).val =
          Localization.mk ((P.degreeZeroEquiv.symm b : P.gradedPieces 0) :
            blowupAlgebra I) (1 : Submonoid.powers f) := by
      simp [AlgebraicGeometry.Proj.toSpecZero,
        AlgebraicGeometry.Proj.basicOpenToSpec,
        Scheme.Hom.comp_base, TopCat.coe_comp]
    have haval :
        (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
          (Submonoid.powers f) (P.degreeZeroEquiv.symm a)).val =
          Localization.mk ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) :
            blowupAlgebra I) (1 : Submonoid.powers f) := by
      rfl
    have hcval :
        (HomogeneousLocalization.Away.mk P.gradedPieces hf n c hc).val =
          Localization.mk c
            (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) := by
      rfl
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
    rw [hbval, haval, hcval]
    rw [P.degreeZeroEquiv_spec b, P.degreeZeroEquiv_spec a]
    rw [Localization.mk_pow, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    rw [← hpoly]
    simpa [g, HomogeneousLocalization.fromZeroRingHom,
      HomogeneousLocalization.val_mk, Localization.mk_mul,
      Localization.mk_pow] using
      (mul_comm (f ^ n) (algebraMap A (blowupAlgebra I) b))
private lemma blowup_base_mem_iff
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I)
    (x : blowupProjPoints P) (a : A) :
    letI : GradedRing P.gradedPieces := P.graded
    a ∈ ((blowupMap P).base x).asIdeal ↔
      (P.degreeZeroEquiv.symm a : blowupAlgebra I) ∈ x.asHomogeneousIdeal := by
  letI : GradedRing P.gradedPieces := P.graded
  have hJ (b : P.gradedPieces 0) :
      b ∈ ((AlgebraicGeometry.Proj.toSpecZero P.gradedPieces).base x).asIdeal ↔
        (b : blowupAlgebra I) ∈ x.asHomogeneousIdeal := by
    have hxcover : ∃ (n : ℕ) (_hn : 0 < n) (f : blowupAlgebra I),
        f ∈ P.gradedPieces n ∧ f ∉ x.asHomogeneousIdeal := by
      classical
      by_contra h
      apply x.not_irrelevant_le
      rw [HomogeneousIdeal.irrelevant_le]
      intro n hn f hf
      by_contra hfn
      exact h ⟨n, hn, f, hf, hfn⟩
    obtain ⟨n, hn, f, hf, hfx⟩ := hxcover
    let x1 : {y : blowupProjPoints P // y ∈ dPlus P.gradedPieces f} :=
      ⟨x, hfx⟩
    let c1 := dPlusHomeomorph P.gradedPieces hf hn
    let aw := AlgebraicGeometry.Proj.awayι P.gradedPieces f hf hn
    have haway : aw.base (c1 x1) = x := by
      let iso := AlgebraicGeometry.Proj.basicOpenIsoSpec
        P.gradedPieces f hf hn
      have hhom : iso.hom.base x1 = c1 x1 := by
        change (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
            P.gradedPieces f).base x1 =
          AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec
            P.gradedPieces f x1
        exact AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq
          P.gradedPieces x1
      have hinv := congrArg (fun q => q.base x1) iso.hom_inv_id
      change aw.base (c1 x1) = x
      have hinv' : iso.inv (c1 x1) = x1 := by
        rw [← hhom]
        change iso.inv (iso.hom x1) = x1 at hinv
        exact hinv
      change (iso.inv (c1 x1)).1 = x
      exact congrArg Subtype.val hinv'
    have hbase :
        (AlgebraicGeometry.Proj.toSpecZero P.gradedPieces).base x =
          PrimeSpectrum.comap
            (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
              (Submonoid.powers f)) (c1 x1) := by
      have hcomp := congrArg (fun q => q.base (c1 x1))
        (AlgebraicGeometry.Proj.awayι_toSpecZero P.gradedPieces f hf hn)
      change (AlgebraicGeometry.Proj.toSpecZero P.gradedPieces).base
          (aw.base (c1 x1)) =
        (Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
            (Submonoid.powers f)))).base (c1 x1) at hcomp
      rw [haway] at hcomp
      change (AlgebraicGeometry.Proj.toSpecZero P.gradedPieces).base x =
        PrimeSpectrum.comap
          (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
            (Submonoid.powers f)) (c1 x1) at hcomp
      exact hcomp
    rw [hbase]
    change b ∈ (PrimeSpectrum.comap
        (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
          (Submonoid.powers f)) (c1 x1)).asIdeal ↔ _
    change b ∈ Ideal.comap
        (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
          (Submonoid.powers f)) (c1 x1).asIdeal ↔ _
    rw [Ideal.mem_comap]
    let z : HomogeneousLocalization.NumDenSameDeg P.gradedPieces
        (Submonoid.powers f) := ⟨0, b, 1, by simp⟩
    have hfrom :
        HomogeneousLocalization.fromZeroRingHom P.gradedPieces
            (Submonoid.powers f) b = HomogeneousLocalization.mk z := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk (b : blowupAlgebra I) _ =
        Localization.mk (b : blowupAlgebra I) _
      rfl
    have hto :
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
          P.gradedPieces f).base x1 = c1 x1 := by
      exact AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq
        P.gradedPieces x1
    rw [hfrom, ← hto]
    exact AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
      (𝒜 := P.gradedPieces) (f := f) x1 z
  change (P.degreeZeroEquiv.symm a : P.gradedPieces 0) ∈
      ((AlgebraicGeometry.Proj.toSpecZero P.gradedPieces).base x).asIdeal ↔ _
  exact hJ _
theorem blowupRestrictionMap_isHomeomorph
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) :
  IsHomeomorph (blowupRestrictionMap P) := by
  letI : GradedRing P.gradedPieces := P.graded
  have dplus_of_degreeZero_mem_not
      (a : A) (haI : a ∈ I) (x : blowupProjPoints P)
      (ha : (P.degreeZeroEquiv.symm a : blowupAlgebra I) ∉
        x.asHomogeneousIdeal) :
      reesHomogeneousElement I 1 (a := a) (by simpa using haI) ∉
        x.asHomogeneousIdeal := by
    intro hf
    apply x.not_irrelevant_le
    rw [HomogeneousIdeal.irrelevant_le]
    intro n hn z hz
    obtain ⟨b, hb, hzeq⟩ := (P.gradedPieces_spec n z).1 hz
    have hpow :
        (P.degreeZeroEquiv.symm a : blowupAlgebra I) ^ n ∉
          x.asHomogeneousIdeal := by
      intro h
      apply ha
      exact (x.isPrime.pow_mem_iff_mem n hn).mp h
    have hprod :
        reesHomogeneousElement I 1 (a := a) (by simpa using haI) ^ n *
            algebraMap A (blowupAlgebra I) b =
          (P.degreeZeroEquiv.symm a : blowupAlgebra I) ^ n * z := by
      apply Subtype.ext
      rw [P.degreeZeroEquiv_spec a]
      change (reesHomogeneousElement I 1 (a := a)
          (by simpa using haI)).1 ^ n * Polynomial.C b =
        Polynomial.C a ^ n * z.1
      simpa [reesHomogeneousElement, hzeq, Polynomial.monomial_pow,
        Polynomial.C_pow] using
        (Polynomial.C_mul_monomial (R := A) (a := a ^ n) (b := b)
          (n := n)).symm
    have hleft :
      reesHomogeneousElement I 1 (a := a) (by simpa using haI) ^ n *
            algebraMap A (blowupAlgebra I) b ∈ x.asHomogeneousIdeal := by
      exact x.asHomogeneousIdeal.toIdeal.mul_mem_right _
        (Ideal.pow_mem_of_mem _ hf n hn)
    rw [hprod] at hleft
    rcases x.isPrime.mem_or_mem hleft with h | h
    · exact (hpow h).elim
    · exact h
  let β := {p : PrimeSpectrum A // p ∈ blowupBaseOpen I}
  let α := {x : blowupProjPoints P // (blowupMap P).base x ∈ blowupBaseOpen I}
  let e₀ : PrimeSpectrum (P.gradedPieces 0) ≃ₜ PrimeSpectrum A :=
    PrimeSpectrum.homeomorphOfRingEquiv P.degreeZeroEquiv
  let V : I → Set β := fun a =>
    {p : β | e₀.symm p.1 ∈
      PrimeSpectrum.basicOpen (P.degreeZeroEquiv.symm (a : A))}
  have hVopen : ∀ a : I, IsOpen (V a) := by
    intro a
    exact PrimeSpectrum.isOpen_basicOpen.preimage
      (e₀.symm.continuous.comp continuous_subtype_val)
  let U : I → Opens β := fun a => ⟨V a, hVopen a⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    refine TopologicalSpace.IsOpenCover.of_sets hVopen ?_
    apply Set.eq_univ_of_forall
    intro p
    by_contra hp
    have hpall : (I : Set A) ⊆ p.1.asIdeal := by
      intro a ha
      by_contra hnot
      apply hp
      apply Set.mem_iUnion.2
      refine ⟨⟨a, ha⟩, ?_⟩
      have hmem : e₀.symm p.1 ∈
          PrimeSpectrum.basicOpen (P.degreeZeroEquiv.symm (a : A)) ↔
          (a : A) ∉ p.1.asIdeal := by
        change (P.degreeZeroEquiv.symm (a : A) : P.gradedPieces 0) ∉
          (PrimeSpectrum.comap P.degreeZeroEquiv.toRingHom p.1).asIdeal ↔ _
        change P.degreeZeroEquiv (P.degreeZeroEquiv.symm (a : A)) ∉
            p.1.asIdeal ↔ (a : A) ∉ p.1.asIdeal
        simp
      exact hmem.mpr hnot
    exact p.2 ((PrimeSpectrum.mem_zeroLocus p.1 (I : Set A)).2 hpall)
  have hcont : Continuous (blowupRestrictionMap P) := by
    change Continuous (fun x : α =>
      (⟨(blowupMap P).base x.1, x.2⟩ : β))
    exact ((blowupMap P).continuous.comp continuous_subtype_val).subtype_mk
      (fun x => x.2)
  rw [hU.isHomeomorph_iff_restrictPreimage hcont]
  intro a
  let f : blowupAlgebra I := reesHomogeneousElement I 1
    (a := (a : A)) (by simpa using a.2)
  have hf : f ∈ P.gradedPieces 1 := by
    rw [P.gradedPieces_spec]
    exact ⟨a.1, by simpa using a.2, by rfl⟩
  have hbij := blowup_chart_awayMap_bijective hf (by omega) a.1
    (by simpa using a.2) rfl
  let r : P.gradedPieces 0 := P.degreeZeroEquiv.symm (a : A)
  let g0 : P.gradedPieces 0 →+*
      degreeZeroLocalization P.gradedPieces f :=
    HomogeneousLocalization.fromZeroRingHom P.gradedPieces (Submonoid.powers f)
  let e : Localization.Away r ≃+*
      Localization.Away (g0 r) :=
    RingEquiv.ofBijective
      (Localization.awayMap
        g0 r) hbij
  let s₀ : Set (PrimeSpectrum (P.gradedPieces 0)) :=
    (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (P.gradedPieces 0)))
  let sA : Set (PrimeSpectrum A) :=
    {p : PrimeSpectrum A | e₀.symm p ∈ s₀}
  have hs : sA ⊆ blowupBaseOpen I := by
    intro p hp
    change p ∉ PrimeSpectrum.zeroLocus (I : Set A)
    intro hpz
    have hpa : (a : A) ∈ p.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus p (I : Set A)).1 hpz a.2
    have hmem : e₀.symm p ∈ PrimeSpectrum.basicOpen r ↔
        (a : A) ∉ p.asIdeal := by
      change P.degreeZeroEquiv (P.degreeZeroEquiv.symm (a : A)) ∉
          p.asIdeal ↔ (a : A) ∉ p.asIdeal
      simp
    exact hmem.mp hp hpa
  let hsub₀ := localizationAwayComapSubtype_isHomeomorph (r : P.gradedPieces 0)
  let hsub₁ := localizationAwayComapSubtype_isHomeomorph (g0 r)
  let htransport := homeomorphSubtypePreimage_isHomeomorph e₀ s₀
  let hnested := subtypeSubtype_isHomeomorph hs
  letI : T0Space (blowupProjPoints P) :=
    (projToPrimeSpectrum_isEmbedding P.gradedPieces).t0Space
  letI : T0Space {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} :=
    (Topology.IsEmbedding.subtypeVal).t0Space
  let c := dPlusHomeomorph P.gradedPieces hf (Nat.zero_lt_succ 0)
  let sx : Set {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} :=
    c ⁻¹' (PrimeSpectrum.basicOpen (g0 r) : Set _)
  let hc₀ := homeomorphSubtypePreimage_isHomeomorph c sx
  let hc₁ : {x : {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} //
      x ∈ sx} ≃ₜ
      {q : PrimeSpectrum (degreeZeroLocalization P.gradedPieces f) //
        q ∈ PrimeSpectrum.basicOpen (g0 r)} :=
    hc₀.homeomorph.trans
      (Homeomorph.ofEqSubtypes (by
        funext q
        simp [sx]))
  let Hchart : {x : {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} //
      x ∈ sx} ≃ₜ {p : β // p ∈ (U a).carrier} :=
    hc₁.trans
      (hsub₁.homeomorph.symm.trans
        ((PrimeSpectrum.homeomorphOfRingEquiv e).symm.trans
          (hsub₀.homeomorph.trans
            (htransport.homeomorph.trans hnested.homeomorph))))
  apply (isHomeomorph_iff_exists_homeomorph).2
  have hchart_mem (x : {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f}) :
      g0 r ∈ (c x).asIdeal ↔ (a : A) ∈ ((blowupMap P).base x.1).asIdeal := by
    have hq : g0 r ∈ (c x).asIdeal ↔
        (P.degreeZeroEquiv.symm (a : A) : blowupAlgebra I) ∈ x.1.asHomogeneousIdeal := by
      let z : HomogeneousLocalization.NumDenSameDeg P.gradedPieces
          (Submonoid.powers f) := ⟨0, r, 1, by simp⟩
      have hc : c x =
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
            P.gradedPieces f).base x := by
        change AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec
            P.gradedPieces f x = _
        exact (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq
          P.gradedPieces x).symm
      rw [hc]
      have hg : g0 r = HomogeneousLocalization.mk z := by
        apply HomogeneousLocalization.val_injective
        change Localization.mk (r : blowupAlgebra I) _ =
          Localization.mk (r : blowupAlgebra I) _
        rfl
      rw [hg]
      exact AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
        (𝒜 := P.gradedPieces) (f := f) x z
    exact hq.trans (blowup_base_mem_iff P (x.1) (a : A)).symm
  have hchart_base
      (z : {x : {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} //
        x ∈ sx}) :
      (blowupMap P).base z.1.1 = (Hchart z).1.1 := by
    apply PrimeSpectrum.ext
    ext b
    change b ∈ ((blowupMap P).base z.1.1).asIdeal ↔
      b ∈ (Hchart z).1.1.asIdeal
    rw [blowup_base_mem_iff P z.1.1 b]
    let hsub₁e : PrimeSpectrum (Localization.Away (g0 r)) ≃ₜ
        {q : PrimeSpectrum (degreeZeroLocalization P.gradedPieces f) //
          q ∈ PrimeSpectrum.basicOpen (g0 r)} := hsub₁.homeomorph
    let q₁ := hsub₁e.symm (hc₁ z)
    let q₂ : PrimeSpectrum (Localization.Away r) :=
      (PrimeSpectrum.homeomorphOfRingEquiv e).symm q₁
    let hsub₀e : PrimeSpectrum (Localization.Away r) ≃ₜ
        {q : PrimeSpectrum (P.gradedPieces 0) // q ∈ s₀} :=
      hsub₀.homeomorph
    let q₀ : {q : PrimeSpectrum (P.gradedPieces 0) // q ∈ s₀} :=
      hsub₀e q₂
    let htransporte : {q : PrimeSpectrum (P.gradedPieces 0) // q ∈ s₀} ≃ₜ
        {p : PrimeSpectrum A // p ∈ sA} := htransport.homeomorph
    let hnestede : {p : PrimeSpectrum A // p ∈ sA} ≃ₜ
        {x : β // x.1 ∈ sA} := hnested.homeomorph
    have hq₁ : hsub₁e q₁ = hc₁ z := by
      exact hsub₁e.apply_symm_apply (hc₁ z)
    change ↑(P.degreeZeroEquiv.symm b) ∈ z.1.1.asHomogeneousIdeal ↔
      b ∈ (hnestede (htransporte q₀)).1.1.asIdeal
    change ↑(P.degreeZeroEquiv.symm b) ∈ z.1.1.asHomogeneousIdeal ↔
      b ∈ (e₀ q₀.1).asIdeal
    change ↑(P.degreeZeroEquiv.symm b) ∈ z.1.1.asHomogeneousIdeal ↔
      P.degreeZeroEquiv.symm b ∈ q₀.1.asIdeal
    change ↑(P.degreeZeroEquiv.symm b) ∈ z.1.1.asHomogeneousIdeal ↔
      Localization.mk (P.degreeZeroEquiv.symm b)
          (1 : Submonoid.powers r) ∈ q₂.asIdeal
    change ↑(P.degreeZeroEquiv.symm b) ∈ z.1.1.asHomogeneousIdeal ↔
      e (Localization.mk (P.degreeZeroEquiv.symm b)
          (1 : Submonoid.powers r)) ∈ q₁.asIdeal
    have heq : e (Localization.mk (P.degreeZeroEquiv.symm b)
          (1 : Submonoid.powers r)) =
        Localization.mk (g0 (P.degreeZeroEquiv.symm b))
          (1 : Submonoid.powers (g0 r)) := by
      change Localization.awayMap g0 r
          (Localization.mk (P.degreeZeroEquiv.symm b)
            (1 : Submonoid.powers r)) = _
      simp only [Localization.mk_eq_mk'_apply]
      change IsLocalization.map (Localization.Away (g0 r)) g0 _
          (IsLocalization.mk' (Localization.Away r)
            (P.degreeZeroEquiv.symm b) (1 : Submonoid.powers r)) = _
      rw [IsLocalization.mk'_one, IsLocalization.mk'_one]
      simp [Localization.awayMap, IsLocalization.Away.map]
    rw [heq]
    change ↑(P.degreeZeroEquiv.symm b) ∈ z.1.1.asHomogeneousIdeal ↔
      g0 (P.degreeZeroEquiv.symm b) ∈ (hsub₁e q₁).1.asIdeal
    rw [hq₁]
    change ↑(P.degreeZeroEquiv.symm b) ∈ z.1.1.asHomogeneousIdeal ↔
      g0 (P.degreeZeroEquiv.symm b) ∈ (c z.1).asIdeal
    let zb : HomogeneousLocalization.NumDenSameDeg P.gradedPieces
        (Submonoid.powers f) :=
      ⟨0, P.degreeZeroEquiv.symm b, 1, by simp⟩
    have hgb : g0 (P.degreeZeroEquiv.symm b) =
        HomogeneousLocalization.mk zb := by
      apply HomogeneousLocalization.val_injective
      change (HomogeneousLocalization.mk
          (⟨0, P.degreeZeroEquiv.symm b, 1, by simp⟩ :
            HomogeneousLocalization.NumDenSameDeg P.gradedPieces
              (Submonoid.powers f))).val =
        (HomogeneousLocalization.mk zb).val
      rw [HomogeneousLocalization.val_mk]
    have hc : c z.1 =
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
          P.gradedPieces f).base z.1 := by
      exact (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq
        P.gradedPieces z.1).symm
    rw [hgb, hc]
    simpa [zb] using
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
        (𝒜 := P.gradedPieces) (f := f) z.1 zb).symm
  refine ⟨?_, ?_⟩
  let hInv : {p : β // p ∈ (U a).carrier} →
      {x : α // (blowupRestrictionMap P) x ∈ (U a).carrier} := fun y =>
    let z := Hchart.symm y
    let x₀ : α := ⟨z.1.1, by
      change (blowupMap P).base z.1.1 ∈ blowupBaseOpen I
      rw [hchart_base z, Hchart.apply_symm_apply y]
      exact y.1.property⟩
    ⟨x₀, by
      have hzbase : (⟨(blowupMap P).base z.1.1, x₀.property⟩ : β) =
          (Hchart z).1 := by
        apply Subtype.ext
        exact hchart_base z
      change (⟨(blowupMap P).base z.1.1, x₀.property⟩ : β) ∈
        (U a).carrier
      rw [hzbase, Hchart.apply_symm_apply y]
      exact y.property⟩
  have hhomeo : IsHomeomorph
      ((U a).carrier.restrictPreimage (blowupRestrictionMap P)) := by
    apply (isHomeomorph_iff_exists_inverse).2
    refine ⟨hcont.restrictPreimage, hInv, ?_, ?_, ?_⟩
    · intro x
      let y : {p : β // p ∈ (U a).carrier} :=
        ⟨blowupRestrictionMap P x, x.property⟩
      have hy : (U a).carrier.restrictPreimage (blowupRestrictionMap P) x = y := by
        apply Subtype.ext
        rfl
      rw [hy]
      have hxU := x.property
      change e₀.symm ((blowupMap P).base x.1.1) ∈
          PrimeSpectrum.basicOpen r at hxU
      have ha_not : (a : A) ∉ ((blowupMap P).base x.1.1).asIdeal := by
        intro hax
        apply hxU
        change P.degreeZeroEquiv.symm (a : A) ∈
            (e₀.symm ((blowupMap P).base x.1.1)).asIdeal
        change P.degreeZeroEquiv (P.degreeZeroEquiv.symm (a : A)) ∈
            ((blowupMap P).base x.1.1).asIdeal
        simpa using hax
      have ha0 : (P.degreeZeroEquiv.symm (a : A) : blowupAlgebra I) ∉
          x.1.1.asHomogeneousIdeal := by
        intro ha0
        exact ha_not ((blowup_base_mem_iff P x.1.1 (a : A)).2 ha0)
      have hxf : f ∉ x.1.1.asHomogeneousIdeal := by
        simpa [f] using dplus_of_degreeZero_mem_not
          (a : A) a.2 x.1.1 ha0
      have hxdp : x.1.1 ∈ dPlus P.gradedPieces f :=
        (mem_dPlus_iff P.gradedPieces f x.1.1).2 hxf
      let zx0 : {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} :=
        ⟨x.1.1, hxdp⟩
      have hzxmem : zx0 ∈ sx := by
        change g0 r ∉ (c zx0).asIdeal
        intro h
        exact ha_not ((hchart_mem zx0).1 h)
      let zx : {x : {x : blowupProjPoints P //
          x ∈ dPlus P.gradedPieces f} // x ∈ sx} := ⟨zx0, hzxmem⟩
      have hzx : Hchart zx = y := by
        apply Subtype.ext
        apply Subtype.ext
        rw [← hchart_base zx]
        rfl
      have hzinv : Hchart.symm y = zx := by
        rw [← hzx]
        exact Hchart.symm_apply_apply zx
      apply Subtype.ext
      change (hInv y).1 = x.1
      dsimp [hInv]
      apply Subtype.ext
      have h := congrArg (fun z => z.1.1) hzinv
      dsimp [zx, zx0] at h
      exact h
    · intro y
      apply Subtype.ext
      apply Subtype.ext
      have hbase : (blowupMap P).base (hInv y).1.1 = y.1.1 := by
        dsimp [hInv]
        rw [hchart_base (Hchart.symm y), Hchart.apply_symm_apply y]
      change (blowupMap P).base (hInv y).1.1 = y.1.1
      exact hbase
    · let g : {p : β // p ∈ (U a).carrier} → blowupProjPoints P :=
        fun y => (Hchart.symm y).1.1
      have hg : Continuous g := by
        dsimp [g]
        exact continuous_subtype_val.comp
          (continuous_subtype_val.comp Hchart.symm.continuous)
      let ga : {p : β // p ∈ (U a).carrier} → α := fun y =>
        ⟨g y, by
          simpa [g, hInv] using (hInv y).1.property⟩
      have hga : Continuous ga := by
        exact hg.subtype_mk (fun y => by
          simpa [ga, g, hInv] using (hInv y).1.property)
      have houter : Continuous (fun y =>
          (⟨ga y, by simpa [ga, hInv] using (hInv y).property⟩ :
            {x : α // (blowupRestrictionMap P) x ∈ (U a).carrier})) := by
        exact hga.subtype_mk (fun y => by
          simpa [ga, hInv] using (hInv y).property)
      simpa [hInv, ga, g] using houter
  · exact IsHomeomorph.homeomorph
      ((U a).carrier.restrictPreimage (blowupRestrictionMap P)) hhomeo
  · rfl
theorem strictTransform_conditions
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    D.genericPoint ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ¬ (D.Z : Set (PrimeSpectrum A)) ⊆
        PrimeSpectrum.zeroLocus (I : Set A) ∧
      D.genericPoint ∈ blowupBaseOpen I ∧
      ((D.Z : Set (PrimeSpectrum A)) ∩ blowupBaseOpen I).Nonempty := by
  refine ⟨D.genericPoint_mem_baseOpen, ?_, D.genericPoint_mem_baseOpen, ?_⟩
  · intro hZ
    have hclosed : IsClosed (PrimeSpectrum.zeroLocus (I : Set A)) :=
      (PrimeSpectrum.isClosed_iff_zeroLocus _).2 ⟨(I : Set A), rfl⟩
    exact D.genericPoint_mem_baseOpen
      ((D.genericPoint_isGeneric.mem_closed_set_iff hclosed).2 hZ)
  · exact D.genericPoint_isGeneric.mem_open_set_iff (blowupBaseOpen_isOpen I) |>.1
      D.genericPoint_mem_baseOpen
theorem strictTransform_eq_viaOpen
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    strictTransform D = strictTransformViaOpen D := by
  let b := (blowupMap P).base
  let U := blowupBaseOpen I
  let e := blowupRestrictionMap P
  have he : IsHomeomorph e := blowupRestrictionMap_isHomeomorph P
  let xl : {x : blowupProjPoints P // b x ∈ U} :=
    ⟨D.lift, by
      change (blowupMap P).base D.lift ∈ blowupBaseOpen I
      rw [D.lift_over_generic]
      exact D.genericPoint_mem_baseOpen⟩
  have hxl : b D.lift ∈ (D.Z : Set (PrimeSpectrum A)) := by
    rw [D.lift_over_generic]
    exact D.genericPoint_isGeneric.mem
  have hxl' : D.lift ∈ b ⁻¹' ((D.Z : Set (PrimeSpectrum A)) ∩ U) := by
    exact ⟨hxl, xl.property⟩
  have hsubset : b ⁻¹' ((D.Z : Set (PrimeSpectrum A)) ∩ U) ⊆
      closure ({D.lift} : Set (blowupProjPoints P)) := by
    intro y hy
    let yl : {x : blowupProjPoints P // b x ∈ U} := ⟨y, hy.2⟩
    have hbase : (D.genericPoint : PrimeSpectrum A) ⤳ b y :=
      D.genericPoint_isGeneric.specializes hy.1
    have hsub : e xl ⤳ e yl := by
      apply (subtype_specializes_iff (e xl) (e yl)).2
      change (blowupMap P).base D.lift ⤳ (blowupMap P).base y
      rw [D.lift_over_generic]
      exact hbase
    have hsub' : xl ⤳ yl := by
      exact (he.homeomorph.isInducing.specializes_iff).mp hsub
    exact (subtype_specializes_iff xl yl).1 hsub' |>.mem_closure
  apply le_antisymm
  · exact closure_mono (Set.singleton_subset_iff.mpr hxl')
  · exact closure_minimal hsubset isClosed_closure
abbrev twoVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

def twoVariableX (k : Type u) [Field k] : twoVariablePolynomialRing k :=
  MvPolynomial.X 0

def twoVariableY (k : Type u) [Field k] : twoVariablePolynomialRing k :=
  MvPolynomial.X 1

def twoVariableMaximalIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span {twoVariableX k, twoVariableY k}

def twoVariableXIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span {twoVariableX k}

def twoVariableYIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span {twoVariableY k}

def twoVariableParabolaIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span {twoVariableX k - twoVariableY k ^ 2}

theorem twoVariableBlowupPresentation_exists (k : Type u) [Field k] :
    Nonempty (BlowupPresentation (twoVariableMaximalIdeal k)) := by
  let A := twoVariablePolynomialRing k
  let I := twoVariableMaximalIdeal k
  let 𝒜 := reesGradedPieces I
  letI : GradedRing 𝒜 := reesGradedRing I
  let φ : 𝒜 0 →+* A :=
    { toFun := fun p => Polynomial.constantCoeff (p.1.1)
      map_one' := by simp
      map_mul' := by intro p q; simp
      map_zero' := by simp
      map_add' := by intro p q; simp }
  have hφ : Function.Bijective φ := by
    constructor
    · intro p q hpq
      apply Subtype.ext
      apply Subtype.ext
      apply Polynomial.ext
      intro n
      have hp := (reesGradedPieces_mem_iff I 0 p.1).1 p.2
      have hq := (reesGradedPieces_mem_iff I 0 q.1).1 q.2
      rcases hp with ⟨a, ha, hpa⟩
      rcases hq with ⟨b, hb, hqb⟩
      have hab : a = b := by simpa [φ, hpa, hqb] using hpq
      subst hab
      simpa [hpa, hqb]
    · intro a
      refine ⟨⟨reesHomogeneousElement I 0 (a := a) (by simp), ?_⟩, ?_⟩
      · exact (reesGradedPieces_mem_iff I 0 _).2 ⟨a, by simp, rfl⟩
      · change Polynomial.constantCoeff (Polynomial.monomial 0 a) = a
        simp
  let e : 𝒜 0 ≃+* A := RingEquiv.ofBijective φ hφ
  have he : ∀ a : A,
      ((e.symm a : 𝒜 0) : blowupAlgebra I) = algebraMap A (blowupAlgebra I) a := by
    intro a
    apply Subtype.ext
    obtain ⟨b, hb, h⟩ :=
      (reesGradedPieces_mem_iff I 0 (e.symm a : blowupAlgebra I)).1
        (e.symm a).property
    have hba : b = a := by
      have hea : φ (e.symm a) = a := by
        change e (e.symm a) = a
        exact e.apply_symm_apply a
      simpa [A, φ, h] using hea
    subst hba
    simpa [A, h]
  refine ⟨{
    gradedPieces := 𝒜
    graded := reesGradedRing I
    degreeZeroEquiv := e
    gradedPieces_spec := ?_
    degreeZeroEquiv_spec := ?_ }⟩
  · intro d x
    exact reesGradedPieces_mem_iff I d x
  · exact he
noncomputable def twoVariableBlowupPresentation (k : Type u) [Field k] :
    BlowupPresentation (twoVariableMaximalIdeal k) :=
  Classical.choice (twoVariableBlowupPresentation_exists k)

theorem twoVariableXIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableXIdeal k).IsPrime := by
  rw [twoVariableXIdeal]
  apply (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero _)).2
  exact MvPolynomial.X_prime
theorem twoVariableYIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableYIdeal k).IsPrime := by
  rw [twoVariableYIdeal]
  apply (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero _)).2
  exact MvPolynomial.X_prime
theorem twoVariableParabolaIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableParabolaIdeal k).IsPrime := by
  let e := MvPolynomial.finSuccEquiv k 1
  let f : MvPolynomial (Fin 2) k :=
    twoVariableX k - twoVariableY k ^ 2
  let g : Polynomial (MvPolynomial (Fin 1) k) :=
    Polynomial.X - Polynomial.C (MvPolynomial.X 0 ^ 2)
  have hg : (Ideal.span {g}).IsPrime := by
    change (Ideal.span {Polynomial.X -
      Polynomial.C (MvPolynomial.X (0 : Fin 1) ^ 2)}).IsPrime
    apply (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero _)).2
    exact Polynomial.prime_X_sub_C _
  letI : (Ideal.span {g}).IsPrime := hg
  have hmap :
      (Ideal.map (e.symm : Polynomial (MvPolynomial (Fin 1) k) →+*
        MvPolynomial (Fin 2) k) (Ideal.span {g})).IsPrime := by
    exact Ideal.map_isPrime_of_equiv e.symm
  have heq :
      Ideal.map (e.symm : Polynomial (MvPolynomial (Fin 1) k) →+*
        MvPolynomial (Fin 2) k) (Ideal.span {g}) = Ideal.span {f} := by
    have hterm : e.symm g = f := by
      apply e.injective
      change e (e.symm (Polynomial.X -
          Polynomial.C (MvPolynomial.X (0 : Fin 1) ^ 2))) =
        e (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ^ 2)
      simp only [map_sub, map_pow, e.apply_symm_apply,
        MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
      · have he0 : e (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
          simpa [e] using (MvPolynomial.finSuccEquiv_X_zero (R := k) (n := 1))
        have he1 : e (MvPolynomial.X (1 : Fin 2)) =
            Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
          simpa [e] using
            (MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 1)
              (j := (0 : Fin 1)))
        simp only [he0, he1]
    rw [Ideal.map_span]
    rw [Set.image_singleton]
    change Ideal.span {e.symm g} = Ideal.span {f}
    rw [hterm]
  rw [twoVariableParabolaIdeal]
  change (Ideal.span {f}).IsPrime
  rw [← heq]
  exact hmap
private theorem primeStrictTransformData_exists_of_baseOpen
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} {p : Ideal A} (hp : p.IsPrime)
    (hbase : (⟨p, hp⟩ : PrimeSpectrum A) ∈ blowupBaseOpen I) :
    Nonempty (PrimeStrictTransformData P p hp) := by
  letI : GradedRing P.gradedPieces := P.graded
  let e := (blowupRestrictionMap_isHomeomorph P).homeomorph
  let y : {q : PrimeSpectrum A // q ∈ blowupBaseOpen I} := ⟨⟨p, hp⟩, hbase⟩
  let x := e.symm y
  refine ⟨{ lift := x.1, lift_over_prime := ?_, lift_unique := ?_ }⟩
  · have hx := e.apply_symm_apply y
    exact congrArg Subtype.val hx
  · intro z hz
    let z' : {q : blowupProjPoints P //
        (blowupMap P).base q ∈ blowupBaseOpen I} :=
      ⟨z, by rw [hz]; exact hbase⟩
    have hz' : e z' = y := by
      apply Subtype.ext
      change (blowupMap P).base z = ⟨p, hp⟩
      exact hz
    have hzx : z' = x := e.injective (hz' |>.trans (e.apply_symm_apply y).symm)
    exact congrArg Subtype.val hzx
private lemma rees_element_mem_of_prime
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} {p : Ideal A} {hp : p.IsPrime}
    (D : PrimeStrictTransformData P p hp) {a b : A}
    (ha : a ∈ p) (haI : a ∈ I) (hb : b ∈ I) (hbn : b ∉ p) :
    letI : GradedRing P.gradedPieces := P.graded
    reesHomogeneousElement I 1 (a := a) (by simpa using haI) ∈
      D.lift.asHomogeneousIdeal := by
  letI : GradedRing P.gradedPieces := P.graded
  have hqa : (P.degreeZeroEquiv.symm a : blowupAlgebra I) ∈
      D.lift.asHomogeneousIdeal := by
    apply (blowup_base_mem_iff P D.lift a).mp
    rw [D.lift_over_prime]
    exact ha
  have hqb : (P.degreeZeroEquiv.symm b : blowupAlgebra I) ∉
      D.lift.asHomogeneousIdeal := by
    intro h
    apply hbn
    have h' := (blowup_base_mem_iff P D.lift b).mpr h
    rw [D.lift_over_prime] at h'
    exact h'
  have hprod :
      reesHomogeneousElement I 1 (a := a) (by simpa using haI) *
          algebraMap A (blowupAlgebra I) b =
        (P.degreeZeroEquiv.symm a : blowupAlgebra I) *
          reesHomogeneousElement I 1 (a := b) (by simpa using hb) := by
    rw [P.degreeZeroEquiv_spec a, ← P.degreeZeroEquiv_spec b]
    apply Subtype.ext
    simp [reesHomogeneousElement, Polynomial.monomial_mul_monomial, mul_comm]
  have hprod' :
      reesHomogeneousElement I 1 (a := a) (by simpa using haI) *
          algebraMap A (blowupAlgebra I) b ∈ D.lift.asHomogeneousIdeal := by
    rw [hprod]
    exact D.lift.asHomogeneousIdeal.toIdeal.mul_mem_right _ hqa
  rcases D.lift.isPrime.mem_or_mem hprod' with h | h
  · exact h
  · rw [P.degreeZeroEquiv_spec b] at hqb
    exact (hqb h).elim
private lemma twoVariable_irrelevant_le_of_mem
    (k : Type u) [Field k]
    {𝒜 : ℕ → Submodule ℤ (blowupAlgebra (twoVariableMaximalIdeal k))}
    [GradedRing 𝒜]
    (hspec : ∀ (d : ℕ) (z : blowupAlgebra (twoVariableMaximalIdeal k)),
      z ∈ 𝒜 d ↔ ∃ a : twoVariablePolynomialRing k, ∃ _ha :
        a ∈ (twoVariableMaximalIdeal k) ^ d,
        z.1 = Polynomial.monomial d a)
    (x : ProjectiveSpectrum 𝒜)
    (hx : reesHomogeneousElement (twoVariableMaximalIdeal k) 1
      (a := twoVariableX k) (by
        rw [pow_one, twoVariableMaximalIdeal]
        exact Ideal.subset_span (by simp))
        ∈ x.asHomogeneousIdeal)
    (hy : reesHomogeneousElement (twoVariableMaximalIdeal k) 1
      (a := twoVariableY k) (by
        rw [pow_one, twoVariableMaximalIdeal]
        exact Ideal.subset_span (by simp))
        ∈ x.asHomogeneousIdeal) :
    HomogeneousIdeal.irrelevant 𝒜 ≤ x.asHomogeneousIdeal := by
  have hdegree_one {a : twoVariablePolynomialRing k}
      (ha : a ∈ twoVariableMaximalIdeal k) :
      reesHomogeneousElement (twoVariableMaximalIdeal k) 1
        (a := a) (by simpa using ha) ∈ x.asHomogeneousIdeal := by
    change a ∈ Ideal.span ({twoVariableX k, twoVariableY k} :
      Set (twoVariablePolynomialRing k)) at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
        have ha' : a = twoVariableX k ∨ a = twoVariableY k := by simpa using ha
        rcases ha' with rfl | rfl
        · exact hx
        · exact hy
    | zero =>
        have hzero : reesHomogeneousElement (twoVariableMaximalIdeal k) 1
              (a := 0) (by simp) = 0 := by
          apply Subtype.ext
          simp [reesHomogeneousElement]
        rw [hzero]
        exact x.asHomogeneousIdeal.zero_mem
    | add a b ha hb hpa hpb =>
        simpa [reesHomogeneousElement, polynomial_monomial_add] using
          x.asHomogeneousIdeal.add_mem hpa hpb
    | smul r a ha hpa =>
        have haI : a ∈ twoVariableMaximalIdeal k := by
          change a ∈ Ideal.span
            ({twoVariableX k, twoVariableY k} : Set (twoVariablePolynomialRing k))
          exact ha
        have hra : r * a ∈ twoVariableMaximalIdeal k := by
          apply (twoVariableMaximalIdeal k).mul_mem_left r
          exact haI
        have hmul := x.asHomogeneousIdeal.toIdeal.mul_mem_left
          (algebraMap (twoVariablePolynomialRing k)
            (blowupAlgebra (twoVariableMaximalIdeal k)) r) hpa
        have heq : reesHomogeneousElement (twoVariableMaximalIdeal k) 1
              (a := r * a) (by simpa [pow_one] using hra) =
            algebraMap (twoVariablePolynomialRing k)
              (blowupAlgebra (twoVariableMaximalIdeal k)) r *
              reesHomogeneousElement (twoVariableMaximalIdeal k) 1
                (a := a) (by simpa [pow_one] using haI) := by
          apply Subtype.ext
          simp [reesHomogeneousElement, Polynomial.monomial_mul_monomial]
        rw [heq]
        exact hmul
  have hpositive : ∀ n : ℕ, 0 < n →
      ∀ a : twoVariablePolynomialRing k,
        ∀ ha : a ∈ (twoVariableMaximalIdeal k) ^ n,
          reesHomogeneousElement (twoVariableMaximalIdeal k) n
            (a := a) (by simpa using ha) ∈ x.asHomogeneousIdeal := by
    intro n
    induction n with
    | zero =>
        intro hn
        omega
    | succ n ih =>
        intro hn a ha
        rw [Ideal.IsTwoSided.pow_succ] at ha
        have hpow : ∀ c : twoVariablePolynomialRing k,
            c ∈ twoVariableMaximalIdeal k * (twoVariableMaximalIdeal k) ^ n →
              c ∈ (twoVariableMaximalIdeal k) ^ (n + 1) := by
          intro c hc
          rw [Ideal.IsTwoSided.pow_succ]
          exact hc
        refine Submodule.mul_induction_on'
          (M := (twoVariableMaximalIdeal k : Submodule
            (twoVariablePolynomialRing k) (twoVariablePolynomialRing k)))
          (N := ((twoVariableMaximalIdeal k) ^ n : Submodule
            (twoVariablePolynomialRing k) (twoVariablePolynomialRing k)))
          (C := fun c hc =>
            reesHomogeneousElement (twoVariableMaximalIdeal k) (n + 1)
              (a := c) (hpow c hc) ∈ x.asHomogeneousIdeal) ?_ ?_ ha
        · intro b hb c hc
          cases n with
          | zero =>
              have hb' := hdegree_one hb
              have hbc : b * c ∈ twoVariableMaximalIdeal k ^ 1 := by
                apply hpow (b * c)
                exact Ideal.mul_mem_mul hb hc
              have heq : reesHomogeneousElement (twoVariableMaximalIdeal k) 1
                    (a := b * c) hbc =
                  algebraMap (twoVariablePolynomialRing k)
                    (blowupAlgebra (twoVariableMaximalIdeal k)) c *
                    reesHomogeneousElement (twoVariableMaximalIdeal k) 1
                      (a := b) (by simpa [pow_one] using hb) := by
                apply Subtype.ext
                simp [reesHomogeneousElement, Polynomial.monomial_mul_monomial,
                  mul_comm]
              rw [heq]
              exact x.asHomogeneousIdeal.toIdeal.mul_mem_left _ hb'
          | succ n =>
              have hb' := hdegree_one hb
              have hc' := ih (Nat.zero_lt_succ n) c hc
              have hbc : b * c ∈ twoVariableMaximalIdeal k ^ (n + 2) := by
                apply hpow (b * c)
                exact Ideal.mul_mem_mul hb hc
              have heq : reesHomogeneousElement (twoVariableMaximalIdeal k) (n + 2)
                    (a := b * c) hbc =
                  reesHomogeneousElement (twoVariableMaximalIdeal k) 1
                      (a := b) (by simpa [pow_one] using hb) *
                    reesHomogeneousElement (twoVariableMaximalIdeal k) (n + 1)
                      (a := c) hc := by
                apply Subtype.ext
                simp [reesHomogeneousElement, Polynomial.monomial_mul_monomial,
                  Nat.add_assoc]
                rw [show n + 2 = 1 + (n + 1) by omega]
              rw [heq]
              exact Ideal.mul_le_left
                (Ideal.mul_mem_mul hb' hc')
        · intro a ha b hb hpa hpb
          simpa [reesHomogeneousElement, polynomial_monomial_add] using
            x.asHomogeneousIdeal.add_mem hpa hpb
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn z hz
  cases n with
  | zero => omega
  | succ n =>
      obtain ⟨a, ha, hzeq⟩ := (hspec (n + 1) z).1 hz
      have hz_eq : z = reesHomogeneousElement (twoVariableMaximalIdeal k) (n + 1)
          (a := a) ha := by
        apply Subtype.ext
        exact hzeq
      rw [hz_eq]
      exact hpositive (n + 1) (Nat.zero_lt_succ n) a ha
private lemma rees_element_coeff_mem_of_prime_lift
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} {p : Ideal A} {hp : p.IsPrime}
    (D : PrimeStrictTransformData P p hp) {d : ℕ} {a : A}
    (ha : a ∈ I ^ d) {b : A} (hb : b ∈ I) (hbp : b ∉ p) :
    letI : GradedRing P.gradedPieces := P.graded
    reesHomogeneousElement I 1 (a := b) (by simpa using hb) ∉
        D.lift.asHomogeneousIdeal →
      reesHomogeneousElement I d (a := a) ha ∈ D.lift.asHomogeneousIdeal →
        a ∈ p := by
  intro hfb haD
  let f : blowupAlgebra I :=
    reesHomogeneousElement I 1 (a := b) (by simpa using hb)
  have hf : f ∈ P.gradedPieces 1 := by
    rw [P.gradedPieces_spec]
    exact ⟨b, by simpa using hb, rfl⟩
  let c := dPlusHomeomorph P.gradedPieces hf (by omega)
  let x : {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} :=
    ⟨D.lift, by simpa [f] using hfb⟩
  let q := c x
  let g0 : P.gradedPieces 0 →+* degreeZeroLocalization P.gradedPieces f :=
    HomogeneousLocalization.fromZeroRingHom P.gradedPieces (Submonoid.powers f)
  let r : P.gradedPieces 0 := P.degreeZeroEquiv.symm b
  let z : HomogeneousLocalization.NumDenSameDeg P.gradedPieces
      (Submonoid.powers f) :=
    ⟨d,
      ⟨reesHomogeneousElement I d (a := a) ha,
        (P.gradedPieces_spec d _).2 ⟨a, ha, rfl⟩⟩,
      ⟨f ^ d, by simpa using SetLike.pow_mem_graded d hf⟩,
      ⟨d, rfl⟩⟩
  have hz : HomogeneousLocalization.mk z ∈ q.asIdeal := by
    have hto :
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
          P.gradedPieces f).base x = q := by
      have hc : q =
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
            P.gradedPieces f).base x := by
        dsimp [q, c]
        change AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec
            P.gradedPieces f x = _
        exact (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq
          P.gradedPieces x).symm
      exact hc.symm
    rw [← hto]
    exact (AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
      (𝒜 := P.gradedPieces) (f := f) x z).2 haD
  have hprod :
      g0 r ^ d * HomogeneousLocalization.mk z =
        g0 (P.degreeZeroEquiv.symm a) := by
    apply HomogeneousLocalization.val_injective
    have hrval : (g0 r).val = Localization.mk (r : blowupAlgebra I)
        (1 : Submonoid.powers f) := by rfl
    have haval : (g0 (P.degreeZeroEquiv.symm a)).val =
        Localization.mk (P.degreeZeroEquiv.symm a : blowupAlgebra I)
          (1 : Submonoid.powers f) := by rfl
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      hrval, haval, HomogeneousLocalization.val_mk]
    dsimp [z]
    change Localization.mk (r : blowupAlgebra I)
          (1 : Submonoid.powers f) ^ d *
        Localization.mk (reesHomogeneousElement I d (a := a) ha : blowupAlgebra I)
          (⟨f ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers f) =
      Localization.mk (P.degreeZeroEquiv.symm a : blowupAlgebra I)
        (1 : Submonoid.powers f)
    have hpoly :
        algebraMap A (blowupAlgebra I) a * f ^ d =
          algebraMap A (blowupAlgebra I) b ^ d *
            reesHomogeneousElement I d (a := a) ha := by
      apply Subtype.ext
      change Polynomial.C a * f.1 ^ d =
        Polynomial.C b ^ d *
          (reesHomogeneousElement I d (a := a) ha).1
      rw [show f.1 = Polynomial.monomial 1 b by rfl,
        show (reesHomogeneousElement I d (a := a) ha).1 =
          Polynomial.monomial d a by rfl]
      rw [Polynomial.monomial_pow, Polynomial.C_mul_monomial,
        ← Polynomial.C_pow, Polynomial.C_mul_monomial]
      congr 1
      · simp [Nat.mul_comm]
      · exact mul_comm _ _
    rw [P.degreeZeroEquiv_spec b, P.degreeZeroEquiv_spec a]
    rw [Localization.mk_pow, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    rw [← hpoly]
    simp [Localization.mk_mul, Localization.mk_pow]
  have hconst : g0 (P.degreeZeroEquiv.symm a) ∈ q.asIdeal := by
    rw [← hprod]
    exact q.asIdeal.mul_mem_left _ hz
  have hconst' :
      (P.degreeZeroEquiv.symm a : blowupAlgebra I) ∈ D.lift.asHomogeneousIdeal := by
    let za : HomogeneousLocalization.NumDenSameDeg P.gradedPieces
        (Submonoid.powers f) :=
      ⟨0, P.degreeZeroEquiv.symm a, 1, by simp⟩
    have hza : g0 (P.degreeZeroEquiv.symm a) = HomogeneousLocalization.mk za := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk (P.degreeZeroEquiv.symm a : blowupAlgebra I) _ = _
      rfl
    have hto :
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
          P.gradedPieces f).base x = q := by
      have hc : q =
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
            P.gradedPieces f).base x := by
        dsimp [q, c]
        change AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec
            P.gradedPieces f x = _
        exact (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq
          P.gradedPieces x).symm
      exact hc.symm
    have hz' : HomogeneousLocalization.mk za ∈
        ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
          P.gradedPieces f).base x).asIdeal := by
      rw [hto]
      rw [← hza]
      exact hconst
    exact (AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
      (𝒜 := P.gradedPieces) (f := f) x za).1 hz'
  have hbase := (blowup_base_mem_iff P D.lift a).mpr hconst'
  rw [D.lift_over_prime] at hbase
  simpa using hbase

theorem twoVariableXStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableXIdeal k) (twoVariableXIdeal_isPrime k)) := by
  let φ : twoVariablePolynomialRing k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k)
      (fun i : Fin 2 => if i = 0 then 0 else 1)
  have hnot : twoVariableY k ∉ twoVariableXIdeal k := by
    intro hy
    have hspan : Ideal.span ({twoVariableX k} : Set (twoVariablePolynomialRing k)) ≤
        Ideal.comap φ ⊥ := by
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases hz with rfl
      change φ (twoVariableX k) ∈ (⊥ : Ideal k)
      simp [φ, twoVariableX]
    have hy' : φ (twoVariableY k) ∈ (⊥ : Ideal k) := by
      exact hspan (by simpa [twoVariableXIdeal] using hy)
    simpa [φ, twoVariableY] using hy'
  refine primeStrictTransformData_exists_of_baseOpen
    (P := twoVariableBlowupPresentation k) (p := twoVariableXIdeal k)
    (twoVariableXIdeal_isPrime k) ?_
  change (⟨twoVariableXIdeal k, twoVariableXIdeal_isPrime k⟩ : PrimeSpectrum _)
      ∉ PrimeSpectrum.zeroLocus
        (twoVariableMaximalIdeal k : Set (twoVariablePolynomialRing k))
  intro hz
  have hy : twoVariableY k ∈ twoVariableMaximalIdeal k := by
    apply Ideal.subset_span
    simp
  exact hnot ((PrimeSpectrum.mem_zeroLocus _ _).1 hz hy)
theorem twoVariableYStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableYIdeal k) (twoVariableYIdeal_isPrime k)) := by
  let φ : twoVariablePolynomialRing k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k)
      (fun i : Fin 2 => if i = 0 then 1 else 0)
  have hnot : twoVariableX k ∉ twoVariableYIdeal k := by
    intro hx
    have hspan : Ideal.span ({twoVariableY k} : Set (twoVariablePolynomialRing k)) ≤
        Ideal.comap φ ⊥ := by
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases hz with rfl
      change φ (twoVariableY k) ∈ (⊥ : Ideal k)
      simp [φ, twoVariableY]
    have hx' : φ (twoVariableX k) ∈ (⊥ : Ideal k) := by
      exact hspan (by simpa [twoVariableYIdeal] using hx)
    simpa [φ, twoVariableX] using hx'
  refine primeStrictTransformData_exists_of_baseOpen
    (P := twoVariableBlowupPresentation k) (p := twoVariableYIdeal k)
    (twoVariableYIdeal_isPrime k) ?_
  change (⟨twoVariableYIdeal k, twoVariableYIdeal_isPrime k⟩ : PrimeSpectrum _)
      ∉ PrimeSpectrum.zeroLocus
        (twoVariableMaximalIdeal k : Set (twoVariablePolynomialRing k))
  intro hz
  have hx : twoVariableX k ∈ twoVariableMaximalIdeal k := by
    apply Ideal.subset_span
    simp
  exact hnot ((PrimeSpectrum.mem_zeroLocus _ _).1 hz hx)
theorem twoVariableParabolaStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableParabolaIdeal k) (twoVariableParabolaIdeal_isPrime k)) := by
  let φ : twoVariablePolynomialRing k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 2 => 1)
  have hnot : twoVariableY k ∉ twoVariableParabolaIdeal k := by
    intro hy
    have hspan :
        Ideal.span ({twoVariableX k - twoVariableY k ^ 2} :
          Set (twoVariablePolynomialRing k)) ≤ Ideal.comap φ ⊥ := by
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases hz with rfl
      change φ (twoVariableX k - twoVariableY k ^ 2) ∈ (⊥ : Ideal k)
      simp [φ, twoVariableX, twoVariableY]
    have hy' : φ (twoVariableY k) ∈ (⊥ : Ideal k) := by
      exact hspan (by simpa [twoVariableParabolaIdeal] using hy)
    simpa [φ, twoVariableY] using hy'
  refine primeStrictTransformData_exists_of_baseOpen
    (P := twoVariableBlowupPresentation k)
    (p := twoVariableParabolaIdeal k)
    (twoVariableParabolaIdeal_isPrime k) ?_
  change (⟨twoVariableParabolaIdeal k, twoVariableParabolaIdeal_isPrime k⟩ :
      PrimeSpectrum _) ∉ PrimeSpectrum.zeroLocus
        (twoVariableMaximalIdeal k : Set (twoVariablePolynomialRing k))
  intro hz
  have hy : twoVariableY k ∈ twoVariableMaximalIdeal k := by
    apply Ideal.subset_span
    simp
  exact hnot ((PrimeSpectrum.mem_zeroLocus _ _).1 hz hy)
noncomputable def twoVariableXStrictTransformData (k : Type u) [Field k] :
    PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableXIdeal k) (twoVariableXIdeal_isPrime k) :=
  Classical.choice (twoVariableXStrictTransformData_exists k)

noncomputable def twoVariableYStrictTransformData (k : Type u) [Field k] :
    PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableYIdeal k) (twoVariableYIdeal_isPrime k) :=
  Classical.choice (twoVariableYStrictTransformData_exists k)

noncomputable def twoVariableParabolaStrictTransformData (k : Type u) [Field k] :
    PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableParabolaIdeal k) (twoVariableParabolaIdeal_isPrime k) :=
  Classical.choice (twoVariableParabolaStrictTransformData_exists k)

theorem twoVariable_x_y_strictTransforms_disjoint (k : Type u) [Field k] :
    Disjoint
      (primeStrictTransform (twoVariableXStrictTransformData k))
      (primeStrictTransform (twoVariableYStrictTransformData k)) := by
  let P := twoVariableBlowupPresentation k
  letI : GradedRing P.gradedPieces := P.graded
  have hXnotY : twoVariableX k ∉ twoVariableYIdeal k := by
    intro hx
    let φ : twoVariablePolynomialRing k →+* k :=
      MvPolynomial.eval₂Hom (RingHom.id k)
        (fun i : Fin 2 => if i = 0 then 1 else 0)
    have hspan : Ideal.span ({twoVariableY k} : Set (twoVariablePolynomialRing k)) ≤
        Ideal.comap φ ⊥ := by
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases hz with rfl
      change φ (twoVariableY k) ∈ (⊥ : Ideal k)
      simp [φ, twoVariableY]
    have hx' : φ (twoVariableX k) ∈ (⊥ : Ideal k) := by
      exact hspan (by simpa [twoVariableYIdeal] using hx)
    simpa [φ, twoVariableX] using hx'
  have hYnotX : twoVariableY k ∉ twoVariableXIdeal k := by
    intro hy
    let φ : twoVariablePolynomialRing k →+* k :=
      MvPolynomial.eval₂Hom (RingHom.id k)
        (fun i : Fin 2 => if i = 0 then 0 else 1)
    have hspan : Ideal.span ({twoVariableX k} : Set (twoVariablePolynomialRing k)) ≤
        Ideal.comap φ ⊥ := by
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases hz with rfl
      change φ (twoVariableX k) ∈ (⊥ : Ideal k)
      simp [φ, twoVariableX]
    have hy' : φ (twoVariableY k) ∈ (⊥ : Ideal k) := by
      exact hspan (by simpa [twoVariableXIdeal] using hy)
    simpa [φ, twoVariableY] using hy'
  have hxM : twoVariableX k ∈ twoVariableMaximalIdeal k := by
    apply Ideal.subset_span
    simp [twoVariableMaximalIdeal]
  have hyM : twoVariableY k ∈ twoVariableMaximalIdeal k := by
    apply Ideal.subset_span
    simp [twoVariableMaximalIdeal]
  let fX : blowupAlgebra (twoVariableMaximalIdeal k) :=
    reesHomogeneousElement (twoVariableMaximalIdeal k) 1
      (a := twoVariableX k) (by simpa using hxM)
  let fY : blowupAlgebra (twoVariableMaximalIdeal k) :=
    reesHomogeneousElement (twoVariableMaximalIdeal k) 1
      (a := twoVariableY k) (by simpa using hyM)
  have hXlift : fX ∈ (twoVariableXStrictTransformData k).lift.asHomogeneousIdeal := by
    dsimp [fX]
    exact rees_element_mem_of_prime (twoVariableXStrictTransformData k)
      (by
        apply Ideal.subset_span
        simp [twoVariableXIdeal]) hxM hyM hYnotX
  have hYlift : fY ∈ (twoVariableYStrictTransformData k).lift.asHomogeneousIdeal := by
    dsimp [fY]
    exact rees_element_mem_of_prime (twoVariableYStrictTransformData k)
      (by
        apply Ideal.subset_span
        simp [twoVariableYIdeal]) hyM hxM hXnotY
  have hXclosed : IsClosed
      (ProjectiveSpectrum.zeroLocus P.gradedPieces ({fX} : Set (blowupAlgebra (twoVariableMaximalIdeal k)))) :=
    ProjectiveSpectrum.isClosed_zeroLocus P.gradedPieces {fX}
  have hYclosed : IsClosed
      (ProjectiveSpectrum.zeroLocus P.gradedPieces ({fY} : Set (blowupAlgebra (twoVariableMaximalIdeal k)))) :=
    ProjectiveSpectrum.isClosed_zeroLocus P.gradedPieces {fY}
  have hXsubset : primeStrictTransform (twoVariableXStrictTransformData k) ⊆
      ProjectiveSpectrum.zeroLocus P.gradedPieces ({fX} : Set (blowupAlgebra (twoVariableMaximalIdeal k))) := by
    rw [primeStrictTransform]
    apply closure_minimal
    · exact Set.singleton_subset_iff.mpr
        ((ProjectiveSpectrum.mem_zeroLocus P.gradedPieces _ _).2
          (Set.singleton_subset_iff.mpr hXlift))
    · exact hXclosed
  have hYsubset : primeStrictTransform (twoVariableYStrictTransformData k) ⊆
      ProjectiveSpectrum.zeroLocus P.gradedPieces ({fY} : Set (blowupAlgebra (twoVariableMaximalIdeal k))) := by
    rw [primeStrictTransform]
    apply closure_minimal
    · exact Set.singleton_subset_iff.mpr
        ((ProjectiveSpectrum.mem_zeroLocus P.gradedPieces _ _).2
          (Set.singleton_subset_iff.mpr hYlift))
    · exact hYclosed
  rw [Set.disjoint_left]
  intro z hzx hzy
  have hxz : fX ∈ z.asHomogeneousIdeal :=
    (ProjectiveSpectrum.mem_zeroLocus P.gradedPieces z _).1
      (hXsubset hzx) (Set.mem_singleton fX)
  have hyz : fY ∈ z.asHomogeneousIdeal :=
    (ProjectiveSpectrum.mem_zeroLocus P.gradedPieces z _).1
      (hYsubset hzy) (Set.mem_singleton fY)
  exact z.not_irrelevant_le (twoVariable_irrelevant_le_of_mem k
    P.gradedPieces_spec z hxz hyz)
theorem twoVariable_x_parabola_strictTransforms_not_disjoint
    (k : Type u) [Field k] :
    ¬ Disjoint
      (primeStrictTransform (twoVariableXStrictTransformData k))
      (primeStrictTransform (twoVariableParabolaStrictTransformData k)) := by
  let P := twoVariableBlowupPresentation k
  letI : GradedRing P.gradedPieces := P.graded
  let fX : blowupAlgebra (twoVariableMaximalIdeal k) :=
    reesHomogeneousElement (twoVariableMaximalIdeal k) 1
      (a := twoVariableX k) (by
        rw [pow_one, twoVariableMaximalIdeal]
        exact Ideal.subset_span (by simp))
  let fY : blowupAlgebra (twoVariableMaximalIdeal k) :=
    reesHomogeneousElement (twoVariableMaximalIdeal k) 1
      (a := twoVariableY k) (by
        rw [pow_one, twoVariableMaximalIdeal]
        exact Ideal.subset_span (by simp))
  have hI : twoVariableMaximalIdeal k =
      MvPolynomial.idealOfVars (Fin 2) k := by
    rw [twoVariableMaximalIdeal, MvPolynomial.idealOfVars]
    congr 1
    ext z
    change z = MvPolynomial.X 0 ∨ z = MvPolynomial.X 1 ↔
      ∃ i : Fin 2, MvPolynomial.X i = z
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
  let K : Ideal (blowupAlgebra (twoVariableMaximalIdeal k)) :=
    Ideal.span ({
      algebraMap (twoVariablePolynomialRing k)
        (blowupAlgebra (twoVariableMaximalIdeal k)) (twoVariableX k),
      algebraMap (twoVariablePolynomialRing k)
        (blowupAlgebra (twoVariableMaximalIdeal k)) (twoVariableY k),
      fX} : Set (blowupAlgebra (twoVariableMaximalIdeal k)))
  have hvanish (n : ℕ) : ∀ z : blowupAlgebra (twoVariableMaximalIdeal k),
      z ∈ K →
        MvPolynomial.coeff (Finsupp.single (1 : Fin 2) n) (z.1.coeff n) = 0 := by
    intro z hz
    change z ∈ Submodule.span (blowupAlgebra (twoVariableMaximalIdeal k))
      ({
        algebraMap (twoVariablePolynomialRing k)
          (blowupAlgebra (twoVariableMaximalIdeal k)) (twoVariableX k),
        algebraMap (twoVariablePolynomialRing k)
          (blowupAlgebra (twoVariableMaximalIdeal k)) (twoVariableY k),
        fX} : Set (blowupAlgebra (twoVariableMaximalIdeal k))) at hz
    obtain ⟨rX, rY, rF, hz'⟩ :=
      (Submodule.mem_span_triple
        (R := blowupAlgebra (twoVariableMaximalIdeal k))
        (w := z)
        (x := algebraMap (twoVariablePolynomialRing k)
          (blowupAlgebra (twoVariableMaximalIdeal k)) (twoVariableX k))
        (y := algebraMap (twoVariablePolynomialRing k)
          (blowupAlgebra (twoVariableMaximalIdeal k)) (twoVariableY k))
        (z := fX)).1 hz
    rw [← hz']
    cases n with
    | zero =>
        simp [fX, reesHomogeneousElement, twoVariableX, twoVariableY,
          Algebra.smul_def, MvPolynomial.coeff_mul_X']
    | succ n =>
        have hrY : rY.1.coeff (n + 1) ∈
            MvPolynomial.idealOfVars (Fin 2) k ^ (n + 1) := by
          simpa [hI] using rY.2 (n + 1)
        have hrY0 : MvPolynomial.coeff (Finsupp.single (1 : Fin 2) n)
              (rY.1.coeff (n + 1)) = 0 := by
          exact (MvPolynomial.mem_pow_idealOfVars_iff' (n + 1)
            (rY.1.coeff (n + 1))).1 hrY _ (by simp)
        have hcoeff :
            (rX • algebraMap (twoVariablePolynomialRing k)
                (blowupAlgebra (twoVariableMaximalIdeal k)) (twoVariableX k) +
              rY • algebraMap (twoVariablePolynomialRing k)
                (blowupAlgebra (twoVariableMaximalIdeal k)) (twoVariableY k) +
              rF • fX).1.coeff (n + 1) =
            rX.1.coeff (n + 1) * MvPolynomial.X 0 +
              rY.1.coeff (n + 1) * MvPolynomial.X 1 +
              rF.1.coeff n * MvPolynomial.X 0 := by
          simp [fX, reesHomogeneousElement, twoVariableX, twoVariableY,
            Algebra.smul_def, Polynomial.coeff_add, Polynomial.coeff_mul_C,
            Polynomial.coeff_mul_monomial]
          rw [Polynomial.coeff_mul_monomial]
        rw [hcoeff]
        simp [MvPolynomial.coeff_mul_X', hrY0]
  have hdisj : Disjoint
      (K : Set (blowupAlgebra (twoVariableMaximalIdeal k)))
      (↑(Submonoid.powers fY) : Set (blowupAlgebra (twoVariableMaximalIdeal k))) := by
    rw [Set.disjoint_left]
    intro z hzK hzp
    change z ∈ Submonoid.powers fY at hzp
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff z fY).1 hzp
    subst z
    have hv := hvanish n (fY ^ n) hzK
    simpa [fY, reesHomogeneousElement, twoVariableY,
      Polynomial.coeff_monomial, MvPolynomial.coeff_X_pow] using hv
  have hdisj' : Disjoint (K : Set (blowupAlgebra (twoVariableMaximalIdeal k)))
      (↑(Submonoid.powers fY) : Set (blowupAlgebra (twoVariableMaximalIdeal k))) := hdisj
  obtain ⟨q, hqprime, hqK, hqdisj⟩ :=
    Ideal.exists_le_prime_disjoint (I := K) (Submonoid.powers fY) hdisj'
  have hfYq : fY ∉ q := by
    intro hf
    exact Set.disjoint_left.mp hqdisj hf (Submonoid.mem_powers fY)
  let qh := q.homogeneousCore P.gradedPieces
  have hqhprime : qh.toIdeal.IsPrime := hqprime.homogeneousCore
  let z : ProjectiveSpectrum P.gradedPieces :=
    { asHomogeneousIdeal := qh
      isPrime := hqhprime
      not_irrelevant_le := by
        intro hirr
        have hfYirr : fY ∈ HomogeneousIdeal.irrelevant P.gradedPieces := by
          apply HomogeneousIdeal.mem_irrelevant_of_mem
          · exact Nat.zero_lt_one
          · rw [P.gradedPieces_spec]
            exact ⟨twoVariableY k, by
              rw [pow_one, twoVariableMaximalIdeal]
              exact Ideal.subset_span (by simp), rfl⟩
        exact hfYq ((Ideal.toIdeal_homogeneousCore_le P.gradedPieces q)
          (hirr hfYirr)) }
  sorry
theorem exists_twoVariable_separatingIdeal (k : Type u) [Field k] :
    ∃ J : Ideal (twoVariablePolynomialRing k),
      PrimeSpectrum.zeroLocus (J : Set (twoVariablePolynomialRing k)) =
        PrimeSpectrum.zeroLocus
          (twoVariableMaximalIdeal k : Set (twoVariablePolynomialRing k)) ∧
      ∃ P : BlowupPresentation J,
        ∃ dx : PrimeStrictTransformData P
          (twoVariableXIdeal k) (twoVariableXIdeal_isPrime k),
        ∃ dp : PrimeStrictTransformData P
          (twoVariableParabolaIdeal k) (twoVariableParabolaIdeal_isPrime k),
          Disjoint (primeStrictTransform dx) (primeStrictTransform dp) := by sorry
theorem projPoints_isEmpty_of_eventually_zero
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (hzero : ∀ᶠ n in Filter.atTop, 𝒜 n = ⊥) :
    IsEmpty (ProjPoints 𝒜) := by sorry
theorem projPoints_irreducibleSpace_of_domain
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] [IsDomain R]
    (hplus : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) :
    IrreducibleSpace (ProjPoints 𝒜) := by sorry
theorem empty_projPoints_not_irreducible
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    [IsEmpty (ProjPoints 𝒜)] :
    ¬ IsIrreducible (Set.univ : Set (ProjPoints 𝒜)) := by sorry
abbrev blowupQuotientRing {A : Type u} [CommRing A] (p : Ideal A) := A ⧸ p

abbrev blowupQuotientIdeal {A : Type u} [CommRing A]
    (I p : Ideal A) : Ideal (blowupQuotientRing p) :=
  quotientIdeal I p

theorem exists_surjective_blowupQuotientRingHom
    {A : Type u} [CommRing A] {I p : Ideal A} :
    ∃ φ : blowupAlgebra I →+* blowupAlgebra (blowupQuotientIdeal I p),
      Function.Surjective φ := by sorry
theorem exists_blowupQuotientMapData
    {A : Type u} [CommRing A] {I p : Ideal A}
    (P : BlowupPresentation I)
    (Q : BlowupPresentation (blowupQuotientIdeal I p)) :
    Nonempty (BlowupQuotientMapData P Q) := by sorry
noncomputable def blowupQuotientMapData
    {A : Type u} [CommRing A] {I p : Ideal A}
    (P : BlowupPresentation I)
    (Q : BlowupPresentation (blowupQuotientIdeal I p)) :
    BlowupQuotientMapData P Q :=
  Classical.choice (exists_blowupQuotientMapData P Q)

theorem blowupQuotientMapData_surjective
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    (F : BlowupQuotientMapData P Q) :
    Function.Surjective F.map :=
  F.surjective

theorem blowupQuotientProjMap_image_strictTransform
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    {hp : p.IsPrime} (F : BlowupQuotientMapData P Q)
    (D : PrimeStrictTransformData P p hp) :
    Function.Injective (blowupQuotientProjMap F).base ∧
      Set.range (blowupQuotientProjMap F).base = primeStrictTransform D := by sorry
noncomputable def blowupStrictTransformComponentAsSet
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    (F : BlowupQuotientMapData P Q) (d : ℕ) :
    letI : GradedRing P.gradedPieces := P.graded
    letI : GradedRing Q.gradedPieces := Q.graded
    Set A :=
  letI : GradedRing P.gradedPieces := P.graded
  letI : GradedRing Q.gradedPieces := Q.graded
  {a | ∃ ha : a ∈ I ^ d,
    reesHomogeneousElement I d ha ∈
      (blowupStrictTransformIdeal F : Set (blowupAlgebra I))}

theorem blowupStrictTransformComponentAsSet_eq
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    (F : BlowupQuotientMapData P Q) (d : ℕ) :
    blowupStrictTransformComponentAsSet F d =
      ((I ^ d : Ideal A) : Set A) ∩ (p : Set A) := by sorry
theorem primeStrictTransform_eq_vPlus_of_blowupQuotient
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    {hp : p.IsPrime} (F : BlowupQuotientMapData P Q)
    (D : PrimeStrictTransformData P p hp) :
    letI : GradedRing P.gradedPieces := P.graded
    letI : GradedRing Q.gradedPieces := Q.graded
    primeStrictTransform D =
      vPlus P.gradedPieces (blowupStrictTransformIdeal F) := by sorry
theorem exists_separating_blowup_for_incomparable_primes
    {A : Type u} [CommRing A] {p q : Ideal A}
    (hp : p.IsPrime) (hq : q.IsPrime)
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    ∃ P : BlowupPresentation (p + q),
      ∃ Dp : PrimeStrictTransformData P p hp,
        ∃ Dq : PrimeStrictTransformData P q hq,
          Disjoint (primeStrictTransform Dp) (primeStrictTransform Dq) := by sorry
