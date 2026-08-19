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
    rfl
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
      rfl
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
theorem blowupRestrictionMap_isHomeomorph
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) :
    IsHomeomorph (blowupRestrictionMap P) := by
  letI : GradedRing P.gradedPieces := P.graded
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
  let r := P.degreeZeroEquiv.symm (a : A)
  let e : Localization.Away r ≃+*
      degreeZeroLocalization P.gradedPieces f :=
    RingEquiv.ofBijective
      (Localization.awayMap
        (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
          (Submonoid.powers f)) r) hbij
  let s : Set (PrimeSpectrum A) :=
    {p | e₀.symm p ∈ PrimeSpectrum.basicOpen r}
  have hs : s ⊆ blowupBaseOpen I := by
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
  let hsub := localizationAwayComapSubtype_isHomeomorph (r : P.gradedPieces 0)
  let htransport := homeomorphSubtypePreimage_isHomeomorph e₀ s
  let hnested := subtypeSubtype_isHomeomorph hs
  let H : {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} ≃ₜ
      {x : α // x ∈ (U a).carrier} :=
    (dPlusHomeomorph P.graded hf (by omega)).trans
      ((PrimeSpectrum.homeomorphOfRingEquiv e).symm.trans
        (hsub.homeomorph.trans (htransport.homeomorph.trans hnested.homeomorph)))
  apply (isHomeomorph_iff_exists_homeomorph).2
  refine ⟨H, ?_⟩
  sorry
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
    (twoVariableXIdeal k).IsPrime := by sorry
theorem twoVariableYIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableYIdeal k).IsPrime := by sorry
theorem twoVariableParabolaIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableParabolaIdeal k).IsPrime := by sorry
theorem twoVariableXStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableXIdeal k) (twoVariableXIdeal_isPrime k)) := by sorry
theorem twoVariableYStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableYIdeal k) (twoVariableYIdeal_isPrime k)) := by sorry
theorem twoVariableParabolaStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableParabolaIdeal k) (twoVariableParabolaIdeal_isPrime k)) := by sorry
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
      (primeStrictTransform (twoVariableYStrictTransformData k)) := by sorry
theorem twoVariable_x_parabola_strictTransforms_not_disjoint
    (k : Type u) [Field k] :
    ¬ Disjoint
      (primeStrictTransform (twoVariableXStrictTransformData k))
      (primeStrictTransform (twoVariableParabolaStrictTransformData k)) := by sorry
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
