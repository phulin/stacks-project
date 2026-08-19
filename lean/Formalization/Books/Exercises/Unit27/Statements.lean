import Formalization.Books.Exercises.Unit27.Core
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

theorem oneVariableDegreeZeroEquiv_spec (A : Type u) [CommRing A] (a : A) :
    (((oneVariableDegreeZeroEquiv A).symm a : oneVariablePolynomialGrading A 0) :
        oneVariablePolynomialRing A) =
      MvPolynomial.C a := by sorry
noncomputable def oneVariableProjScheme (A : Type u) [CommRing A] : Scheme :=
  letI : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  AlgebraicGeometry.«Proj» (oneVariablePolynomialGrading A)

noncomputable def oneVariableProjToSpec (A : Type u) [CommRing A] :
    oneVariableProjScheme A ⟶ Spec (CommRingCat.of A) :=
  letI : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A) ≫
    Spec.map (CommRingCat.ofHom (oneVariableDegreeZeroEquiv A).symm.toRingHom)

theorem oneVariableProjToSpec_bijective (A : Type u) [CommRing A] :
    Function.Bijective (oneVariableProjToSpec A).base := by sorry
theorem oneVariableProjToSpec_isHomeomorph (A : Type u) [CommRing A] :
    IsHomeomorph (oneVariableProjToSpec A).base := by sorry
theorem blowupBaseOpen_isOpen {A : Type u} [CommRing A] (I : Ideal A) :
    IsOpen (blowupBaseOpen I) := by sorry
theorem blowupRestrictionMap_isHomeomorph
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) :
    IsHomeomorph (blowupRestrictionMap P) := by sorry
theorem strictTransform_conditions
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    D.genericPoint ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ¬ (D.Z : Set (PrimeSpectrum A)) ⊆
        PrimeSpectrum.zeroLocus (I : Set A) ∧
      D.genericPoint ∈ blowupBaseOpen I ∧
      ((D.Z : Set (PrimeSpectrum A)) ∩ blowupBaseOpen I).Nonempty := by sorry
theorem strictTransform_eq_viaOpen
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    strictTransform D = strictTransformViaOpen D := by sorry
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
    Nonempty (BlowupPresentation (twoVariableMaximalIdeal k)) := by sorry
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
