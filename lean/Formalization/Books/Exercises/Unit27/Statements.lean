import Formalization.Books.Exercises.Unit27.Core
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
  exact Ideal.IsHomogeneous.iff_exists 𝒜 I

theorem homogeneousIdeal_iff_components
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (I : Ideal R) :
    IsHomogeneousIdeal 𝒜 I ↔
      ∀ r, r ∈ I → ∀ n, GradedRing.proj 𝒜 n r ∈ I := by
  constructor
  · intro hI r hr n
    exact hI n hr
  · intro hI n r hr
    exact hI r hr n

theorem homogeneousIdeal_components_mem_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {I : Ideal R} (hI : IsHomogeneousIdeal 𝒜 I) (r : R) :
    r ∈ I ↔ ∀ n, GradedRing.proj 𝒜 n r ∈ I := by
  simpa only [GradedRing.proj_apply] using hI.mem_iff

/-! ## 27.2. The point set `Proj(R)` and its topology -/

/- The point set is the relevant homogeneous-prime subtype supplied by
   `ProjectiveSpectrum`; the following interface records its identification
   with the corresponding subset of `Spec(R)`. -/
theorem projToPrimeSpectrum_injective
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    Function.Injective (projToPrimeSpectrum 𝒜) := by
  intro x y h
  change (⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩ : PrimeSpectrum R) =
    ⟨y.asHomogeneousIdeal.toIdeal, y.isPrime⟩ at h
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  exact congrArg PrimeSpectrum.asIdeal h

theorem projToPrimeSpectrum_inducing
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsInducing (projToPrimeSpectrum 𝒜) := by
  refine ⟨?_⟩
  rw [ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜 |>.eq_generateFrom,
    PrimeSpectrum.isTopologicalBasis_basic_opens.eq_generateFrom,
    induced_generateFrom_eq]
  congr 1
  ext U
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨(↑(PrimeSpectrum.basicOpen r) : Set _), ⟨r, rfl⟩, ?_⟩
    rfl
  · rintro ⟨U, ⟨r, hr⟩, hU⟩
    refine ⟨r, ?_⟩
    rw [← hU, ← hr]
    rfl

theorem projToPrimeSpectrum_isEmbedding
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsEmbedding (projToPrimeSpectrum 𝒜) := by
  exact ⟨projToPrimeSpectrum_inducing 𝒜, projToPrimeSpectrum_injective 𝒜⟩

/-! ## 27.3. Degree-zero localization and standard closed/open sets -/

theorem mem_dPlus_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (f : R) (x : ProjPoints 𝒜) :
    x ∈ dPlus 𝒜 f ↔ f ∉ x.asHomogeneousIdeal := by
  rfl

theorem mem_vPlus_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) (x : ProjPoints 𝒜) :
    x ∈ vPlus 𝒜 I ↔ (I : Set R) ⊆ x.asHomogeneousIdeal := by
  rfl

/-! ## 27.4. The topology of `Proj(R)` -/

theorem isOpen_dPlus
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (f : R) :
    IsOpen (dPlus 𝒜 f) := by
  exact ProjectiveSpectrum.isOpen_basicOpen 𝒜

theorem isOpen_dPlus_of_positive_homogeneous
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {m : ℕ} {f : R} (_hf : f ∈ 𝒜 m) (_hm : 0 < m) :
    IsOpen (dPlus 𝒜 f) := by
  exact isOpen_dPlus 𝒜 f

theorem dPlus_mul
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (f f' : R) :
    dPlus 𝒜 (f * f') = dPlus 𝒜 f ∩ dPlus 𝒜 f' := by
  change (ProjectiveSpectrum.basicOpen 𝒜 (f * f') : Set (ProjectiveSpectrum 𝒜)) =
    (ProjectiveSpectrum.basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜)) ∩
      (ProjectiveSpectrum.basicOpen 𝒜 f' : Set (ProjectiveSpectrum 𝒜))
  rw [ProjectiveSpectrum.basicOpen_mul]
  rfl

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
  rw [dOnProj_eq_iUnion_projections]
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨n, hn⟩
    by_cases h : n = 0
    · left
      simpa [h] using hn
    · right
      exact ⟨⟨n, Nat.pos_of_ne_zero h⟩, hn⟩
  · rintro (hn | ⟨n, hn⟩)
    · exact ⟨0, hn⟩
    · exact ⟨n.1, hn⟩

theorem dOnProj_degree_zero_eq_iUnion_mul
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {g : R} (_hg : g ∈ 𝒜 0) {ι : Type v} (f : ι → R)
    (_hf : ∀ i, ∃ n : ℕ, 0 < n ∧ f i ∈ 𝒜 n)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range f)) :
    dOnProj 𝒜 g = ⋃ i, dPlus 𝒜 (g * f i) := by
  ext x
  simp only [Set.mem_iUnion, mem_dPlus_iff]
  constructor
  · intro hg
    have hfi : ∃ i, f i ∉ x.asHomogeneousIdeal := by
      by_contra h
      apply x.not_irrelevant_le
      exact hspan.trans (Ideal.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        by_contra hfi
        exact h ⟨i, hfi⟩))
    obtain ⟨i, hfi⟩ := hfi
    exact ⟨i, x.isPrime.mul_notMem hg hfi⟩
  · rintro ⟨i, hi⟩ hg
    exact hi (x.asHomogeneousIdeal.toIdeal.mul_mem_right (f i) hg)

theorem dPlus_isTopologicalBasis
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsTopologicalBasis
      {U : Set (ProjPoints 𝒜) |
        ∃ (n : ℕ) (_hn : 0 < n) (f : R), f ∈ 𝒜 n ∧ U = dPlus 𝒜 f} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨n, _hn, f, _hf, rfl⟩
    exact isOpen_dPlus 𝒜 f
  · intro x U hx hU
    obtain ⟨V, ⟨r, rfl⟩, hxV, hVU⟩ :=
      (ProjectiveSpectrum.isTopologicalBasis_basic_opens (𝒜 := 𝒜)).mem_nhds_iff.mp
        (hU.mem_nhds hx)
    change x ∈ dOnProj 𝒜 r at hxV
    change dOnProj 𝒜 r ⊆ U at hVU
    rw [dOnProj_eq_iUnion_projections] at hxV
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxV
    by_cases hn : 0 < n
    · refine ⟨dPlus 𝒜 (GradedRing.proj 𝒜 n r),
        ⟨n, hn, GradedRing.proj 𝒜 n r, SetLike.coe_mem _, rfl⟩, hxn, ?_⟩
      intro y hy
      apply hVU
      rw [dOnProj_eq_iUnion_projections]
      exact Set.mem_iUnion.mpr ⟨n, hy⟩
    · have hpos : ∃ (m : ℕ) (hm : 0 < m) (f : R),
          f ∈ 𝒜 m ∧ f ∉ x.asHomogeneousIdeal := by
        by_contra h
        apply x.not_irrelevant_le
        refine (HomogeneousIdeal.irrelevant_le 𝒜).mpr ?_
        intro m hm z hz
        by_contra hzp
        exact h ⟨m, hm, z, hz, hzp⟩
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      have hxn0 : GradedRing.proj 𝒜 0 r ∉ x.asHomogeneousIdeal :=
        (mem_dPlus_iff 𝒜 _ x).mp hxn
      obtain ⟨m, hm, f, hf, hxf⟩ := hpos
      have hproj0 : GradedRing.proj 𝒜 0 r ∈ 𝒜 0 := by
        rw [GradedRing.proj_apply]
        exact SetLike.coe_mem _
      have hq : GradedRing.proj 𝒜 0 r * f ∈ 𝒜 m := by
        simpa using SetLike.mul_mem_graded hproj0 hf
      refine ⟨dPlus 𝒜 (GradedRing.proj 𝒜 0 r * f),
        ⟨m, hm, _, hq, rfl⟩, ?_, ?_⟩
      · rw [mem_dPlus_iff]
        exact x.isPrime.mul_notMem hxn0 hxf
      · intro y hy
        apply hVU
        have hy' : y ∈ dPlus 𝒜 (GradedRing.proj 𝒜 0 r) ∩ dPlus 𝒜 f := by
          rw [← dPlus_mul]
          exact hy
        rw [dOnProj_eq_iUnion_projections]
        exact Set.mem_iUnion.mpr ⟨0, hy'.1⟩

/- Mathlib's chart isomorphism is the source's canonical bijection and
   homeomorphism `D₊(f) ≅ Spec(R_(f))`. -/
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

/- The source's non-quasi-compact example is represented by the standard
   grading on a polynomial ring in infinitely many variables. -/
abbrev InfinitePolynomialGrading (k : Type u) [CommRing k] :
    ℕ → Submodule k (MvPolynomial ℕ k) :=
  MvPolynomial.homogeneousSubmodule ℕ k

noncomputable def infinitePolynomialProj (k : Type u) [CommRing k] : Type u :=
  letI : GradedAlgebra (InfinitePolynomialGrading k) := MvPolynomial.gradedAlgebra
  ProjectiveSpectrum (InfinitePolynomialGrading k)

theorem infinitePolynomialProj_not_quasiCompact (k : Type u) [Field k] :
    letI : GradedAlgebra (InfinitePolynomialGrading k) := MvPolynomial.gradedAlgebra
    ¬ CompactSpace (ProjectiveSpectrum (InfinitePolynomialGrading k)) := by
  classical
  let _ : GradedAlgebra (InfinitePolynomialGrading k) := MvPolynomial.gradedAlgebra
  intro hcompact
  let _ := hcompact
  have hXrange : Set.range (MvPolynomial.X : ℕ → MvPolynomial ℕ k) =
      MvPolynomial.X '' (Set.univ : Set ℕ) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, Set.mem_univ _, rfl⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  have hspan : (HomogeneousIdeal.irrelevant (InfinitePolynomialGrading k)).toIdeal ≤
      Ideal.span (MvPolynomial.X '' (Set.univ : Set ℕ)) := by
    rw [HomogeneousIdeal.irrelevant_eq_span]
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨n, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hn, hp⟩
    apply (MvPolynomial.mem_ideal_span_X_image (x := p) (s := Set.univ)).mpr
    intro m hm
    have hdeg :=
      (MvPolynomial.mem_homogeneousSubmodule n p).mp hp |>.degree_eq_sum_deg_support hm
    have hsum : 0 < ∑ i ∈ m.support, m i := hdeg ▸ hn
    by_contra hnonempty
    simp only [not_exists, not_and, not_not] at hnonempty
    have hsum_zero : (∑ i ∈ m.support, m i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hnonempty i (Set.mem_univ _)
    exact (Nat.not_lt_zero _ (hsum_zero ▸ hsum))
  have hspan_range : (HomogeneousIdeal.irrelevant (InfinitePolynomialGrading k)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : ℕ → MvPolynomial ℕ k)) := by
    rw [hXrange]
    exact hspan
  have htop :
      (⨆ i, ProjectiveSpectrum.basicOpen (InfinitePolynomialGrading k)
        (MvPolynomial.X i)) = ⊤ := by
    change (⨆ i, AlgebraicGeometry.Proj.basicOpen (InfinitePolynomialGrading k)
        (MvPolynomial.X i)) = ⊤
    exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
      (InfinitePolynomialGrading k)
      (MvPolynomial.X : ℕ → MvPolynomial ℕ k) hspan_range
  have hcover : (Set.univ : Set (ProjectiveSpectrum (InfinitePolynomialGrading k))) ⊆
      ⋃ i, (ProjectiveSpectrum.basicOpen (InfinitePolynomialGrading k) (MvPolynomial.X i) :
        Set (ProjectiveSpectrum (InfinitePolynomialGrading k))) := by
    rw [← TopologicalSpace.Opens.coe_iSup, htop]
    exact subset_rfl
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (ProjectiveSpectrum.basicOpen (InfinitePolynomialGrading k) (MvPolynomial.X i) :
      Set (ProjectiveSpectrum (InfinitePolynomialGrading k))))
    (fun _ => ProjectiveSpectrum.isOpen_basicOpen (InfinitePolynomialGrading k))
    hcover
  obtain ⟨n, hn⟩ := s.exists_notMem
  let q : MvPolynomial ℕ k →+* MvPolynomial ℕ k :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i => if i ∈ s then 0 else MvPolynomial.X i)
  let qg : InfinitePolynomialGrading k →+*ᵍ InfinitePolynomialGrading k :=
    { q with
      map_mem := by
        intro d p hp
        rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
        simpa [q] using hp.eval₂ (n := 1) MvPolynomial.C
          (fun i => if i ∈ s then 0 else MvPolynomial.X i)
          (fun r => MvPolynomial.isHomogeneous_C _ _)
          (fun i => by
            by_cases hi : i ∈ s
            · simp [hi, MvPolynomial.isHomogeneous_zero]
            · simp [hi, MvPolynomial.isHomogeneous_X]) }
  let P : HomogeneousIdeal (InfinitePolynomialGrading k) :=
    HomogeneousIdeal.comap qg (⊥ : HomogeneousIdeal (InfinitePolynomialGrading k))
  have hPprime : P.toIdeal.IsPrime := by
    dsimp [P]
    infer_instance
  let x : ProjectiveSpectrum (InfinitePolynomialGrading k) :=
    { asHomogeneousIdeal := P
      isPrime := hPprime
      not_irrelevant_le := by
        intro hle
        have hxn_gr : MvPolynomial.X n ∈ InfinitePolynomialGrading k 1 := by
          exact (MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X n)).mpr
            (MvPolynomial.isHomogeneous_X k n)
        have hxn_irr : MvPolynomial.X n ∈
            HomogeneousIdeal.irrelevant (InfinitePolynomialGrading k) :=
          HomogeneousIdeal.mem_irrelevant_of_mem (InfinitePolynomialGrading k)
            (by decide) hxn_gr
        have hxnP : MvPolynomial.X n ∈ P := hle hxn_irr
        have hqzero : q (MvPolynomial.X n) = 0 := by
          change q (MvPolynomial.X n) ∈ (⊥ : Ideal (MvPolynomial ℕ k)) at hxnP
          simpa only [Ideal.mem_bot] using hxnP
        have hqeval : q (MvPolynomial.X n) = MvPolynomial.X n := by
          simp [q, hn]
        have : MvPolynomial.X n = 0 := hqeval ▸ hqzero
        exact MvPolynomial.X_ne_zero n this }
  have hXiP : ∀ i ∈ s, MvPolynomial.X i ∈ P := by
    intro i hi
    change q (MvPolynomial.X i) ∈ (⊥ : Ideal (MvPolynomial ℕ k))
    simp [q, hi]
  rcases Set.mem_iUnion.mp (hs (Set.mem_univ x)) with ⟨i, hi⟩
  rcases Set.mem_iUnion.mp hi with ⟨his, hxi⟩
  have hnot : MvPolynomial.X i ∉ x.asHomogeneousIdeal :=
    (ProjectiveSpectrum.mem_coe_basicOpen (InfinitePolynomialGrading k)
      (MvPolynomial.X i) x).mp hxi
  exact hnot (hXiP i his)

theorem exists_homogeneousIdeal_eq_vPlus
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (T : Set (ProjPoints 𝒜)) (hT : IsClosed T) :
    ∃ I : HomogeneousIdeal 𝒜, T = vPlus 𝒜 I := by
  sorry

/-! ## 27.5. The map to the degree-zero spectrum -/

noncomputable def projToSpecZeroPointMap
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    ProjPoints 𝒜 → PrimeSpectrum (𝒜 0) :=
  (projToSpecZeroScheme 𝒜).base

theorem projToSpecZeroPointMap_continuous
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    Continuous (projToSpecZeroPointMap 𝒜) := by
  sorry

/-! ## 27.6. The one-variable polynomial example -/

/- `MvPolynomial (Fin 1) A` is Mathlib's graded polynomial presentation; its
   standard algebra equivalence identifies it with the usual one-variable
   polynomial ring. -/
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
  sorry

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

theorem oneVariableProjToSpec_bijective (A : Type u) [CommRing A] :
    Function.Bijective (oneVariableProjToSpec A).base := by
  sorry

theorem oneVariableProjToSpec_isHomeomorph (A : Type u) [CommRing A] :
    IsHomeomorph (oneVariableProjToSpec A).base := by
  sorry

/-! ## 27.7. Blowing up and strict transforms -/

theorem blowupBaseOpen_isOpen {A : Type u} [CommRing A] (I : Ideal A) :
    IsOpen (blowupBaseOpen I) := by
  sorry

theorem blowupRestrictionMap_isHomeomorph
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) :
    IsHomeomorph (blowupRestrictionMap P) := by
  sorry

theorem strictTransform_conditions
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    D.genericPoint ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ¬ (D.Z : Set (PrimeSpectrum A)) ⊆
        PrimeSpectrum.zeroLocus (I : Set A) ∧
      D.genericPoint ∈ blowupBaseOpen I ∧
      ((D.Z : Set (PrimeSpectrum A)) ∩ blowupBaseOpen I).Nonempty := by
  sorry

theorem strictTransform_eq_viaOpen
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    strictTransform D = strictTransformViaOpen D := by
  sorry

/-! ## 27.8. The two-variable blowup examples -/

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
  sorry

noncomputable def twoVariableBlowupPresentation (k : Type u) [Field k] :
    BlowupPresentation (twoVariableMaximalIdeal k) :=
  Classical.choice (twoVariableBlowupPresentation_exists k)

theorem twoVariableXIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableXIdeal k).IsPrime := by
  sorry

theorem twoVariableYIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableYIdeal k).IsPrime := by
  sorry

theorem twoVariableParabolaIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableParabolaIdeal k).IsPrime := by
  sorry

theorem twoVariableXStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableXIdeal k) (twoVariableXIdeal_isPrime k)) := by
  sorry

theorem twoVariableYStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableYIdeal k) (twoVariableYIdeal_isPrime k)) := by
  sorry

theorem twoVariableParabolaStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableParabolaIdeal k) (twoVariableParabolaIdeal_isPrime k)) := by
  sorry

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
  sorry

theorem twoVariable_x_parabola_strictTransforms_not_disjoint
    (k : Type u) [Field k] :
    ¬ Disjoint
      (primeStrictTransform (twoVariableXStrictTransformData k))
      (primeStrictTransform (twoVariableParabolaStrictTransformData k)) := by
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
          Disjoint (primeStrictTransform dx) (primeStrictTransform dp) := by
  sorry

/-! ## 27.9. When `Proj` is empty or irreducible -/

theorem projPoints_isEmpty_of_eventually_zero
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (hzero : ∀ᶠ n in Filter.atTop, 𝒜 n = ⊥) :
    IsEmpty (ProjPoints 𝒜) := by
  sorry

theorem projPoints_irreducibleSpace_of_domain
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] [IsDomain R]
    (hplus : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) :
    IrreducibleSpace (ProjPoints 𝒜) := by
  sorry

theorem empty_projPoints_not_irreducible
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    [IsEmpty (ProjPoints 𝒜)] :
    ¬ IsIrreducible (Set.univ : Set (ProjPoints 𝒜)) := by
  sorry

/-! ## 27.10. Blowing up: Part III -/

abbrev blowupQuotientRing {A : Type u} [CommRing A] (p : Ideal A) := A ⧸ p

abbrev blowupQuotientIdeal {A : Type u} [CommRing A]
    (I p : Ideal A) : Ideal (blowupQuotientRing p) :=
  quotientIdeal I p

theorem exists_surjective_blowupQuotientRingHom
    {A : Type u} [CommRing A] {I p : Ideal A} :
    ∃ φ : blowupAlgebra I →+* blowupAlgebra (blowupQuotientIdeal I p),
      Function.Surjective φ := by
  sorry

theorem exists_blowupQuotientMapData
    {A : Type u} [CommRing A] {I p : Ideal A}
    (P : BlowupPresentation I)
    (Q : BlowupPresentation (blowupQuotientIdeal I p)) :
    Nonempty (BlowupQuotientMapData P Q) := by
  sorry

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
      Set.range (blowupQuotientProjMap F).base = primeStrictTransform D := by
  sorry

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
      ((I ^ d : Ideal A) : Set A) ∩ (p : Set A) := by
  sorry

theorem primeStrictTransform_eq_vPlus_of_blowupQuotient
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    {hp : p.IsPrime} (F : BlowupQuotientMapData P Q)
    (D : PrimeStrictTransformData P p hp) :
    letI : GradedRing P.gradedPieces := P.graded
    letI : GradedRing Q.gradedPieces := Q.graded
    primeStrictTransform D =
      vPlus P.gradedPieces (blowupStrictTransformIdeal F) := by
  sorry

theorem exists_separating_blowup_for_incomparable_primes
    {A : Type u} [CommRing A] {p q : Ideal A}
    (hp : p.IsPrime) (hq : q.IsPrime)
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    ∃ P : BlowupPresentation (p + q),
      ∃ Dp : PrimeStrictTransformData P p hp,
        ∃ Dq : PrimeStrictTransformData P q hq,
          Disjoint (primeStrictTransform Dp) (primeStrictTransform Dq) := by
  sorry

end Formalization.Books.Exercises.Unit27
