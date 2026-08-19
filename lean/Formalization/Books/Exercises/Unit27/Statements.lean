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
  refine ⟨ProjectiveSpectrum.vanishingIdeal T, ?_⟩
  rw [vPlus, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hT.closure_eq]

/-! ## 27.5. The map to the degree-zero spectrum -/

noncomputable def projToSpecZeroPointMap
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    ProjPoints 𝒜 → PrimeSpectrum (𝒜 0) :=
  (projToSpecZeroScheme 𝒜).base

theorem projToSpecZeroPointMap_continuous
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    Continuous (projToSpecZeroPointMap 𝒜) := by
  exact (projToSpecZeroScheme 𝒜).continuous

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
  let e : (oneVariablePolynomialGrading A 0) ≃+* A :=
    { toFun := fun p => MvPolynomial.constantCoeff p.1
      invFun := fun a => ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ _⟩
      left_inv := by
        intro p
        apply Subtype.ext
        exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
          ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p.1)).mpr p.2)).symm
      right_inv := by
        intro a
        simp
      map_add' := by
        intro p q
        simp
      map_mul' := by
        intro p q
        simp }
  refine ⟨⟨e, ?_⟩⟩
  intro a
  simp [e]

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
  let _ : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  let X1 : oneVariablePolynomialRing A := MvPolynomial.X (0 : Fin 1)
  have hX : X1 ∈ oneVariablePolynomialGrading A 1 := by
    exact (MvPolynomial.mem_homogeneousSubmodule 1 X1).mpr
      (MvPolynomial.isHomogeneous_X A 0)
  have hspan : (HomogeneousIdeal.irrelevant (oneVariablePolynomialGrading A)).toIdeal ≤
      Ideal.span ({X1} : Set (oneVariablePolynomialRing A)) := by
    rw [HomogeneousIdeal.irrelevant_eq_span]
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨n, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hn, hp⟩
    rw [show ({X1} : Set (oneVariablePolynomialRing A)) =
        MvPolynomial.X '' ({0} : Set (Fin 1)) by
      ext q
      simp [X1]]
    apply (MvPolynomial.mem_ideal_span_X_image (x := p) (s := ({0} : Set (Fin 1)))).mpr
    intro m hm
    have hdeg :=
      (MvPolynomial.mem_homogeneousSubmodule n p).mp hp |>.degree_eq_sum_deg_support hm
    have hsum : 0 < ∑ i ∈ m.support, m i := hdeg ▸ hn
    have hm0 : m 0 ≠ 0 := by
      by_contra hm0
      have hsum_zero : (∑ i ∈ m.support, m i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi0 : i = 0 := Fin.eq_zero i
        simp [hi0, hm0]
      exact (Nat.not_lt_zero _ (hsum_zero ▸ hsum))
    exact ⟨0, by simp, hm0⟩
  have hfactor : ∀ (n : ℕ) (p : oneVariablePolynomialRing A),
      p ∈ oneVariablePolynomialGrading A n →
        p = MvPolynomial.C (p.coeff (Finsupp.single (0 : Fin 1) n)) *
          MvPolynomial.X 0 ^ n := by
    intro n p hp
    apply MvPolynomial.ext
    intro m
    by_cases hm : m = Finsupp.single (0 : Fin 1) n
    · rw [hm, MvPolynomial.C_mul_X_pow_eq_monomial]
      simp
    · have hmzero : MvPolynomial.coeff m p = 0 := by
        by_contra hmzero
        apply hm
        have hmem : m ∈ p.support := MvPolynomial.mem_support_iff.mpr hmzero
        have hdeg :=
          (MvPolynomial.mem_homogeneousSubmodule n p).mp hp |>.degree_eq_sum_deg_support hmem
        have hsum0 : m 0 = (∑ i ∈ m.support, m i) := by
          classical
          rw [Finset.sum_eq_single 0]
          · intro i hi hi0
            exact (hi0 (Fin.eq_zero i)).elim
          · intro h0
            simpa [Finsupp.mem_support_iff] using h0
        have hmn : m 0 = n := hsum0.trans hdeg.symm
        apply Finsupp.ext
        intro i
        have hi0 : i = 0 := Fin.eq_zero i
        simp [hi0, hmn]
      rw [MvPolynomial.C_mul_X_pow_eq_monomial]
      simp only [MvPolynomial.coeff_monomial]
      split_ifs with h
      · exact (hm h.symm).elim
      · exact hmzero
  have hS : Submonoid.powers X1 ≤ nonZeroDivisors (oneVariablePolynomialRing A) := by
    rintro _ ⟨n, rfl⟩
    exact isRegular_iff_mem_nonZeroDivisors.mp
      (MvPolynomial.isRegular_X_pow (R := A) (σ := Fin 1) n)
  have hf0inj : Function.Injective
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers X1)) := by
    intro a b hab
    apply Subtype.ext
    have hval := congrArg HomogeneousLocalization.val hab
    change algebraMap (oneVariablePolynomialRing A) (Localization (Submonoid.powers X1)) a =
      algebraMap (oneVariablePolynomialRing A) (Localization (Submonoid.powers X1)) b at hval
    exact IsLocalization.injective _ hS hval
  have hf0surj : Function.Surjective
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers X1)) := by
    intro z
    obtain ⟨n, p, hp, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (oneVariablePolynomialGrading A) hX z
    let a0 : oneVariablePolynomialGrading A 0 :=
      ⟨MvPolynomial.C (p.coeff (Finsupp.single (0 : Fin 1) n)),
        MvPolynomial.isHomogeneous_C _ _⟩
    refine ⟨a0, ?_⟩
    apply HomogeneousLocalization.val_injective
    change algebraMap (oneVariablePolynomialRing A)
      (Localization (Submonoid.powers X1)) a0.1 =
      Localization.mk p ⟨X1 ^ n, by
        exact (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩
    have hp' : p ∈ oneVariablePolynomialGrading A n := by simpa using hp
    rw [hfactor n p hp']
    rw [Localization.mk_eq_mk']
    dsimp [X1]
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    dsimp [a0]
    simp only [map_mul, map_pow]
  have hf0 : Function.Bijective
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers X1)) := ⟨hf0inj, hf0surj⟩
  let eAway : (oneVariablePolynomialGrading A 0) ≃+*
      HomogeneousLocalization.Away (oneVariablePolynomialGrading A) X1 :=
    RingEquiv.ofBijective _ hf0
  have htopi :
      (⨆ i : Fin 1, ProjectiveSpectrum.basicOpen (oneVariablePolynomialGrading A)
        (MvPolynomial.X i)) = ⊤ := by
    change (⨆ i : Fin 1, AlgebraicGeometry.Proj.basicOpen
        (oneVariablePolynomialGrading A) (MvPolynomial.X i)) = ⊤
    have hrange : (HomogeneousIdeal.irrelevant (oneVariablePolynomialGrading A)).toIdeal ≤
        Ideal.span (Set.range (MvPolynomial.X : Fin 1 → oneVariablePolynomialRing A)) := by
      rw [show Set.range (MvPolynomial.X : Fin 1 → oneVariablePolynomialRing A) =
          ({X1} : Set (oneVariablePolynomialRing A)) by
        ext q
        simp [X1, eq_comm]]
      exact hspan
    exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
      (oneVariablePolynomialGrading A) (MvPolynomial.X : Fin 1 → oneVariablePolynomialRing A) hrange
  have htop : AlgebraicGeometry.Proj.basicOpen (oneVariablePolynomialGrading A) X1 = ⊤ := by
    change ProjectiveSpectrum.basicOpen (oneVariablePolynomialGrading A) X1 = ⊤
    simpa [X1] using htopi
  have hawayIso : IsIso
      (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0)) :=
    AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
      rw [AlgebraicGeometry.Proj.opensRange_awayι, htop])
  have haway : Function.Bijective
      (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0)).base :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso _
  have hSpecAway : Function.Bijective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
          (Submonoid.powers X1)))).base := by
    change Function.Bijective (PrimeSpectrum.comap
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers X1)))
    exact (PrimeSpectrum.comapEquiv eAway).symm.bijective
  have hcomp : Function.Bijective
      ((AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A)).base ∘
        (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
          (Nat.zero_lt_succ 0)).base) := by
    have heq := congrArg (fun f => f.base)
      (AlgebraicGeometry.Proj.awayι_toSpecZero (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0))
    change Function.Bijective
      ((AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0) ≫
        AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A)).base)
    rw [heq]
    exact hSpecAway
  have hzero : Function.Bijective
      (AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A)).base := by
    constructor
    · intro x y hxy
      obtain ⟨x, rfl⟩ := haway.surjective x
      obtain ⟨y, rfl⟩ := haway.surjective y
      have hxy' : x = y := hcomp.injective (by
        simpa [Function.comp_def] using hxy)
      exact congrArg
        (fun z => (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
          (Nat.zero_lt_succ 0)).base z) hxy'
    · intro y
      obtain ⟨z, hz⟩ := hcomp.surjective y
      exact ⟨(AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0)).base z, hz⟩
  have hSpec0 : Function.Bijective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (oneVariableDegreeZeroEquiv A).symm.toRingHom)).base := by
    change Function.Bijective (PrimeSpectrum.comap
      (oneVariableDegreeZeroEquiv A).symm.toRingHom)
    exact (PrimeSpectrum.comapEquiv (oneVariableDegreeZeroEquiv A)).bijective
  change Function.Bijective (fun x =>
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (oneVariableDegreeZeroEquiv A).symm.toRingHom)).base
      ((AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A)).base x))
  exact hSpec0.comp hzero

private theorem oneVariableProj_X_basicOpen_eq_top (A : Type u) [CommRing A] :
    let _ : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
    ProjectiveSpectrum.basicOpen (oneVariablePolynomialGrading A)
        (MvPolynomial.X (0 : Fin 1)) = ⊤ := by
  let _ : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  let X1 : oneVariablePolynomialRing A := MvPolynomial.X (0 : Fin 1)
  have hX : X1 ∈ oneVariablePolynomialGrading A 1 := by
    exact (MvPolynomial.mem_homogeneousSubmodule 1 X1).mpr
      (MvPolynomial.isHomogeneous_X A 0)
  have hspan : (HomogeneousIdeal.irrelevant (oneVariablePolynomialGrading A)).toIdeal ≤
      Ideal.span ({X1} : Set (oneVariablePolynomialRing A)) := by
    rw [HomogeneousIdeal.irrelevant_eq_span]
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨n, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hn, hp⟩
    rw [show ({X1} : Set (oneVariablePolynomialRing A)) =
        MvPolynomial.X '' ({0} : Set (Fin 1)) by
      ext q
      simp [X1]]
    apply (MvPolynomial.mem_ideal_span_X_image (x := p) (s := ({0} : Set (Fin 1)))).mpr
    intro m hm
    have hdeg :=
      (MvPolynomial.mem_homogeneousSubmodule n p).mp hp |>.degree_eq_sum_deg_support hm
    have hsum : 0 < ∑ i ∈ m.support, m i := hdeg ▸ hn
    have hm0 : m 0 ≠ 0 := by
      by_contra hm0
      have hsum_zero : (∑ i ∈ m.support, m i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi0 : i = 0 := Fin.eq_zero i
        simp [hi0, hm0]
      exact (Nat.not_lt_zero _ (hsum_zero ▸ hsum))
    exact ⟨0, by simp, hm0⟩
  have htopi :
      (⨆ i : Fin 1, ProjectiveSpectrum.basicOpen (oneVariablePolynomialGrading A)
        (MvPolynomial.X i)) = ⊤ := by
    change (⨆ i : Fin 1, AlgebraicGeometry.Proj.basicOpen
        (oneVariablePolynomialGrading A) (MvPolynomial.X i)) = ⊤
    have hrange : (HomogeneousIdeal.irrelevant (oneVariablePolynomialGrading A)).toIdeal ≤
        Ideal.span (Set.range (MvPolynomial.X : Fin 1 → oneVariablePolynomialRing A)) := by
      rw [show Set.range (MvPolynomial.X : Fin 1 → oneVariablePolynomialRing A) =
          ({X1} : Set (oneVariablePolynomialRing A)) by
        ext q
        simp [X1, eq_comm]]
      exact hspan
    exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
      (oneVariablePolynomialGrading A) (MvPolynomial.X : Fin 1 → oneVariablePolynomialRing A) hrange
  simpa [X1] using htopi

private theorem oneVariable_fromZero_bijective (A : Type u) [CommRing A] :
    let _ : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
    Function.Bijective
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 1)))) := by
  let _ : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  let X1 : oneVariablePolynomialRing A := MvPolynomial.X (0 : Fin 1)
  have hX : X1 ∈ oneVariablePolynomialGrading A 1 := by
    exact (MvPolynomial.mem_homogeneousSubmodule 1 X1).mpr
      (MvPolynomial.isHomogeneous_X A 0)
  have hfactor : ∀ (n : ℕ) (p : oneVariablePolynomialRing A),
      p ∈ oneVariablePolynomialGrading A n →
        p = MvPolynomial.C (p.coeff (Finsupp.single (0 : Fin 1) n)) *
          MvPolynomial.X 0 ^ n := by
    intro n p hp
    apply MvPolynomial.ext
    intro m
    by_cases hm : m = Finsupp.single (0 : Fin 1) n
    · rw [hm, MvPolynomial.C_mul_X_pow_eq_monomial]
      simp
    · have hmzero : MvPolynomial.coeff m p = 0 := by
        by_contra hmzero
        apply hm
        have hmem : m ∈ p.support := MvPolynomial.mem_support_iff.mpr hmzero
        have hdeg :=
          (MvPolynomial.mem_homogeneousSubmodule n p).mp hp |>.degree_eq_sum_deg_support hmem
        have hsum0 : m 0 = (∑ i ∈ m.support, m i) := by
          classical
          rw [Finset.sum_eq_single 0]
          · intro i hi hi0
            exact (hi0 (Fin.eq_zero i)).elim
          · intro h0
            simpa [Finsupp.mem_support_iff] using h0
        have hmn : m 0 = n := hsum0.trans hdeg.symm
        apply Finsupp.ext
        intro i
        have hi0 : i = 0 := Fin.eq_zero i
        simp [hi0, hmn]
      rw [MvPolynomial.C_mul_X_pow_eq_monomial]
      simp only [MvPolynomial.coeff_monomial]
      split_ifs with h
      · exact (hm h.symm).elim
      · exact hmzero
  have hS : Submonoid.powers X1 ≤ nonZeroDivisors (oneVariablePolynomialRing A) := by
    rintro _ ⟨n, rfl⟩
    exact isRegular_iff_mem_nonZeroDivisors.mp
      (MvPolynomial.isRegular_X_pow (R := A) (σ := Fin 1) n)
  have hf0inj : Function.Injective
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers X1)) := by
    intro a b hab
    apply Subtype.ext
    have hval := congrArg HomogeneousLocalization.val hab
    change algebraMap (oneVariablePolynomialRing A) (Localization (Submonoid.powers X1)) a =
      algebraMap (oneVariablePolynomialRing A) (Localization (Submonoid.powers X1)) b at hval
    exact IsLocalization.injective _ hS hval
  have hf0surj : Function.Surjective
      (HomogeneousLocalization.fromZeroRingHom (oneVariablePolynomialGrading A)
        (Submonoid.powers X1)) := by
    intro z
    obtain ⟨n, p, hp, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (oneVariablePolynomialGrading A) hX z
    let a0 : oneVariablePolynomialGrading A 0 :=
      ⟨MvPolynomial.C (p.coeff (Finsupp.single (0 : Fin 1) n)),
        MvPolynomial.isHomogeneous_C _ _⟩
    refine ⟨a0, ?_⟩
    apply HomogeneousLocalization.val_injective
    change algebraMap (oneVariablePolynomialRing A)
      (Localization (Submonoid.powers X1)) a0.1 =
      Localization.mk p ⟨X1 ^ n, by
        exact (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩
    have hp' : p ∈ oneVariablePolynomialGrading A n := by simpa using hp
    rw [hfactor n p hp']
    rw [Localization.mk_eq_mk']
    dsimp [X1]
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    dsimp [a0]
    simp only [map_mul, map_pow]
  exact ⟨hf0inj, hf0surj⟩

theorem oneVariableProjToSpec_isHomeomorph (A : Type u) [CommRing A] :
    IsHomeomorph (oneVariableProjToSpec A).base := by
  let _ : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  let X1 : oneVariablePolynomialRing A := MvPolynomial.X (0 : Fin 1)
  have hX : X1 ∈ oneVariablePolynomialGrading A 1 := by
    exact (MvPolynomial.mem_homogeneousSubmodule 1 X1).mpr
      (MvPolynomial.isHomogeneous_X A 0)
  have htop : AlgebraicGeometry.Proj.basicOpen (oneVariablePolynomialGrading A) X1 = ⊤ := by
    change ProjectiveSpectrum.basicOpen (oneVariablePolynomialGrading A) X1 = ⊤
    simpa [X1] using oneVariableProj_X_basicOpen_eq_top A
  have hawayIso : IsIso
      (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0)) :=
    AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
      rw [AlgebraicGeometry.Proj.opensRange_awayι, htop])
  have haway : Function.Bijective
      (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0)).base :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso _
  have hawayHomeo : IsHomeomorph
      (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0)).base := by
    refine ⟨by fun_prop, ?_, haway⟩
    exact (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
      (Nat.zero_lt_succ 0)).isOpenEmbedding.isOpenMap
  have hf0 := oneVariable_fromZero_bijective A
  let eAway : (oneVariablePolynomialGrading A 0) ≃+*
      HomogeneousLocalization.Away (oneVariablePolynomialGrading A) X1 :=
    RingEquiv.ofBijective _ hf0
  let e : A ≃+* HomogeneousLocalization.Away (oneVariablePolynomialGrading A) X1 :=
    (oneVariableDegreeZeroEquiv A).symm.trans eAway
  have hcat :
      AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
          (Nat.zero_lt_succ 0) ≫ oneVariableProjToSpec A =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom e.toRingHom) := by
    dsimp [oneVariableProjToSpec, oneVariableProjScheme]
    rw [← Category.assoc]
    rw [AlgebraicGeometry.Proj.awayι_toSpecZero]
    rw [← AlgebraicGeometry.Spec.map_comp]
    rfl
  have hcompHomeo : IsHomeomorph
      ((oneVariableProjToSpec A).base ∘
        (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
          (Nat.zero_lt_succ 0)).base) := by
    change IsHomeomorph
      ((AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
          (Nat.zero_lt_succ 0) ≫ oneVariableProjToSpec A).base)
    rw [hcat]
    change IsHomeomorph (PrimeSpectrum.comap e.toRingHom)
    exact PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective
  refine ⟨by fun_prop, ?_, oneVariableProjToSpec_bijective A⟩
  intro U hU
  dsimp [oneVariableProjScheme] at U
  have hpre : IsOpen
      ((AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
          (Nat.zero_lt_succ 0)).base ⁻¹' U) :=
    hU.preimage hawayHomeo.continuous
  have himg := hcompHomeo.isOpenMap _ hpre
  have hEq :
      (oneVariableProjToSpec A).base '' U =
      ((oneVariableProjToSpec A).base ∘
        (AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
          (Nat.zero_lt_succ 0)).base) ''
        ((AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
          (Nat.zero_lt_succ 0)).base ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, rfl⟩ := haway.surjective z
      exact ⟨x, hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(AlgebraicGeometry.Proj.awayι (oneVariablePolynomialGrading A) X1 hX
        (Nat.zero_lt_succ 0)).base x, hx, rfl⟩
  rw [hEq]
  exact himg

/-! ## 27.7. Blowing up and strict transforms -/

theorem blowupBaseOpen_isOpen {A : Type u} [CommRing A] (I : Ideal A) :
    IsOpen (blowupBaseOpen I) := by
  unfold blowupBaseOpen
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

private theorem blowup_base_mem_iff
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I)
    (x : blowupProjPoints P) (a : A) :
    letI : GradedRing P.gradedPieces := P.graded
    a ∈ ((blowupMap P).base x).asIdeal ↔
      ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) ∈
        x.asHomogeneousIdeal := by
  dsimp
  simp [blowupMap, AlgebraicGeometry.Proj.toSpecZero]

private theorem blowup_rees_not_mem
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) (x : blowupProjPoints P)
    {a : A} (ha : a ∈ I)
    (hbase : a ∉ ((blowupMap P).base x).asIdeal) :
    letI : GradedRing P.gradedPieces := P.graded
    reesHomogeneousElement I 1 (by simpa using ha) ∉ x.asHomogeneousIdeal := by
  dsimp
  have ha1 : a ∈ I ^ 1 := by simpa using ha
  intro hfx
  have ha0 :
      ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) ∉
        x.asHomogeneousIdeal := by
    intro ha0x
    exact hbase ((blowup_base_mem_iff P x a).mpr ha0x)
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro m hm g hg
  obtain ⟨c, hc, hcg⟩ := (P.gradedPieces_spec m g).mp hg
  have hmul :
      (reesHomogeneousElement I 1 ha1) ^ m *
          ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) =
        ((P.degreeZeroEquiv.symm (a ^ m) : P.gradedPieces 0) : blowupAlgebra I) * g := by
    apply Subtype.ext
    apply Polynomial.ext
    intro d
    rw [hcg, reesHomogeneousElement, Polynomial.coeff_mul,
      Polynomial.coeff_mul, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    simp [P.degreeZeroEquiv_spec, reesHomogeneousElement]
  have hleft :
      (reesHomogeneousElement I 1 ha1) ^ m *
          ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
        x.asHomogeneousIdeal :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem x.asHomogeneousIdeal hfx m)
  have hright :
      ((P.degreeZeroEquiv.symm (a ^ m) : P.gradedPieces 0) : blowupAlgebra I) * g ∈
        x.asHomogeneousIdeal := hmul ▸ hleft
  have ham :
      ((P.degreeZeroEquiv.symm (a ^ m) : P.gradedPieces 0) : blowupAlgebra I) ∉
        x.asHomogeneousIdeal := by
    intro hamx
    apply ha0
    rw [← P.degreeZeroEquiv.map_pow]
    exact (show ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) ^ m ∈
        x.asHomogeneousIdeal from x.asHomogeneousIdeal.pow_mem hamx m)
  exact x.isPrime.mem_or_mem hright |>.resolve_left ham

private theorem blowup_square_rees_not_mem
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) (x : blowupProjPoints P)
    {a : A} (ha : a ∈ I)
    (hbase : a ∉ ((blowupMap P).base x).asIdeal) :
    letI : GradedRing P.gradedPieces := P.graded
    reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha) ∉
      x.asHomogeneousIdeal := by
  dsimp
  have ha1 : a ∈ I ^ 1 := by simpa using ha
  have hmem :
      ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) ∉
        x.asHomogeneousIdeal := by
    intro h
    exact hbase ((blowup_base_mem_iff P x a).mpr h)
  have hrees := blowup_rees_not_mem P x ha hbase
  have hfactor :
      reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha) =
        ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) *
          reesHomogeneousElement I 1 ha1 := by
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    rw [reesHomogeneousElement, P.degreeZeroEquiv_spec,
      reesHomogeneousElement, Polynomial.coeff_mul,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial]
    simp [mul_comm]
  intro h
  apply (x.isPrime.mul_notMem hmem hrees)
  rw [← hfactor]
  exact h

private theorem blowup_dplus_base_not_mem
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) (x : blowupProjPoints P)
    {a : A} (ha : a ∈ I)
    (hf : reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha) ∉
      x.asHomogeneousIdeal) :
    letI : GradedRing P.gradedPieces := P.graded
    a * a ∉ ((blowupMap P).base x).asIdeal := by
  dsimp
  have ha1 : a ∈ I ^ 1 := by simpa using ha
  intro hxa
  obtain ⟨hxa', _⟩ := ((blowupMap P).base x).isPrime.mem_or_mem hxa
  have hmem := (blowup_base_mem_iff P x a).mpr hxa'
  have hfactor :
      reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha) =
        ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) *
          reesHomogeneousElement I 1 ha1 := by
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    rw [reesHomogeneousElement, P.degreeZeroEquiv_spec,
      reesHomogeneousElement, Polynomial.coeff_mul,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial]
    simp [mul_comm]
  apply hf
  rw [hfactor]
  exact Ideal.mul_mem_left _ _ hmem

private theorem blowup_chart_ring_equiv
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I)
    (a b : A) (ha : a ∈ I) (hb : b ∈ I) :
    letI : GradedRing P.gradedPieces := P.graded;
    let f : blowupAlgebra I :=
      reesHomogeneousElement I 1 (by simpa using I.mul_mem_left b ha);
    ∃ e : HomogeneousLocalization.Away P.gradedPieces f ≃+*
        Localization.Away (a * b),
      e.toRingHom.comp
          ((HomogeneousLocalization.fromZeroRingHom P.gradedPieces
            (Submonoid.powers f)).comp P.degreeZeroEquiv.symm.toRingHom) =
        algebraMap A (Localization.Away (a * b)) := by
  dsimp
  let c : A := a * b
  have hcI : c ∈ I := by
    exact I.mul_mem_left b ha
  have hcI1 : c ∈ I ^ 1 := by simpa using hcI
  have hcI2 : c ∈ I ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul ha hb
  let f : blowupAlgebra I := reesHomogeneousElement I 1 hcI1
  have hf : f ∈ P.gradedPieces 1 := by
    apply (P.gradedPieces_spec 1 f).2
    exact ⟨c, hcI1, rfl⟩
  let ev : Polynomial A →+* Localization.Away c :=
    Polynomial.eval₂Hom (algebraMap A (Localization.Away c))
      (IsLocalization.Away.invSelf c)
  let g : blowupAlgebra I →+* Localization.Away c :=
    ev.comp (algebraMap (blowupAlgebra I) (Polynomial A))
  have gf : g f = 1 := by
    simp [g, ev, f, reesHomogeneousElement, Polynomial.eval₂Hom_monomial,
      IsLocalization.Away.mul_invSelf]
  let ψ : HomogeneousLocalization.Away P.gradedPieces f →+* Localization.Away c :=
    (Localization.awayLift g (by
      rintro ⟨n, rfl⟩
      rw [map_pow, gf]
      exact isUnit_one)).comp
      (algebraMap (HomogeneousLocalization.Away P.gradedPieces f)
        (Localization (Submonoid.powers f)))
  let φ : A →+* HomogeneousLocalization.Away P.gradedPieces f :=
    (HomogeneousLocalization.fromZeroRingHom P.gradedPieces (Submonoid.powers f)).comp
      P.degreeZeroEquiv.symm.toRingHom
  let s0 : HomogeneousLocalization.Away P.gradedPieces f :=
    HomogeneousLocalization.Away.mk P.gradedPieces hf 2
      (reesHomogeneousElement I 2 hcI2) (by
        apply (P.gradedPieces_spec 2 _).2
        exact ⟨c, hcI2, rfl⟩)
  have hφc : φ c * s0 = 1 := by
    apply Subtype.ext
    change algebraMap (blowupAlgebra I) (Localization (Submonoid.powers f))
        ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) *
        (Localization.mk (reesHomogeneousElement I 2 hcI2)
          ⟨f ^ 2, Submonoid.mem_powers f 2⟩) = 1
    rw [P.degreeZeroEquiv_spec]
    apply (IsLocalization.eq_mk'_iff_mul_eq).2
    simp [f, reesHomogeneousElement, c, pow_two, mul_assoc, mul_left_comm,
      mul_comm]
  have hunit : IsUnit (φ c) := by
    exact ⟨⟨s0, 1, hφc, by
      apply Subtype.ext
      change
        Localization.mk (reesHomogeneousElement I 2 hcI2)
            ⟨f ^ 2, Submonoid.mem_powers f 2⟩ *
          algebraMap (blowupAlgebra I) (Localization (Submonoid.powers f))
            ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) = 1
      rw [P.degreeZeroEquiv_spec]
      apply (IsLocalization.eq_mk'_iff_mul_eq).2
      simp [f, reesHomogeneousElement, c, pow_two, mul_assoc, mul_left_comm,
        mul_comm]⟩⟩
  let θ : Localization.Away c →+* HomogeneousLocalization.Away P.gradedPieces f :=
    Localization.awayLift φ hunit
  have hθψ : Function.LeftInverse θ ψ := by
    intro z
    obtain ⟨n, x, hx, hz⟩ :=
      HomogeneousLocalization.Away.mk_surjective P.gradedPieces hf z
    obtain ⟨d, hd, hxd⟩ := (P.gradedPieces_spec n x).mp hx
    have hxeq : x = reesHomogeneousElement I n hd := by
      apply Subtype.ext
      exact hxd
    subst x
    subst z
    simp [θ, ψ, φ, HomogeneousLocalization.algebraMap_eq,
      reesHomogeneousElement, f, c, Localization.awayLift_mk,
      IsLocalization.eq_mk'_iff_mul_eq, pow_two, mul_assoc, mul_left_comm,
      mul_comm]
  have hψθ : Function.RightInverse θ ψ := by
    intro z
    obtain ⟨⟨r, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers c) z
    simp [θ, ψ, φ, HomogeneousLocalization.algebraMap_eq]
  have hψφ : ψ.comp φ = algebraMap A (Localization.Away c) := by
    ext z
    simp [ψ, φ, g, ev, HomogeneousLocalization.algebraMap_eq,
      P.degreeZeroEquiv_spec]
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro x y hxy
      calc
        x = θ (ψ x) := (hθψ x).symm
        _ = θ (ψ y) := congrArg θ hxy
        _ = y := hθψ y
    · intro z
      refine ⟨θ z, ?_⟩
      exact hψθ z
  refine ⟨RingEquiv.ofBijective ψ hψbij, ?_⟩
  simpa [φ] using hψφ

private theorem blowup_chart_isHomeomorph
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I)
    (a : A) (ha : a ∈ I) :
    letI : GradedRing P.gradedPieces := P.graded;
    let f : blowupAlgebra I :=
      reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha);
    IsHomeomorph (fun q : PrimeSpectrum
        (HomogeneousLocalization.Away P.gradedPieces f) =>
      (⟨(AlgebraicGeometry.Proj.awayι P.gradedPieces f
          (by
            apply (P.gradedPieces_spec 1 f).2
            exact ⟨a * a, by simpa using I.mul_mem_left a ha, rfl⟩)
          (Nat.zero_lt_succ 0)).base q, by
        rw [mem_dPlus_iff]
        have hq : (AlgebraicGeometry.Proj.awayι P.gradedPieces f
            (by
              apply (P.gradedPieces_spec 1 f).2
              exact ⟨a * a, by simpa using I.mul_mem_left a ha, rfl⟩)
            (Nat.zero_lt_succ 0)).base q ∈
            (AlgebraicGeometry.Proj.awayι P.gradedPieces f
              (by
                apply (P.gradedPieces_spec 1 f).2
                exact ⟨a * a, by simpa using I.mul_mem_left a ha, rfl⟩)
              (Nat.zero_lt_succ 0)).opensRange :=
          ⟨q, rfl⟩
        rwa [AlgebraicGeometry.Proj.opensRange_awayι] at hq⟩ :
        {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f}) := by
  dsimp
  let f : blowupAlgebra I :=
    reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha)
  have hf : f ∈ P.gradedPieces 1 := by
    apply (P.gradedPieces_spec 1 f).2
    exact ⟨a * a, by simpa using I.mul_mem_left a ha, rfl⟩
  let away := AlgebraicGeometry.Proj.awayι P.gradedPieces f hf (Nat.zero_lt_succ 0)
  let chart : PrimeSpectrum (HomogeneousLocalization.Away P.gradedPieces f) →
      {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} := fun q =>
    ⟨away.base q, by
      rw [mem_dPlus_iff]
      have hq : away.base q ∈ away.opensRange := ⟨q, rfl⟩
      rwa [AlgebraicGeometry.Proj.opensRange_awayι] at hq⟩
  change IsHomeomorph chart
  refine ⟨?_, ?_, ?_⟩
  · exact away.continuous.subtype_mk (fun q => q.2)
  · intro V hV
    apply (isOpen_dPlus P.gradedPieces f).isOpenEmbedding_subtypeVal
      .isOpen_iff_image_isOpen.mpr
    change IsOpen (away.base '' V)
    exact away.isOpenEmbedding.isOpenMap V hV
  · constructor
    · intro x y hxy
      exact away.isOpenEmbedding.inj (congrArg Subtype.val hxy)
    · intro x
      have hx : x.1 ∈ away.opensRange := by
        rw [AlgebraicGeometry.Proj.opensRange_awayι]
        exact x.2
      rcases hx with ⟨q, hq⟩
      exact ⟨q, Subtype.ext hq⟩

private theorem blowup_chart_base_isOpenMap
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I)
    (a : A) (ha : a ∈ I) :
    letI : GradedRing P.gradedPieces := P.graded;
    let f : blowupAlgebra I :=
      reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha);
    IsOpenMap (fun q : PrimeSpectrum
        (HomogeneousLocalization.Away P.gradedPieces f) =>
      (blowupMap P).base
        ((AlgebraicGeometry.Proj.awayι P.gradedPieces f
          (by
            apply (P.gradedPieces_spec 1 f).2
            exact ⟨a * a, by simpa using I.mul_mem_left a ha, rfl⟩)
          (Nat.zero_lt_succ 0)).base q) := by
  dsimp
  let f : blowupAlgebra I :=
    reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha)
  have hf : f ∈ P.gradedPieces 1 := by
    apply (P.gradedPieces_spec 1 f).2
    exact ⟨a * a, by simpa using I.mul_mem_left a ha, rfl⟩
  let away := AlgebraicGeometry.Proj.awayι P.gradedPieces f hf (Nat.zero_lt_succ 0)
  let φ : A →+* HomogeneousLocalization.Away P.gradedPieces f :=
    (HomogeneousLocalization.fromZeroRingHom P.gradedPieces (Submonoid.powers f)).comp
      P.degreeZeroEquiv.symm.toRingHom
  obtain ⟨e, he⟩ := blowup_chart_ring_equiv P a a ha ha
  have hcat : away ≫ blowupMap P =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) := by
    dsimp [away, blowupMap, φ]
    rw [← Category.assoc]
    rw [AlgebraicGeometry.Proj.awayι_toSpecZero]
    rw [← AlgebraicGeometry.Spec.map_comp]
    rfl
  have hbase : (fun q => (blowupMap P).base (away.base q)) =
      PrimeSpectrum.comap φ := by
    funext q
    have hq := congrArg (fun h => h.base q) hcat
    simpa [Function.comp_def] using hq
  have hehomeo : IsHomeomorph (PrimeSpectrum.comap e.symm.toRingHom) :=
    PrimeSpectrum.isHomeomorph_comap_of_bijective e.symm.bijective
  have hloc : IsOpenMap
      (PrimeSpectrum.comap (algebraMap A (Localization.Away (a * a)))) :=
    (PrimeSpectrum.localization_away_isOpenEmbedding
      (Localization.Away (a * a)) (a * a)).isOpenMap
  have hfactor : PrimeSpectrum.comap φ =
      (PrimeSpectrum.comap (algebraMap A (Localization.Away (a * a)))) ∘
        PrimeSpectrum.comap e.symm.toRingHom := by
    apply PrimeSpectrum.ext
    intro q
    change Ideal.comap φ q.asIdeal = _
    rw [← he]
    rw [Ideal.comap_comap]
    rfl
  rw [hbase, hfactor]
  intro U hU
  exact hloc _ (hehomeo.isOpenMap _ hU)

private theorem blowup_chart_restriction_isOpenMap
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I)
    (a : A) (ha : a ∈ I) :
    letI : GradedRing P.gradedPieces := P.graded;
    let f : blowupAlgebra I :=
      reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha);
    IsOpenMap (fun x : {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} =>
      (blowupMap P).base x.1) := by
  dsimp
  let f : blowupAlgebra I :=
    reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a ha)
  have hf : f ∈ P.gradedPieces 1 := by
    apply (P.gradedPieces_spec 1 f).2
    exact ⟨a * a, by simpa using I.mul_mem_left a ha, rfl⟩
  let chart : PrimeSpectrum (HomogeneousLocalization.Away P.gradedPieces f) →
      {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} := fun q =>
    ⟨(AlgebraicGeometry.Proj.awayι P.gradedPieces f hf
        (Nat.zero_lt_succ 0)).base q, by
      rw [mem_dPlus_iff]
      have hq := (⟨q, rfl⟩ :
        (AlgebraicGeometry.Proj.awayι P.gradedPieces f hf
          (Nat.zero_lt_succ 0)).base q ∈
          (AlgebraicGeometry.Proj.awayι P.gradedPieces f hf
            (Nat.zero_lt_succ 0)).opensRange)
      rwa [AlgebraicGeometry.Proj.opensRange_awayι] at hq⟩
  have hchart : IsHomeomorph chart := by
    exact blowup_chart_isHomeomorph P a ha
  have hamb : IsOpenMap (fun q : PrimeSpectrum
      (HomogeneousLocalization.Away P.gradedPieces f) =>
      (blowupMap P).base
        ((AlgebraicGeometry.Proj.awayι P.gradedPieces f hf
          (Nat.zero_lt_succ 0)).base q) := by
    exact blowup_chart_base_isOpenMap P a ha
  intro V hV
  have hEq : ((fun x => (blowupMap P).base x.1) '' V) =
      ((fun q => (blowupMap P).base (chart q).1) '' (chart ⁻¹' V)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨q, hq⟩ := hchart.surjective x
      exact ⟨q, ⟨by simpa [hq] using hx, hq⟩, by simp [hq]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨chart q, hq, rfl⟩
  rw [hEq]
  exact hamb _ (hV.preimage hchart.continuous)

theorem blowupRestrictionMap_isHomeomorph
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) :
    IsHomeomorph (blowupRestrictionMap P) := by
  letI : GradedRing P.gradedPieces := P.graded
  unfold blowupRestrictionMap
  refine ⟨?_, ?_, ?_⟩
  · exact ((blowupMap P).continuous.comp continuous_subtype_val).subtype_mk (fun x => x.2)
  · let ι := {a : A // a ∈ I}
    let f : ι → blowupAlgebra I := fun a =>
      reesHomogeneousElement I 1 (by simpa using I.mul_mem_left a.1 a.2)
    let U : ι → Opens {x : blowupProjPoints P //
        (blowupMap P).base x ∈ blowupBaseOpen I} := fun a =>
      ⟨(fun x : {x : blowupProjPoints P //
          (blowupMap P).base x ∈ blowupBaseOpen I} => x.1) ⁻¹'
          dPlus P.gradedPieces (f a),
        (isOpen_dPlus P.gradedPieces (f a)).preimage continuous_subtype_val⟩
    have hcover : TopologicalSpace.IsOpenCover U := by
      intro x
      have hp : ¬ (I : Set A) ⊆ ((blowupMap P).base x.1).asIdeal := by
        simpa [blowupBaseOpen, PrimeSpectrum.mem_zeroLocus] using x.2
      obtain ⟨a, ha, hap⟩ := Set.not_subset.mp hp
      let i : ι := ⟨a, ha⟩
      refine ⟨i, ?_⟩
      change f i ∉ x.1.asHomogeneousIdeal
      exact blowup_square_rees_not_mem P x.1 ha hap
    apply (TopologicalSpace.IsOpenCover.isOpenMap_iff_comp hcover).2
    intro i
    intro V hV
    apply (blowupBaseOpen_isOpen I).isOpenEmbedding_subtypeVal
      .isOpen_iff_image_isOpen.mpr
    let fa : blowupAlgebra I := f i
    have hsource (x : {x : blowupProjPoints P //
        x ∈ dPlus P.gradedPieces fa}) :
        (blowupMap P).base x.1 ∈ blowupBaseOpen I := by
      have hxf : fa ∉ x.1.asHomogeneousIdeal :=
        (mem_dPlus_iff P.gradedPieces fa x.1).mp x.2
      have hcnot := blowup_dplus_base_not_mem P x.1 i.2 hxf
      have hI : ¬ (I : Set A) ⊆ ((blowupMap P).base x.1).asIdeal := by
        intro h
        exact hcnot (h (I.mul_mem_left i.1 i.2))
      simpa [blowupBaseOpen, PrimeSpectrum.mem_zeroLocus] using hI
    let e :
        {x : {x : blowupProjPoints P //
            (blowupMap P).base x ∈ blowupBaseOpen I} //
          x.1 ∈ dPlus P.gradedPieces fa} ≃ₜ
        {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces fa} := by
      let e0 :
          {x : {x : blowupProjPoints P //
              (blowupMap P).base x ∈ blowupBaseOpen I} //
            x.1 ∈ dPlus P.gradedPieces fa} ≃
          {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces fa} :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun x => ⟨⟨x.1, hsource x⟩, x.2⟩
          left_inv := by
            intro x
            apply Subtype.ext
            rfl
          right_inv := by
            intro x
            apply Subtype.ext
            rfl }
      refine { toEquiv := e0, continuous_toFun := ?_, continuous_invFun := ?_ }
      · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
          (fun x => x.2)
      · exact (continuous_subtype_val.subtype_mk (fun x => hsource x)).subtype_mk
          (fun x => x.2)
    have hamb := blowup_chart_restriction_isOpenMap P i.1 i.2
    have hEq :
        ((fun x => (blowupMap P).base x.1.1) '' V) =
          ((fun x => (blowupMap P).base x.1) '' (e '' V)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [hEq]
    exact hamb _ (e.isOpenMap _ hV)
  · constructor
    · intro x y hxy
      apply Subtype.ext
      apply ProjectiveSpectrum.ext
      apply HomogeneousIdeal.ext'
      intro n z hz
      have hbase : (blowupMap P).base (x : blowupProjPoints P) =
          (blowupMap P).base (y : blowupProjPoints P) := congrArg Subtype.val hxy
      have hbase_mem (c : A) : c ∈ ((blowupMap P).base (x : blowupProjPoints P)).asIdeal ↔
          ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
            (x : blowupProjPoints P).asHomogeneousIdeal := by
        simp [blowupMap, AlgebraicGeometry.Proj.toSpecZero]
      have hp : ¬ (I : Set A) ⊆ ((blowupMap P).base (x : blowupProjPoints P)).asIdeal := by
        simpa [blowupBaseOpen, PrimeSpectrum.mem_zeroLocus] using x.property
      obtain ⟨a, haI, hap⟩ := Set.not_subset.mp hp
      have ha1 : a ∈ I ^ 1 := by simpa using haI
      let f : blowupAlgebra I := reesHomogeneousElement I 1 ha1
      have hf : f ∈ P.gradedPieces 1 := by
        apply (P.gradedPieces_spec 1 f).2
        exact ⟨a, ha1, rfl⟩
      have hfa_of (q : blowupProjPoints P)
          (hbase_mem_q : ∀ c : A, c ∈ ((blowupMap P).base q).asIdeal ↔
            ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
              q.asHomogeneousIdeal)
          (ha_q : a ∉ ((blowupMap P).base q).asIdeal) :
          f ∉ q.asHomogeneousIdeal := by
        intro hfx
        have ha0 :
            ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) ∉
              q.asHomogeneousIdeal := by
          intro ha0x
          exact ha_q ((hbase_mem_q a).mpr ha0x)
        apply q.not_irrelevant_le
        rw [HomogeneousIdeal.irrelevant_le]
        intro m hm g hg
        obtain ⟨c, hc, hcg⟩ := (P.gradedPieces_spec m g).mp hg
        have hmul :
            f ^ m * ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) =
              ((P.degreeZeroEquiv.symm (a ^ m) : P.gradedPieces 0) : blowupAlgebra I) * g := by
          apply Subtype.ext
          apply Polynomial.ext
          intro d
          rw [hcg, reesHomogeneousElement, Polynomial.coeff_mul,
            Polynomial.coeff_mul, Polynomial.coeff_monomial,
            Polynomial.coeff_monomial]
          simp [P.degreeZeroEquiv_spec, f, reesHomogeneousElement]
        have hleft : f ^ m *
              ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
            q.asHomogeneousIdeal :=
          Ideal.mul_mem_left _ _ (Ideal.pow_mem q.asHomogeneousIdeal hfx m)
        have hright :
            ((P.degreeZeroEquiv.symm (a ^ m) : P.gradedPieces 0) : blowupAlgebra I) * g ∈
              (x : blowupProjPoints P).asHomogeneousIdeal := hmul ▸ hleft
        have ham :
            ((P.degreeZeroEquiv.symm (a ^ m) : P.gradedPieces 0) : blowupAlgebra I) ∉
              q.asHomogeneousIdeal := by
          intro hamx
          apply ha0
          rw [← P.degreeZeroEquiv.map_pow]
          exact (show ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) ^ m ∈
              q.asHomogeneousIdeal from q.asHomogeneousIdeal.pow_mem hamx m)
        exact q.isPrime.mem_or_mem hright |>.resolve_left ham
      have hfa : f ∉ (x : blowupProjPoints P).asHomogeneousIdeal :=
        hfa_of (x : blowupProjPoints P) hbase_mem hap
      have hbase_mem_y (c : A) : c ∈ ((blowupMap P).base (y : blowupProjPoints P)).asIdeal ↔
          ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
            (y : blowupProjPoints P).asHomogeneousIdeal := by
        simp [blowupMap, AlgebraicGeometry.Proj.toSpecZero]
      have hap_y : a ∉ ((blowupMap P).base (y : blowupProjPoints P)).asIdeal := by
        simpa [hbase] using hap
      have hfa_y : f ∉ (y : blowupProjPoints P).asHomogeneousIdeal :=
        hfa_of (y : blowupProjPoints P) hbase_mem_y hap_y
      obtain ⟨c, hc, hzg⟩ := (P.gradedPieces_spec n z).mp hz
      have hmul_z :
          f ^ n * ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) =
            ((P.degreeZeroEquiv.symm (a ^ n) : P.gradedPieces 0) : blowupAlgebra I) * z := by
        apply Subtype.ext
        apply Polynomial.ext
        intro d
        rw [hzg, reesHomogeneousElement, Polynomial.coeff_mul,
          Polynomial.coeff_mul, Polynomial.coeff_monomial,
          Polynomial.coeff_monomial]
        simp [P.degreeZeroEquiv_spec, f, reesHomogeneousElement]
      have hmem_of (q : blowupProjPoints P)
          (hqf : f ∉ q.asHomogeneousIdeal)
          (hqa : ((P.degreeZeroEquiv.symm a : P.gradedPieces 0) : blowupAlgebra I) ∉
            q.asHomogeneousIdeal) :
          z ∈ q.asHomogeneousIdeal ↔
            ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
              q.asHomogeneousIdeal := by
        constructor
        · intro hzm
          have hprod :
              f ^ n * ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
                q.asHomogeneousIdeal := by
            exact q.asHomogeneousIdeal.mul_mem
              (q.asHomogeneousIdeal.pow_mem hqf n) (q.asHomogeneousIdeal.zero_mem)
          have hpowf : f ^ n ∉ q.asHomogeneousIdeal := by
            intro h
            exact hqf (q.isPrime.pow_mem_iff_mem.mp h)
          exact q.isPrime.mem_or_mem hprod |>.resolve_left hpowf
        · intro hcm
          have hprod :
              ((P.degreeZeroEquiv.symm (a ^ n) : P.gradedPieces 0) : blowupAlgebra I) * z ∈
                q.asHomogeneousIdeal := hmul_z ▸
              q.asHomogeneousIdeal.mul_mem
                (q.asHomogeneousIdeal.pow_mem hcm n) (q.asHomogeneousIdeal.zero_mem)
          have hpowaa :
              ((P.degreeZeroEquiv.symm (a ^ n) : P.gradedPieces 0) : blowupAlgebra I) ∉
                q.asHomogeneousIdeal := by
            intro h
            apply hqa
            rw [← P.degreeZeroEquiv.map_pow]
            exact q.asHomogeneousIdeal.pow_mem h n
          exact q.isPrime.mem_or_mem hprod |>.resolve_left hpowaa
      have hcxcy :
          ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
              (x : blowupProjPoints P).asHomogeneousIdeal ↔
            ((P.degreeZeroEquiv.symm c : P.gradedPieces 0) : blowupAlgebra I) ∈
              (y : blowupProjPoints P).asHomogeneousIdeal := by
        calc
          _ ↔ c ∈ ((blowupMap P).base (x : blowupProjPoints P)).asIdeal :=
            (hbase_mem c).symm
          _ ↔ c ∈ ((blowupMap P).base (y : blowupProjPoints P)).asIdeal := by rw [hbase]
          _ ↔ _ := hbase_mem_y c
      exact (hmem_of (x : blowupProjPoints P) hfa
        ((fun h => hap ((hbase_mem a).mpr h)) ))
        |>.trans (hcxcy.trans (hmem_of (y : blowupProjPoints P) hfa_y
          (fun h => hap_y ((hbase_mem_y a).mpr h))).symm)
    · intro p
      have hp : ¬ (I : Set A) ⊆ p.asIdeal := by
        simpa [blowupBaseOpen, PrimeSpectrum.mem_zeroLocus] using p.property
      obtain ⟨a, haI, hap⟩ := Set.not_subset.mp hp
      have ha1 : a ∈ I ^ 1 := by simpa using haI
      let f : blowupAlgebra I := reesHomogeneousElement I 1 ha1
      have hf : f ∈ P.gradedPieces 1 := by
        apply (P.gradedPieces_spec 1 f).2
        exact ⟨a, ha1, rfl⟩
      have hpa : a * a ∉ p.asIdeal := by
        intro haa
        rcases p.1.isPrime.mem_or_mem haa with ha' | ha' <;> exact hap ha'
      have hp' : p.1 ∈ (PrimeSpectrum.basicOpen (a * a) :
          Set (PrimeSpectrum A)) := by
        exact hpa
      rw [← PrimeSpectrum.localization_away_comap_range
        (Localization.Away (a * a)) (a * a)] at hp'
      obtain ⟨q, hq⟩ := hp'
      obtain ⟨e, he⟩ := blowup_chart_ring_equiv P a a haI haI
      let away := AlgebraicGeometry.Proj.awayι P.gradedPieces f hf
        (Nat.zero_lt_succ 0)
      let chart : PrimeSpectrum (HomogeneousLocalization.Away P.gradedPieces f) →
          {x : blowupProjPoints P // x ∈ dPlus P.gradedPieces f} := fun q =>
        ⟨away.base q, by
          rw [mem_dPlus_iff]
          have hq' : away.base q ∈ away.opensRange := ⟨q, rfl⟩
          rwa [AlgebraicGeometry.Proj.opensRange_awayι] at hq'⟩
      have hchart : IsHomeomorph chart := by
        exact blowup_chart_isHomeomorph P a haI
      let qS : PrimeSpectrum (HomogeneousLocalization.Away P.gradedPieces f) :=
        PrimeSpectrum.comap e.toRingHom q
      let xD := chart qS
      have hxU : (blowupMap P).base xD.1 ∈ blowupBaseOpen I := by
        have hxf : f ∉ xD.1.asHomogeneousIdeal :=
          (mem_dPlus_iff P.gradedPieces f xD.1).mp xD.2
        have hcnot := blowup_dplus_base_not_mem P xD.1 haI hxf
        have hI : ¬ (I : Set A) ⊆ ((blowupMap P).base xD.1).asIdeal := by
          intro h
          exact hcnot (h (I.mul_mem_left a haI))
        simpa [blowupBaseOpen, PrimeSpectrum.mem_zeroLocus] using hI
      let x : {x : blowupProjPoints P //
          (blowupMap P).base x ∈ blowupBaseOpen I} := ⟨xD.1, hxU⟩
      let φ : A →+* HomogeneousLocalization.Away P.gradedPieces f :=
        (HomogeneousLocalization.fromZeroRingHom P.gradedPieces
          (Submonoid.powers f)).comp P.degreeZeroEquiv.symm.toRingHom
      have hcat : away ≫ blowupMap P =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) := by
        dsimp [away, blowupMap, φ]
        rw [← Category.assoc]
        rw [AlgebraicGeometry.Proj.awayι_toSpecZero]
        rw [← AlgebraicGeometry.Spec.map_comp]
        rfl
      have hbase : (blowupMap P).base xD.1 =
          PrimeSpectrum.comap φ qS := by
        have hqS := congrArg (fun h => h.base qS) hcat
        simpa [xD, chart, Function.comp_def] using hqS
      refine ⟨x, ?_⟩
      apply Subtype.ext
      calc
        (blowupMap P).base x.1 = (blowupMap P).base xD.1 := by rfl
        _ = PrimeSpectrum.comap φ qS := hbase
        _ = PrimeSpectrum.comap (algebraMap A (Localization.Away (a * a))) q := by
          apply PrimeSpectrum.ext
          change Ideal.comap φ (Ideal.comap e.toRingHom q.asIdeal) = _
          rw [Ideal.comap_comap, he]
          exact congrArg PrimeSpectrum.asIdeal hq
        _ = p.1 := hq

theorem strictTransform_conditions
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    D.genericPoint ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ¬ (D.Z : Set (PrimeSpectrum A)) ⊆
        PrimeSpectrum.zeroLocus (I : Set A) ∧
      D.genericPoint ∈ blowupBaseOpen I ∧
      ((D.Z : Set (PrimeSpectrum A)) ∩ blowupBaseOpen I).Nonempty := by
  have hgen : D.genericPoint ∈ (D.Z : Set (PrimeSpectrum A)) := by
    rw [← D.genericPoint_isGeneric.def]
    exact subset_closure (Set.mem_singleton D.genericPoint)
  have hnot : D.genericPoint ∉ PrimeSpectrum.zeroLocus (I : Set A) := by
    simpa [blowupBaseOpen] using D.genericPoint_mem_baseOpen
  refine ⟨hnot, ?_, D.genericPoint_mem_baseOpen, ?_⟩
  · intro hZ
    exact hnot (hZ hgen)
  · exact ⟨D.genericPoint, hgen, D.genericPoint_mem_baseOpen⟩

theorem strictTransform_eq_viaOpen
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    strictTransform D = strictTransformViaOpen D := by
  let liftU : {x : blowupProjPoints P // (blowupMap P).base x ∈ blowupBaseOpen I} :=
    ⟨D.lift, by rw [D.lift_over_generic]; exact D.genericPoint_mem_baseOpen⟩
  let genericU : {p : PrimeSpectrum A // p ∈ blowupBaseOpen I} :=
    ⟨D.genericPoint, D.genericPoint_mem_baseOpen⟩
  have hfiber :
      (blowupRestrictionMap P) ⁻¹' ({genericU} : Set _) = {liftU} := by
    ext z
    constructor
    · intro hz
      apply Subtype.ext
      apply D.lift_unique
      have hz' := Set.mem_singleton_iff.mp hz
      simpa [blowupRestrictionMap, genericU] using hz'
    · intro hz
      have hz' : z = liftU := Set.mem_singleton_iff.mp hz
      subst z
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      change (blowupMap P).base (D.lift : blowupProjPoints P) = D.genericPoint
      exact D.lift_over_generic
  apply Set.Subset.antisymm
  · apply closure_mono
    apply Set.singleton_subset_iff.mpr
    change (blowupMap P).base D.lift ∈ (D.Z : Set (PrimeSpectrum A)) ∩
      blowupBaseOpen I
    rw [D.lift_over_generic]
    exact ⟨D.genericPoint_isGeneric.mem, D.genericPoint_mem_baseOpen⟩
  · intro x hx
    let xU : {x : blowupProjPoints P // (blowupMap P).base x ∈ blowupBaseOpen I} :=
      ⟨x, hx.2.2⟩
    have hxU : xU ∈
        (blowupRestrictionMap P) ⁻¹' closure ({genericU} : Set _) := by
      have hy : (blowupRestrictionMap P xU : PrimeSpectrum A) ∈
          closure ({D.genericPoint} : Set (PrimeSpectrum A)) := by
        rw [D.genericPoint_isGeneric.def]
        exact hx.1
      have hy' : blowupRestrictionMap P xU ∈ closure ({genericU} : Set _) := by
        rw [closure_subtype]
        simpa [genericU] using hy
      exact hy'
    rw [(blowupRestrictionMap_isHomeomorph P).homeomorph.preimage_closure] at hxU
    rw [hfiber] at hxU
    have hx' : x ∈ closure ({D.lift} : Set (blowupProjPoints P)) := by
      simpa [xU, liftU] using (closure_subtype.mp hxU)
    exact hx'

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
  classical
  let A := twoVariablePolynomialRing k
  let I : Ideal A := twoVariableMaximalIdeal k
  let B := blowupAlgebra I
  let piece : ℕ → Submodule ℤ B := fun d =>
    { carrier := {x | ∀ n, n ≠ d → x.1.coeff n = 0}
      zero_mem' := by
        intro n hn
        simp
      add_mem' := by
        intro x y hx hy n hn
        simp [hx n hn, hy n hn]
      smul_mem' := by
        intro c x hx n hn
        simp [hx n hn] }
  have hpiece_eq (d : ℕ) (x : B) (hx : x ∈ piece d) :
      x.1 = Polynomial.monomial d (x.1.coeff d) := by
    apply Polynomial.ext
    intro n
    by_cases h : n = d
    · subst h
      simp
    · have h' : ¬ d = n := by
        intro hdn
        exact h hdn.symm
      rw [Polynomial.coeff_monomial, if_neg h']
      exact hx n h
  have hpiece_spec (d : ℕ) (x : B) :
      x ∈ piece d ↔
        ∃ a : A, ∃ _ha : a ∈ I ^ d,
          x.1 = Polynomial.monomial d a := by
    constructor
    · intro hx
      refine ⟨x.1.coeff d, x.2 d, hpiece_eq d x hx⟩
    · rintro ⟨a, ha, hx⟩
      change ∀ n, n ≠ d → x.1.coeff n = 0
      intro n hn
      have h' : ¬ d = n := by
        intro hdn
        exact hn hdn.symm
      rw [hx, Polynomial.coeff_monomial, if_neg h']
  let component : ∀ d : ℕ, A → piece d := fun d a =>
    if ha : a ∈ I ^ d then
      ⟨reesHomogeneousElement I d ha, by
        change ∀ n, n ≠ d → (Polynomial.monomial d a).coeff n = 0
        intro n hn
        have h' : ¬ d = n := by
          intro hdn
          exact hn hdn.symm
        rw [Polynomial.coeff_monomial, if_neg h']⟩
    else 0
  have component_of_mem (d : ℕ) (a : A) (ha : a ∈ I ^ d) :
      component d a =
        ⟨reesHomogeneousElement I d ha, by
          change ∀ n, n ≠ d → (Polynomial.monomial d a).coeff n = 0
          intro n hn
          have h' : ¬ d = n := by
            intro hdn
            exact hn hdn.symm
          rw [Polynomial.coeff_monomial, if_neg h']⟩ := by
    dsimp [component]
    rw [dif_pos ha]
  have component_add (d : ℕ) (a b : A) (ha : a ∈ I ^ d) (hb : b ∈ I ^ d) :
      component d (a + b) = component d a + component d b := by
    simp only [component_of_mem d (a + b) ((I ^ d).add_mem ha hb),
      component_of_mem d a ha, component_of_mem d b hb]
    apply Subtype.ext
    rw [Submodule.coe_add]
    change (reesHomogeneousElement I d ((I ^ d).add_mem ha hb) : B) =
      (reesHomogeneousElement I d ha : B) + reesHomogeneousElement I d hb
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    change (Polynomial.monomial d (a + b)).coeff n =
      (Polynomial.monomial d a + Polynomial.monomial d b).coeff n
    rw [Polynomial.coeff_add, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial]
    by_cases h : d = n
    · simp [h]
    · simp [h]
  have component_zero (d : ℕ) : component d 0 = 0 := by
    dsimp [component]
    rw [dif_pos (I ^ d).zero_mem]
    apply Subtype.ext
    apply Subtype.ext
    simp [reesHomogeneousElement]
  let decompose : B →+ DirectSum ℕ (fun d => piece d) :=
    { toFun := fun x =>
        Finsupp.sum x.1.toFinsupp.coeff
          (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))
      map_zero' := by
        apply DirectSum.ext
        intro n
        change
          (Finsupp.sum (0 : Polynomial A).toFinsupp.coeff
            (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n = 0
        have hzero : (0 : Polynomial A).toFinsupp.coeff = 0 := by
          ext d
          simp
        rw [hzero]
        exact congrArg (fun q => q n)
          (Finsupp.sum_zero_index
            (h := fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a)))
      map_add' := by
        intro x y
        apply DirectSum.ext
        intro n
        have happly (z : B) :
            (Finsupp.sum z.1.toFinsupp.coeff
              (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n =
                component n (z.1.coeff n) := by
          rw [Finsupp.sum_eq_single n]
          · rw [DirectSum.of_eq_same]
            rfl
          · intro b hb hbn
            have hnb : n ≠ b := Ne.symm hbn
            rw [DirectSum.of_eq_of_ne _ _ _ hnb]
          · intro hnzero
            rw [component_zero]
            exact map_zero _
        change
          (Finsupp.sum ((x + y).1.toFinsupp.coeff)
            (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n =
            (Finsupp.sum x.1.toFinsupp.coeff
              (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n +
            (Finsupp.sum y.1.toFinsupp.coeff
              (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n
        rw [happly (x + y), happly x, happly y]
        exact component_add n (x.1.coeff n) (y.1.coeff n) (x.2 n) (y.2 n)
    }
  have hdecompose_apply (x : B) (n : ℕ) :
      decompose x n = component n (x.1.coeff n) := by
    change
      (Finsupp.sum x.1.toFinsupp.coeff
        (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n =
        component n (x.1.coeff n)
    rw [Finsupp.sum_eq_single n]
    · rw [DirectSum.of_eq_same, DirectSum.of_apply]
      rfl
    · intro b hb hbn
      simp [hbn]
    · rw [component_zero]
      apply DirectSum.ext
      intro i
      by_cases hi : i = n
      · subst i
        rw [DirectSum.of_eq_same, DirectSum.of_apply]
        simp
      · rw [DirectSum.of_eq_of_ne _ _ _ hi]
  have hdecompose_of (d : ℕ) (x : B) (hx : x ∈ piece d) :
      decompose x = DirectSum.of (fun d => ↥(piece d)) d ⟨x, hx⟩ := by
    apply DirectSum.ext
    intro n
    rw [hdecompose_apply]
    by_cases h : n = d
    · subst h
      apply Subtype.ext
      apply Subtype.ext
      exact (hpiece_eq d x hx).symm
    · simp [DirectSum.of_eq_of_ne, h]
  have hgradedOne : SetLike.GradedOne piece := by
    refine ⟨?_⟩
    change ∀ n, n ≠ 0 → (1 : Polynomial A).coeff n = 0
    intro n hn
    simp [hn]
  have hgradedMul : SetLike.GradedMul piece := by
    refine ⟨?_⟩
    intro i j x y hx hy
    change ∀ n, n ≠ i + j → (x.1 * y.1).coeff n = 0
    rw [hpiece_eq i x hx, hpiece_eq j y hy]
    intro n hn
    rw [Polynomial.coeff_mul, Polynomial.coeff_monomial_mul_monomial]
    simp only [if_neg (Ne.symm hn)]
  let : SetLike.GradedMonoid piece := ⟨hgradedOne, hgradedMul⟩
  have hleft (x : B) :
      DirectSum.coeAddMonoidHom piece (decompose x) = x := by
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    change
      (Finsupp.sum x.1.toFinsupp.coeff
        (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n = _
    rw [Finsupp.sum_eq_single n]
    · rw [DirectSum.of_eq_same, DirectSum.of_apply]
      rfl
    · intro b hb hbn
      simp [hbn]
    · rw [component_zero]
      simp
  have hright (z : DirectSum ℕ (fun d => piece d)) :
      decompose (DirectSum.coeAddMonoidHom piece z) = z := by
    apply DirectSum.ext
    intro n
    rw [DirectSum.coeAddMonoidHom_eq_dfinsupp_sum]
    rw [DFinsupp.sum_eq_single n]
    · rw [hdecompose_of]
      simp
    · intro b hb hbn
      rw [hdecompose_of]
      simp [hbn]
    · intro hnzero
      rw [hdecompose_of]
      simp
  let graded : GradedRing piece :=
    { toGradedMonoid := inferInstance
      decompose' := decompose
      left_inv := hleft
      right_inv := hright }
  let e : (piece 0) ≃+* A :=
    { toFun := fun x => x.1.coeff 0
      invFun := fun a =>
        ⟨reesHomogeneousElement I 0 (by simp), by
          change ∀ n, n ≠ 0 → (Polynomial.monomial 0 a).coeff n = 0
          intro n hn
          simpa only [Polynomial.coeff_monomial]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        exact (hpiece_eq 0 x x.2).symm
      right_inv := by
        intro a
        simp }
  refine ⟨
    { gradedPieces := piece
      graded := graded
      degreeZeroEquiv := e
      gradedPieces_spec := ?_
      degreeZeroEquiv_spec := ?_ }⟩
  · exact hpiece_spec
  · intro a
    apply Subtype.ext
    apply Subtype.ext
    simp [e, reesHomogeneousElement]
  
/-
  classical
  let A := twoVariablePolynomialRing k
  let I : Ideal A := twoVariableMaximalIdeal k
  let B := blowupAlgebra I
  let piece : ℕ → Submodule ℤ B := fun d =>
    { carrier := {x | ∀ n, n ≠ d → x.1.coeff n = 0}
      zero_mem' := by
        intro n hn
        simp
      add_mem' := by
        intro x y hx hy n hn
        simp [hx n hn, hy n hn]
      smul_mem' := by
        intro c x hx n hn
        simp [hx n hn] }
  have hpiece_eq (d : ℕ) (x : B) (hx : x ∈ piece d) :
      x.1 = Polynomial.monomial d (x.1.coeff d) := by
    apply Polynomial.ext
    intro n
    by_cases h : n = d
    · subst h
      simp
    · have h' : ¬ d = n := by
        intro hdn
        exact h hdn.symm
      rw [Polynomial.coeff_monomial, if_neg h']
      exact hx n h
  have hpiece_spec (d : ℕ) (x : B) :
      x ∈ piece d ↔
        ∃ a : A, ∃ _ha : a ∈ I ^ d,
          x.1 = Polynomial.monomial d a := by
    constructor
    · intro hx
      refine ⟨x.1.coeff d, x.2 d, hpiece_eq d x hx⟩
    · rintro ⟨a, ha, hx⟩
      change ∀ n, n ≠ d → x.1.coeff n = 0
      intro n hn
      have h' : ¬ d = n := by
        intro hdn
        exact hn hdn.symm
      rw [hx, Polynomial.coeff_monomial, if_neg h']
  let component : ∀ d : ℕ, A → piece d := fun d a =>
    if ha : a ∈ I ^ d then
      ⟨reesHomogeneousElement I d ha, by
        change ∀ n, n ≠ d → (Polynomial.monomial d a).coeff n = 0
        intro n hn
        have h' : ¬ d = n := by
          intro hdn
          exact hn hdn.symm
        rw [Polynomial.coeff_monomial, if_neg h']⟩
    else 0
  have component_of_mem (d : ℕ) (a : A) (ha : a ∈ I ^ d) :
      component d a =
        ⟨reesHomogeneousElement I d ha, by
          change ∀ n, n ≠ d → (Polynomial.monomial d a).coeff n = 0
          intro n hn
          have h' : ¬ d = n := by
            intro hdn
            exact hn hdn.symm
          rw [Polynomial.coeff_monomial, if_neg h']⟩ := by
    dsimp [component]
    rw [dif_pos ha]
  have component_add (d : ℕ) (a b : A) (ha : a ∈ I ^ d) (hb : b ∈ I ^ d) :
      component d (a + b) = component d a + component d b := by
    simp only [component_of_mem d (a + b) ((I ^ d).add_mem ha hb),
      component_of_mem d a ha, component_of_mem d b hb]
    apply Subtype.ext
    rw [Submodule.coe_add]
    change (reesHomogeneousElement I d ((I ^ d).add_mem ha hb) : B) =
      (reesHomogeneousElement I d ha : B) + reesHomogeneousElement I d hb
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    change (Polynomial.monomial d (a + b)).coeff n =
      (Polynomial.monomial d a + Polynomial.monomial d b).coeff n
    rw [Polynomial.coeff_add, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial]
    by_cases h : d = n
    · simp [h]
    · simp [h]
  have component_zero (d : ℕ) : component d 0 = 0 := by
    dsimp [component]
    rw [dif_pos (I ^ d).zero_mem]
    apply Subtype.ext
    apply Subtype.ext
    simp [reesHomogeneousElement]
  let decompose : B →+ DirectSum ℕ (fun d => ↥(piece d)) :=
    { toFun := fun x =>
        Finsupp.sum x.1.toFinsupp.coeff
          (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))
      map_zero' := by
        apply DirectSum.ext
        intro n
        change
          (Finsupp.sum (0 : Polynomial A).toFinsupp.coeff
            (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n = 0
        have hzero : (0 : Polynomial A).toFinsupp.coeff = 0 := by
          ext d
          simp
        rw [hzero]
        exact congrArg (fun q => q n)
          (Finsupp.sum_zero_index
            (h := fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a)))
      map_add' := by
        intro x y
        apply DirectSum.ext
        intro n
        have happly (z : B) :
            (Finsupp.sum z.1.toFinsupp.coeff
              (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n =
                component n (z.1.coeff n) := by
          change
            (Finsupp.sum z.1.toFinsupp.coeff
              (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n =
                component n (z.1.coeff n)
          rw [Finsupp.sum_eq_single n]
          · rw [DirectSum.of_eq_same]
            exact congrArg (component n) (by rfl)
          · intro b hb hbn
            have hnb : n ≠ b := Ne.symm hbn
            rw [DirectSum.of_eq_of_ne _ _ _ hnb]
          · intro hnzero
            rw [component_zero]
            exact map_zero _
        change
          (Finsupp.sum ((x + y).1.toFinsupp.coeff)
            (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n =
            (Finsupp.sum x.1.toFinsupp.coeff
              (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n +
            (Finsupp.sum y.1.toFinsupp.coeff
              (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n
        rw [happly (x + y), happly x, happly y]
        exact component_add n (x.1.coeff n) (y.1.coeff n) (x.2 n) (y.2 n)
    }
  have hdecompose_apply (x : B) (n : ℕ) :
      decompose x n = component n (x.1.coeff n) := by
    change
      (Finsupp.sum x.1.toFinsupp.coeff
        (fun d a => DirectSum.of (fun d => ↥(piece d)) d (component d a))) n =
        component n (x.1.coeff n)
    rw [Finsupp.sum_eq_single n]
    · rw [DirectSum.of_eq_same, DirectSum.of_apply]
      rfl
    · intro b hb hbn
      simp [hbn]
    · rw [component_zero]
      apply DirectSum.ext
      intro i
      by_cases hi : i = n
      · subst i
        rw [DirectSum.of_eq_same, DirectSum.of_apply]
        simp
      · rw [DirectSum.of_eq_of_ne _ _ _ hi]
  have hdecompose_of (d : ℕ) (x : B) (hx : x ∈ piece d) :
      decompose x = DirectSum.of (fun d => ↥(piece d)) d ⟨x, hx⟩ := by
    apply DirectSum.ext
    intro n
    rw [hdecompose_apply]
    by_cases h : n = d
    · subst h
      apply Subtype.ext
      apply Subtype.ext
      exact (hpiece_eq d x hx).symm
    · simp [DirectSum.of_eq_of_ne, h]
  sorry
-/

noncomputable def twoVariableBlowupPresentation (k : Type u) [Field k] :
    BlowupPresentation (twoVariableMaximalIdeal k) :=
  Classical.choice (twoVariableBlowupPresentation_exists k)

theorem twoVariableXIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableXIdeal k).IsPrime := by
  classical
  let e := MvPolynomial.finSuccEquiv k 1
  have hprime :
      (Ideal.span ({Polynomial.X} :
        Set (Polynomial (MvPolynomial (Fin 1) k)))).IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  have heq :
      (Ideal.span ({Polynomial.X} :
        Set (Polynomial (MvPolynomial (Fin 1) k)))).comap e.toRingHom =
        Ideal.span ({MvPolynomial.X (0 : Fin 2)} :
          Set (MvPolynomial (Fin 2) k)) := by
    apply le_antisymm
    · intro p hp
      rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨e.symm q, ?_⟩
      apply e.injective
      calc
        e ((e.symm q) * MvPolynomial.X (0 : Fin 2)) =
            e (e.symm q) * e (MvPolynomial.X (0 : Fin 2)) := by
              rw [map_mul]
        _ = q * Polynomial.X := by
          rw [e.apply_symm_apply, MvPolynomial.finSuccEquiv_X_zero]
        _ = e p := hq
    · intro p hp
      rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨e q, ?_⟩
      change e q * Polynomial.X = e p
      calc
        e q * Polynomial.X =
            e q * e (MvPolynomial.X (0 : Fin 2)) := by
              rw [MvPolynomial.finSuccEquiv_X_zero]
        _ = e (q * MvPolynomial.X (0 : Fin 2)) := by rw [map_mul]
        _ = e p := congrArg e hq
  have hcp :
      (Ideal.span ({Polynomial.X} :
        Set (Polynomial (MvPolynomial (Fin 1) k)))).comap e.toRingHom |>.IsPrime := by
    constructor
    · exact Ideal.comap_ne_top _ hprime.1
    · intro x y hxy
      apply hprime.2
      simpa only [Ideal.mem_comap, map_mul] using hxy
  change (Ideal.span ({MvPolynomial.X (0 : Fin 2)} :
    Set (MvPolynomial (Fin 2) k))).IsPrime
  exact heq ▸ hcp

theorem twoVariableYIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableYIdeal k).IsPrime := by
  classical
  let e₀ := MvPolynomial.finSuccEquiv k 1
  let e₁ := MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1)
  let e := e₁.trans e₀
  have hprime :
      (Ideal.span ({Polynomial.X} :
        Set (Polynomial (MvPolynomial (Fin 1) k)))).IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  have heq :
      (Ideal.span ({Polynomial.X} :
        Set (Polynomial (MvPolynomial (Fin 1) k)))).comap e.toRingHom =
        Ideal.span ({MvPolynomial.X (1 : Fin 2)} :
          Set (MvPolynomial (Fin 2) k)) := by
    apply le_antisymm
    · intro p hp
      rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨e.symm q, ?_⟩
      apply e.injective
      calc
        e ((e.symm q) * MvPolynomial.X (1 : Fin 2)) =
            e (e.symm q) * e (MvPolynomial.X (1 : Fin 2)) := by
              rw [map_mul]
        _ = q * Polynomial.X := by
          rw [e.apply_symm_apply]
          dsimp [e, e₀, e₁]
          simp [MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_zero]
        _ = e p := hq
    · intro p hp
      rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨e q, ?_⟩
      change e q * Polynomial.X = e p
      calc
        e q * Polynomial.X =
            e q * e (MvPolynomial.X (1 : Fin 2)) := by
              dsimp [e, e₀, e₁]
              simp [MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_zero]
        _ = e (q * MvPolynomial.X (1 : Fin 2)) := by rw [map_mul]
        _ = e p := congrArg e hq
  have hcp :
      (Ideal.span ({Polynomial.X} :
        Set (Polynomial (MvPolynomial (Fin 1) k)))).comap e.toRingHom |>.IsPrime := by
    constructor
    · exact Ideal.comap_ne_top _ hprime.1
    · intro x y hxy
      apply hprime.2
      simpa only [Ideal.mem_comap, map_mul] using hxy
  change (Ideal.span ({MvPolynomial.X (1 : Fin 2)} :
    Set (MvPolynomial (Fin 2) k))).IsPrime
  exact heq ▸ hcp

theorem twoVariableParabolaIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableParabolaIdeal k).IsPrime := by
  classical
  let e := MvPolynomial.finSuccEquiv k 1
  let g : Polynomial (MvPolynomial (Fin 1) k) :=
    Polynomial.X - Polynomial.C (MvPolynomial.X (0 : Fin 1)) ^ 2
  have hprime : (Ideal.span ({g} : Set (Polynomial (MvPolynomial (Fin 1) k)))).IsPrime :=
    /- Prior attempt:
    (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero
      (R := MvPolynomial (Fin 1) k)
      (MvPolynomial.X (0 : Fin 1) ^ 2))).mpr (by
        simpa [g] using
          (Polynomial.prime_X_sub_C (MvPolynomial.X (0 : Fin 1) ^ 2))) -/
    sorry
  have heq :
      (Ideal.span ({g} : Set (Polynomial (MvPolynomial (Fin 1) k)))).comap e.toRingHom =
        Ideal.span ({MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ^ 2} :
          Set (MvPolynomial (Fin 2) k)) := by
    /- Prior attempt:
    apply le_antisymm
    · intro p hp
      rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨e.symm q, ?_⟩
      apply e.injective
      calc
        e ((e.symm q) *
            (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ^ 2)) =
            e (e.symm q) *
              e (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ^ 2) := by
                rw [map_mul]
        _ = q * g := by
          rw [e.apply_symm_apply]
          simp [e, g, MvPolynomial.finSuccEquiv_X_zero,
            MvPolynomial.finSuccEquiv_X_succ]
        _ = e p := hq
    · intro p hp
      rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨e q, ?_⟩
      have he :
          e (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ^ 2) = g := by
        simp [e, g, MvPolynomial.finSuccEquiv_X_zero,
          MvPolynomial.finSuccEquiv_X_succ]
      calc
        e q * g = e q * e
            (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ^ 2) := by
              rw [he]
        _ = e (q * (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ^ 2)) := by
              rw [map_mul]
        _ = e p := congrArg e hq -/
    sorry
  have hcp :
      (Ideal.span ({g} : Set (Polynomial (MvPolynomial (Fin 1) k)))).comap e.toRingHom |>.IsPrime := by
    constructor
    · exact Ideal.comap_ne_top _ hprime.1
    · intro x y hxy
      apply hprime.2
      simpa only [Ideal.mem_comap, map_mul] using hxy
  change (Ideal.span ({MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ^ 2} :
    Set (MvPolynomial (Fin 2) k))).IsPrime
  exact heq ▸ hcp

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
