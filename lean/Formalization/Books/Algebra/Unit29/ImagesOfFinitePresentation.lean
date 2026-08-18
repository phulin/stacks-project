import Formalization.Books.Algebra.Unit17.Spectrum
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Commutative Algebra, Chapter 29: Images of ring maps of finite presentation

The source's constructible sets and quasi-compact maps use Mathlib's canonical
`Topology.IsConstructible`, `IsRetrocompact`, `IsCompact`, and `IsSpectralMap`
predicates.  The finite-union normal form is represented by
`PrimeSpectrum.ConstructibleSetData`; the source's basic pieces are precisely
the `BasicConstructibleSetData.toSet` pieces.  Localization and quotient
spectrum maps use the canonical maps from Chapter 17.
-/

namespace Formalization.Books.Algebra.Unit29

open Set
open _root_.Topology
open scoped TensorProduct

universe u

/-! ## Quasi-compact opens and constructible sets -/

/-
For an open subset of an affine spectrum, the four conditions in the source
are stated together.  `IsCompact` is the set-level quasi-compactness predicate.
-/
theorem isRetrocompact_iff_isCompact_iff_finite_union_basicOpen_iff_exists_fg_ideal
    {R : Type u} [CommRing R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U) :
    IsRetrocompact U ↔
      IsCompact U ∧
        (∃ s : Finset R,
          U = ⋃ f ∈ s, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) ∧
          ∃ I : Ideal R, I.FG ∧
            (PrimeSpectrum.zeroLocus (I : Set R))ᶜ = U := by
  constructor
  · intro h
    have hcomp : IsCompact U :=
      (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hU).mp h
    have hfin := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hcomp, hU⟩
    have hideal := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hcomp, hU⟩
    refine ⟨hcomp, ?_, hideal⟩
    obtain ⟨s, hs⟩ := hfin
    refine ⟨s, ?_⟩
    rw [← hs]
    ext p
    simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, SetLike.mem_coe,
      Set.subset_def, Set.mem_iUnion, Finset.mem_coe, PrimeSpectrum.mem_basicOpen]
    constructor
    · intro hp
      push_neg at hp
      exact ⟨hp.choose, hp.choose_spec.1, hp.choose_spec.2⟩
    · rintro ⟨i, hi, hpi⟩ hsub
      exact hpi (hsub i hi)
  · rintro ⟨hcomp, -, -⟩
    exact (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hU).mpr hcomp

/-
Mathlib's `IsSpectralMap` is the canonical Lean interface for a continuous
quasi-compact map between spectral spaces: it includes continuity and compact
preimages of compact opens.  The second conjunct is the source's inverse-image
assertion for constructible sets.
-/
theorem affine_map_quasiCompact_and_constructible_preimage
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    IsSpectralMap (PrimeSpectrum.comap φ) ∧
      ∀ E : Set (PrimeSpectrum R), IsConstructible E →
        IsConstructible (PrimeSpectrum.comap φ ⁻¹' E) := by
  classical
  have hφ : IsSpectralMap (PrimeSpectrum.comap φ) := by
    refine ⟨PrimeSpectrum.continuous_comap φ, ?_⟩
    intro U hUopen hUcomp
    obtain ⟨s, hs⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hUcomp, hUopen⟩
    rw [← hs, Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
    apply (PrimeSpectrum.isCompact_isOpen_iff.mpr ⟨s.image φ, ?_⟩).1
    simp only [Finset.coe_image, Set.image_image]
  refine ⟨hφ, ?_⟩
  intro E hE
  exact hE.preimage hφ.continuous fun U hUopen hUretro ↦ by
      exact (QuasiSeparatedSpace.isRetrocompact_iff_isCompact
        (hUopen.preimage hφ.continuous)).mpr
        (hφ.isCompact_preimage_of_isOpen hUopen hUretro.isCompact)

/-!
The source's finite union of sets `D(f) ∩ V(g₁, ..., gₘ)` is exactly
`PrimeSpectrum.ConstructibleSetData.toSet`.  We expose the equivalent
source-facing orientation of Mathlib's canonical equivalence, without defining
a parallel constructible-set data type.
-/
theorem isConstructible_iff_exists_constructibleSetData
    {R : Type u} [CommRing R] {T : Set (PrimeSpectrum R)} :
    IsConstructible T ↔
      ∃ S : PrimeSpectrum.ConstructibleSetData R, S.toSet = T := by
  exact PrimeSpectrum.exists_constructibleSetData_iff.symm

/-! ## Constructible sets as images -/

theorem exists_finitePresentation_ringHom_of_isConstructible
    {R : Type u} [CommRing R] {T : Set (PrimeSpectrum R)}
    (hT : IsConstructible T) :
    ∃ (S : Type u) (_ : CommRing S) (φ : R →+* S),
      RingHom.FinitePresentation φ ∧
        Set.range (PrimeSpectrum.comap φ) = T := by
  obtain ⟨s, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hT
  let S := Π i : s,
    Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f)
  let φ : R →+* S := algebraMap R S
  refine ⟨S, inferInstance, φ, ?_, ?_⟩
  · letI : ∀ i : s,
      Algebra.FinitePresentation R
        (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f)) := by
      intro i
      letI : Algebra.FinitePresentation R
          (R ⧸ Ideal.span (Set.range i.1.g)) :=
        Algebra.FinitePresentation.quotient
          ⟨(Set.finite_range i.1.g).toFinset, by simp⟩
      infer_instance
    dsimp [φ]
    apply (RingHom.finitePresentation_algebraMap (A := R) (B := S)).2
    exact Algebra.FinitePresentation.pi _
  · rw [← PrimeSpectrum.iUnion_range_comap_comp_evalRingHom,
      PrimeSpectrum.ConstructibleSetData.toSet]
    simp_rw [← Finset.mem_coe, Set.biUnion_eq_iUnion]
    congr! with _ _ C
    let I := Ideal.span (Set.range C.1.g)
    let f := Ideal.Quotient.mk I C.1.f
    trans PrimeSpectrum.comap (Ideal.Quotient.mk I) ''
        (Set.range (PrimeSpectrum.comap (algebraMap _ (Localization.Away f))))
    · rw [← Set.range_comp]
      rfl
    · rw [PrimeSpectrum.localization_away_comap_range _ f, ← PrimeSpectrum.comap_basicOpen,
        TopologicalSpace.Opens.coe_comap, ContinuousMap.coe_mk,
        Set.image_preimage_eq_inter_range,
        range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        PrimeSpectrum.BasicConstructibleSetData.toSet, Set.sdiff_eq_compl_inter,
        PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Ideal.mk_ker,
        PrimeSpectrum.zeroLocus_span]

theorem isConstructible_image_of_localization
    {R : Type u} [CommRing R] (f : R)
    {E : Set (PrimeSpectrum (Localization.Away f))}
    (hE : IsConstructible E) :
    IsConstructible
      (PrimeSpectrum.comap (algebraMap R (Localization.Away f)) '' E) := by
  exact PrimeSpectrum.isConstructible_comap_image
    (RingHom.finitePresentation_algebraMap.mpr (IsLocalization.Away.finitePresentation f)) hE

theorem isConstructible_image_of_fg_quotient
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    {E : Set (PrimeSpectrum (R ⧸ I))} (hE : IsConstructible E) :
    IsConstructible (PrimeSpectrum.comap (Ideal.Quotient.mk I) '' E) := by
  exact PrimeSpectrum.isConstructible_comap_image
    (RingHom.FinitePresentation.of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)) hE

/-! ## The affine line -/

theorem polynomial_spectrum_comap_isOpen_and_standardOpen_image_isCompactOpen
    {R : Type u} [CommRing R] :
    IsOpenMap (PrimeSpectrum.comap (Polynomial.C : R →+* Polynomial R)) ∧
      ∀ f : Polynomial R,
        IsCompact
            (PrimeSpectrum.comap (Polynomial.C : R →+* Polynomial R) ''
              (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial R)))) ∧
          IsOpen
            (PrimeSpectrum.comap (Polynomial.C : R →+* Polynomial R) ''
              (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial R)))) := by
  classical
  refine ⟨Polynomial.isOpenMap_comap_C, fun f ↦ ?_⟩
  rw [Polynomial.image_comap_C_basicOpen]
  refine (PrimeSpectrum.isCompact_isOpen_iff.mpr ⟨f.support.image f.coeff, ?_⟩)
  ext p
  simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Finset.coe_image]
  apply not_congr
  constructor
  · intro h a ha
    obtain ⟨i, rfl⟩ := ha
    by_cases hi : i ∈ f.support
    · exact h ⟨i, hi, rfl⟩
    · rw [Polynomial.notMem_support_iff.mp hi]
      exact p.asIdeal.zero_mem
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact h ⟨i, rfl⟩

/-! ## Characteristic polynomials and the affine-line special case -/

/-
The finite-free hypothesis in the source is represented by Mathlib's canonical
`Module.Free` and `Module.Finite` typeclasses.  `Algebra.lmul R A f` is the
source's multiplication map, and membership of all coefficients below the
finite rank is the source's `V(r₀, ..., rₙ₋₁)` condition.
-/
theorem characteristic_polynomial_prime
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] (f : A) (p : PrimeSpectrum R) :
    IsNilpotent (algebraMap A (A ⊗[R] p.asIdeal.ResidueField) f) ↔
      ∀ i < Module.finrank R A,
        (Algebra.lmul R A f).charpoly.coeff i ∈ p.asIdeal := by
  exact isNilpotent_tensor_residueField_iff f p.asIdeal

theorem exists_fin_union_basicOpen_image_of_isUnit_leadingCoeff
    {R : Type u} [CommRing R] (f g : Polynomial R)
    (hg : IsUnit g.leadingCoeff) :
    ∃ n : ℕ, ∃ r : Fin n → R,
      PrimeSpectrum.comap (Polynomial.C : R →+* Polynomial R) ''
          ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial R))) ∩
            PrimeSpectrum.zeroLocus ({g} : Set (Polynomial R))) =
        ⋃ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)) := by
  classical
  let g' : Polynomial R := hg.unit⁻¹ • g
  have hg' : g'.Monic := by
    dsimp [g']
    exact Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hg
  have hzero : PrimeSpectrum.zeroLocus ({g'} : Set (Polynomial R)) =
      PrimeSpectrum.zeroLocus ({g} : Set (Polynomial R)) := by
    ext q
    simp only [PrimeSpectrum.mem_zeroLocus, singleton_subset_iff, g', Units.smul_def,
      Algebra.smul_def]
    change (Polynomial.C (↑hg.unit⁻¹ : R) * g ∈ q.asIdeal) ↔ g ∈ q.asIdeal
    have hu : Polynomial.C (↑hg.unit⁻¹ : R) ∉ q.asIdeal := by
      intro hq
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq
        ((hg.unit⁻¹).isUnit.map Polynomial.C))
    exact Ideal.IsPrime.mul_mem_left_iff (I := q.asIdeal) hu
  obtain ⟨t, ht⟩ := Polynomial.exists_image_comap_of_monic f g' hg'
  have hdomain :
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial R))) ∩
          PrimeSpectrum.zeroLocus ({g} : Set (Polynomial R)) =
        PrimeSpectrum.zeroLocus ({g'} : Set (Polynomial R)) \ PrimeSpectrum.zeroLocus ({f} : Set (Polynomial R)) := by
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, hzero]
    ext q
    simp [and_comm]
  refine ⟨t.card, fun i => (t.equivFin.symm i : R), ?_⟩
  rw [hdomain, ht, ← (t : Set R).iUnion_of_singleton_coe,
    PrimeSpectrum.zeroLocus_iUnion, Set.compl_iInter]
  apply Set.iUnion_congr_of_surjective (t.equivFin) t.equivFin.surjective
  intro x
  simp

/-! ## Chevalley's theorem -/

theorem isConstructible_image_of_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FinitePresentation φ)
    {E : Set (PrimeSpectrum S)} (hE : IsConstructible E) :
    IsConstructible (PrimeSpectrum.comap φ '' E) := by
  exact PrimeSpectrum.isConstructible_comap_image hφ hE

/-
The source's warning that an affine open need not be a standard open is already
represented by the distinction between arbitrary open subsets and the basic
opens in Mathlib.  The displayed partitions, polynomial coefficient formulas,
and induction reductions in the proof narration are consequences of the
canonical spectrum, localization, quotient, polynomial, and constructible-set
APIs above; they do not introduce additional source-level definitions.
-/

end Formalization.Books.Algebra.Unit29
