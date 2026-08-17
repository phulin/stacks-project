import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 17: The spectrum of a ring

The source's spectrum, vanishing sets, standard opens, and Zariski topology
are already provided by Mathlib as `PrimeSpectrum`,
`PrimeSpectrum.zeroLocus`, `PrimeSpectrum.basicOpen`, and the
`PrimeSpectrum.zariskiTopology` instance.  This file records the source-facing
interfaces and the localization and quotient homeomorphisms built from those
canonical constructions.
-/

namespace Formalization.Books.Algebra.Unit17

open Set
open Topology

universe u v

noncomputable section

/-! ## The spectrum and the Zariski topology -/

/-
The three definitions in the source are represented directly by Mathlib:

* `PrimeSpectrum R` is the type of prime ideals of `R`;
* `PrimeSpectrum.zeroLocus T` is `V(T)`;
* `PrimeSpectrum.basicOpen f` is `D(f)`, as an open of the Zariski topology.

The topology itself is the canonical `PrimeSpectrum.zariskiTopology` instance.
-/

theorem spectrum_isEmpty_iff_zero_eq_one (R : Type u) [CommRing R] :
    IsEmpty (PrimeSpectrum R) ↔ (0 : R) = 1 :=
  PrimeSpectrum.isEmpty_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm

theorem exists_maximal_ideal (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ I : Ideal R, I.IsMaximal := by
  exact Ideal.exists_maximal R

theorem exists_minimal_prime (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
  exact ⟨⟨p, hp.isPrime⟩, hp⟩

theorem exists_minimal_prime_between {R : Type u} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ q : PrimeSpectrum R, q.asIdeal ∈ I.minimalPrimes ∧ q.asIdeal ≤ p.asIdeal := by
  letI : p.asIdeal.IsPrime := p.2
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le
    (I := I) (J := p.asIdeal) hIp
  exact ⟨⟨q, hq.isPrime⟩, hq, hqle⟩

theorem zeroLocus_span {R : Type u} [CommRing R] (T : Set R) :
    PrimeSpectrum.zeroLocus (Ideal.span T : Set R) = PrimeSpectrum.zeroLocus T := by
  exact PrimeSpectrum.zeroLocus_span T

theorem zeroLocus_radical {R : Type u} [CommRing R] (I : Ideal R) :
    PrimeSpectrum.zeroLocus (I.radical : Set R) = PrimeSpectrum.zeroLocus I := by
  exact PrimeSpectrum.zeroLocus_radical I

theorem radical_eq_sInf_prime_over {R : Type u} [CommRing R] (I : Ideal R) :
    I.radical = sInf {P : Ideal R | I ≤ P ∧ P.IsPrime} := by
  exact Ideal.radical_eq_sInf I

theorem zeroLocus_empty_iff_eq_top {R : Type u} [CommRing R] (I : Ideal R) :
    PrimeSpectrum.zeroLocus (I : Set R) = ∅ ↔ I = ⊤ := by
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top

theorem zeroLocus_inf {R : Type u} [CommRing R] (I J : Ideal R) :
    PrimeSpectrum.zeroLocus (I : Set R) ∪ PrimeSpectrum.zeroLocus (J : Set R) =
      PrimeSpectrum.zeroLocus ((I ⊓ J : Ideal R) : Set R) := by
  exact (PrimeSpectrum.zeroLocus_inf I J).symm

theorem zeroLocus_iInf {R : Type u} [CommRing R] {ι : Type v} (I : ι → Ideal R) :
    (⋂ i, PrimeSpectrum.zeroLocus (I i : Set R)) =
      PrimeSpectrum.zeroLocus (⋃ i, (I i : Set R)) := by
  exact (PrimeSpectrum.zeroLocus_iUnion (fun i => (I i : Set R))).symm

theorem standard_open_and_zeroLocus_partition {R : Type u} [CommRing R] (f : R) :
    Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
        (PrimeSpectrum.zeroLocus ({f} : Set R)) ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∪
          PrimeSpectrum.zeroLocus ({f} : Set R) = Set.univ := by
  constructor <;> simp [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.disjoint_left]

theorem standard_open_eq_empty_iff_nilpotent {R : Type u} [CommRing R] (f : R) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) = ∅ ↔ IsNilpotent f := by
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, nilpotent_iff_mem_prime,
    Set.compl_empty_iff, PrimeSpectrum.mem_zeroLocus, SetLike.mem_coe]
  constructor
  · intro h I hI
    exact h ⟨I, hI⟩
  · intro h p
    exact h p.asIdeal p.2

theorem standard_open_unit_mul {R : Type u} [CommRing R] (f f' : R)
    (h : ∃ u : R, IsUnit u ∧ f = u * f') :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen f' : Set (PrimeSpectrum R)) := by
  rcases h with ⟨u, hu, rfl⟩
  ext p
  change u * f' ∉ p.asIdeal ↔ f' ∉ p.asIdeal
  constructor
  · intro h hf'
    exact h (p.asIdeal.mul_mem_left u hf')
  · intro hf' hmul
    exact hf' ((p.2.mul_mem_iff_mem_or_mem.mp hmul).resolve_left
      (Ideal.notMem_of_isUnit p.asIdeal hu))

theorem exists_standard_open_separating_ideal {R : Type u} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R)
    (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set R)) :
    ∃ f ∈ I,
      p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∧
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
            PrimeSpectrum.zeroLocus (I : Set R) = ∅ := by
  rw [PrimeSpectrum.mem_zeroLocus] at hp
  obtain ⟨f, hfI, hfp⟩ := not_subset.mp hp
  refine ⟨f, hfI, (PrimeSpectrum.mem_basicOpen f p).2 hfp, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.2
  intro q hq
  exact (PrimeSpectrum.mem_basicOpen f q).mp hq.1
    ((PrimeSpectrum.mem_zeroLocus q (I : Set R)).mp hq.2 hfI)

theorem standard_open_mul {R : Type u} [CommRing R] (f g : R) :
    PrimeSpectrum.basicOpen (f * g) =
      PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g := by
  exact PrimeSpectrum.basicOpen_mul f g

theorem standard_open_iUnion_eq_compl_zeroLocus {R : Type u} [CommRing R]
    {ι : Type v} (f : ι → R) :
    (⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R))) =
      (PrimeSpectrum.zeroLocus (Set.range f))ᶜ := by
  ext p
  simp only [Set.mem_iUnion, PrimeSpectrum.mem_basicOpen, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · rintro ⟨i, hi⟩ h
    exact hi (h ⟨i, rfl⟩)
  · intro hp
    by_contra hnot
    apply hp
    rintro x ⟨i, rfl⟩
    by_contra hi
    exact hnot ⟨i, hi⟩

theorem standard_open_eq_univ_implies_isUnit {R : Type u} [CommRing R] (f : R)
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) = Set.univ) :
    IsUnit f := by
  have hV : PrimeSpectrum.zeroLocus ({f} : Set R) = ∅ := by
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] at hf
    have h := congrArg (fun s : Set (PrimeSpectrum R) => sᶜ) hf
    simpa only [compl_compl, compl_univ] using h
  apply Ideal.span_singleton_eq_top.mp
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  simpa only [PrimeSpectrum.zeroLocus_span] using hV

theorem zariski_isClosed_iff_zeroLocus {R : Type u} [CommRing R]
    (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ T : Set R, Z = PrimeSpectrum.zeroLocus T := by
  exact PrimeSpectrum.isClosed_iff_zeroLocus Z

theorem standard_open_isOpen {R : Type u} [CommRing R] (f : R) :
    IsOpen (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.isOpen_basicOpen

theorem standard_opens_form_basis {R : Type u} [CommRing R] :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : R => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) := by
  exact PrimeSpectrum.isTopologicalBasis_basic_opens

/-! ## Functoriality -/

theorem spectrum_map_continuous {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) : Continuous (PrimeSpectrum.comap φ) := by
  exact PrimeSpectrum.continuous_comap φ

theorem spectrum_map_preimage_standard_open {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) :
    PrimeSpectrum.comap φ ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (φ f) : Set (PrimeSpectrum S)) := by
  ext p
  simp

theorem spectrum_map_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) :
    PrimeSpectrum.comap (ψ.comp φ) =
      (PrimeSpectrum.comap φ).comp (PrimeSpectrum.comap ψ) := by
  exact PrimeSpectrum.comap_comp φ ψ

/-! ## Localization -/

/-- The spectrum map into the subspace of primes disjoint from a submonoid. -/
def localizationSpectrumMap {R : Type u} [CommRing R] (S : Submonoid R) :
    PrimeSpectrum (Localization S) →
      {p : PrimeSpectrum R // Disjoint (S : Set R) p.asIdeal} :=
  fun p =>
    ⟨PrimeSpectrum.comap (algebraMap R (Localization S)) p,
      by
        change PrimeSpectrum.comap (algebraMap R (Localization S)) p ∈
          {q : PrimeSpectrum R | Disjoint (S : Set R) q.asIdeal}
        rw [← PrimeSpectrum.localization_comap_range (Localization S) S]
        exact ⟨p, rfl⟩⟩

/-- Extension of a prime disjoint from `S` to the localization. -/
def localizationSpectrumInverse {R : Type u} [CommRing R] (S : Submonoid R) :
    {p : PrimeSpectrum R // Disjoint (S : Set R) p.asIdeal} →
      PrimeSpectrum (Localization S) :=
  fun p =>
    ⟨p.1.asIdeal.map (algebraMap R (Localization S)),
      IsLocalization.isPrime_of_isPrime_disjoint S (Localization S) _ p.1.2 p.2⟩

/-- The localization spectrum map is a homeomorphism onto its induced subspace. -/
noncomputable def localizationSpectrumHomeomorph {R : Type u} [CommRing R]
    (S : Submonoid R) :
    PrimeSpectrum (Localization S) ≃ₜ
      {p : PrimeSpectrum R // Disjoint (S : Set R) p.asIdeal} := by
  let h : IsEmbedding (PrimeSpectrum.comap (algebraMap R (Localization S))) :=
    PrimeSpectrum.localization_comap_isEmbedding (Localization S) S
  exact h.toHomeomorph.trans
    (Homeomorph.setCongr (PrimeSpectrum.localization_comap_range (Localization S) S))

theorem localizationSpectrumHomeomorph_apply {R : Type u} [CommRing R]
    (S : Submonoid R) (p : PrimeSpectrum (Localization S)) :
    localizationSpectrumHomeomorph S p = localizationSpectrumMap S p := by
  rfl

theorem localizationSpectrumHomeomorph_symm_apply {R : Type u} [CommRing R]
    (S : Submonoid R)
    (p : {p : PrimeSpectrum R // Disjoint (S : Set R) p.asIdeal}) :
    (localizationSpectrumHomeomorph S).symm p = localizationSpectrumInverse S p := by
  apply (localizationSpectrumHomeomorph S).injective
  rw [(localizationSpectrumHomeomorph S).apply_symm_apply]
  rw [localizationSpectrumHomeomorph_apply]
  apply Subtype.ext
  apply PrimeSpectrum.ext
  simpa [localizationSpectrumMap, localizationSpectrumInverse,
    PrimeSpectrum.comap_asIdeal, Ideal.under_def] using
    (IsLocalization.under_map_of_isPrime_disjoint S (Localization S) p.1.2 p.2).symm

/-! ## Standard opens and closed subsets -/

/-- The spectrum of `R_f` is homeomorphic to the standard open `D(f)`. -/
noncomputable def standardOpenSpectrumHomeomorph {R : Type u} [CommRing R] (f : R) :
    PrimeSpectrum (Localization.Away f) ≃ₜ
      {p : PrimeSpectrum R // p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))} := by
  let h : IsOpenEmbedding
      (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) :=
    PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f
  exact h.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr
      (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f))

/-- The inverse map for the standard-open homeomorphism, written as extension of ideals. -/
def standardOpenSpectrumInverse {R : Type u} [CommRing R] (f : R) :
    {p : PrimeSpectrum R // p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))} →
      PrimeSpectrum (Localization.Away f) :=
  fun p =>
    ⟨p.1.asIdeal.map (algebraMap R (Localization.Away f)),
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
        (Localization.Away f) _ p.1.2 (by
          apply Set.disjoint_left.2
          intro x hxS hxP
          rcases hxS with ⟨n, rfl⟩
          exact (PrimeSpectrum.mem_basicOpen f p.1).mp p.2
            (p.1.2.mem_of_pow_mem _ hxP))⟩

theorem standardOpenSpectrumHomeomorph_apply {R : Type u} [CommRing R] (f : R)
    (p : PrimeSpectrum (Localization.Away f)) :
    standardOpenSpectrumHomeomorph f p =
      ⟨PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p, by
        rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
        exact ⟨p, rfl⟩⟩ := by
  rfl

theorem standardOpenSpectrumHomeomorph_symm_apply {R : Type u} [CommRing R] (f : R)
    (p : {p : PrimeSpectrum R // p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))}) :
    (standardOpenSpectrumHomeomorph f).symm p = standardOpenSpectrumInverse f p := by
  apply (standardOpenSpectrumHomeomorph f).injective
  rw [(standardOpenSpectrumHomeomorph f).apply_symm_apply]
  rw [standardOpenSpectrumHomeomorph_apply]
  apply Subtype.ext
  apply PrimeSpectrum.ext
  have hdisj : Disjoint (Submonoid.powers f : Set R) p.1.asIdeal := by
    apply Set.disjoint_left.2
    intro x hxS hxP
    rcases hxS with ⟨n, rfl⟩
    exact (PrimeSpectrum.mem_basicOpen f p.1).mp p.2
      (p.1.2.mem_of_pow_mem _ hxP)
  simpa [standardOpenSpectrumInverse, PrimeSpectrum.comap_asIdeal, Ideal.under_def] using
    (IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers f) (Localization.Away f) p.1.2 hdisj).symm

/-- The spectrum of a quotient is homeomorphic to the corresponding closed subset. -/
noncomputable def quotientSpectrumHomeomorph {R : Type u} [CommRing R] (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃ₜ
      {p : PrimeSpectrum R // p ∈ PrimeSpectrum.zeroLocus (I : Set R)} := by
  let h : IsClosedEmbedding (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective
      (R ⧸ I) (Ideal.Quotient.mk I) Quotient.mk_surjective
  exact h.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr <| by
      simpa [I.mk_ker] using
        (range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
          Quotient.mk_surjective))

/-- The inverse map for the quotient-spectrum homeomorphism, written as `p / I`. -/
def quotientSpectrumInverse {R : Type u} [CommRing R] (I : Ideal R) :
    {p : PrimeSpectrum R // p ∈ PrimeSpectrum.zeroLocus (I : Set R)} →
      PrimeSpectrum (R ⧸ I) :=
  fun p =>
    ⟨p.1.asIdeal.map (Ideal.Quotient.mk I),
      p.1.asIdeal.map_isPrime_of_surjective Quotient.mk_surjective (by
        rw [I.mk_ker]
        exact (PrimeSpectrum.mem_zeroLocus p.1 (I : Set R)).mp p.2)⟩

theorem quotientSpectrumHomeomorph_apply {R : Type u} [CommRing R] (I : Ideal R)
    (p : PrimeSpectrum (R ⧸ I)) :
    quotientSpectrumHomeomorph I p =
      ⟨PrimeSpectrum.comap (Ideal.Quotient.mk I) p, by
        have hp : PrimeSpectrum.comap (Ideal.Quotient.mk I) p ∈
            PrimeSpectrum.zeroLocus
              (RingHom.ker (Ideal.Quotient.mk I) : Set R) := by
          rw [← range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
            Quotient.mk_surjective]
          exact ⟨p, rfl⟩
        simpa only [I.mk_ker] using hp⟩ := by
  rfl

theorem quotientSpectrumHomeomorph_symm_apply {R : Type u} [CommRing R] (I : Ideal R)
    (p : {p : PrimeSpectrum R // p ∈ PrimeSpectrum.zeroLocus (I : Set R)}) :
    (quotientSpectrumHomeomorph I).symm p = quotientSpectrumInverse I p := by
  apply (quotientSpectrumHomeomorph I).injective
  rw [(quotientSpectrumHomeomorph I).apply_symm_apply]
  rw [quotientSpectrumHomeomorph_apply]
  apply Subtype.ext
  apply PrimeSpectrum.ext
  change p.1.asIdeal =
    Ideal.comap (Ideal.Quotient.mk I)
      (Ideal.map (Ideal.Quotient.mk I) p.1.asIdeal)
  rw [p.1.asIdeal.comap_map_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective]
  rw [← RingHom.ker_eq_comap_bot, I.mk_ker]
  exact Eq.symm (sup_eq_left.mpr
    ((PrimeSpectrum.mem_zeroLocus p.1 (I : Set R)).mp p.2))

/-! ## Quasi-compactness -/

theorem spectrum_is_quasi_compact {R : Type u} [CommRing R] :
    IsCompact (Set.univ : Set (PrimeSpectrum R)) := by
  exact isCompact_univ

theorem standard_open_is_quasi_compact {R : Type u} [CommRing R] (f : R) :
    IsCompact (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.isCompact_basicOpen f

theorem spectrum_has_quasi_compact_basis {R : Type u} [CommRing R] :
    TopologicalSpace.IsTopologicalBasis
        (Set.range fun f : R => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) ∧
      ∀ U ∈ Set.range (fun f : R => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))),
        IsCompact U := by
  constructor
  · exact standard_opens_form_basis
  · rintro U ⟨f, rfl⟩
    exact PrimeSpectrum.isCompact_basicOpen f

theorem quasi_compact_open_intersection {R : Type u} [CommRing R]
    (U V : Set (PrimeSpectrum R))
    (hU_open : IsOpen U) (hU_compact : IsCompact U)
    (hV_open : IsOpen V) (hV_compact : IsCompact V) :
    IsCompact (U ∩ V) := by
  exact IsCompact.inter_of_isOpen hU_compact hV_compact hU_open hV_open

/-
The source warns that not every affine open of a spectrum is standard and
refers to a later example.  “Affine open” is scheme-theoretic terminology and
is intentionally not introduced in this algebra-only chapter; the warning is
therefore accounted for here rather than duplicated with a parallel notion.
-/

end

end Formalization.Books.Algebra.Unit17
