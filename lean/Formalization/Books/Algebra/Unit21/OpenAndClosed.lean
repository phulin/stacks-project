import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.Topology.Connected.Basic
import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Algebra.Unit20.Nakayama

/-!
# Commutative Algebra, Chapter 21: Open and closed subsets of spectra

The spectrum, standard opens, zero loci, and the Zariski topology use
Mathlib's canonical `PrimeSpectrum` interfaces.  In particular, Mathlib
already supplies the product-spectrum homeomorphism, the clopen/idempotent
equivalence, and the finitely generated idempotent-ideal criterion.
-/

namespace Formalization.Books.Algebra.Unit21

universe u v

noncomputable section

open Set

/-! ## Idempotent decompositions of spectra -/

/-- An idempotent decomposes the spectrum into the two complementary standard
opens associated to it and to its complement. -/
theorem idempotent_spec_partition
    {R : Type u} [CommRing R] (e : R) (he : IsIdempotentElem e) :
    Disjoint (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R))
        (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) ∧
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) ∪
          (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) = Set.univ := by
  constructor
  · rw [Set.disjoint_left]
    intro p h₁ h₂
    change e ∉ p.asIdeal at h₁
    change 1 - e ∉ p.asIdeal at h₂
    have hmul : e * (1 - e) ∈ p.asIdeal := by
      have hzero : e * (1 - e) = 0 := by
        calc
          e * (1 - e) = e - e * e := by rw [mul_sub, mul_one]
          _ = 0 := by rw [he.eq, sub_self]
      rw [hzero]
      exact p.asIdeal.zero_mem
    exact (p.isPrime.mul_mem_iff_mem_or_mem.mp hmul).elim h₁ h₂
  · ext p
    change (e ∉ p.asIdeal ∨ 1 - e ∉ p.asIdeal) ↔ True
    by_cases h : e ∈ p.asIdeal
    · constructor
      · intro _
        trivial
      · intro _
        right
        intro h'
        exact p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top
          (by simpa using p.asIdeal.add_mem h h')
    · constructor
      · intro _
        trivial
      · intro _
        exact Or.inl h

/-! ## Products of rings -/

/-- The map on spectra induced by the first projection of a product ring. -/
def productSpectrumMapLeft {R₁ : Type u} {R₂ : Type v}
    [CommRing R₁] [CommRing R₂] :
    PrimeSpectrum R₁ → PrimeSpectrum (R₁ × R₂) :=
  PrimeSpectrum.comap (RingHom.fst R₁ R₂)

/-- The map on spectra induced by the second projection of a product ring. -/
def productSpectrumMapRight {R₁ : Type u} {R₂ : Type v}
    [CommRing R₁] [CommRing R₂] :
    PrimeSpectrum R₂ → PrimeSpectrum (R₁ × R₂) :=
  PrimeSpectrum.comap (RingHom.snd R₁ R₂)

theorem continuous_productSpectrumMapLeft {R₁ : Type u} {R₂ : Type v}
    [CommRing R₁] [CommRing R₂] :
    Continuous (productSpectrumMapLeft (R₁ := R₁) (R₂ := R₂)) := by
  exact PrimeSpectrum.continuous_comap _

theorem continuous_productSpectrumMapRight {R₁ : Type u} {R₂ : Type v}
    [CommRing R₁] [CommRing R₂] :
    Continuous (productSpectrumMapRight (R₁ := R₁) (R₂ := R₂)) := by
  exact PrimeSpectrum.continuous_comap _

/-- The spectrum of a product is homeomorphic to the disjoint union of the
spectra of its factors. -/
noncomputable def productSpectrumHomeomorph {R₁ : Type u} {R₂ : Type v}
    [CommRing R₁] [CommRing R₂] :
    PrimeSpectrum R₁ ⊕ PrimeSpectrum R₂ ≃ₜ PrimeSpectrum (R₁ × R₂) :=
  (PrimeSpectrum.primeSpectrumProdHomeo (R := R₁) (S := R₂)).symm

theorem productSpectrumHomeomorph_inl_apply {R₁ : Type u} {R₂ : Type v}
    [CommRing R₁] [CommRing R₂] (p : PrimeSpectrum R₁) :
    productSpectrumHomeomorph (R₁ := R₁) (R₂ := R₂) (Sum.inl p) =
      productSpectrumMapLeft (R₁ := R₁) (R₂ := R₂) p := by
  simp [productSpectrumHomeomorph, productSpectrumMapLeft,
    PrimeSpectrum.primeSpectrumProdHomeo, PrimeSpectrum.primeSpectrumProd_symm_inl]

theorem productSpectrumHomeomorph_inr_apply {R₁ : Type u} {R₂ : Type v}
    [CommRing R₁] [CommRing R₂] (p : PrimeSpectrum R₂) :
    productSpectrumHomeomorph (R₁ := R₁) (R₂ := R₂) (Sum.inr p) =
      productSpectrumMapRight (R₁ := R₁) (R₂ := R₂) p := by
  simp [productSpectrumHomeomorph, productSpectrumMapRight,
    PrimeSpectrum.primeSpectrumProdHomeo, PrimeSpectrum.primeSpectrumProd_symm_inr]

/-! ## Clopen subsets and idempotents -/

/-- Every clopen subset of a spectrum is a unique standard open defined by an
idempotent. -/
theorem existsUnique_idempotent_basicOpen_eq_of_isClopen
    {R : Type u} [CommRing R] {U : Set (PrimeSpectrum R)} (hU : IsClopen U) :
    ∃! e : R, IsIdempotentElem e ∧
      U = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen hU

/-- The source's one-to-one correspondence between idempotents and clopen
subsets is Mathlib's canonical order equivalence. -/
noncomputable def idempotentClopenEquiv {R : Type u} [CommRing R] :
    {e : R // IsIdempotentElem e} ≃o
      TopologicalSpace.Clopens (PrimeSpectrum R) :=
  PrimeSpectrum.isIdempotentElemEquivClopens

/-! ## Connected spectra -/

/-- A nonzero ring has connected spectrum exactly when it has no nontrivial
idempotents. -/
theorem primeSpectrum_connected_iff_no_nontrivial_idempotents
    (R : Type u) [CommRing R] [Nontrivial R] :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  constructor
  · intro h e he
    have hcl : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
      PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
    obtain ⟨_, hparts⟩ := connectedSpace_iff_clopen.mp h
    rcases hparts _ hcl with h_empty | h_univ
    · left
      apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.zero
      exact SetLike.ext' (by simpa using h_empty)
    · right
      apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.one
      exact SetLike.ext' (by simpa using h_univ)
  · intro h
    apply connectedSpace_iff_clopen.mpr
    refine ⟨inferInstance, ?_⟩
    intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases h e he with rfl | rfl
    · left
      simp
    · right
      simp

/-! ## Finitely generated idempotent ideals -/

/-- A finitely generated ideal satisfying `I = I²` is generated by an
idempotent; its quotient, complementary localization, and vanishing locus
have the forms stated in the source. -/
theorem fg_idempotent_ideal_components
    {R : Type u} [CommRing R] (I : Ideal R) (hI_fg : I.FG)
    (hI_sq : I = I ^ 2) :
    ∃ e : R, IsIdempotentElem e ∧
      I = Ideal.span ({e} : Set R) ∧
      Nonempty ((R ⧸ I) ≃+* Localization.Away (1 - e)) ∧
      IsClopen (PrimeSpectrum.zeroLocus (I : Set R)) := by
  have hI_idem : IsIdempotentElem I := by
    change I * I = I
    simpa [pow_two] using hI_sq.symm
  obtain ⟨e, he, hIe⟩ := (I.isIdempotentElem_iff_of_fg hI_fg).mp hI_idem
  have hspan : I = Ideal.span ({e} : Set R) := by
    simpa [Ideal.submodule_span_eq] using hIe
  refine ⟨e, he, hspan, ?_, ?_⟩
  · rw [hspan]
    have hloc : IsLocalization.Away (1 - e) (R ⧸ Ideal.span ({e} : Set R)) := by
      have h := IsLocalization.Away.quotient_of_isIdempotentElem he.one_sub
      rw [sub_sub_cancel] at h
      exact h
    let awayOneSub : Localization.Away (1 - e) ≃+* R ⧸ Ideal.span ({e} : Set R) :=
      (@IsLocalization.algEquiv R _ (Submonoid.powers (1 - e))
        (Localization.Away (1 - e)) _ _ _ (R ⧸ Ideal.span ({e} : Set R)) _ _ hloc).toRingEquiv
    exact ⟨awayOneSub.symm⟩
  · rw [hspan, PrimeSpectrum.zeroLocus_span]
    exact PrimeSpectrum.isClopen_iff_zeroLocus.mpr ⟨e, he, rfl⟩

/- The source announces a later reproof of the clopen/idempotent statement
   after the glueing-of-functions lemma.  The canonical equivalence above is
   the single chapter interface, so no duplicate declaration is needed here. -/

end

end Formalization.Books.Algebra.Unit21
