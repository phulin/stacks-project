import Formalization.Books.Algebra.Unit29.ImagesOfFinitePresentation
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Commutative Algebra, Chapter 30: More on images

The source's spectrum maps are represented by Mathlib's canonical
`PrimeSpectrum.comap`.  Ideals, radicals, minimal primes, constructible sets,
finite type and finite presentation use the corresponding canonical Mathlib
interfaces.  The only source-facing construction below is the localization
map needed to write the generic finite-presentation statement with explicit
denominators.
-/

namespace Formalization.Books.Algebra.Unit30

open Set
open _root_.Topology
open scoped TensorProduct

/-! ## Generic finite presentation and constructible images -/

/- The map in the first lemma is the canonical map
`R_f → S_{φ(f)g}`.  It is obtained by the universal property of localization;
the image of `f` is invertible because it divides `φ(f) * g`. -/
noncomputable def localizationAwayMulMap
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R) (g : S) :
    Localization.Away f →+* Localization.Away (φ f * g) :=
  Localization.awayLift
    ((algebraMap S (Localization.Away (φ f * g))).comp φ) f
    (by
      change IsUnit (algebraMap S (Localization.Away (φ f * g)) (φ f))
      exact IsLocalization.Away.isUnit_of_dvd
        (S := Localization.Away (φ f * g))
        (x := φ f * g) (r := φ f) (dvd_mul_right (φ f) g))

/-- A finite-type inclusion of domains becomes finitely presented after
localizing the source and target at suitable nonzero elements. -/
theorem exists_localization_away_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (hft : RingHom.FiniteType φ) :
    ∃ f : R, f ≠ 0 ∧ ∃ g : S, g ≠ 0 ∧
      RingHom.FinitePresentation (localizationAwayMulMap φ f g) := by
  sorry

/- The quotient/localization square in the source proof is proof scaffolding:
the canonical quotient spectra and `PrimeSpectrum.comap` already provide its
four arrows.  The theorem below records the resulting relative open-dense
statement directly. -/
/- The displayed polynomial relation in the source's proof of the last lemma
is likewise an argument for the theorem, not an additional chapter-level
interface. -/

/- A constructible image of a finite-type map contains a relatively open dense
subset of the closure of every point it contains. -/
theorem image_constructible_contains_open_dense_subset_of_finiteType
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FiniteType φ) {E : Set (PrimeSpectrum S)}
    (hE : IsConstructible E) {ξ : PrimeSpectrum R}
    (hξ : ξ ∈ PrimeSpectrum.comap φ '' E) :
    ∃ U : Set (closure ({ξ} : Set (PrimeSpectrum R))),
      IsOpen U ∧ Dense U ∧
        (U : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.comap φ '' E := by
  sorry

/-! ## Surjectivity on spectra and radical ideals -/

/- The four conditions in the source are stated as a single `List.TFAE`, so
the ideal-map/comap directions and the prime-spectrum range are visible in
one reusable interface. -/
theorem spectrum_surjective_radical_ideal_conditions
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    List.TFAE
      [ Function.Surjective (PrimeSpectrum.comap φ),
        ∀ I : Ideal R,
          Ideal.comap φ (I.map φ).radical = I.radical,
        ∀ I : Ideal R, I.IsRadical →
          Ideal.comap φ (I.map φ) = I,
        ∀ p : PrimeSpectrum R,
          Ideal.comap φ (p.asIdeal.map φ) = p.asIdeal ] := by
  sorry

/- The source's base-change clause asserts preservation of the first three
conditions.  The tensor product uses the algebra structures induced by the
two displayed ring maps. -/
theorem spectrum_surjective_radical_ideal_conditions_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective (PrimeSpectrum.comap φ))
    {R' : Type*} [CommRing R'] (ψ : R →+* R') :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra R R' := ψ.toAlgebra
    List.TFAE
      [ Function.Surjective
          (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))),
        ∀ I : Ideal R',
          Ideal.comap (algebraMap R' (R' ⊗[R] S))
            (I.map (algebraMap R' (R' ⊗[R] S))).radical = I.radical,
        ∀ I : Ideal R', I.IsRadical →
          Ideal.comap (algebraMap R' (R' ⊗[R] S))
            (I.map (algebraMap R' (R' ⊗[R] S))) = I ] := by
  sorry

/-! ## Dense images and minimal primes -/

/- `DenseRange` is the canonical set-level formulation of the source's
statement that the image contains a dense set of points. -/
theorem domain_injective_dense_spectrum_image_conditions
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] (φ : R →+* S) :
    List.TFAE
      [ Function.Injective φ,
        DenseRange (PrimeSpectrum.comap φ),
        ∃ q : PrimeSpectrum S,
          Ideal.comap φ q.asIdeal = (⊥ : Ideal R) ] := by
  sorry

theorem injective_spectrum_image_contains_minimalPrimes
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ minimalPrimes R) :
    p ∈ Set.range (PrimeSpectrum.comap φ) := by
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hφ p.asIdeal hp
  refine ⟨⟨q, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  exact hqp

theorem spectrum_image_dense_kernel_nilpotent_conditions
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    List.TFAE
      [ (∀ x : R, x ∈ RingHom.ker φ → IsNilpotent x),
        ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
          p ∈ Set.range (PrimeSpectrum.comap φ),
        DenseRange (PrimeSpectrum.comap φ) ] := by
  sorry

theorem minimalPrime_in_spectrum_image_of_minimalPrime
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (hpImage : p ∈ Set.range (PrimeSpectrum.comap φ)) :
    ∃ q : PrimeSpectrum S, q.asIdeal ∈ minimalPrimes S ∧
      PrimeSpectrum.comap φ q = p := by
  sorry

/-! ## Algebraic fraction fields -/

/- The source's ``A ⊂ B`` is represented by an injective algebra map.  The
fraction fields and their compatibility with the inclusion are kept explicit,
so this interface also applies to any chosen fraction-field models. -/
theorem ideal_comap_ne_bot_of_algebraic_fractionFields
    {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra A L]
    [Algebra B L] [Algebra K L] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    (hAB : Function.Injective (algebraMap A B)) (J : Ideal B) (hJ : J ≠ ⊥) :
    Ideal.comap (algebraMap A B) J ≠ (⊥ : Ideal A) := by
  sorry

/- The final sentence of the source lemma is recorded as its direct spectral
consequence for a proper closed subset. -/
theorem image_proper_closed_not_dense_of_algebraic_fractionFields
    {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra A L]
    [Algebra B L] [Algebra K L] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    (hAB : Function.Injective (algebraMap A B))
    {Z : Set (PrimeSpectrum B)} (hZclosed : IsClosed Z)
    (hZproper : Z ≠ Set.univ) :
    ¬ Dense (PrimeSpectrum.comap (algebraMap A B) '' Z) := by
  sorry

end Formalization.Books.Algebra.Unit30
