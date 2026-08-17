import Formalization.Books.Algebra.Unit09.Localization
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Commutative Algebra, Chapter 25: Zerodivisors and total rings of fractions

This file formalizes the definitions and theorem interfaces in the
`Zerodivisors and total rings of fractions` section of `books/algebra.tex`.
The total quotient ring is the canonical localization at `nonZeroDivisors`.
-/

namespace Formalization.Books.Algebra.Unit25

universe u

noncomputable section

/-! ## Zerodivisors and minimal-prime localizations -/

/-- The set of zerodivisors, expressed using Mathlib's canonical submonoid of
non-zero-divisors. -/
def zeroDivisors {R : Type u} [CommRing R] : Set R :=
  {x | x ∉ nonZeroDivisors R}

/-- The minimal prime ideals, packaged as points of the prime spectrum. -/
abbrev MinimalPrimeSpectrum (R : Type u) [CommRing R] :=
  {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}

/-- The product of the localizations at all minimal primes. -/
abbrev minimalPrimeLocalizations (R : Type u) [CommRing R] :=
  ∀ p : MinimalPrimeSpectrum R, Localization.AtPrime p.1.asIdeal

/-- The canonical map from a ring to the product of its minimal-prime
localizations. -/
def mapToMinimalPrimeLocalizations {R : Type u} [CommRing R] :
    R →+* minimalPrimeLocalizations R :=
  RingHom.pi fun p => algebraMap R (Localization.AtPrime p.1.asIdeal)

/-- The image of the canonical map is a subring of the product. -/
def minimalPrimeLocalizationRange {R : Type u} [CommRing R] :
    Subring (minimalPrimeLocalizations R) :=
  (mapToMinimalPrimeLocalizations (R := R)).range

/-- Every element of the maximal ideal of the localization at a minimal prime
is nilpotent. -/
theorem isNilpotent_mem_maximalIdeal_localizationAt_minimalPrime
    {R : Type u} [CommRing R] (p : MinimalPrimeSpectrum R)
    {x : Localization.AtPrime p.1.asIdeal}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.1.asIdeal)) :
    IsNilpotent x := by
  sorry

/-- If the ring is reduced, each factor in the minimal-prime localization
product is a field. -/
theorem isField_localizationAt_minimalPrime_of_isReduced
    {R : Type u} [CommRing R] [IsReduced R] (p : MinimalPrimeSpectrum R) :
    IsField (Localization.AtPrime p.1.asIdeal) := by
  sorry

/-- A reduced ring is isomorphic to the subring given by its canonical map
into the product of the localizations at its minimal primes. -/
theorem reduced_ring_equiv_minimalPrimeLocalizationRange
    {R : Type u} [CommRing R] [IsReduced R] :
    Nonempty (R ≃+* minimalPrimeLocalizationRange (R := R)) := by
  sorry

/-- The canonical map into the product of the localizations at the minimal
primes is injective for a reduced ring. -/
theorem mapToMinimalPrimeLocalizations_injective
    {R : Type u} [CommRing R] [IsReduced R] :
    Function.Injective (mapToMinimalPrimeLocalizations (R := R)) := by
  sorry

/-- In a reduced ring, the union of the minimal primes is exactly the set of
zerodivisors. -/
theorem iUnion_minimalPrimeSpectrum_eq_zeroDivisors
    {R : Type u} [CommRing R] [IsReduced R] :
    (⋃ p : MinimalPrimeSpectrum R, (p.1.asIdeal : Set R)) =
      zeroDivisors (R := R) := by
  sorry

/-! ## Total rings of fractions -/

/-- Localizing a ring at a multiplicative set of non-zero-divisors does not
change its total quotient ring, up to ring equivalence. -/
theorem totalQuotientRing_equiv_localization
    {R : Type u} [CommRing R] (S : Submonoid R)
    (hS : S ≤ nonZeroDivisors R) :
    Nonempty (Formalization.Books.Algebra.Unit09.totalQuotientRing R ≃+*
      Formalization.Books.Algebra.Unit09.totalQuotientRing (Localization S)) := by
  sorry

/-- The total quotient ring is unchanged by forming the total quotient ring
again. -/
theorem totalQuotientRing_equiv_self {R : Type u} [CommRing R] :
    Nonempty (Formalization.Books.Algebra.Unit09.totalQuotientRing R ≃+*
      Formalization.Books.Algebra.Unit09.totalQuotientRing
        (Formalization.Books.Algebra.Unit09.totalQuotientRing R)) := by
  sorry

/-- If the distinct finitely many minimal primes are `q i` and their union is
the set of zerodivisors, the total quotient ring is their product of
localizations. -/
theorem totalQuotientRing_equiv_pi_minimalPrime_localizations
    {R : Type u} [CommRing R] (n : ℕ) (q : Fin n → PrimeSpectrum R)
    (hq : Set.range (fun i : Fin n => (q i).asIdeal) = minimalPrimes R)
    (hq_injective : Function.Injective q)
    (hz : (⋃ i : Fin n, ((q i).asIdeal : Set R)) = zeroDivisors (R := R)) :
    Nonempty (Formalization.Books.Algebra.Unit09.totalQuotientRing R ≃+*
      (∀ i : Fin n, Localization.AtPrime (q i).asIdeal)) := by
  sorry

end

end Formalization.Books.Algebra.Unit25
