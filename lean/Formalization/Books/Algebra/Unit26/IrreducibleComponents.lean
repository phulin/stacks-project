import Formalization.Books.Algebra.Unit25.ZerodivisorsAndTotalRingsOfFractions
import Formalization.Books.Topology.Unit08.IrreducibleComponents
import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 26: Irreducible components of spectra

The canonical Mathlib notions `PrimeSpectrum.zeroLocus`, `IsIrreducible`,
`irreducibleComponents`, and `IsProfiniteSpace` are used for the statements in
this chapter.  The unfinished ninth item in the final source list is recorded
in the accompanying formalization report rather than translated into a
mathematical proposition.
-/

namespace Formalization.Books.Algebra.Unit26

open Set _root_.Topology

universe u

/-! ## Irreducible components of spectra -/

section Irreducible

variable {R : Type u} [CommRing R]

/-! ### Closure of a prime and irreducible closed subsets -/

/-- The closure of a point of the prime spectrum is its vanishing locus. -/
theorem closure_singleton_prime (p : PrimeSpectrum R) :
    closure ({p} : Set (PrimeSpectrum R)) =
      PrimeSpectrum.zeroLocus (p.asIdeal : Set R) :=
  PrimeSpectrum.closure_singleton p

/-- The irreducible closed subsets of a prime spectrum are the vanishing
loci of prime ideals. -/
theorem isClosed_and_isIrreducible_iff_zeroLocus_prime
    (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ∧ IsIrreducible Z ↔
      ∃ p : PrimeSpectrum R,
        Z = PrimeSpectrum.zeroLocus (p.asIdeal : Set R) := by
  constructor
  · rintro ⟨hZclosed, hZirreducible⟩
    let P : Ideal R := PrimeSpectrum.vanishingIdeal Z
    have hPprime : P.IsPrime :=
      (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime).mp hZirreducible
    refine ⟨⟨P, hPprime⟩, ?_⟩
    exact hZclosed.closure_eq.symm.trans
      (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z).symm
  · rintro ⟨p, rfl⟩
    refine ⟨PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
    rw [← PrimeSpectrum.closure_singleton p]
    exact isIrreducible_singleton.closure

/-- The irreducible components of a prime spectrum are exactly the vanishing
loci of its minimal prime ideals. -/
theorem zeroLocus_minimalPrimes_eq_irreducibleComponents :
    PrimeSpectrum.zeroLocus ∘ (↑) '' minimalPrimes R =
      irreducibleComponents (PrimeSpectrum R) := by
  exact PrimeSpectrum.zeroLocus_minimalPrimes R

/-! The source's accompanying generic-point assertion. -/

/-- Every irreducible closed subset of a prime spectrum has a unique generic
point. -/
theorem irreducibleClosed_existsUnique_genericPoint :
    ∀ Z : Set (PrimeSpectrum R), IsIrreducible Z → IsClosed Z →
      ∃! p : PrimeSpectrum R, IsGenericPoint p Z := by
  exact
    (Formalization.Books.Topology.Unit08.quasiSober_and_t0_iff_unique_genericPoint
      (X := PrimeSpectrum R)).mp ⟨inferInstance, inferInstance⟩

/- The source's sober-space assertion is represented by Mathlib's canonical
`QuasiSober` and `T0Space` pair. -/
theorem primeSpectrum_is_sober :
    QuasiSober (PrimeSpectrum R) ∧ T0Space (PrimeSpectrum R) := by
  exact ⟨inferInstance, inferInstance⟩

/-! ### Spectrality -/

/-- The spectrum of a commutative ring is a spectral space. -/
theorem primeSpectrum_is_spectral : SpectralSpace (PrimeSpectrum R) := by
  infer_instance

/-! ### Components through a point -/

/-- Irreducible closed subsets through a prime correspond to primes of the
localization at that prime. -/
theorem irreducibleClosedSets_through_prime_correspond_localization
    (p : PrimeSpectrum R) :
    Nonempty
      ({Z : Set (PrimeSpectrum R) // IsClosed Z ∧ IsIrreducible Z ∧ p ∈ Z} ≃
        PrimeSpectrum (Localization.AtPrime p.asIdeal)) := by
  sorry

/-- Irreducible components through a prime correspond to minimal primes of the
localization at that prime. -/
theorem irreducibleComponents_through_prime_correspond_minimalPrimes_localization
    (p : PrimeSpectrum R) :
    Nonempty
      ({C : Set (PrimeSpectrum R) //
          C ∈ irreducibleComponents (PrimeSpectrum R) ∧ p ∈ C} ≃
        {q : PrimeSpectrum (Localization.AtPrime p.asIdeal) //
          q.asIdeal ∈ minimalPrimes (Localization.AtPrime p.asIdeal)}) := by
  sorry

/-! ### A standard open avoiding a minimal prime -/

/-- A quasi-compact open avoiding a minimal prime is disjoint from a standard
open containing that minimal prime. -/
theorem exists_basicOpen_disjoint_of_minimalPrime
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    {W : Set (PrimeSpectrum R)} (hWopen : IsOpen W) (hWcompact : IsCompact W)
    (hpW : p ∉ W) :
    ∃ f : R, f ∉ p.asIdeal ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩ W = ∅ := by
  sorry

/-! ### Rings with no nontrivial prime inclusions -/

/-- The eight substantive conditions listed in the source are equivalent for
the spectrum of a commutative ring. -/
theorem isProfinite_TFAE_primeSpectrum_separation_conditions :
    List.TFAE
      [Formalization.Books.Topology.Unit22.IsProfiniteSpace (PrimeSpectrum R),
        T2Space (PrimeSpectrum R),
        TotallyDisconnectedSpace (PrimeSpectrum R),
        (∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U),
        (∀ p q : Ideal R, p.IsPrime → q.IsPrime → p ≤ q → p = q),
        (∀ p : Ideal R, p.IsPrime → p.IsMaximal),
        (∀ p : Ideal R, p.IsPrime → p ∈ minimalPrimes R),
        (∀ f : R, IsClosed (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)))] := by
  sorry

end Irreducible

end Formalization.Books.Algebra.Unit26
