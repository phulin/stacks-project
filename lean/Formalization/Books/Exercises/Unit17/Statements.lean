import Formalization.Books.Exercises.Unit17.Core

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Exercises, Chapter 17: Dimension

The declarations below follow the three exercises in source order.  Proofs are
deferred to the proving stage; the constructions use Mathlib's canonical
polynomial, ideal, prime-spectrum, Krull-dimension, and localization objects.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit17

/-! ## Exercise `dimension-bigger-one-finite-nr-primes` -/

/-- There is a commutative ring with finitely many prime ideals and Krull
dimension strictly greater than one. -/
theorem exists_ring_with_finitely_many_prime_ideals_and_dimension_gt_one :
    ∃ (R : Type u) (inst : CommRing R),
      @HasFinitePrimeSpectrumAndDimensionAboveOne R inst := by
  sorry

/-! ## Exercise `hypersurface-in-A2-dimension-one` -/

/-- The quotient of `ℂ[x,y]` by a nonconstant polynomial has dimension one. -/
theorem complex_bivariate_hypersurface_has_dimension_one
    (f : complexBivariatePolynomialRing)
    (hf : IsNonconstantComplexBivariatePolynomial f) :
    ringKrullDim (complexBivariateHypersurfaceRing f) = 1 := by
  sorry

/-! ## Exercise `dimension-polynomial-ring` -/

/-- The ideal `(𝔪, x₁, ..., xₙ)` in a polynomial ring over a local ring is
maximal. -/
theorem polynomialMaximalIdeal_isMaximal
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    (polynomialMaximalIdeal R n).IsMaximal := by
  sorry

instance polynomialMaximalIdeal_isPrime
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    (polynomialMaximalIdeal R n).IsPrime :=
  (polynomialMaximalIdeal_isMaximal R n).isPrime

/- The localization at the displayed maximal ideal. -/
abbrev polynomialLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :=
  Localization.AtPrime (polynomialMaximalIdeal R n)

/-- For a Noetherian local ring, localizing its `n`-variable polynomial ring
at `(𝔪, x₁, ..., xₙ)` raises the dimension by `n` (for `n ≥ 1`). -/
theorem polynomial_localization_dimension_formula
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (hn : 1 ≤ n) :
    ringKrullDim (polynomialLocalRing R n) = ringKrullDim R + n := by
  sorry

end Formalization.Books.Exercises.Unit17
