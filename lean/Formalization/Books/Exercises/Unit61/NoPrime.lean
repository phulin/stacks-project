import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Basic

import Formalization.Books.Exercises.Unit21.Core

/-!
# Exercises, Chapter 61: No prime

The relation `xy = 0` is imposed in a quotient of the three-variable complex
polynomial ring.  The two ideals below are the quotient versions of the two
specified points, and the final theorem records the requested vanishing-set
obstruction as ideal containment.
-/

namespace Formalization.Books.Exercises.Unit61

open Formalization.Books.Exercises.Unit21

universe u

noncomputable section

/-- The three-variable polynomial ring over `ℂ`. -/
abbrev noPrimePolynomialRing := nVariablePolynomialRing ℂ 3

/-- The relation ideal `(xy)`. -/
def noPrimeRelationIdeal : Ideal noPrimePolynomialRing :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (1 : Fin 3)} :
      Set noPrimePolynomialRing)

/-- The ring `ℂ[x,y,z]/(xy)`. -/
abbrev noPrimeRing := noPrimePolynomialRing ⧸ noPrimeRelationIdeal

/-- The quotient ideal `(x,y-1,z-5)`. -/
def noPrimeFirstPoint : Ideal noPrimeRing :=
  Ideal.span
    ({Ideal.Quotient.mk noPrimeRelationIdeal (MvPolynomial.X (0 : Fin 3)),
      Ideal.Quotient.mk noPrimeRelationIdeal
        (MvPolynomial.X (1 : Fin 3) - MvPolynomial.C 1),
      Ideal.Quotient.mk noPrimeRelationIdeal
        (MvPolynomial.X (2 : Fin 3) - MvPolynomial.C 5)} :
      Set noPrimeRing)

/-- The quotient ideal `(x-1,y,z-7)`. -/
def noPrimeSecondPoint : Ideal noPrimeRing :=
  Ideal.span
    ({Ideal.Quotient.mk noPrimeRelationIdeal
        (MvPolynomial.X (0 : Fin 3) - MvPolynomial.C 1),
      Ideal.Quotient.mk noPrimeRelationIdeal (MvPolynomial.X (1 : Fin 3)),
      Ideal.Quotient.mk noPrimeRelationIdeal
        (MvPolynomial.X (2 : Fin 3) - MvPolynomial.C 7)} :
      Set noPrimeRing)

/-- The two displayed quotient ideals are prime point ideals. -/
theorem noPrimeFirstPoint_isPrime : noPrimeFirstPoint.IsPrime := by
  sorry

theorem noPrimeSecondPoint_isPrime : noPrimeSecondPoint.IsPrime := by
  sorry

/-- No prime ideal is contained in both point ideals.  Since `V(p)` consists
of primes containing `p`, this is exactly the source's assertion that no
`V(p)` contains both displayed points. -/
theorem no_prime_with_both_points_in_vanishing_set :
    ¬ ∃ p : Ideal noPrimeRing, p.IsPrime ∧
      p ≤ noPrimeFirstPoint ∧ p ≤ noPrimeSecondPoint := by
  sorry

/-- The same obstruction written with Mathlib's canonical `V(I)` notation
`PrimeSpectrum.zeroLocus`. -/
theorem no_prime_with_both_points_in_zeroLocus :
    ¬ ∃ p : PrimeSpectrum noPrimeRing,
      (⟨noPrimeFirstPoint, noPrimeFirstPoint_isPrime⟩ : PrimeSpectrum noPrimeRing) ∈
          PrimeSpectrum.zeroLocus (p.asIdeal : Set noPrimeRing) ∧
        (⟨noPrimeSecondPoint, noPrimeSecondPoint_isPrime⟩ : PrimeSpectrum noPrimeRing) ∈
          PrimeSpectrum.zeroLocus (p.asIdeal : Set noPrimeRing) := by
  sorry

end

end Formalization.Books.Exercises.Unit61
