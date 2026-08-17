import Formalization.Books.Exercises.Unit57.Definitions

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Exercises, Chapter 57: the regular surface `xy = 7`

The quotient is written with Mathlib's multivariate polynomial and ideal
quotient constructions, while regularity is Mathlib's canonical
`IsRegularRing` predicate.
-/

namespace Formalization.Books.Exercises.Unit57

universe u

noncomputable section

/-! ## Exercise `regular-over-Z` -/

abbrev integerTwoVariablePolynomialRing := MvPolynomial (Fin 2) ℤ

def regularOverZRelationIdeal : Ideal integerTwoVariablePolynomialRing :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (7 : ℤ)} : Set integerTwoVariablePolynomialRing)

abbrev regularOverZRing :=
  integerTwoVariablePolynomialRing ⧸ regularOverZRelationIdeal

/-- The ring `ℤ[x,y]/(xy − 7)` is regular. -/
theorem regularOverZRing_is_regular :
    IsRegularRing regularOverZRing := by
  sorry

end

end Formalization.Books.Exercises.Unit57
