import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Div

/-!
# Exercises, Chapter 15: Constructible sets

This file records the source-facing interface for the non-monic polynomial
division exercise.  The coefficient list is indexed by `Fin`, so the
polynomial with coefficients `a 0, ..., a (d - 1)` is available uniformly
also when `d = 0`.
-/

namespace Formalization.Books.Exercises.Unit15

universe u

noncomputable section

/-! ## Exercise `division-with-remainder` -/

/-- The polynomial `a 0 + a 1 X + ⋯ + a (d - 1) X^(d - 1)`. -/
def polynomialOfCoefficients {R : Type u} [Semiring R] (d : ℕ)
    (a : Fin d → R) : Polynomial R :=
  ∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

/-- Pseudo-division by a polynomial over a ring: after multiplying by a power
of the leading coefficient, the remainder has degree strictly below the
prescribed degree. -/
theorem exists_pseudo_division
    {R : Type u} [CommRing R] (d : ℕ) (a : Fin (d + 1) → R)
    (g : Polynomial R) :
    ∃ N : ℕ, ∃ q r : Polynomial R,
      Polynomial.C ((a (Fin.last d)) ^ N) * g =
        q * polynomialOfCoefficients (d + 1) a + r ∧
        Polynomial.degree r < d ∧
        ∃ c : Fin d → R, r = polynomialOfCoefficients d c := by
  sorry

end

end Formalization.Books.Exercises.Unit15
