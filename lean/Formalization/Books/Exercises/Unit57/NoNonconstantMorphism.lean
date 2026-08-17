import Formalization.Books.Exercises.Unit57.Definitions

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Exercises, Chapter 57: no nonconstant map from the Laurent line

The source's `k[x, x⁻¹]` is represented by Mathlib's canonical localization
`Localization.Away Polynomial.X`; the image of the polynomial generator is
the corresponding localization algebra map.
-/

namespace Formalization.Books.Exercises.Unit57

universe u

noncomputable section

/-! ## Exercise `no-nonconstant-morphism` -/

abbrev LaurentPolynomialRing (k : Type u) [Field k] :=
  Localization.Away (Polynomial.X : Polynomial k)

def LaurentPolynomialGenerator (k : Type u) [Field k] : LaurentPolynomialRing k :=
  algebraMap (Polynomial k) (LaurentPolynomialRing k) Polynomial.X

/-- Every `k`-algebra map from `k[x,x⁻¹]` to `k[y]` sends `x` to a constant. -/
theorem algHom_laurentPolynomial_to_polynomial_maps_generator_to_constant
    (k : Type u) [Field k]
    (φ : LaurentPolynomialRing k →ₐ[k] Polynomial k) :
    ∃ c : k, φ (LaurentPolynomialGenerator k) = Polynomial.C c := by
  sorry

end

end Formalization.Books.Exercises.Unit57
