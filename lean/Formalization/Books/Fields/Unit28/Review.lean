import Formalization.Books.Fields.Unit14.PurelyInseparableExtensions
import Mathlib.FieldTheory.Galois.Basic

/-!
# Fields, Chapter 28: Review

The source reviews the canonical notions of algebraic, separable, purely
inseparable, normal, and Galois extensions.  Those notions are already
provided by Mathlib and the earlier Fields chapters, so this file adds only
the source-facing interfaces that are not already available there.
-/

namespace Formalization.Books.Fields.Unit28

noncomputable section

open Polynomial

/-! ## Algebraic and separable elements -/

/- The algebraic/transcendental dichotomy is already the exact theorem
   `Unit08.simple_extension_algebraic_or_transcendental`.  Likewise,
   `minpoly` is the canonical minimal polynomial, and Unit09 already records
   its monicity, irreducibility, annihilation, and uniqueness properties.  In
   particular, the source's degree of an algebraic element is represented by
   `(minpoly k α).natDegree`; Unit09 also identifies this natural degree with
   the finite dimension of the simple extension. -/

/-- The minimal-polynomial data listed in the Review holds for every
    algebraic element. -/
theorem review_minimal_polynomial_data
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) :
    (minpoly k α).Monic ∧
      Irreducible (minpoly k α) ∧
        Polynomial.aeval α (minpoly k α) = 0 := by
  sorry

/-- The monic irreducible polynomial annihilating an algebraic element is its
    minimal polynomial. -/
theorem review_minimal_polynomial_unique
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) {P : k[X]}
    (hP_monic : P.Monic) (hP_irreducible : Irreducible P)
    (hP_root : Polynomial.aeval α P = 0) :
    P = minpoly k α := by
  sorry

/- The derivative criterion and the distinct-root formulation are already
   supplied by the separability API.  The following theorem places both
   formulations directly beside the Review's minimal-polynomial discussion.
-/
/-- An algebraic element is separable exactly when its minimal polynomial has
    nonzero derivative. -/
theorem review_separable_iff_minpoly_derivative_ne_zero
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) :
    IsSeparable k α ↔ (minpoly k α).derivative ≠ 0 := by
  sorry

/-- An algebraic element is separable exactly when its minimal polynomial has
    pairwise distinct roots in the algebraic closure. -/
theorem review_separable_iff_distinct_algebraic_closure_roots
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) :
    IsSeparable k α ↔
      ((minpoly k α).aroots (AlgebraicClosure k)).Nodup := by
  sorry

/-- The distinct-root condition can equivalently be written as the displayed
    product of the monic linear factors in the algebraic closure. -/
theorem review_separable_iff_minpoly_product_of_distinct_roots
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α) :
    IsSeparable k α ↔
      ∃ roots : Multiset (AlgebraicClosure k),
        roots.Nodup ∧ roots.card = (minpoly k α).natDegree ∧
          (minpoly k α).map (algebraMap k (AlgebraicClosure k)) =
            (roots.map (fun r => X - C r)).prod := by
  sorry

/- The earlier separability chapter's Frobenius-contraction theorem supplies
   the polynomial-in-a-power assertion in the inseparable case.  This
   source-facing statement also records the maximal exponent and the
   separability of the corresponding powered element.
-/
/-- If the minimal polynomial of an algebraic element has zero derivative,
    it is a polynomial in a largest Frobenius power, and the corresponding
    power of the element is separable. -/
theorem review_inseparable_frobenius_contraction
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {α : K} (hα : IsAlgebraic k α)
    (hderiv : (minpoly k α).derivative = 0) :
    ∃ (p e : ℕ) (Q : k[X]),
      p.Prime ∧ CharP k p ∧ Q.Separable ∧ Irreducible Q ∧
        Polynomial.expand k (p ^ e) Q = minpoly k α ∧
          (∀ m : ℕ,
            (∃ R : k[X], Polynomial.expand k (p ^ m) R = minpoly k α) →
              m ≤ e) ∧
          IsSeparable k (α ^ (p ^ e)) := by
  sorry

/-! ## Algebraic field extensions -/

/- The five extension definitions in the source are canonical declarations,
   not parallel local predicates:

   * `Algebra.IsAlgebraic k K` is algebraicness, with
     `Unit08.algebraic_extension_iff_all_elements_algebraic` as its
     pointwise characterization.
   * `Algebra.IsSeparable k K` is separability; Mathlib's definition already
     implies algebraicity, and Unit12 records its pointwise characterization.
   * `IsPurelyInseparable k K` is the canonical purely inseparable class.
     Unit14's `purely_inseparable_extension_iff_pow_mem` gives the source's
     p-power characterization when `CharP k p` holds for a prime `p`.
   * `Normal k K` packages algebraicity with splitting of every minimal
     polynomial, exposed pointwise by Mathlib's `normal_iff` and `Normal.splits`.
   * `IsGalois k K` is separable and normal, exactly as stated by
     `isGalois_iff`.

   No duplicate definitions are introduced for these established notions.
-/

/-! ## The p-th-root lemma -/

/- “Pairwise distinct roots in an algebraic closure” is represented by
   `Polynomial.Separable`, whose root formulation is the theorem used above.
   “All coefficients are p-th powers” is kept inline as a condition on
   `Polynomial.coeff`; this avoids introducing a second polynomial predicate.
-/

/-- In a separable algebraic extension, an element whose minimal-polynomial
    coefficients are p-th powers already has a p-th root in the extension. -/
theorem pth_root_of_minpoly_coefficients
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] (p : ℕ) (hp : p.Prime) [CharP K p]
    (α : L)
    (hcoeff : ∀ i : ℕ, ∃ b : K, (minpoly K α).coeff i = b ^ p) :
    ∃ β : L, β ^ p = α := by
  sorry

/-- More generally, a root in a separable algebraic extension of a separable
    polynomial with p-th-power coefficients has a p-th root in the extension.
-/
theorem pth_root_of_separable_polynomial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] (p : ℕ) (hp : p.Prime) [CharP K p]
    (α : L) (P : K[X])
    (hroot : Polynomial.aeval α P = 0)
    (hseparable : P.Separable)
    (hcoeff : ∀ i : ℕ, ∃ b : K, P.coeff i = b ^ p) :
    ∃ β : L, β ^ p = α := by
  sorry

end

end Formalization.Books.Fields.Unit28
