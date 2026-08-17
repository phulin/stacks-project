import Formalization.Books.Fields.Unit09.MinimalPolynomials
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Fields, Chapter 10: Algebraic closure

The source's algebraically closed field is Mathlib's `IsAlgClosed` typeclass,
and its algebraic closure is Mathlib's `IsAlgClosure` interface.  The
canonical construction `AlgebraicClosure F` supplies existence, while
`IsAlgClosed.lift` and `IsAlgClosure.equiv` supply the extension and
uniqueness statements.
-/

namespace Formalization.Books.Fields.Unit10

noncomputable section

universe u v w

/-! ## Algebraically closed fields -/

/- The opening fundamental-theorem assertion is Mathlib's complex
   algebraic-closedness instance. -/
/-- The complex numbers are algebraically closed. -/
theorem complex_is_algebraically_closed : IsAlgClosed ℂ := by
  infer_instance

/- The source's definition of algebraically closed is exactly the existing
   `IsAlgClosed` class, so no parallel predicate is introduced.  In the
   polynomial criteria below, `p.Splits` is the canonical assertion that a
   polynomial is a scalar multiple of a product of linear factors. -/
/--
The four standard characterizations of an algebraically closed field.

The `natDegree ≠ 0` hypotheses express “nonconstant” in Mathlib's polynomial
API.
-/
theorem algebraically_closed_iff_polynomial_criteria (F : Type u) [Field F] :
    IsAlgClosed F ↔
      (∀ p : Polynomial F, Irreducible p → p.degree = 1) ∧
        (∀ p : Polynomial F, p.natDegree ≠ 0 → ∃ x : F, Polynomial.IsRoot p x) ∧
          (∀ p : Polynomial F, p.natDegree ≠ 0 → p.Splits) := by
  sorry

/-! ## Algebraic closures -/

/- The source's definition is Mathlib's `IsAlgClosure`; its two fields are
   algebraicity over the base and algebraic closedness of the top field. -/

/-- A field is its own algebraic closure when it is algebraically closed. -/
theorem algebraically_closed_field_is_algebraic_closure
    (F : Type u) [Field F] [IsAlgClosed F] :
    IsAlgClosure F F := by
  infer_instance

/-- Every field has the canonical algebraic closure `AlgebraicClosure F`. -/
theorem algebraic_closure_exists (F : Type u) [Field F] :
    IsAlgClosure F (AlgebraicClosure F) := by
  infer_instance

/- The source's map lemma is the canonical algebraically-closed lifting
   construction, with an arbitrary chosen algebraic closure as target. -/
/-- A field extension algebraic over `F` maps into any algebraic closure of `F`. -/
noncomputable def map_into_algebraic_closure
    {F M E : Type*} [Field F] [Field M] [Field E]
    [Algebra F M] [Algebra F E] [IsAlgClosure F E]
    (hM : Algebra.IsAlgebraic F M) : M →ₐ[F] E := by
  letI : Algebra.IsAlgebraic F M := hM
  letI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
  exact IsAlgClosed.lift

/- The source's uniqueness lemma is the canonical Mathlib algebra equivalence
   between two instances of `IsAlgClosure`.  This is a chosen equivalence,
   not a universal-property or uniqueness assertion, matching the source's
   warning that algebraic closures are not unique up to a unique isomorphism. -/
/-- Any two algebraic closures of a field are isomorphic as field extensions. -/
noncomputable def algebraic_closures_equiv
    (F : Type u) (E E' : Type v) [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] [IsAlgClosure F E] [IsAlgClosure F E'] :
    E ≃ₐ[F] E' :=
  IsAlgClosure.equiv F E E'

end

end Formalization.Books.Fields.Unit10
