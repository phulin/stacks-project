import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Exercises, Chapter 5: Flat ring maps

This file records the two explicit witnesses requested for the failure of
flatness over `k[x,y]`.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit05

open scoped TensorProduct

/-! ## The polynomial ring and the ideal `(x,y)` -/

/-- The two-variable polynomial ring used in both examples. -/
abbrev twoVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The ideal `(x,y)` in `k[x,y]`. -/
def polynomialXYIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (twoVariablePolynomialRing k))

/-- The inclusion of `(x,y)` into `k[x,y]`. -/
def polynomialXYIdealInclusion (k : Type u) [Field k] :
    (polynomialXYIdeal k : Type u) →ₗ[twoVariablePolynomialRing k]
      twoVariablePolynomialRing k :=
  (polynomialXYIdeal k).subtype

/-- The map obtained by tensoring the ideal inclusion with `(x,y)`. -/
def polynomialXYIdealTensorInclusion (k : Type u) [Field k] :
    ((polynomialXYIdeal k : Type u) ⊗[twoVariablePolynomialRing k]
        (polynomialXYIdeal k : Type u)) →ₗ[twoVariablePolynomialRing k]
      (twoVariablePolynomialRing k ⊗[twoVariablePolynomialRing k]
        (polynomialXYIdeal k : Type u)) :=
  (polynomialXYIdeal k).subtype.rTensor (polynomialXYIdeal k)

/-- For `N = (x,y)`, the ideal inclusion is an injection whose tensor with
`N` is not injective. -/
theorem polynomialXYIdeal_tensor_counterexample (k : Type u) [Field k] :
    Function.Injective (polynomialXYIdealInclusion k) ∧
      ¬ Function.Injective (polynomialXYIdealTensorInclusion k) := by
  constructor
  · exact Submodule.injective_subtype (polynomialXYIdeal k)
  · sorry

/-! ## The quotient `k[x,y]/(x,y)` -/

/-- The residue-field quotient at `(x,y)`. -/
abbrev polynomialXYQuotient (k : Type u) [Field k] :=
  twoVariablePolynomialRing k ⧸ polynomialXYIdeal k

/-- Multiplication by `x` on `k[x,y]`. -/
def multiplicationByFirstVariable (k : Type u) [Field k] :
    twoVariablePolynomialRing k →ₗ[twoVariablePolynomialRing k]
      twoVariablePolynomialRing k :=
  LinearMap.mulLeft _ (MvPolynomial.X (0 : Fin 2))

/-- The tensor of multiplication by `x` with the quotient `k[x,y]/(x,y)`. -/
def multiplicationByFirstVariableTensorQuotient (k : Type u) [Field k] :
    (twoVariablePolynomialRing k ⊗[twoVariablePolynomialRing k]
        polynomialXYQuotient k) →ₗ[twoVariablePolynomialRing k]
      (twoVariablePolynomialRing k ⊗[twoVariablePolynomialRing k]
        polynomialXYQuotient k) :=
  (multiplicationByFirstVariable k).rTensor (polynomialXYQuotient k)

/-- For `N = k[x,y]/(x,y)`, multiplication by `x` is an injection before
tensoring but becomes non-injective after tensoring with `N`. -/
theorem polynomialXYQuotient_tensor_counterexample (k : Type u) [Field k] :
    Function.Injective (multiplicationByFirstVariable k) ∧
      ¬ Function.Injective (multiplicationByFirstVariableTensorQuotient k) := by
  constructor <;> sorry

end Formalization.Books.Exercises.Unit05
