import Formalization.Books.Exercises.Unit26.Core
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/- The quotient examples below use the canonical ideal-quotient ring API. -/

/-!
# Exercises, Chapter 26: Hilbert functions

The propositions below are the formal interfaces for the chapter's seven
exercises.  Their proofs are intentionally deferred to the proving stage.
-/

noncomputable section

universe u v

open CategoryTheory

namespace Formalization.Books.Exercises.Unit26

/-! ## Exercise 1: Euler–Poincaré functions over a field -/

/-- The value of an Euler–Poincaré function on the one-dimensional vector space. -/
def fieldEulerParameter {k : Type u} [Field k]
    (φ : EulerPoincareFunction k) : ℤ :=
  φ (FGModuleCat.of k k)

/-- Over a field, an Euler–Poincaré function is determined by its value on `k`.
The bijectivity statement packages both the classification and the existence of
all integer-valued choices. -/
theorem eulerPoincareFunction_field_classification (k : Type u) [Field k] :
    Function.Bijective (fieldEulerParameter (k := k)) := by
  sorry

/-- Explicit form of the field classification. -/
theorem eulerPoincareFunction_field_formula (k : Type u) [Field k]
    (φ : EulerPoincareFunction k) (M : FGModuleCat.{u} k) :
    φ M = fieldEulerParameter φ * (Module.finrank k (M : Type u) : ℤ) := by
  sorry

/-! ## Exercise 2: Euler–Poincaré functions over the integers -/

/-- The value of an Euler–Poincaré function on the rank-one free `ℤ`-module. -/
def integerEulerParameter (φ : EulerPoincareFunction ℤ) : ℤ :=
  φ (FGModuleCat.of ℤ ℤ)

/-- Additivity forces every finite torsion module to have value zero, so an
Euler–Poincaré function on finitely generated abelian groups is determined by
its single value on `ℤ`. -/
theorem eulerPoincareFunction_integer_classification :
    Function.Bijective integerEulerParameter := by
  sorry

/-! ## Exercise 3: the node `k[x,y]/(xy)` -/

/-- The homogeneous relation defining the nodal affine curve. -/
def nodePolynomialIdeal (k : Type u) [Field k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}

/-- The nodal ring `k[x,y]/(xy)`. -/
abbrev nodeRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ nodePolynomialIdeal k

/-- The two component ideals in the nodal ring. -/
def nodeXIdeal (k : Type u) [Field k] : Ideal (nodeRing k) :=
  Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k) (MvPolynomial.X 0)}

def nodeYIdeal (k : Type u) [Field k] : Ideal (nodeRing k) :=
  Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k) (MvPolynomial.X 1)}

/-- The two cyclic modules supported on the irreducible components of the node. -/
abbrev nodeXComponent (k : Type u) [Field k] : Type u :=
  nodeRing k ⧸ nodeXIdeal k

abbrev nodeYComponent (k : Type u) [Field k] : Type u :=
  nodeRing k ⧸ nodeYIdeal k

/-- The two component values of an Euler–Poincaré function on the nodal ring. -/
def nodeEulerParameters (k : Type u) [Field k]
    (φ : EulerPoincareFunction (nodeRing k)) : ℤ × ℤ :=
  (φ (FGModuleCat.of (nodeRing k) (nodeXComponent k)),
    φ (FGModuleCat.of (nodeRing k) (nodeYComponent k)))

/-- For an algebraically closed field, the two component values classify all
Euler–Poincaré functions on the nodal ring. -/
theorem eulerPoincareFunction_node_classification
    (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Bijective (nodeEulerParameters (k := k)) := by
  sorry

/-! ## Exercise 4: kernels of locally finite graded maps -/

/-- The kernel of a degree-preserving map between locally finite graded modules
admits the induced grading and remains locally finite. -/
theorem kernel_of_graded_map_is_locally_finite
    {A M N : Type u} {ι : Type v}
    [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [DecidableEq ι]
    (G : GradedModuleData A M ι) (H : GradedModuleData A N ι)
    (hG : G.LocallyFinite) (hH : H.LocallyFinite)
    (f : GradedLinearMap G H) :
    ∃ K : GradedModuleData A (LinearMap.ker f.toLinearMap) ι,
      (∀ n : ι, K.component n = f.kernelComponent n) ∧ K.LocallyFinite := by
  sorry

/-! ## Exercise 5: a weighted polynomial ring -/

/-- The weights `2` and `3` on the two polynomial variables. -/
def twoThreeWeights : Fin 2 → ℕ := fun i => if i = 0 then 2 else 3

/-- The canonical weighted decomposition of `k[x,y]` with weights `2` and `3`. -/
def weightedPolynomialGradedModule (k : Type u) [Field k] :
    GradedModuleData k (MvPolynomial (Fin 2) k) ℕ :=
  { component := MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights
    decomposition := MvPolynomial.weightedDecomposition k twoThreeWeights }

/-- The vector-space dimension of a homogeneous component. -/
def fieldDimensionHilbertFunction
    {k M : Type u} {ι : Type v} [Field k]
    [AddCommGroup M] [Module k M] [DecidableEq ι]
    (G : GradedModuleData k M ι) (n : ι) : ℕ :=
  Module.finrank k (G.component n)

def weightedPolynomialHilbertFunction (k : Type u) [Field k] (n : ℕ) : ℕ :=
  fieldDimensionHilbertFunction (weightedPolynomialGradedModule k) n

/-- The number of solutions of `2a + 3b = n`. -/
def weightedTwoThreeFormula (n : ℕ) : ℕ :=
  if n % 6 = 1 then n / 6 else n / 6 + 1

theorem weighted_polynomial_grading_locally_finite (k : Type u) [Field k] :
    (weightedPolynomialGradedModule k).LocallyFinite := by
  sorry

/-- The weighted polynomial Hilbert function is the solution-counting formula. -/
theorem weighted_polynomial_hilbert_function (k : Type u) [Field k] (n : ℕ) :
    weightedPolynomialHilbertFunction k n = weightedTwoThreeFormula n := by
  sorry

/-- The periodic weighted Hilbert function does not eventually agree with a
numerical polynomial. -/
theorem weighted_polynomial_no_hilbert_polynomial (k : Type u) [Field k] :
    ¬ HasHilbertPolynomialOnNat (weightedPolynomialHilbertFunction k) := by
  sorry

/-! ## Exercise 6: a weighted quotient -/

/-- The homogeneous ideal `(x², xy)` in the weighted polynomial ring. -/
def truncatedPolynomialIdeal (k : Type u) [Field k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1}

/-- The quotient `k[x,y]/(x²,xy)` with `deg x = 2` and `deg y = 3`. -/
abbrev truncatedPolynomialRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ truncatedPolynomialIdeal k

/-- The computed Hilbert function of the weighted quotient. -/
def truncatedPolynomialHilbertFunction (n : ℕ) : ℕ :=
  if n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n) then 1 else 0

/-- The quotient has the grading induced from the weighted homogeneous pieces,
and its Hilbert function is the displayed formula. -/
theorem truncated_polynomial_graded_quotient_exists (k : Type u) [Field k] :
    ∃ G : GradedModuleData k (truncatedPolynomialRing k) ℕ,
      G.LocallyFinite ∧
        (∀ n : ℕ,
          G.component n =
            (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n).map
              (Ideal.Quotient.mkₐ k (truncatedPolynomialIdeal k)).toLinearMap) ∧
        ∀ n : ℕ,
          fieldDimensionHilbertFunction G n = truncatedPolynomialHilbertFunction n := by
  sorry

theorem truncated_polynomial_no_hilbert_polynomial :
    ¬ HasHilbertPolynomialOnNat truncatedPolynomialHilbertFunction := by
  sorry

/-! ## Exercise 7: a degree-`d` plane hypersurface -/

/-- The homogeneous equation defining the degree-`d` hypersurface. -/
def hypersurfacePolynomial (k : Type u) [Field k] (d : ℕ) :
    MvPolynomial (Fin 3) k :=
  MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d + MvPolynomial.X 2 ^ d

/-- The homogeneous coordinate ring of the degree-`d` hypersurface. -/
abbrev hypersurfaceRing (k : Type u) [Field k] (d : ℕ) : Type u :=
  MvPolynomial (Fin 3) k ⧸ Ideal.span {hypersurfacePolynomial k d}

/-- The degree-`n` Hilbert-function formula for the hypersurface quotient. -/
def hypersurfaceHilbertFunction (d n : ℕ) : ℕ :=
  Nat.choose (n + 2) 2 - if d ≤ n then Nat.choose (n - d + 2) 2 else 0

/-- The eventual Hilbert polynomial of a plane degree-`d` hypersurface. -/
def hypersurfaceHilbertPolynomial (d : ℕ) : Polynomial ℚ :=
  Polynomial.C (d : ℚ) * Polynomial.X +
    Polynomial.C ((d : ℚ) * (3 - (d : ℚ)) / 2)

/-- The hypersurface quotient has the grading induced from the homogeneous
pieces and the displayed Hilbert-function formula. -/
theorem hypersurface_graded_quotient_exists (k : Type u) [Field k]
    (d : ℕ) (hd : 0 < d) :
    ∃ G : GradedModuleData k (hypersurfaceRing k d) ℕ,
      G.LocallyFinite ∧
        (∀ n : ℕ,
          G.component n =
            (MvPolynomial.homogeneousSubmodule (Fin 3) k n).map
              (Ideal.Quotient.mkₐ k (Ideal.span {hypersurfacePolynomial k d})).toLinearMap) ∧
        ∀ n : ℕ,
          fieldDimensionHilbertFunction G n = hypersurfaceHilbertFunction d n := by
  sorry

/-- For positive `d`, the hypersurface Hilbert function eventually agrees with
the stated numerical polynomial. -/
theorem hypersurface_hilbert_polynomial (d : ℕ) (hd : 0 < d) :
    IsNumericalPolynomial (hypersurfaceHilbertPolynomial d) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (hypersurfaceHilbertFunction d n : ℚ) =
          (hypersurfaceHilbertPolynomial d).eval (n : ℚ) := by
  sorry

end Formalization.Books.Exercises.Unit26
