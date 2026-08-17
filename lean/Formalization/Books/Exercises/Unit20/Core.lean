import Mathlib.Algebra.Algebra.Operations
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.EssentialFiniteness

/-!
# Exercises, Chapter 20: Transcendence degree

This file contains the source-facing growth predicate used in the final
exercise.  Finite-dimensional subvector spaces are represented by Mathlib's
`Submodule`, their product by `Submodule.mul`, and their powers by the
canonical power operation on submodules.
-/

namespace Formalization.Books.Exercises.Unit20

universe u v

noncomputable section

/- The source leaves the coefficient fields of the constants implicit.  The
   standard real-valued formulation makes the polynomial-growth inequalities
   precise while retaining the natural-number exponent forced by `n ^ d`. -/
/-- The prescribed two-sided polynomial growth for powers of finite-dimensional
subvector spaces. -/
def HasSubvectorSpacePowerGrowth
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] (d : ℕ) : Prop :=
  (∃ V : Submodule k K, FiniteDimensional k V ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ n : ℕ, 1 ≤ n →
          (Module.finrank k ((V ^ n : Submodule k K) : Type v) : ℝ) ≥
            ε * (n : ℝ) ^ d) ∧
    (∀ V : Submodule k K, FiniteDimensional k V →
      ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 1 ≤ n →
          (Module.finrank k ((V ^ n : Submodule k K) : Type v) : ℝ) ≤
            C * (n : ℝ) ^ d)

/- The displayed identities `V² = VV`, `V³ = VV²`, and so on use the canonical
   `Submodule` power operation.  Mathlib's `Submodule.pow_succ` recurses as
   `V ^ (n + 1) = V ^ n * V`; commutativity of the field identifies this with
   the source's `V * V ^ n` presentation, so no parallel power definition is
   introduced. -/

end

end Formalization.Books.Exercises.Unit20
