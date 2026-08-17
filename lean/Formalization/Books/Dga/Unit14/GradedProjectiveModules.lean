import Formalization.Books.Dga.Unit14.Core
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Differential Graded Algebra, Chapter 14: Projective modules over graded algebras

This file formalizes the second source section.  The shift convention is
`M[k]^n = M^(n+k)`, so the degree-zero generator of `A[k]` lies in degree
`-k`, exactly as in the displayed Hom formula in the source.
-/

namespace Formalization.Books.Dga.Unit14

open CategoryTheory
open Limits

universe u v w

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-- The graded-module category used in this section is abelian. -/
theorem graded_right_module_category_is_abelian :
    Nonempty (Abelian (GradedRightModuleCategory (R := R) (A := A))) := by
  sorry

/-! ## Shifts -/

/-- Data specifying the standard shift of a graded right module.

The component equation is recorded explicitly; `action_eq` says that the
action is transported from `M` along that equation.  The existence proof is a
proposition-level interface because its only content is the routine cast
bookkeeping for integer addition.
-/
structure GradedShiftSpec
    (M : GradedRightModule (R := R) (A := A)) (k : ℤ) where
  object : GradedRightModule (R := R) (A := A)
  component_eq : ∀ n : ℤ, object.component n = M.component (n + k)
  action_eq : ∀ {i j : ℤ} (m : M.component (i + k)) (a : A j),
    HEq
      (object.action (cast (component_eq i).symm m) a)
      (M.action m a)

theorem gradedShiftSpec_nonempty
    (M : GradedRightModule (R := R) (A := A)) (k : ℤ) :
    Nonempty (GradedShiftSpec (R := R) (A := A) M k) := by
  sorry

/-- The graded shift `M[k]`, with component `n` equal to `M^(n+k)`. -/
noncomputable def gradedShift
    (M : GradedRightModule (R := R) (A := A)) (k : ℤ) :
    GradedRightModule (R := R) (A := A) :=
  (Classical.choice (gradedShiftSpec_nonempty (R := R) (A := A) M k)).object

theorem gradedShift_component
    (M : GradedRightModule (R := R) (A := A)) (k n : ℤ) :
    (gradedShift M k).component n = M.component (n + k) :=
  (Classical.choice (gradedShiftSpec_nonempty (R := R) (A := A) M k)).component_eq n

/-- The shifted regular graded module `A[k]`. -/
noncomputable def gradedAlgebraShift (k : ℤ) : GradedRightModule (R := R) (A := A) :=
  gradedShift (gradedRegularModule (R := R) (A := A)) k

/-! ## Hom evaluation and projectivity -/

/-- Evaluation at the shifted unit identifies the degree-zero Hom from `A[k]`
with the `(-k)`-component of the target. -/
theorem graded_shift_hom_evaluation_equiv
    (k : ℤ) (M : GradedRightModule (R := R) (A := A)) :
    Nonempty
      (GradedRightModuleHom (R := R) (A := A) (gradedAlgebraShift (R := R) (A := A) k) M
        ≃ M.component (-k)) := by
  sorry

/-- Every shift of the regular graded module is projective in the graded
module category. -/
theorem graded_algebra_shift_projective (k : ℤ) :
    GradedProjective (gradedAlgebraShift (R := R) (A := A) k) := by
  sorry

/-! ## Direct sums of shifts -/

/-- A degree-zero map of graded modules is surjective when it is surjective in
every homogeneous degree. -/
def GradedRightModuleHom.DegreewiseSurjective
    {M N : GradedRightModule (R := R) (A := A)}
    (f : GradedRightModuleHom M N) : Prop :=
  ∀ n : ℤ, Function.Surjective (f.app n)

/-- The categorical coproduct of a family of shifts, when it exists. -/
noncomputable def gradedDirectSumOfShifts
    (I : Type w) (degree : I → ℤ)
    (h : HasCoproduct (fun i => gradedAlgebraShift (R := R) (A := A) (degree i))) :
    GradedRightModule (R := R) (A := A) := by
  letI := h
  exact ∐ fun i => gradedAlgebraShift (R := R) (A := A) (degree i)

/-- Every graded module is a quotient of a direct sum of shifts of `A`. -/
theorem every_graded_module_quotient_of_shifted_free
    (M : GradedRightModule (R := R) (A := A)) :
    ∃ (I : Type w) (degree : I → ℤ)
      (h : HasCoproduct (fun i => gradedAlgebraShift (R := R) (A := A) (degree i)))
      (f : gradedDirectSumOfShifts (R := R) (A := A) I degree h ⟶ M),
      GradedRightModuleHom.DegreewiseSurjective f := by
  sorry

/-- A projective graded module is a direct summand of a direct sum of shifts
of the regular graded module. -/
theorem graded_projective_is_direct_summand_of_shifted_free
    (P : GradedRightModule (R := R) (A := A)) (hP : GradedProjective P) :
    ∃ (I : Type w) (degree : I → ℤ)
      (h : HasCoproduct (fun i => gradedAlgebraShift (R := R) (A := A) (degree i)))
      (i : P ⟶ gradedDirectSumOfShifts (R := R) (A := A) I degree h)
      (s : gradedDirectSumOfShifts (R := R) (A := A) I degree h ⟶ P),
      i ≫ s = 𝟙 P := by
  sorry

/-- The graded-module category has enough projectives. -/
theorem graded_right_module_category_has_enough_projectives :
    EnoughProjectives (GradedRightModuleCategory (R := R) (A := A)) := by
  sorry

end Formalization.Books.Dga.Unit14
