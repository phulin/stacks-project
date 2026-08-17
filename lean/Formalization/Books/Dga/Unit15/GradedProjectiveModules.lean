import Formalization.Books.Dga.Unit14.GradedProjectiveModules
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Differential Graded Algebra, Chapter 15: Projective modules over graded algebras

This file records the source section's graded right-module interfaces.  The
componentwise graded-module category and its shift/projective API are reused
from the earlier Unit14 formalization; the declarations below expose the
chapter's statements under the chapter-local namespace.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Formalization.Books.Dga.Unit15

open Formalization.Books.Dga.Unit14

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-! ## The category and shifts -/

/- The earlier chapter's structure is the canonical representation of the
source's category of graded right modules. -/
abbrev GradedModule :=
  Formalization.Books.Dga.Unit14.GradedRightModule.{u, v, w} (R := R) (A := A)

abbrev GradedModuleHom :=
  Formalization.Books.Dga.Unit14.GradedRightModuleHom.{u, v, w} (R := R) (A := A)

abbrev GradedModuleCategory :=
  Formalization.Books.Dga.Unit14.GradedRightModuleCategory.{u, v, w} (R := R) (A := A)

abbrev GradedProjective (M : GradedModule (R := R) (A := A)) : Prop :=
  Formalization.Books.Dga.Unit14.GradedProjective M

/- The source's `A[k]` is the shifted regular graded module. -/
abbrev shiftedRegularModule (k : ℤ) : GradedModule (R := R) (A := A) :=
  Formalization.Books.Dga.Unit14.gradedAlgebraShift (R := R) (A := A) k

theorem shiftedRegularModule_component (k n : ℤ) :
    (shiftedRegularModule (R := R) (A := A) k).component n = A (n + k) :=
  Formalization.Books.Dga.Unit14.gradedShift_component
    (Formalization.Books.Dga.Unit14.gradedRegularModule (R := R) (A := A)) k n

/-! ## The exact component functor -/

/- The source uses exactness of `M ↦ M^(-k)` to prove projectivity of `A[k]`.
The functor is made explicit here; its exactness theorem remains a statement
interface for the later proof stage. -/
def gradedComponentFunctor (k : ℤ) :
    GradedModuleCategory (R := R) (A := A) ⥤ ModuleCat.{w} R where
  obj M := ModuleCat.of R (M.component (-k))
  map f := ModuleCat.ofHom (f.app (-k))
  map_id := by
    intro M
    apply ModuleCat.hom_ext
    rfl
  map_comp := by
    intro M N P f g
    apply ModuleCat.hom_ext
    rfl

def gradedComponentFunctorIsExact (k : ℤ) : Prop :=
  exactFunctor (GradedModuleCategory (R := R) (A := A)) (ModuleCat.{w} R)
    (gradedComponentFunctor (R := R) (A := A) k)

theorem gradedComponentFunctor_isExact (k : ℤ) :
    gradedComponentFunctorIsExact (R := R) (A := A) k := by
  sorry

/-! ## Hom evaluation and projectivity -/

/- The displayed Hom equality is represented by the canonical evaluation
equivalence, which is stronger and retains the usable map data. -/
theorem hom_from_shift_equiv (k : ℤ) (M : GradedModule (R := R) (A := A)) :
    Nonempty
      (GradedModuleHom (R := R) (A := A) (shiftedRegularModule (R := R) (A := A) k) M
        ≃ M.component (-k)) := by
  exact Formalization.Books.Dga.Unit14.graded_shift_hom_evaluation_equiv k M

theorem shifted_regular_projective (k : ℤ) :
    GradedProjective (R := R) (A := A)
      (shiftedRegularModule (R := R) (A := A) k) := by
  exact Formalization.Books.Dga.Unit14.graded_algebra_shift_projective k

/-! ## Shifted-free presentations and direct summands -/

abbrev GradedMapSurjective {M N : GradedModule (R := R) (A := A)}
    (f : GradedModuleHom (R := R) (A := A) M N) : Prop :=
  Formalization.Books.Dga.Unit14.GradedRightModuleHom.DegreewiseSurjective f

theorem every_graded_module_is_quotient_of_shifted_free
    (M : GradedModule (R := R) (A := A)) :
    ∃ (I : Type w) (degree : I → ℤ)
      (h : HasCoproduct
        (fun i => shiftedRegularModule (R := R) (A := A) (degree i)))
      (f : Formalization.Books.Dga.Unit14.gradedDirectSumOfShifts
        (R := R) (A := A) I degree h ⟶ M),
      GradedMapSurjective (R := R) (A := A) f := by
  simpa using
    (Formalization.Books.Dga.Unit14.every_graded_module_quotient_of_shifted_free
      (R := R) (A := A) M)

theorem graded_projective_is_direct_summand_of_shifted_free
    (P : GradedModule (R := R) (A := A))
    (hP : GradedProjective (R := R) (A := A) P) :
    ∃ (I : Type w) (degree : I → ℤ)
      (h : HasCoproduct
        (fun i => shiftedRegularModule (R := R) (A := A) (degree i)))
      (i : P ⟶ Formalization.Books.Dga.Unit14.gradedDirectSumOfShifts
        (R := R) (A := A) I degree h)
      (s : Formalization.Books.Dga.Unit14.gradedDirectSumOfShifts
        (R := R) (A := A) I degree h ⟶ P),
      i ≫ s = 𝟙 P := by
  simpa using
    (Formalization.Books.Dga.Unit14.graded_projective_is_direct_summand_of_shifted_free
      (R := R) (A := A) P hP)

/-! ## The source's concluding assertions -/

theorem graded_module_category_has_enough_projectives :
    EnoughProjectives (GradedModuleCategory (R := R) (A := A)) := by
  exact Formalization.Books.Dga.Unit14.graded_right_module_category_has_enough_projectives

end Formalization.Books.Dga.Unit15
