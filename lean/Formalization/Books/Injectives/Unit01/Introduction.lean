import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Injectives, Chapter 1: Introduction

The introductory source section contains one precise observation: abelian
groups and modules over a ring have enough injectives.  The two declarations
below expose the canonical Mathlib instances and theorem for that observation.
The surrounding discussion of future applications is motivation rather than a
mathematical assertion.
-/

namespace Formalization.Books.Injectives.Unit01

open CategoryTheory

universe u

/-- The category of abelian groups has enough injectives. -/
theorem abelian_groups_have_enough_injectives :
    EnoughInjectives (AddCommGrpCat.{u}) := by
  infer_instance

/-- The category of modules over a ring has enough injectives. -/
theorem modules_have_enough_injectives {R : Type u} [Ring R] :
    EnoughInjectives (ModuleCat.{u} R) := by
  exact ModuleCat.enoughInjectives R

end Formalization.Books.Injectives.Unit01
