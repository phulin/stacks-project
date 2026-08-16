import Formalization.«Books.SpacesGroupoids».Unit24.Core

/-!
# Algebraic Spaces and Groupoids, Chapter 24, Section 24

Explicit description of quotient stacks.
-/

namespace Formalization.«Books.SpacesGroupoids».Unit24

open CategoryTheory
open CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Every quotient-stack object is described by the descent data introduced
in this section, and morphisms are exactly morphisms of those data. -/
theorem quotient_stack_objects
    {J : GrothendieckTopology C} {S B : C}
    (Q : QuotientStackData J S B) :
    QuotientStackObjectsStatement Q := by
  sorry

end Formalization.«Books.SpacesGroupoids».Unit24
