import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Categories, Chapter 1: Introduction

The source introduction says that categories and stacks form 2-categories.
Mathlib models a 2-category by `CategoryTheory.Bicategory`; its canonical
`Cat` construction already has the stronger strict-bicategory structure.

The phrase “the category of stacks” is made precise here for a fixed site and
fixed universes: stacks are the stack-valued pseudofunctors on that site, and
their 1- and 2-morphisms are inherited from the ambient pseudofunctor
bicategory by `InducedBicategory`.
-/

universe w v u

namespace Formalization.Books.Categories.Unit01

open CategoryTheory
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

/- The universe-indexed `Cat` is the usable Lean replacement for the source's
   proper-class category of all categories. -/
theorem categories_form_a_two_category :
    CategoryTheory.Bicategory.Strict (CategoryTheory.Cat.{v, u}) := by
  infer_instance

/-! ## Stacks on a fixed site -/

/-- The universe-bounded type of stacks on a fixed site. -/
def Stacks (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) :=
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w} // F.IsStack J}

/-- The full sub-bicategory of stack-valued pseudofunctors on a fixed site. -/
abbrev StackBicategory (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) :=
  CategoryTheory.Bicategory.InducedBicategory
    (Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    (fun F : Stacks C J => F.1)

/-- Stacks on a fixed site form a bicategory, with pseudonatural
transformations as 1-morphisms and modifications as 2-morphisms. -/
instance stacks_form_a_two_category (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) :
    CategoryTheory.Bicategory (StackBicategory C J) :=
  inferInstance

end Formalization.Books.Categories.Unit01
