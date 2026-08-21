import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Formalization.Books.Categories.Unit38
import Formalization.Books.Stacks.Unit06.Setoids

/-!
# Examples of Stacks, Chapter 10: The stack associated to a sheaf

This chapter records the set-valued presheaf construction from the source.
The underlying category and its projection reuse the canonical
CoGrothendieck construction formalized in `Categories.Unit38`.
-/

namespace Formalization.Books.ExamplesStacks.Unit10

open CategoryTheory
open AlgebraicGeometry
open Opposite

open Formalization.Books.Categories.Unit36
open Formalization.Books.Categories.Unit38
open Formalization.Books.Stacks.Unit01

universe w u

/-! ## The fppf site over a scheme -/

/-- The category of schemes over the fixed base scheme `S`. -/
abbrev SchemeOver (S : Scheme.{u}) := CategoryTheory.Over S

/-- The fppf topology on the big site of schemes over `S`. -/
abbrev FppfTopology (S : Scheme.{u}) : GrothendieckTopology (SchemeOver S) :=
  Scheme.fppfTopology.over S

/-- A set-valued presheaf on the fppf site over `S`. -/
abbrev FppfPresheaf (S : Scheme.{u}) := (SchemeOver S)ᵒᵖ ⥤ Type w

/-! ## The associated category fibred in sets -/

/- The following abbreviations are source-facing names for the canonical
   set-valued CoGrothendieck construction. -/

/-- The category `\mathcal S_F` associated to a set-valued presheaf `F`. -/
abbrev associatedCategory {S : Scheme.{u}} (F : FppfPresheaf S) :=
  setPresheafCategory F

/-- The projection `p_F : \mathcal S_F → (Sch/S)`. -/
abbrev associatedProjection {S : Scheme.{u}} (F : FppfPresheaf S) :
    associatedCategory F ⥤ SchemeOver S :=
  setPresheafProjection F

/-- The pseudofunctor presentation of `p_F` used by the stack predicates. -/
abbrev associatedFiberedCategory {S : Scheme.{u}} (F : FppfPresheaf S) :
    FiberedCategory (SchemeOver S) :=
  splitFibredPseudofunctor (setPresheafToCat F)

/-- The associated projection is a category fibred in sets. -/
theorem associated_projection_is_fibred_in_sets
    {S : Scheme.{u}} (F : FppfPresheaf S) :
    IsCategoryFibredInSets (associatedProjection F) := by
  exact setPresheaf_category_isFibredInSets F

/-! ## The stack criterion -/

/-- `F` is a sheaf for the fppf topology on schemes over `S`. -/
def IsFppfSheaf {S : Scheme.{u}} (F : FppfPresheaf S) : Prop :=
  Presheaf.IsSheaf (FppfTopology S) F

/-- The associated category is a stack in sets exactly when `F` is a sheaf. -/
theorem associated_is_stack_in_sets_iff_is_fppf_sheaf
    {S : Scheme.{u}} (F : FppfPresheaf S) :
    StackInSets (associatedFiberedCategory F) (FppfTopology S) ↔
      IsFppfSheaf F := by
  sorry

end Formalization.Books.ExamplesStacks.Unit10
