import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Simplicial Methods, Chapter 12: Truncated simplicial objects and skeleton functors

Mathlib already contains the source's truncated simplex category and the
corresponding category of truncated simplicial objects.  We therefore use
`SimplexCategory.Truncated`, `SimplicialObject.Truncated`, and
`SimplicialObject.truncation` directly, and record the source-facing
descriptions of these canonical declarations below.

The source calls the truncation functor `sk_n`.  This is terminology specific
to the source: Mathlib's `SimplicialObject.sk` is instead the endofunctor built
from a left Kan extension, when the relevant Kan extensions exist.
-/

namespace Formalization.Books.Simplicial.Unit12

open CategoryTheory

universe v u

/-! ## The truncated simplex category -/

/--
The source's `Δ₍≤ n₎` is Mathlib's full subcategory on objects of length at
most `n`.
-/
theorem truncated_simplex_category_is_full_subcategory (n : ℕ) :
    SimplexCategory.Truncated n =
      ObjectProperty.FullSubcategory
        (fun a : SimplexCategory => a.len ≤ n) := rfl

/-- An object of the truncated simplex category has dimension at most `n`. -/
theorem truncated_simplex_category_object_property
    {n : ℕ} (X : SimplexCategory.Truncated n) :
    X.obj.len ≤ n :=
  X.property

/-- The standard object `⦋m⦌` belongs to `Δ₍≤ n₎` whenever `m ≤ n`. -/
theorem truncated_simplex_category_mk_obj
    (n m : ℕ) (h : m ≤ n) :
    (⟨SimplexCategory.mk m, h⟩ : SimplexCategory.Truncated n).obj =
      SimplexCategory.mk m := rfl

/-! ## Truncated simplicial objects -/

/-
`SimplicialObject.Truncated C n` is the category of contravariant functors
from `Δ₍≤ n₎` to `C`.  Its inherited functor-category structure supplies the
source's category `Simp_n(C)`, and its morphisms are natural transformations.
-/

/-- The source's definition of an `n`-truncated simplicial object. -/
theorem truncated_simplicial_object_is_functor_category
    {C : Type u} [Category.{v} C] (n : ℕ) :
    SimplicialObject.Truncated C n =
      Functor ((SimplexCategory.Truncated n)ᵒᵖ) C := rfl

/-- Morphisms of `n`-truncated simplicial objects are natural transformations. -/
theorem truncated_simplicial_object_hom_is_nat_trans
    {C : Type u} [Category.{v} C] {n : ℕ}
    (U V : SimplicialObject.Truncated C n) :
    (U ⟶ V) = NatTrans U V := rfl

/-! ## Truncation (the source's skeleton functor) -/

/--
The object part of the source's `sk_n` is restriction along the inclusion
`Δ₍≤ n₎ᵒᵖ ⥤ Δᵒᵖ`.
-/
theorem truncation_obj_eq_restriction
    {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject C) :
    (SimplicialObject.truncation (C := C) n).obj U =
      (SimplexCategory.Truncated.inclusion n).op ⋙ U := rfl

/-- Restriction sends a natural transformation to its componentwise restriction. -/
theorem truncation_map_app
    {C : Type u} [Category.{v} C] {n : ℕ}
    {U V : SimplicialObject C} (f : U ⟶ V)
    (X : (SimplexCategory.Truncated n)ᵒᵖ) :
    ((SimplicialObject.truncation (C := C) n).map f).app X =
      f.app ((SimplexCategory.Truncated.inclusion n).op.obj X) := rfl

end Formalization.Books.Simplicial.Unit12
