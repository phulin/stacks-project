import Formalization.Books.Categories.Unit29.TwoCategories

/-!
# Categories, Chapter 30: (2, 1)-categories

The source's strict `(2, 1)`-categories are the strict bicategories whose
hom-categories are groupoids.  Mathlib calls the latter condition
`Bicategory.IsLocallyGroupoid`; `Bicategory.Pith` is its canonical
construction that retains only invertible 2-morphisms.
-/

namespace Formalization.Books.Categories.Unit30

open CategoryTheory
open CategoryTheory.Bicategory

universe w v u w' v' u'

/-! ## The definition and the associated construction -/

/-- The source-facing name for Mathlib's locally groupoidal bicategory.

For a strict bicategory, this is precisely the condition that all
2-morphisms are isomorphisms.  The strictness part of the source's
"strict `(2, 1)`-category" is recorded by `IsStrictTwoOneCategory` below. -/
abbrev IsTwoOneCategory (C : Type u) [Bicategory.{w, v} C] : Prop :=
  Bicategory.IsLocallyGroupoid C

/-- A strict `(2, 1)`-category: a strict 2-category which is locally groupoidal. -/
abbrev IsStrictTwoOneCategory (C : Type u) [Bicategory.{w, v} C] : Prop :=
  Formalization.Books.Categories.Unit29.IsStrictTwoCategory C ∧ IsTwoOneCategory C

/-- The canonical `(2, 1)`-category associated to a bicategory.

This is Mathlib's `Bicategory.Pith`: it has the same underlying objects and
1-morphisms up to the canonical wrappers, and its 2-morphisms are the
invertible 2-morphisms of the original bicategory. -/
abbrev AssociatedTwoOneCategory (C : Type u) [Bicategory.{w, v} C] :=
  Bicategory.Pith C

/-- The canonical inclusion of the associated `(2, 1)`-category. -/
abbrev associatedTwoOneCategoryInclusion (C : Type u) [Bicategory.{w, v} C] :
    Pseudofunctor (AssociatedTwoOneCategory C) C :=
  Bicategory.Pith.inclusion C

theorem associatedTwoOneCategory_is_two_one_category
    (C : Type u) [Bicategory.{w, v} C] :
    IsTwoOneCategory (AssociatedTwoOneCategory C) := by
  infer_instance

theorem associatedTwoOneCategory_inclusion_obj
    (C : Type u) [Bicategory.{w, v} C]
    (x : AssociatedTwoOneCategory C) :
    (associatedTwoOneCategoryInclusion C).obj x = x.as := rfl

theorem associatedTwoOneCategory_inclusion_map
    (C : Type u) [Bicategory.{w, v} C]
    {x y : AssociatedTwoOneCategory C} (f : x ⟶ y) :
    (associatedTwoOneCategoryInclusion C).map f = f.of := rfl

theorem associatedTwoOneCategory_two_morphism_is_iso
    (C : Type u) [Bicategory.{w, v} C]
    {x y : AssociatedTwoOneCategory C} {f g : x ⟶ y}
    (η : f ⟶ g) : IsIso η := by
  infer_instance

/- The source works throughout with strict 2-categories.  Mathlib supplies
   the locally groupoidal part of `Pith` as an instance; the strictness
   transfer is the only additional interface needed to state the source's
   strict associated construction. -/
theorem associatedTwoOneCategory_is_strict
    (C : Type u) [Bicategory.{w, v} C] [Bicategory.Strict C] :
    Bicategory.Strict (AssociatedTwoOneCategory C) := by
  sorry

theorem associatedTwoOneCategory_is_strict_two_one_category
    (C : Type u) [Bicategory.{w, v} C] [Bicategory.Strict C] :
    IsStrictTwoOneCategory (AssociatedTwoOneCategory C) := by
  exact ⟨associatedTwoOneCategory_is_strict C,
    associatedTwoOneCategory_is_two_one_category C⟩

/-! ## The category and groupoid examples -/

/-- `Cat` with only invertible natural transformations as 2-morphisms. -/
theorem categories_form_a_two_one_category :
    IsTwoOneCategory
      (AssociatedTwoOneCategory (CategoryTheory.Cat.{v, u})) := by
  exact associatedTwoOneCategory_is_two_one_category _

theorem categories_form_a_strict_two_one_category :
    IsStrictTwoOneCategory
      (AssociatedTwoOneCategory (CategoryTheory.Cat.{v, u})) := by
  exact associatedTwoOneCategory_is_strict_two_one_category _

/-- A natural transformation between functors into a groupoid is invertible.

This records the source's warning that transformations between functors
between groupoids are automatically isomorphisms; the source groupoid
hypothesis on the domain is retained even though only the codomain is needed
for this particular conclusion. -/
theorem natural_transformation_between_groupoids_is_iso
    {A : Type u} [Category.{v} A] [IsGroupoid A]
    {B : Type u'} [Category.{v'} B] [IsGroupoid B]
    {F G : A ⥤ B} (η : F ⟶ G) : IsIso η := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  infer_instance

/-- The 2-category of groupoids, with functors and natural transformations. -/
theorem groupoids_form_a_strict_two_one_category :
    IsStrictTwoOneCategory
      (Formalization.Books.Categories.Unit29.FullSubTwoCategory
        (CategoryTheory.Cat.{v, u})
        Formalization.Books.Categories.Unit29.groupoidObjectProperty) := by
  exact ⟨
    Formalization.Books.Categories.Unit29.groupoids_form_a_strict_two_category,
    Formalization.Books.Categories.Unit29.groupoids_form_a_two_one_category⟩

/- The source also lists the analogous `(2, 1)`-categories of categories
   fibred in groupoids over a fixed category and of stacks.  Their carriers
   and 2-categorical structures are introduced in later chapters, so this
   section records the precise generic construction above and the groupoid
   instance here without introducing a premature parallel bicategory API. -/

end Formalization.Books.Categories.Unit30
