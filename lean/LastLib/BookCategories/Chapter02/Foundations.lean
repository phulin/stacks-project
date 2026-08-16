/-!
# Categories, Chapter 2: categories, isomorphisms, groupoids, and subcategories

The source section's basic category definition is already Mathlib's
`CategoryStruct` data together with the `Category` axioms.  This file keeps
that canonical API and records the source-facing propositions which are not
otherwise named in the imported interface.

The source's discussion of large categories is a universe convention rather
than a second category structure.  Lean expresses it with `SmallCategory`,
`LargeCategory`, and the universe parameters of `Category`; the list of
examples in the remark therefore needs no parallel collection of categories.
Likewise, the remarks about set-valued functors are scope guidance and are
accounted for by the existing category of types and functor API.
-/
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.SingleObj

namespace LastLib.BookCategories.Chapter02

open CategoryTheory

universe v u

/- The data in the source definition are precisely Mathlib's category data. -/
abbrev CategoryData (C : Type u) := CategoryStruct.{v} C

/- The identity predicate is useful when reading the source's uniqueness
   remark literally; the canonical `Category` class supplies `𝟙` itself. -/
def IsIdentityMorphism {C : Type u} [Category.{v} C] (X : C) (e : X ⟶ X) : Prop :=
  (∀ {Y : C} (f : X ⟶ Y), e ≫ f = f) ∧
    ∀ {Y : C} (f : Y ⟶ X), f ≫ e = f

theorem identity_morphism_unique {C : Type u} [Category.{v} C] {X : C}
    {e e' : X ⟶ X} (he : IsIdentityMorphism X e) (he' : IsIdentityMorphism X e') :
    e = e' := by
  sorry

/- `Iso` and `IsIso` are the bundled and unbundled forms of the source's
   invertible-morphism definition. -/
abbrev Isomorphism {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) : Prop :=
  IsIso f

theorem inverse_morphism_unique {C : Type u} [Category.{v} C] {X Y : C}
    {f : X ⟶ Y} {g h : Y ⟶ X}
    (hg₁ : f ≫ g = 𝟙 X) (hg₂ : g ≫ f = 𝟙 Y)
    (hh₁ : f ≫ h = 𝟙 X) (hh₂ : h ≫ f = 𝟙 Y) :
    g = h := by
  sorry

/- `Aut X` is Mathlib's automorphism group of `X`; its existing `Group`
   instance formalizes the source's automorphism-group assertion. -/
abbrev AutomorphismGroup {C : Type u} [Category.{v} C] (X : C) := Aut X

/- A category in which every morphism is invertible is represented by the
   existing proposition-valued `IsGroupoid` class. -/
abbrev GroupoidCategory (C : Type u) [Category.{v} C] : Prop := IsGroupoid C

theorem groupoid_iff_all_morphisms_invertible {C : Type u} [Category.{v} C] :
    GroupoidCategory C ↔ ∀ {X Y : C} (f : X ⟶ Y), IsIso f := by
  sorry

/- The two examples in the source use Mathlib's canonical constructions. -/
def oneObjectCategoryOfGroup (G : Type u) [Group G] : Type u :=
  SingleObj G

theorem oneObjectCategoryOfGroup_is_groupoid (G : Type u) [Group G] :
    IsGroupoid (oneObjectCategoryOfGroup G) := by
  infer_instance

def discreteCategoryOn (C : Type u) : Type u :=
  Discrete C

theorem discreteCategoryOn_is_groupoid (C : Type u) :
    IsGroupoid (discreteCategoryOn C) := by
  infer_instance

/- A full subcategory is Mathlib's `ObjectProperty.FullSubcategory`.  For
   such a subcategory, the source's "strictly full" condition is exactly the
   canonical `IsClosedUnderIsomorphisms` typeclass on its object property. -/
abbrev BookFullSubcategory (C : Type u) [Category.{v} C]
    (P : ObjectProperty C) := P.FullSubcategory

abbrev StrictlyFullObjectProperty {C : Type u} [Category.{v} C]
    (P : ObjectProperty C) : Prop :=
  ObjectProperty.IsClosedUnderIsomorphisms P

theorem full_subcategory_inclusion_is_full_and_faithful
    {C : Type u} [Category.{v} C] (P : ObjectProperty C) :
    P.ι.Full ∧ P.ι.Faithful := by
  exact ⟨inferInstance, inferInstance⟩

end LastLib.BookCategories.Chapter02
