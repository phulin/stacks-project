import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Categories, Chapter 26: Categorically compact objects

The source calls an object categorically compact when its hom functor preserves
filtered colimits.  Mathlib's `IsFinitelyPresentable` is the canonical API for
this condition (and is explicitly documented there as the compact-object
notion), so the source terminology is exposed below as an alias rather than a
parallel definition.
-/

namespace Formalization.Books.Categories.Unit26

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v'

noncomputable section

/-! ## Categorically compact objects -/

/-- The source's terminology for Mathlib's finitely presentable objects. -/
abbrev IsCategoricallyCompact {C : Type u} [Category.{v} C] (X : C) : Prop :=
  IsFinitelyPresentable.{v} X

/--
An extension of a functor on a small full subcategory which commutes with
filtered colimits.  The restriction is recorded up to natural isomorphism,
which is the categorical meaning of extension in the source lemma.
-/
structure FilteredColimitExtension
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (P : ObjectProperty C) (F' : P.FullSubcategory ⥤ D) where
  /-- The extended functor on the ambient category. -/
  functor : C ⥤ D
  /-- The extended functor commutes with filtered colimits. -/
  preservesFilteredColimits : PreservesFilteredColimits functor
  /-- Its restriction to the full subcategory agrees with `F'`. -/
  restrictionIso : P.ι ⋙ functor ≅ F'

/--
Every functor from a small full subcategory of categorically compact objects
which generates `C` under filtered colimits extends to a functor on `C` that
commutes with filtered colimits.  Such an extension is unique up to the
unique natural isomorphism compatible with the chosen restriction isomorphisms.

`ObjectProperty.ind` is Mathlib's canonical presentation of an object as a
filtered colimit of objects satisfying an object property.
-/
theorem exists_filteredColimitExtension_unique_up_to_iso
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    [HasFilteredColimits C] [HasFilteredColimits D]
    (P : ObjectProperty C) [ObjectProperty.Small.{v} P]
    (hcompact : ∀ X : C, P X → IsCategoricallyCompact X)
    (hgenerated : ∀ X : C, ObjectProperty.ind.{v} P X)
    (F' : P.FullSubcategory ⥤ D) :
    ∃ E : FilteredColimitExtension P F',
      ∀ E' : FilteredColimitExtension P F',
        ∃! e : E.functor ≅ E'.functor,
          Functor.isoWhiskerLeft P.ι e ≪≫ E'.restrictionIso = E.restrictionIso := by
  sorry

end

end Formalization.Books.Categories.Unit26
