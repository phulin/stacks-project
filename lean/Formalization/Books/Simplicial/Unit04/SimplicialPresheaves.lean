import Formalization.Books.Simplicial.Unit03.SimplicialObjects

/-!
# Simplicial Methods, Chapter 4: Simplicial objects as presheaves

The source's simplicial object in a category `C` is already Mathlib's
`SimplicialObject C`, whose underlying object is a functor
`SimplexCategoryᵒᵖ ⥤ C`.  Thus the source's presheaf viewpoint is represented
by the canonical functor-category definition; no parallel presheaf alias is
introduced here.

The source writes the hom-set identity using `PSh(Δ)`, but the Sites chapter
defines that notation for set-valued presheaves.  For a general target `C`,
the source-faithful interpretation is the category of `C`-valued presheaves,
whose morphisms are natural transformations.
-/

namespace Formalization.Books.Simplicial.Unit04

open CategoryTheory

universe v u

/-!
The two presentations of a simplicial object have the same type: Mathlib's
`SimplicialObject C` is the contravariant functor category over `Δ`.
-/

theorem simplicial_object_is_presheaf
    {C : Type u} [Category.{v} C] :
    SimplicialObject C = (SimplexCategoryᵒᵖ ⥤ C) := rfl

/-!
The homs in the functor category of `C`-valued presheaves are natural
transformations, which is the corrected form of the source's displayed
identity.
-/

theorem simplicial_object_hom_is_presheaf_morphism
    {C : Type u} [Category.{v} C]
    (U U' : SimplicialObject C) :
    (U ⟶ U') = NatTrans U U' := rfl

end Formalization.Books.Simplicial.Unit04
