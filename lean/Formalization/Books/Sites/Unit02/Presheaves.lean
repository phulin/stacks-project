import Formalization.Books.Categories.Unit03.Opposite

/-!
# Sites and Sheaves, Chapter 2: Presheaves

This file formalizes the precise statements in `books/sites.tex`, lines
44--137.  The category-valued contravariant-functor interface, the category
of set-valued presheaves, representables, and the Yoneda equivalence are
re-exported from the earlier category-theory formalization.  The declarations
below add the source-facing language for sections, restriction maps, and
their functoriality.

The source's references to `Sets` and to big categories are represented at
Lean's universe levels.  The functor category already supplies the category
structure on presheaves, so no second category structure is introduced here.
-/

namespace Formalization.Books.Sites.Unit02

open CategoryTheory Opposite

universe v u v' u'

/-! ## Set-valued presheaves -/

/-- A set-valued presheaf, reusing the canonical earlier-chapter interface. -/
abbrev Presheaf (C : Type u) [Category.{v} C] :=
  Formalization.Books.Categories.Unit03.Presheaf C

/-- The sections of a presheaf over an object of its source category. -/
abbrev Sections {C : Type u} [Category.{v} C] (F : Presheaf C) (U : C) :=
  F.obj (op U)

/-- Pullback/restriction of a section along a morphism `V ⟶ U`. -/
def sectionRestriction {C : Type u} [Category.{v} C]
    (F : Presheaf C) {U V : C} (f : V ⟶ U) :
    Sections F U → Sections F V :=
  fun s => F.map f.op s

/- The source's notation `f*` and `s|_V` is represented by the explicit
   morphism argument.  This is necessary because a category can have more
   than one morphism with the same source and target. -/

/-- Restriction along an identity morphism is the identity on sections. -/
@[simp]
theorem sectionRestriction_id {C : Type u} [Category.{v} C]
    (F : Presheaf C) {U : C} (s : Sections F U) :
    sectionRestriction F (𝟙 U) s = s := by
  simp [sectionRestriction]

/-- Successive restrictions agree with restriction along a composite. -/
theorem sectionRestriction_comp {C : Type u} [Category.{v} C]
    (F : Presheaf C) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (s : Sections F U) :
    sectionRestriction F g (sectionRestriction F f s) =
      sectionRestriction F (g ≫ f) s := by
  simp [sectionRestriction]

/-! ## Morphisms and representables -/

/-- A morphism of set-valued presheaves is a natural transformation. -/
abbrev PresheafMorphism {C : Type u} [Category.{v} C]
    {F G : Presheaf C} := F ⟶ G

/-- The category of set-valued presheaves on `C`, denoted `PSh(C)` in the source. -/
abbrev PSh (C : Type u) [Category.{v} C] :=
  Formalization.Books.Categories.Unit03.PresheafCategory C

/-- Naturality of a presheaf morphism along a restriction morphism. -/
theorem presheafMorphism_naturality {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (η : PresheafMorphism (F := F) (G := G))
    {U V : C} (f : V ⟶ U) :
    F.map f.op ≫ η.app (op V) = η.app (op U) ≫ G.map f.op :=
  η.naturality f.op

/-- The representable presheaf `h_U`, reusing the Yoneda embedding. -/
abbrev representablePresheaf {C : Type u} [Category.{v} C] (U : C) :
    Presheaf C :=
  Formalization.Books.Categories.Unit03.representablePresheaf U

/-- The Yoneda bijection `Mor_PSh(h_U, F) ≃ F(U)`. -/
abbrev yonedaHomEquiv {C : Type u} [Category.{v} C]
    (U : C) (F : Presheaf C) :
    (representablePresheaf U ⟶ F) ≃ Sections F U :=
  Formalization.Books.Categories.Unit03.yonedaBijection U F

/-! ## Presheaves with values in a category -/

/-- A presheaf with values in `A` is a functor `Cᵒᵖ ⥤ A`. -/
abbrev PresheafWithValues (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] :=
  Formalization.Books.Categories.Unit03.ContravariantFunctor C A

/-- A morphism of `A`-valued presheaves is a natural transformation. -/
abbrev PresheafWithValuesMorphism {C : Type u} [Category.{v} C]
    {A : Type u'} [Category.{v'} A]
    {F G : PresheafWithValues C A} := F ⟶ G

/-- The category of `A`-valued presheaves, with its functor-category structure. -/
abbrev PresheafWithValuesCategory (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] :=
  PresheafWithValues C A

end Formalization.Books.Sites.Unit02
