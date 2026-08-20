import Formalization.Books.Categories.Unit03.Opposite
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Étale Cohomology, Chapter 9: Presheaves

This file formalizes the source section `Presheaves` in
`books/etale-cohomology.tex`.  Presheaves, representables, and the Yoneda
equivalence are reused from the canonical category-theory interfaces already
formalized in `Formalization.Books.Categories.Unit03.Opposite`; the local
aliases and formulas below keep this chapter's terminology and statements
available from its own namespace.

The source's final warning that representable presheaves need not be sheaves
for an arbitrary topology is recorded by the interface boundary here: the
notion of a site and its sheaf condition is introduced in the following source
section, so no forward chapter import is used to manufacture a second sheaf
definition in this file.
-/

namespace Formalization.Books.EtaleCohomology.Unit09

open CategoryTheory Opposite

universe u v

/-! ## Presheaves and their sections -/

/-- A presheaf of sets on `C`, namely a functor `Cᵒᵖ ⥤ Type`. -/
abbrev Presheaf (C : Type u) [Category.{v} C] :=
  Formalization.Books.Categories.Unit03.Presheaf C

/-- An abelian presheaf on `C`, namely a functor to abelian groups. -/
abbrev AbelianPresheaf (C : Type u) [Category.{v} C] :=
  Cᵒᵖ ⥤ AddCommGrpCat.{v}

/-- The sections of a presheaf over an object `U`. -/
abbrev Sections {C : Type u} [Category.{v} C] (F : Presheaf C) (U : C) :=
  F.obj (op U)

/-- The value of a presheaf at an object, in the source's `Γ(U, F)` notation. -/
abbrev Gamma {C : Type u} [Category.{v} C] (F : Presheaf C) (U : C) :=
  Sections F U

/-- Restriction of a section along a morphism `V ⟶ U`. -/
def sectionRestriction {C : Type u} [Category.{v} C]
    (F : Presheaf C) {U V : C} (f : V ⟶ U) :
    Sections F U → Sections F V :=
  fun s => F.map f.op s

/-- Restriction along an identity morphism is the identity. -/
@[simp]
theorem sectionRestriction_id {C : Type u} [Category.{v} C]
    (F : Presheaf C) {U : C} (s : Sections F U) :
    sectionRestriction F (𝟙 U) s = s := by
  simp [sectionRestriction]

/-- Successive restrictions agree with restriction along the composite. -/
theorem sectionRestriction_comp {C : Type u} [Category.{v} C]
    (F : Presheaf C) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (s : Sections F U) :
    sectionRestriction F g (sectionRestriction F f s) =
      sectionRestriction F (g ≫ f) s := by
  simp [sectionRestriction]

/-! ## The categories of presheaves -/

/-- A morphism of presheaves is a natural transformation. -/
abbrev PresheafMorphism {C : Type u} [Category.{v} C]
    {F G : Presheaf C} := F ⟶ G

/-- The category `PSh(C)` of set-valued presheaves. -/
abbrev PSh (C : Type u) [Category.{v} C] := Presheaf C

/-- The category `PAb(C)` of abelian presheaves. -/
abbrev PAb (C : Type u) [Category.{v} C] := AbelianPresheaf C

/-- Naturality of a morphism of presheaves along a restriction map. -/
theorem presheafMorphism_naturality {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (η : PresheafMorphism (F := F) (G := G))
    {U V : C} (f : V ⟶ U) :
    F.map f.op ≫ η.app (op V) = η.app (op U) ≫ G.map f.op :=
  η.naturality f.op

/-! ## Representable presheaves -/

/-- The representable presheaf `h_X`, reused from the Yoneda embedding. -/
abbrev representablePresheaf {C : Type u} [Category.{v} C] (X : C) :
    Presheaf C :=
  Formalization.Books.Categories.Unit03.representablePresheaf X

/-- Its value at `U` is the hom-set `Mor_C(U, X)`. -/
theorem representablePresheaf_obj {C : Type u} [Category.{v} C]
    (X U : C) :
    (representablePresheaf X).obj (op U) = (U ⟶ X) := rfl

/-- The restriction map of `h_X` is precomposition. -/
theorem representablePresheaf_map_apply {C : Type u} [Category.{v} C]
    {X U V : C} (f : V ⟶ U) (g : U ⟶ X) :
    (representablePresheaf X).map f.op g = f ≫ g := rfl

/-- The morphism of representables induced by `ψ : X ⟶ Y`. -/
def representableMap {C : Type u} [Category.{v} C] {X Y : C} (ψ : X ⟶ Y) :
    representablePresheaf X ⟶ representablePresheaf Y :=
  (Formalization.Books.Categories.Unit03.functorOfPoints (C := C)).map ψ

/-- On sections, `h_ψ` is the map `f ↦ f ≫ ψ`. -/
@[simp]
theorem representableMap_app_apply {C : Type u} [Category.{v} C]
    {X Y U : C} (ψ : X ⟶ Y) (f : U ⟶ X) :
    (representableMap ψ).app (op U) f = f ≫ ψ := rfl

/-- Yoneda's natural bijection in the source-facing direction. -/
def yonedaHomEquiv {C : Type u} [Category.{v} C] (X Y : C) :
    (X ⟶ Y) ≃ (representablePresheaf X ⟶ representablePresheaf Y) :=
  (Formalization.Books.Categories.Unit03.yonedaBijection X
      (representablePresheaf Y)).symm

/-- The Yoneda bijection sends `ψ` to the natural transformation `h_ψ`. -/
theorem yonedaHomEquiv_apply {C : Type u} [Category.{v} C] {X Y : C}
    (ψ : X ⟶ Y) :
    yonedaHomEquiv X Y ψ = representableMap ψ := by
  apply (Formalization.Books.Categories.Unit03.yonedaBijection X
    (representablePresheaf Y)).injective
  simp only [yonedaHomEquiv, Equiv.apply_symm_apply]
  simpa [representableMap,
    Formalization.Books.Categories.Unit03.functorOfPoints,
    Formalization.Books.Categories.Unit03.yonedaBijection] using
    (CategoryTheory.yonedaEquiv_yoneda_map ψ).symm

/-- The Yoneda bijection respects identities. -/
@[simp]
theorem yonedaHomEquiv_id {C : Type u} [Category.{v} C] (X : C) :
    yonedaHomEquiv X X (𝟙 X) = 𝟙 (representablePresheaf X) := by
  rw [yonedaHomEquiv_apply]
  exact (Formalization.Books.Categories.Unit03.functorOfPoints (C := C)).map_id X

/-- The Yoneda bijection respects composition. -/
theorem yonedaHomEquiv_comp {C : Type u} [Category.{v} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    yonedaHomEquiv X Z (f ≫ g) =
      yonedaHomEquiv X Y f ≫ yonedaHomEquiv Y Z g := by
  rw [yonedaHomEquiv_apply, yonedaHomEquiv_apply, yonedaHomEquiv_apply]
  exact (Formalization.Books.Categories.Unit03.functorOfPoints (C := C)).map_comp f g

end Formalization.Books.EtaleCohomology.Unit09
