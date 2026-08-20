import Formalization.Books.Categories.Unit03.Opposite
import Formalization.Books.Sites.Unit02.Presheaves
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Étale Cohomology, Chapter 9: Presheaves

This file formalizes the source section `Presheaves` in
`books/etale-cohomology.tex`.  Presheaves, representables, and the Yoneda
equivalence are reused from the canonical category-theory interfaces already
formalized in earlier chapters; the local aliases and formulas below keep
this chapter's terminology and statements available from its own namespace.

The source's smallness convention for `PSh(C)` and `PAb(C)` is represented by
Lean's universe-bounded functor categories.  The source's warning that a
representable presheaf need not be a sheaf for an arbitrary topology is
recorded at the interface boundary below, since the sheaf condition is
introduced in the following source section.

-/

namespace Formalization.Books.EtaleCohomology.Unit09

open CategoryTheory Opposite

universe u v w

/-! ## Presheaves and their sections -/

/-- A presheaf of sets on `C`, reusing the established site-level interface. -/
abbrev Presheaf (C : Type u) [Category.{v} C] :=
  Formalization.Books.Sites.Unit02.Presheaf C

/-- An abelian presheaf on `C`, namely a functor to abelian groups. -/
abbrev AbelianPresheaf (C : Type u) [Category.{v} C] :=
  Formalization.Books.Sites.Unit02.PresheafWithValues C AddCommGrpCat.{w}

/-- The sections of a presheaf over an object `U`. -/
abbrev Sections {C : Type u} [Category.{v} C] (F : Presheaf C) (U : C) :=
  Formalization.Books.Sites.Unit02.Sections F U

/-- The value of a presheaf at an object, in the source's `Γ(U, F)` notation. -/
abbrev Gamma {C : Type u} [Category.{v} C] (F : Presheaf C) (U : C) :=
  Sections F U

/-- Restriction of a section along a morphism `V ⟶ U`. -/
def sectionRestriction {C : Type u} [Category.{v} C]
    (F : Presheaf C) {U V : C} (f : V ⟶ U) :
    Sections F U → Sections F V :=
  Formalization.Books.Sites.Unit02.sectionRestriction F f

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
  exact Formalization.Books.Sites.Unit02.sectionRestriction_comp F f g s

/-! The same terminology for abelian-group-valued presheaves. -/

/-- The underlying type of sections of an abelian presheaf. -/
abbrev AbelianSections {C : Type u} [Category.{v} C]
    (F : AbelianPresheaf C) (U : C) :=
  (F.obj (op U) : Type w)

/-- The value of an abelian presheaf at `U`, in `Γ(U, F)` notation. -/
abbrev AbelianGamma {C : Type u} [Category.{v} C]
    (F : AbelianPresheaf C) (U : C) :=
  AbelianSections F U

/-- Restriction of an abelian section along a morphism `V ⟶ U`. -/
def abelianSectionRestriction {C : Type u} [Category.{v} C]
    (F : AbelianPresheaf C) {U V : C} (f : V ⟶ U) :
    AbelianSections F U → AbelianSections F V :=
  fun s => F.map f.op s

@[simp]
theorem abelianSectionRestriction_id {C : Type u} [Category.{v} C]
    (F : AbelianPresheaf C) {U : C} (s : AbelianSections F U) :
    abelianSectionRestriction F (𝟙 U) s = s := by
  simp [abelianSectionRestriction]

theorem abelianSectionRestriction_comp {C : Type u} [Category.{v} C]
    (F : AbelianPresheaf C) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (s : AbelianSections F U) :
    abelianSectionRestriction F g (abelianSectionRestriction F f s) =
      abelianSectionRestriction F (g ≫ f) s := by
  simp [abelianSectionRestriction]

/-! ## The categories of presheaves -/

/-- A morphism of presheaves is a natural transformation. -/
abbrev PresheafMorphism {C : Type u} [Category.{v} C]
    {F G : Presheaf C} :=
  Formalization.Books.Sites.Unit02.PresheafMorphism (F := F) (G := G)

/-- The category `PSh(C)` of set-valued presheaves. -/
abbrev PSh (C : Type u) [Category.{v} C] :=
  Formalization.Books.Sites.Unit02.PSh C

/-- The category `PAb(C)` of abelian presheaves. -/
abbrev PAb (C : Type u) [Category.{v} C] := AbelianPresheaf C

/-- Naturality of a morphism of presheaves along a restriction map. -/
theorem presheafMorphism_naturality {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (η : PresheafMorphism (F := F) (G := G))
    {U V : C} (f : V ⟶ U) :
    F.map f.op ≫ η.app (op V) = η.app (op U) ≫ G.map f.op :=
  η.naturality f.op

/-- A morphism of abelian presheaves is a natural transformation. -/
abbrev AbelianPresheafMorphism {C : Type u} [Category.{v} C]
    {F G : AbelianPresheaf C} := F ⟶ G

/-- Naturality of an abelian-presheaf morphism along restriction. -/
theorem abelianPresheafMorphism_naturality {C : Type u} [Category.{v} C]
    {F G : AbelianPresheaf C} (η : AbelianPresheafMorphism (F := F) (G := G))
    {U V : C} (f : V ⟶ U) :
    F.map f.op ≫ η.app (op V) = η.app (op U) ≫ G.map f.op :=
  η.naturality f.op

/-! ## Representable presheaves -/

/-- The representable presheaf `h_X`, reused from the Yoneda embedding. -/
abbrev representablePresheaf {C : Type u} [Category.{v} C] (X : C) :
    Presheaf C :=
  Formalization.Books.Sites.Unit02.representablePresheaf X

/-- Its value at `U` is the hom-set `Mor_C(U, X)`. -/
theorem representablePresheaf_obj {C : Type u} [Category.{v} C]
    (X U : C) :
    (representablePresheaf X).obj (op U) = (U ⟶ X) := rfl

/-- The restriction map of `h_X` is precomposition. -/
theorem representablePresheaf_map_apply {C : Type u} [Category.{v} C]
    {X U V : C} (f : V ⟶ U) (g : U ⟶ X) :
    (representablePresheaf X).map f.op g = f ≫ g := rfl

/- The source notes that representables are not sheaves for every topology.
   Mathlib already provides the topology and sheaf-condition interfaces, so
   the warning can be recorded without importing the later Étale Cohomology
   sheaf section. -/

private instance unitBoolCategory : Category.{v} (ULift.{u} Unit) where
  Hom _ _ := ULift.{v} Bool
  id _ := ULift.up true
  comp f g := ULift.up (f.down && g.down)
  comp_id := by
    intro X Y f
    cases f
    all_goals simp
  id_comp := by
    intro X Y f
    cases f
    all_goals simp
  assoc := by
    intro W X Y Z f g k
    cases f
    all_goals
      cases g
      all_goals
        cases k
        all_goals simp [Bool.and_assoc]

/-- Not every representable presheaf is a sheaf for every Grothendieck topology. -/
theorem representablePresheaf_not_sheaf_in_every_topology :
    ¬ (∀ (C : Type u) [Category.{v} C]
      (J : GrothendieckTopology C) (X : C),
      CategoryTheory.Presheaf.IsSheaf J (representablePresheaf X)) := by
  intro h
  let C : Type u := ULift.{u} Unit
  let X : C := ULift.up ()
  have hsheaf :
      CategoryTheory.Presheaf.IsSheaf
        (CategoryTheory.GrothendieckTopology.discrete C)
        (representablePresheaf X) :=
    h C (CategoryTheory.GrothendieckTopology.discrete C) X
  have hcover : (⊥ : Sieve X) ∈
      (CategoryTheory.GrothendieckTopology.discrete C) X := by
    change True
    trivial
  have hbot :
      CategoryTheory.Presieve.IsSheafFor (representablePresheaf X)
        (⊥ : CategoryTheory.Presieve X) := by
    simpa using hsheaf.isSheafFor (⊥ : Sieve X) hcover
  let x :
      CategoryTheory.Presieve.FamilyOfElements (representablePresheaf X)
        (⊥ : CategoryTheory.Presieve X) :=
    fun _ _ hf => False.elim hf
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomp
    exact False.elim h₁
  obtain ⟨t, ht, huniq⟩ := hbot x hx
  let tFalse : (representablePresheaf X).obj (op X) :=
    (show X ⟶ X from ULift.up false)
  let tTrue : (representablePresheaf X).obj (op X) :=
    (show X ⟶ X from ULift.up true)
  have htFalse : x.IsAmalgamation tFalse := by
    intro Y f hf
    exact False.elim hf
  have htTrue : x.IsAmalgamation tTrue := by
    intro Y f hf
    exact False.elim hf
  have heq : tFalse = tTrue :=
    (huniq tFalse htFalse).trans (huniq tTrue htTrue).symm
  change (ULift.up false : ULift.{v} Bool) = ULift.up true at heq
  have hbool : false = true := congrArg ULift.down heq
  cases hbool

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
