import Formalization.Books.Sheaves.Unit05.PresheavesOfAlgebraicStructures
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Sheaves on Spaces, Chapter 6: Presheaves of modules

The source section is formalized with Mathlib's canonical
`PresheafOfModules` construction.  Its objects carry a module over the ring
assigned to every open and semilinear restriction maps; its morphisms are the
componentwise linear maps satisfying the naturality condition.  Thus the
canonical structure subsumes the source's equivalent presentation by an
abelian presheaf with an action of the presheaf of rings.

For a morphism of presheaves of rings, Mathlib's presheaf change-of-rings
API supplies restriction of scalars and the canonical left-adjoint
`pullback`.  The latter provides the categorical change-of-rings interface
for the pointwise tensor-product construction in the source.
-/

namespace Formalization.Books.Sheaves.Unit06

open CategoryTheory Opposite TopologicalSpace
open scoped ChangeOfRings

universe w v

/-! ## Presheaves of rings and modules -/

/-- A presheaf of rings on `X`, represented by Mathlib's canonical functor. -/
abbrev RingPresheaf (X : TopCat.{v}) := TopCat.Presheaf (RingCat.{w}) X

/-- A morphism of presheaves of rings. -/
abbrev RingPresheafMorphism {X : TopCat.{v}} {O₁ O₂ : RingPresheaf.{w, v} X} :=
  O₁ ⟶ O₂

/-- A presheaf of modules over a presheaf of rings. -/
abbrev PresheafOfOModules {X : TopCat.{v}} (O : RingPresheaf.{w, v} X) :=
  _root_.PresheafOfModules.{w} O

/-- The category `PMod(O)` of presheaves of `O`-modules. -/
abbrev PMod {X : TopCat.{v}} (O : RingPresheaf.{w, v} X) :=
  PresheafOfOModules O

/-- A morphism of presheaves of `O`-modules. -/
abbrev PresheafOfOModulesMorphism {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O} := F ⟶ G

/-- The source's `Hom_O(F, G)`, represented by the canonical hom type. -/
abbrev OModuleHom {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F G : PMod O) := F ⟶ G

/-- The abelian-group-valued presheaf underlying a presheaf of modules. -/
noncomputable abbrev underlyingAbelianPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} (F : PMod O) := F.presheaf

/-- The module of sections over an open set. -/
abbrev moduleOn {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F : PMod O) (U : Opens X) := F.obj (op U)

/-- The restriction morphism of a presheaf of modules along an open inclusion. -/
abbrev moduleRestriction {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F : PMod O) {U V : Opens X} (h : V ≤ U) :
    F.obj (op U) ⟶
      (ModuleCat.restrictScalars (O.map (homOfLE h).op).hom).obj (F.obj (op V)) :=
  F.map (homOfLE h).op

/-!
The following theorem exposes the source's commuting restriction square in
the canonical `PresheafOfModules.Hom` interface.  The module action and the
linearity of every component are fields of the canonical bundled modules.
-/

/-- A morphism of presheaves of modules commutes with restriction maps. -/
theorem presheafOfOModulesMorphism_naturality {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O}
    (φ : PresheafOfOModulesMorphism (F := F) (G := G))
    {U V : Opens X} (h : V ≤ U) :
    moduleRestriction F h ≫
        (ModuleCat.restrictScalars (O.map (homOfLE h).op).hom).map
          (φ.app (op V)) =
      φ.app (op U) ≫ moduleRestriction G h := by
  exact φ.naturality (homOfLE h).op

/-- Every component of an `O`-module morphism is linear over the sections. -/
theorem presheafOfOModulesMorphism_smul {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O}
    (φ : PresheafOfOModulesMorphism (F := F) (G := G)) (U : Opens X)
    (r : O.obj (op U)) (m : F.obj (op U)) :
    φ.app (op U) (r • m) = r • φ.app (op U) m := by
  exact (φ.app (op U)).hom.map_smul r m

/-!
`PresheafOfModules.pullback` is parameterized by a functor between the
indexing categories.  For the present section that functor is the identity
on `Opens X`; this helper only changes the type of the ring morphism and
introduces no additional mathematical data.
-/

/-- View a ring-presheaf morphism as one over the identity on the opens. -/
noncomputable def asIdentityRingPresheafMorphism {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) :
    O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂ := by
  exact α ≫
    (Functor.isoWhiskerRight (Functor.opId (Opens X)) O₂ ≪≫
      Functor.leftUnitor O₂).inv

/-- The identity-functor transport in `asIdentityRingPresheafMorphism` is
componentwise trivial. -/
theorem asIdentityRingPresheafMorphism_app {X : TopCat.{w}}
    {O O' : RingPresheaf.{w, w} X} (α : O ⟶ O') (U : (Opens X)ᵒᵖ) :
    (asIdentityRingPresheafMorphism α).app U = α.app U := by
  simp [asIdentityRingPresheafMorphism]

/-! ## Restriction of scalars -/

/-- Restriction of scalars for a morphism of presheaves of rings. -/
noncomputable abbrev restrictionOfScalars {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) :
    PMod O₂ ⥤ PMod O₁ :=
  _root_.PresheafOfModules.pushforward
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The restriction of an individual presheaf of modules to the smaller ring. -/
noncomputable abbrev restrictedModule {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) (F : PMod O₂) : PMod O₁ :=
  (restrictionOfScalars α).obj F

/-! ## Tensor product and change of rings -/

/-!
The Mathlib pullback existence theorem is stated for a small indexing
category and a presheaf of rings in the same universe.  The change-of-rings
interface below follows that established universe convention for `Opens X`;
the imported canonical instance supplies the right adjoint for the
restriction-of-scalars functor.
-/

/-!
This private spelling keeps the source order: the tensor-product object is
introduced before the public change-of-rings functor, while both reuse the
same canonical pullback functor.
-/

noncomputable abbrev changeOfRingsCore {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    PMod O₁ ⥤ PMod O₂ :=
  _root_.PresheafOfModules.pullback
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The tensor product presheaf described in the source. -/
noncomputable abbrev tensorProductPresheaf {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) (G : PMod O₁) : PMod O₂ :=
  (changeOfRingsCore α).obj G

/-- A presheaf of commutative rings, viewed before forgetting to `RingCat`. -/
abbrev CommRingPresheaf (X : TopCat.{w}) :=
  TopCat.Presheaf (CommRingCat.{w}) X

/-- A presheaf of modules over a commutative-ring presheaf. -/
abbrev CommRingPresheafModule {X : TopCat.{w}} (O : CommRingPresheaf X) :=
  PMod (O ⋙ (forget₂ CommRingCat RingCat))

/-- The underlying `RingCat` morphism of a commutative-ring-presheaf map. -/
abbrev commRingPresheafMorphismToRingPresheaf
    {X : TopCat.{w}} {O₁ O₂ : CommRingPresheaf X} (α : O₁ ⟶ O₂) :
    (O₁ ⋙ (forget₂ CommRingCat RingCat)) ⟶
      (O₂ ⋙ (forget₂ CommRingCat RingCat)) :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-! ### A sectionwise model for extension of scalars -/

/-- The transpose of the restriction map in the sectionwise
extension-of-scalars construction. -/
noncomputable def pointwiseExtensionAdjointMap
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ModuleCat.of (O.obj U) (G.obj U) ⟶
      (ModuleCat.restrictScalars (α.app U).hom).obj
        ((ModuleCat.restrictScalars (O'.map i).hom).obj
          ((ModuleCat.extendScalars (α.app V).hom).obj
            (ModuleCat.of (O.obj V) (G.obj V)))) := by
  let E : ModuleCat (O'.obj V) :=
    (ModuleCat.extendScalars (α.app V).hom).obj
      (ModuleCat.of (O.obj V) (G.obj V))
  let η := ModuleCat.ExtendRestrictScalarsAdj.Unit.map (α.app V).hom
    (X := ModuleCat.of (O.obj V) (G.obj V))
  let hα : (α.app V).hom.comp (O.map i).hom =
      (O'.map i).hom.comp (α.app U).hom :=
    congrArg CommRingCat.Hom.hom (α.naturality i)
  exact G.map i ≫
    (ModuleCat.restrictScalars (O.map i).hom).map η ≫
    (ModuleCat.restrictScalarsComp'App
      (O.map i).hom (α.app V).hom
      ((α.app V).hom.comp (O.map i).hom) rfl E).inv ≫
    (ModuleCat.restrictScalarsCongr hα).hom.app E ≫
    (ModuleCat.restrictScalarsComp'App
      (α.app U).hom (O'.map i).hom
      ((O'.map i).hom.comp (α.app U).hom) rfl E).hom

/-- The restriction map on sectionwise extensions of scalars. -/
noncomputable def pointwiseExtensionMap
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.extendScalars (α.app U).hom).obj
        (ModuleCat.of (O.obj U) (G.obj U)) ⟶
      (ModuleCat.restrictScalars (O'.map i).hom).obj
        ((ModuleCat.extendScalars (α.app V).hom).obj
          (ModuleCat.of (O.obj V) (G.obj V))) := by
  refine ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv
    (ModuleCat.of (O.obj U) (G.obj U)) _).symm
      (pointwiseExtensionAdjointMap α G i)

@[simp]
theorem pointwiseExtensionMap_adj
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _
      (pointwiseExtensionMap α G i) = pointwiseExtensionAdjointMap α G i := by
  simp [pointwiseExtensionMap]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem pointwiseExtensionMap_one_tmul
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : G.obj U) :
    pointwiseExtensionMap α G i
        ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m) =
      (1 : O'.obj V) ⊗ₜ[(O.obj V), (α.app V).hom] G.map i m := by
  calc
    _ = ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _
        (pointwiseExtensionMap α G i)) m :=
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
        (φ := pointwiseExtensionMap α G i) m).symm
    _ = _ := by
      rw [pointwiseExtensionMap_adj]
      dsimp [pointwiseExtensionAdjointMap]
      simp only [CategoryTheory.comp_apply, ModuleCat.restrictScalars.map_apply,
        ModuleCat.restrictScalarsComp'App_inv_apply,
        ModuleCat.restrictScalarsCongr_hom_app,
        ModuleCat.restrictScalarsComp'App_hom_apply]
      change (1 : O'.obj V) ⊗ₜ[(O.obj V), (α.app V).hom]
        (show G.obj V from G.map i m) = _
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf whose sections are obtained by extension of scalars. -/
noncomputable def pointwiseExtensionObj
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O) :
    CommRingPresheafModule O' where
  obj U := (ModuleCat.extendScalars (α.app U).hom).obj
    (ModuleCat.of (O.obj U) (G.obj U))
  map i := pointwiseExtensionMap α G i
  map_id U := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rw [pointwiseExtensionMap_one_tmul, G.map_id]
    rfl
  map_comp i j := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rw [pointwiseExtensionMap_one_tmul]
    simp only [CategoryTheory.comp_apply]
    change (1 : O'.obj _) ⊗ₜ[(O.obj _), (α.app _).hom] G.map (i ≫ j) m =
      pointwiseExtensionMap α G j
        (pointwiseExtensionMap α G i
          ((1 : O'.obj _) ⊗ₜ[(O.obj _), (α.app _).hom] m))
    rw [pointwiseExtensionMap_one_tmul, pointwiseExtensionMap_one_tmul,
      G.map_comp_apply]

set_option backward.isDefEq.respectTransparency false in
noncomputable def pointwiseExtensionObjMap
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') {G H : CommRingPresheafModule O} (φ : G ⟶ H) :
    pointwiseExtensionObj α G ⟶ pointwiseExtensionObj α H where
  app U := (ModuleCat.extendScalars (α.app U).hom).map (φ.app U)
  naturality i := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    dsimp only [pointwiseExtensionObj]
    simp only [CategoryTheory.comp_apply]
    change (ModuleCat.extendScalars (α.app _).hom).map (φ.app _)
        (pointwiseExtensionMap α G i
          ((1 : O'.obj _) ⊗ₜ[(O.obj _), (α.app _).hom] m)) =
      pointwiseExtensionMap α H i
        ((ModuleCat.extendScalars (α.app _).hom).map (φ.app _)
          ((1 : O'.obj _) ⊗ₜ[(O.obj _), (α.app _).hom] m))
    rw [pointwiseExtensionMap_one_tmul, ModuleCat.ExtendScalars.map_tmul,
      ModuleCat.ExtendScalars.map_tmul, pointwiseExtensionMap_one_tmul]
    congr 1
    exact PresheafOfModules.naturality_apply φ i m

set_option backward.isDefEq.respectTransparency false in
/-- The functorial sectionwise model of change of rings. -/
noncomputable def pointwiseExtension
    {X : TopCat.{w}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    CommRingPresheafModule O ⥤ CommRingPresheafModule O' where
  obj := pointwiseExtensionObj α
  map := pointwiseExtensionObjMap α
  map_id G := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.app U).hom).map_id (G.obj U)
  map_comp φ ψ := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.app U).hom).map_comp (φ.app U) (ψ.app U)

noncomputable abbrev directRestrictionOfScalars
    {X : TopCat.{w}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :=
  _root_.PresheafOfModules.restrictScalars
    (commRingPresheafMorphismToRingPresheaf α)

set_option backward.isDefEq.respectTransparency false in
noncomputable def pointwiseExtensionUnit
    {X : TopCat.{w}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    𝟭 (CommRingPresheafModule O) ⟶
      pointwiseExtension α ⋙ directRestrictionOfScalars α where
  app G :=
    { app := fun U ↦ ModuleCat.ExtendRestrictScalarsAdj.Unit.map (α.app U).hom
      naturality := fun {U V} i ↦ by
        ext m
        dsimp [directRestrictionOfScalars, pointwiseExtension,
          pointwiseExtensionObj]
        change (1 : O'.obj V) ⊗ₜ[(O.obj V), (α.app V).hom]
            (show G.obj V from G.map i m) =
          pointwiseExtensionMap α G i
            ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m)
        rw [pointwiseExtensionMap_one_tmul] }
  naturality G H φ := by
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change (1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] φ.app U m =
      (ModuleCat.extendScalars (α.app U).hom).map (φ.app U)
        ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m)
    rw [ModuleCat.ExtendScalars.map_tmul]
    rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def pointwiseExtensionCounit
    {X : TopCat.{w}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    directRestrictionOfScalars α ⋙ pointwiseExtension α ⟶
      𝟭 (CommRingPresheafModule O') where
  app F :=
    { app := fun U ↦
        ModuleCat.ExtendRestrictScalarsAdj.Counit.map (α.app U).hom
      naturality := fun {U V} i ↦ by
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        dsimp [directRestrictionOfScalars, pointwiseExtension,
          pointwiseExtensionObj]
        change ModuleCat.ExtendRestrictScalarsAdj.Counit.map (α.app V).hom
            (pointwiseExtensionMap α
              ((_root_.PresheafOfModules.restrictScalars
                (commRingPresheafMorphismToRingPresheaf α)).obj F) i
              ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m)) =
          F.map i (ModuleCat.ExtendRestrictScalarsAdj.Counit.map
            (α.app U).hom
            ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m))
        rw [pointwiseExtensionMap_one_tmul]
        change ModuleCat.ExtendRestrictScalarsAdj.Counit.map (α.app V).hom
            ((1 : O'.obj V) ⊗ₜ[(O.obj V), (α.app V).hom]
              (show F.obj V from F.map i (show F.obj U from m))) =
          F.map i (ModuleCat.ExtendRestrictScalarsAdj.Counit.map (α.app U).hom
            ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom]
              (show F.obj U from m)))
        change (1 : O'.obj V) •
            (show F.obj V from F.map i (show F.obj U from m)) =
          F.map i ((1 : O'.obj U) • (show F.obj U from m))
        simp }
  naturality F H φ := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    dsimp [directRestrictionOfScalars, pointwiseExtension,
      pointwiseExtensionObjMap]
    simp only [PresheafOfModules.comp_app, CategoryTheory.comp_apply]
    change ModuleCat.ExtendRestrictScalarsAdj.Counit.map (α.app U).hom
        ((ModuleCat.extendScalars (α.app U).hom).map
          ((ModuleCat.restrictScalars (α.app U).hom).map (φ.app U))
          ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m)) =
      φ.app U (ModuleCat.ExtendRestrictScalarsAdj.Counit.map (α.app U).hom
        ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m))
    rw [ModuleCat.ExtendScalars.map_tmul]
    change (1 : O'.obj U) •
        (show H.obj U from φ.app U (show F.obj U from m)) =
      φ.app U ((1 : O'.obj U) • (show F.obj U from m))
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise extension functor is left adjoint to direct restriction
of scalars. -/
noncomputable def pointwiseExtensionAdjunction
    {X : TopCat.{w}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    pointwiseExtension α ⊣ directRestrictionOfScalars α :=
  Adjunction.mkOfUnitCounit
    { unit := pointwiseExtensionUnit α
      counit := pointwiseExtensionCounit α
      left_triangle := by
        ext G U m
        change (ModuleCat.ExtendRestrictScalarsAdj.Counit.map (α.app U).hom)
          ((ModuleCat.extendScalars (α.app U).hom).map
            (ModuleCat.ExtendRestrictScalarsAdj.Unit.map (α.app U).hom) m) = m
        exact CategoryTheory.congr_fun
          ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).left_triangle_components
            (G.obj U)) m
      right_triangle := by
        ext F U m
        change (ModuleCat.restrictScalars (α.app U).hom).map
          (ModuleCat.ExtendRestrictScalarsAdj.Counit.map (α.app U).hom)
          (ModuleCat.ExtendRestrictScalarsAdj.Unit.map (α.app U).hom m) = m
        exact CategoryTheory.congr_fun
          ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).right_triangle_components
            (F.obj U)) m }

set_option backward.isDefEq.respectTransparency false in
/-- Direct restriction of scalars agrees with the identity-pushforward model
used by `restrictionOfScalars`. -/
noncomputable def directRestrictionOfScalarsIso
    {X : TopCat.{w}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    directRestrictionOfScalars α ≅
      restrictionOfScalars (commRingPresheafMorphismToRingPresheaf α) :=
  NatIso.ofComponents (fun F ↦
    PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsCongr
        (congrArg RingCat.Hom.hom
          (asIdentityRingPresheafMorphism_app
            (commRingPresheafMorphismToRingPresheaf α) U).symm)).app (F.obj U))
      (fun {U V} i ↦ by ext m; rfl))
    (fun φ ↦ by ext U m; rfl)

noncomputable def pointwiseExtensionAbstractAdjunction
    {X : TopCat.{w}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    pointwiseExtension α ⊣
      restrictionOfScalars (commRingPresheafMorphismToRingPresheaf α) :=
  (pointwiseExtensionAdjunction α).ofNatIsoRight
    (directRestrictionOfScalarsIso α)

/-- The change-of-rings functor `PMod(O₁) ⥤ PMod(O₂)`. -/
noncomputable abbrev changeOfRings {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    PMod O₁ ⥤ PMod O₂ :=
  changeOfRingsCore α

/-- The explicit sectionwise construction agrees naturally with Mathlib's
abstract pullback. -/
noncomputable def pointwiseExtensionIsoChangeOfRings
    {X : TopCat.{w}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    pointwiseExtension α ≅
      changeOfRings (commRingPresheafMorphismToRingPresheaf α) :=
  (pointwiseExtensionAbstractAdjunction α).leftAdjointUniq
    (_root_.PresheafOfModules.pullbackPushforwardAdjunction
      (F := 𝟭 (Opens X))
      (asIdentityRingPresheafMorphism
        (commRingPresheafMorphismToRingPresheaf α)))

/-- Evaluation of an isomorphism of presheaves of modules on an object. -/
noncomputable def presheafOfModulesIsoApp
    {X : TopCat.{w}} {O : RingPresheaf.{w, w} X}
    {G H : PMod O} (e : G ≅ H) (U : (Opens X)ᵒᵖ) :
    G.obj U ≅ H.obj U where
  hom := e.hom.app U
  inv := e.inv.app U
  hom_inv_id := by
    rw [← PresheafOfModules.comp_app, e.hom_inv_id]
    rfl
  inv_hom_id := by
    rw [← PresheafOfModules.comp_app, e.inv_hom_id]
    rfl

/-!
## Change of rings and stalks

This comparison belongs with `tensorProductPresheaf`, rather than with a
later consumer of that construction.  It is the missing computational API
for Mathlib's abstract left-adjoint implementation of presheaf pullback.
-/

/-!
The sectionwise comparison is the shared prerequisite for localization in
Modules 27 and for the counterexample in Sheaves 20.  It is important that
the comparison is made as an isomorphism of presheaves of modules: choosing
an isomorphism separately at each open does not provide the compatibility
with restriction maps needed by either application.
-/

/-- The sectionwise extension-of-scalars object at an open. -/
noncomputable abbrev sectionwiseExtensionOfScalarsSection
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    (U : (Opens X)ᵒᵖ) : ModuleCat (O'.obj U) :=
  (ModuleCat.extendScalars (α.app U).hom).obj
    (ModuleCat.of (O.obj U) (G.obj U))

/-- Existence of the restriction map for the sectionwise extension.

The map is obtained by transposing the unit of
`ModuleCat.extendRestrictScalarsAdj` through the naturality square of `α`.
The explicit construction is intentionally hidden behind this interface;
the presheaf and all of its coherence data use one fixed map for each arrow.
-/
theorem sectionwiseExtensionOfScalarsMap_exists
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    Nonempty
      (sectionwiseExtensionOfScalarsSection α G U ⟶
        (ModuleCat.restrictScalars (O'.map i).hom).obj
          (sectionwiseExtensionOfScalarsSection α G V)) := by
  exact ⟨pointwiseExtensionMap α G i⟩

/-- The canonical restriction map on sectionwise extensions of scalars. -/
noncomputable def sectionwiseExtensionOfScalarsMap
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    sectionwiseExtensionOfScalarsSection α G U ⟶
      (ModuleCat.restrictScalars (O'.map i).hom).obj
        (sectionwiseExtensionOfScalarsSection α G V) :=
  pointwiseExtensionMap α G i

/-- Identity coherence for the sectionwise extension restriction maps. -/
theorem sectionwiseExtensionOfScalarsMap_id
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O) (U : (Opens X)ᵒᵖ) :
    sectionwiseExtensionOfScalarsMap α G (𝟙 U) =
      (ModuleCat.restrictScalarsId' (O'.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (O'.map_id U))).inv.app _ := by
  change pointwiseExtensionMap α G (𝟙 U) = _
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change pointwiseExtensionMap α G (𝟙 U)
      ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m) = _
  rw [pointwiseExtensionMap_one_tmul]
  rw [G.map_id]
  simp only [ModuleCat.restrictScalarsId'_inv_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composition coherence for the sectionwise extension restriction maps. -/
theorem sectionwiseExtensionOfScalarsMap_comp
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    sectionwiseExtensionOfScalarsMap α G (i ≫ j) =
      sectionwiseExtensionOfScalarsMap α G i ≫
        (ModuleCat.restrictScalars (O'.map i).hom).map
          (sectionwiseExtensionOfScalarsMap α G j) ≫
        (ModuleCat.restrictScalarsComp' (O'.map i).hom (O'.map j).hom
          (O'.map (i ≫ j)).hom
          (congrArg CommRingCat.Hom.hom (O'.map_comp i j))).inv.app _ := by
  change pointwiseExtensionMap α G (i ≫ j) = _
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change pointwiseExtensionMap α G (i ≫ j)
      ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m) = _
  rw [pointwiseExtensionMap_one_tmul]
  change (1 : O'.obj W) ⊗ₜ[(O.obj W), (α.app W).hom]
      (show G.obj W from G.map (i ≫ j) m) =
    (ModuleCat.restrictScalarsComp' (O'.map i).hom (O'.map j).hom
        (O'.map (i ≫ j)).hom
        (congrArg CommRingCat.Hom.hom (O'.map_comp i j))).inv.app _
      ((ModuleCat.restrictScalars (O'.map i).hom).map
        (pointwiseExtensionMap α G j)
        (pointwiseExtensionMap α G i
          ((1 : O'.obj U) ⊗ₜ[(O.obj U), (α.app U).hom] m)))
  simp only [ModuleCat.restrictScalars.map_apply,
    ModuleCat.restrictScalarsComp'_inv_app,
    ModuleCat.restrictScalarsComp'App_inv_apply]
  rw [pointwiseExtensionMap_one_tmul, pointwiseExtensionMap_one_tmul,
    G.map_comp_apply]
  rfl

/-- The presheaf whose sections are the explicit sectionwise extensions of scalars. -/
noncomputable def sectionwiseExtensionOfScalars
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O) :
    CommRingPresheafModule O' where
  obj U := sectionwiseExtensionOfScalarsSection α G U
  map i := sectionwiseExtensionOfScalarsMap α G i
  map_id U := sectionwiseExtensionOfScalarsMap_id α G U
  map_comp i j := sectionwiseExtensionOfScalarsMap_comp α G i j

/-- A single sectionwise comparison, natural in the open, with `changeOfRingsCore`. -/
theorem tensorProductPresheaf_sectionwiseIso_exists
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O) :
    Nonempty
      (sectionwiseExtensionOfScalars α G ≅
        tensorProductPresheaf
          (commRingPresheafMorphismToRingPresheaf α) G) := by
  refine ⟨?_⟩
  have hobj : sectionwiseExtensionOfScalars α G = (pointwiseExtension α).obj G := by
    rfl
  rw [hobj]
  exact (pointwiseExtensionIsoChangeOfRings α).app G

/-- The coherent sectionwise extension-of-scalars comparison. -/
noncomputable def tensorProductPresheaf_sectionwiseIso
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O) :
    sectionwiseExtensionOfScalars α G ≅
      tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) G :=
  Classical.choice (tensorProductPresheaf_sectionwiseIso_exists α G)

/-- The commutative restriction square for the sectionwise comparison. -/
theorem tensorProductPresheaf_sectionwiseIso_naturality
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    sectionwiseExtensionOfScalarsMap α G i ≫
        (ModuleCat.restrictScalars (O'.map i).hom).map
          ((tensorProductPresheaf_sectionwiseIso α G).hom.app V) =
      (tensorProductPresheaf_sectionwiseIso α G).hom.app U ≫
        ((changeOfRingsCore
          (commRingPresheafMorphismToRingPresheaf α)).obj G).map i := by
  exact (tensorProductPresheaf_sectionwiseIso α G).hom.naturality i

/-- The same commutative square written for the inclusion of opens `V ≤ U`. -/
theorem tensorProductPresheaf_sectionwiseIso_naturality_of_le
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O)
    {U V : Opens X} (h : V ≤ U) :
    sectionwiseExtensionOfScalarsMap α G (homOfLE h).op ≫
        (ModuleCat.restrictScalars (O'.map (homOfLE h).op).hom).map
          ((tensorProductPresheaf_sectionwiseIso α G).hom.app (op V)) =
      (tensorProductPresheaf_sectionwiseIso α G).hom.app (op U) ≫
        ((changeOfRingsCore
          (commRingPresheafMorphismToRingPresheaf α)).obj G).map
          (homOfLE h).op := by
  exact tensorProductPresheaf_sectionwiseIso_naturality α G (homOfLE h).op

/-- The old objectwise interface, obtained from the coherent comparison. -/
theorem tensorProductPresheaf_obj_iso
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (G : CommRingPresheafModule O) (U : (Opens X)ᵒᵖ) :
    Nonempty
      ((ModuleCat.extendScalars (α.app U).hom).obj
          (ModuleCat.of (O.obj U) (G.obj U)) ≅
        ModuleCat.of (O'.obj U)
          ((tensorProductPresheaf
            (commRingPresheafMorphismToRingPresheaf α) G).obj U)) := by
  let e := tensorProductPresheaf_sectionwiseIso α G
  exact ⟨
    { hom := e.hom.app U
      inv := e.inv.app U
      hom_inv_id := by
        change e.hom.app U ≫ e.inv.app U =
          𝟙 ((sectionwiseExtensionOfScalars α G).obj U)
        simpa only [PresheafOfModules.comp_app, PresheafOfModules.id_app] using
          congrArg (fun f => f.app U) e.hom_inv_id
      inv_hom_id := by
        change e.inv.app U ≫ e.hom.app U =
          𝟙 ((tensorProductPresheaf
            (commRingPresheafMorphismToRingPresheaf α) G).obj U)
        simpa only [PresheafOfModules.comp_app, PresheafOfModules.id_app] using
          congrArg (fun f => f.app U) e.inv_hom_id }⟩

/-- Change of rings for presheaves of modules commutes with passage to a
stalk.  The source writes the left side in the symmetric order
`F_x ⊗_{O_x} O'_x`; `ModuleCat.extendScalars` uses the canonically
isomorphic order `O'_x ⊗_{O_x} F_x`.

Proof roadmap:

1. Use `tensorProductPresheaf_obj_iso` to replace every section by explicit
   extension of scalars.
2. Express both stalks as the filtered colimit over neighbourhoods of `x`.
   Use the pointwise natural isomorphism and the fact that tensor
   product, as a left adjoint, preserves these colimits.
3. Identify the colimits of the section rings and modules with `O.stalk x`,
   `O'.stalk x`, and `F.stalk x`; transport the resulting isomorphism through
   the canonical `ModuleCat` stalk actions and verify `O'.stalk x`-linearity.

The remaining proof uses this coherent sectionwise comparison to commute
extension of scalars with the filtered colimit defining a stalk.
-/
theorem tensorProductPresheaf_stalk_iso
    {X : TopCat.{w}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (F : CommRingPresheafModule O) (x : X) :
    Nonempty
      ((ModuleCat.extendScalars
          ((TopCat.Presheaf.stalkFunctor (CommRingCat.{w}) x).map α).hom).obj
        (ModuleCat.of (O.stalk x)
          (↑(TopCat.Presheaf.stalk F.presheaf x))) ≅
        ModuleCat.of (O'.stalk x)
          (↑(TopCat.Presheaf.stalk
            (tensorProductPresheaf
              (commRingPresheafMorphismToRingPresheaf α) F).presheaf x))) := by
  sorry

/-! ## Adjointness -/

/-- Change of rings is left adjoint to restriction of scalars. -/
noncomputable def changeOfRingsAdjunction {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    changeOfRings α ⊣ restrictionOfScalars α :=
  _root_.PresheafOfModules.pullbackPushforwardAdjunction
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The source-facing Hom bijection for change of rings and restriction. -/
noncomputable def changeOfRingsHomEquiv {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂)
    (G : PMod O₁) (F : PMod O₂) :
    (G ⟶ restrictedModule α F) ≃
      (tensorProductPresheaf α G ⟶ F) := by
  exact (changeOfRingsAdjunction α).homEquiv G F |>.symm

end Formalization.Books.Sheaves.Unit06
