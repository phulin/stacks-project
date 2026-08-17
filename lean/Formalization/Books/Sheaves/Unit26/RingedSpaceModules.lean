import Formalization.Books.Sheaves.Unit22.RingedSpaces
import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Sheaves on Spaces, Chapter 26: Morphisms of ringed spaces and modules

This file formalizes `books/sheaves.tex:3108-3268`.  The constructions use
Mathlib's canonical presheaf and sheaf module functors.  The local helper
names below are the focused Chapter 26 interface; they avoid introducing a
second mathematical notion of a ringed space or of a module pullback.

The literal equality of functors in the source is represented by Mathlib's
canonical natural isomorphism.  Equalities of module objects are stated as
usable `ModuleCat` isomorphisms, retaining the scalar structure.
-/

namespace Formalization.Books.Sheaves.Unit26

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10

universe v

noncomputable section

/-! ## Ringed spaces and module functors -/

abbrev RingedSpace := Formalization.Books.Sheaves.Unit22.RingedSpace

abbrev RingedSpaceHom := Formalization.Books.Sheaves.Unit22.RingedSpaceHom

/-- Pushforward of sheaves of rings along a continuous map. -/
abbrev moduleRingSheafPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingSheaf X ⥤ RingSheaf Y :=
  TopCat.Sheaf.pushforward RingCat f

/-- Pullback of sheaves of rings along a continuous map. -/
abbrev moduleRingSheafPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    RingSheaf Y ⥤ RingSheaf X :=
  TopCat.Sheaf.pullback RingCat f

/-- The scalar map from a sheaf to the pushforward of its pullback. -/
noncomputable def moduleSheafPullbackUnit {X Y : TopCat.{v}}
    (f : X ⟶ Y) (O : RingSheaf Y) :
    O ⟶ (moduleRingSheafPushforward f).obj
      ((moduleRingSheafPullback f).obj O) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f).unit.app O

/-- Pushforward of modules along a continuous map and a scalar map. -/
noncomputable def moduleSheafPushforwardAlong {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X) :
    Mod O_X ⥤ Mod O_Y :=
  SheafOfModules.pushforward (F := Opens.map f) α

/-- Pushforward of modules with the induced pushed-forward scalar sheaf. -/
noncomputable def moduleSheafPushforward {X Y : TopCat.{v}}
    {O : RingSheaf X} (f : X ⟶ Y) :
    Mod O ⥤ Mod ((moduleRingSheafPushforward f).obj O) :=
  moduleSheafPushforwardAlong f (𝟙 _)

/-- Pullback of modules along a continuous map and a scalar map. -/
noncomputable def moduleSheafPullbackAlong {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} (f : X ⟶ Y)
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)] :
    Mod O_Y ⥤ Mod O_X :=
  SheafOfModules.pullback (F := Opens.map f) α

/-- Pullback of modules with the induced pulled-back scalar sheaf. -/
noncomputable def moduleSheafPullback {X Y : TopCat.{v}}
    {O : RingSheaf Y} (f : X ⟶ Y)
    [((SheafOfModules.pushforward (F := Opens.map f)
      (moduleSheafPullbackUnit f O)).IsRightAdjoint)] :
    Mod O ⥤ Mod ((moduleRingSheafPullback f).obj O) :=
  moduleSheafPullbackAlong f (moduleSheafPullbackUnit f O)

/-! The sheaf tensor construction used in the displayed pullback formula. -/

/-- The presheaf extension of scalars underlying the source's tensor sheaf. -/
noncomputable abbrev moduleSheafTensorProductPresheaf {X : TopCat.{v}}
    {O₁ O₂ : RingSheaf X} (α : O₁ ⟶ O₂) (G : Mod O₁) :
    PMod O₂.obj :=
  Formalization.Books.Sheaves.Unit06.tensorProductPresheaf α.hom G.val

/-- The source's tensor product sheaf, obtained by module sheafification. -/
noncomputable def moduleSheafTensorProduct {X : TopCat.{v}}
    {O₁ O₂ : RingSheaf X} (α : O₁ ⟶ O₂) (G : Mod O₁) :
    Mod O₂ := by
  exact (PresheafOfModules.sheafification (𝟙 O₂.obj)).obj
    (moduleSheafTensorProductPresheaf α G)

/-! The ringed-space scalar map and module functors. -/

/-- The sheaf-of-rings map corresponding to `f♯`. -/
noncomputable def ringedSpacePullbackRingMap {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    (moduleRingSheafPullback f.continuous).obj Y.structureSheaf ⟶
      X.structureSheaf :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f.continuous).homEquiv
    Y.structureSheaf X.structureSheaf |>.symm f.sharp

/-- The inverse-image module over the pulled-back structure sheaf. -/
noncomputable def ringedSpaceInverseImageModule {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (moduleSheafPullbackUnit f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    Mod Y.structureSheaf ⥤
      Mod ((moduleRingSheafPullback f.continuous).obj Y.structureSheaf) :=
  moduleSheafPullbackAlong f.continuous
    (moduleSheafPullbackUnit f.continuous Y.structureSheaf)

/-- Pushforward of modules along a morphism of ringed spaces. -/
noncomputable def ringedSpaceModulePushforward {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    Mod X.structureSheaf ⥤ Mod Y.structureSheaf :=
  moduleSheafPushforwardAlong f.continuous f.sharp

/-- Pullback of modules along a morphism of ringed spaces. -/
noncomputable def ringedSpaceModulePullback {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    Mod Y.structureSheaf ⥤ Mod X.structureSheaf :=
  moduleSheafPullbackAlong f.continuous f.sharp

/-- The source's tensor description of the pullback module. -/
theorem ringedSpaceModulePullback_formula {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (moduleSheafPullbackUnit f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    Nonempty
      ((ringedSpaceModulePullback f).obj G ≅
        moduleSheafTensorProduct
          (ringedSpacePullbackRingMap f)
          ((ringedSpaceInverseImageModule f).obj G)) := by
  sorry

/-! ## Adjunction, composition, and module `f`-maps -/

/-- The pullback/pushforward adjunction for modules on a ringed space. -/
noncomputable def ringedSpaceModuleAdjunction {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    ringedSpaceModulePullback f ⊣ ringedSpaceModulePushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction
    (F := Opens.map f.continuous) f.sharp

/-- The canonical Hom equivalence for the module adjunction. -/
noncomputable abbrev ringedSpaceModuleHomEquiv {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    (F : Mod X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    ((ringedSpaceModulePullback f).obj G ⟶ F) ≃
      (G ⟶ (ringedSpaceModulePushforward f).obj F) :=
  (ringedSpaceModuleAdjunction f).homEquiv G F

/-- The canonical pushforward comparison for a composite. -/
noncomputable def ringedSpaceModulePushforwardCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) :
    ringedSpaceModulePushforward f ⋙ ringedSpaceModulePushforward g ≅
      ringedSpaceModulePushforward
        (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g) :=
  SheafOfModules.pushforwardComp g.sharp f.sharp

/-- The pushforward comparison as a source-facing existence statement. -/
theorem exists_ringedSpaceModulePushforwardCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) :
    Nonempty
      (ringedSpaceModulePushforward f ⋙ ringedSpaceModulePushforward g ≅
        ringedSpaceModulePushforward
          (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g)) := by
  exact ⟨ringedSpaceModulePushforwardCompIso f g⟩

/-- The canonical pullback comparison for a composite. -/
noncomputable def ringedSpaceModulePullbackCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward
      (F := Opens.map
        (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g).continuous)
      (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g).sharp).IsRightAdjoint)] :
    ringedSpaceModulePullback
        (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g) ≅
      ringedSpaceModulePullback g ⋙ ringedSpaceModulePullback f :=
  (SheafOfModules.pullbackComp g.sharp f.sharp).symm

/-- The pullback comparison as a source-facing existence statement. -/
theorem exists_ringedSpaceModulePullbackCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward
      (F := Opens.map
        (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g).continuous)
      (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g).sharp).IsRightAdjoint)] :
    Nonempty
      (ringedSpaceModulePullback
          (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g) ≅
        ringedSpaceModulePullback g ⋙ ringedSpaceModulePullback f) := by
  exact ⟨ringedSpaceModulePullbackCompIso f g⟩

/-- A module `f`-map, represented canonically as a map to the pushforward. -/
abbrev RingedSpaceModuleFMap {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    (F : Mod X.structureSheaf) : Type _ :=
  G ⟶ (ringedSpaceModulePushforward f).obj F

/-- The definitional Hom equivalence for module `f`-maps. -/
noncomputable abbrev ringedSpaceModuleFMapHomEquiv
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (F : Mod X.structureSheaf) :
    RingedSpaceModuleFMap f G F ≃
      (G ⟶ (ringedSpaceModulePushforward f).obj F) :=
  Equiv.refl _

/-- The pullback/Hom equivalence for module `f`-maps. -/
noncomputable abbrev ringedSpaceModuleFMapPullbackHomEquiv
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (F : Mod X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    ((ringedSpaceModulePullback f).obj G ⟶ F) ≃
      RingedSpaceModuleFMap f G F :=
  (ringedSpaceModuleAdjunction f).homEquiv G F

/-- Composition of module `f`-maps. -/
noncomputable def ringedSpaceModuleFMapComp
    {X Y Z : RingedSpace.{v}} {f : RingedSpaceHom X Y}
    {g : RingedSpaceHom Y Z} {F : Mod X.structureSheaf}
    {G : Mod Y.structureSheaf} {H : Mod Z.structureSheaf}
    (φ : RingedSpaceModuleFMap f G F)
    (ψ : RingedSpaceModuleFMap g H G) :
    RingedSpaceModuleFMap
        (Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g) H F := by
  exact ψ ≫ (ringedSpaceModulePushforward g).map φ ≫
    (ringedSpaceModulePushforwardCompIso f g).hom.app F

/-! ## Stalk maps and the stalk pullback formula -/

/-- The scalar map on stalks induced by `f♯`. -/
noncomputable abbrev moduleSheafFMapStalkScalarMap {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X) (x : X) :
    TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x) ⟶
      TopCat.Presheaf.stalk (C := RingCat.{v}) O_X.obj x :=
  (TopCat.Presheaf.stalkFunctor (RingCat.{v}) (f x)).map α.hom ≫
    TopCat.Presheaf.stalkPushforward (RingCat.{v}) f O_X.obj x

/-- The target stalk module with scalars restricted along `α_x`. -/
noncomputable abbrev moduleSheafFMapStalkTarget {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    (F : Mod O_X) (x : X) :=
  (ModuleCat.restrictScalars (moduleSheafFMapStalkScalarMap α x).hom).obj
    (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O_X.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x)))

/-- The underlying additive morphism on stalks of a module `f`-map. -/
noncomputable abbrev moduleSheafFMapStalkAddMap {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    {G : Mod O_Y} {F : Mod O_X}
    (φ : G ⟶ (moduleSheafPushforwardAlong f α).obj F) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf (f x) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x)).map
      ((PresheafOfModules.toPresheaf O_Y.obj).map φ.val) ≫
    TopCat.Presheaf.stalkPushforward (AddCommGrpCat.{v}) f F.val.presheaf x

/-- The stalk additive map is linear for the scalar map induced by `α`. -/
theorem moduleSheafFMapStalkAddMap_smul {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    {G : Mod O_Y} {F : Mod O_X}
    (φ : G ⟶ (moduleSheafPushforwardAlong f α).obj F) (x : X)
    (r : TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x)) :
    moduleSheafFMapStalkAddMap α φ x ≫
        (moduleSheafFMapStalkTarget α F x).smul r =
      (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x))
        (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          G.val.presheaf (f x)))).smul r ≫
        moduleSheafFMapStalkAddMap α φ x := by
  sorry

/-- The induced module morphism on stalks of a module `f`-map. -/
noncomputable def moduleSheafFMapStalkMap {X Y : TopCat.{v}}
    {O_X : RingSheaf X} {O_Y : RingSheaf Y} {f : X ⟶ Y}
    (α : O_Y ⟶ (moduleRingSheafPushforward f).obj O_X)
    {G : Mod O_Y} {F : Mod O_X}
    (φ : G ⟶ (moduleSheafPushforwardAlong f α).obj F) (x : X) :
    ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O_Y.obj (f x))
        (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          G.val.presheaf (f x))) ⟶
      moduleSheafFMapStalkTarget α F x := by
  exact ModuleCat.homMk (moduleSheafFMapStalkAddMap α φ x)
    (moduleSheafFMapStalkAddMap_smul α φ x)

/-- The scalar map on stalks of a ringed-space morphism. -/
noncomputable abbrev ringedSpaceModuleStalkScalarMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (x : X) :
    TopCat.Presheaf.stalk (C := RingCat.{v}) Y.structureSheaf.obj
        (f.continuous x) ⟶
      TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x :=
  moduleSheafFMapStalkScalarMap f.sharp x

/-- The target stalk module with scalars restricted along `f♯_x`. -/
noncomputable abbrev ringedSpaceModuleStalkTarget
    {X Y : RingedSpace.{v}} {f : RingedSpaceHom X Y}
    (F : Mod X.structureSheaf) (x : X) :=
  moduleSheafFMapStalkTarget f.sharp F x

/-- The induced module morphism on stalks of a module `f`-map. -/
noncomputable abbrev ringedSpaceModuleFMapStalkMap
    {X Y : RingedSpace.{v}} {f : RingedSpaceHom X Y}
    {G : Mod Y.structureSheaf} {F : Mod X.structureSheaf}
    (φ : RingedSpaceModuleFMap f G F) (x : X) :
    ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v})
        Y.structureSheaf.obj (f.continuous x))
        (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          G.val.presheaf (f.continuous x))) ⟶
      ringedSpaceModuleStalkTarget F x :=
  moduleSheafFMapStalkMap f.sharp φ x

/-!
The direct stalk tensor in the source is represented by the stalk of the
canonical sheaf tensor product.  Its inverse-image factor is the canonical
module pullback, and the preceding stalk construction retains the full
`O_{X,x}`-module structure.
-/

/-- The canonical module object representing the source's stalk tensor. -/
noncomputable def ringedSpaceModulePullbackStalkTensor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (x : X)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (moduleSheafPullbackUnit f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    ModuleCat (↑(TopCat.Presheaf.stalk (C := RingCat.{v})
      X.structureSheaf.obj x)) :=
  ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v})
      X.structureSheaf.obj x)
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
      (moduleSheafTensorProduct
        (ringedSpacePullbackRingMap f)
        ((ringedSpaceInverseImageModule f).obj G)).val.presheaf x))

/-- The stalk of the pullback module is the source's stalk tensor module. -/
theorem ringedSpaceModulePullback_stalk_formula
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (x : X)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (moduleSheafPullbackUnit f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    Nonempty
      (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v})
          X.structureSheaf.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
            ((ringedSpaceModulePullback f).obj G).val.presheaf x)) ≅
        ringedSpaceModulePullbackStalkTensor f G x) := by
  sorry

end

end Formalization.Books.Sheaves.Unit26
