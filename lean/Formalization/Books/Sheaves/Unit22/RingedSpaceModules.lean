import Formalization.Books.Sheaves.Unit22.RingedSpaces
import Formalization.Books.Sheaves.Unit22.Modules
import Formalization.Books.Sheaves.Unit20.SheafificationOfPresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Sheaves on Spaces, Chapter 22, Section 5: Morphisms of ringed spaces and modules

The scalar map on a ringed-space morphism is converted by the sheaf
pullback/pushforward adjunction.  Pushforward is the canonical module
pushforward along that map; pullback is the corresponding inverse-image module
followed by extension of scalars.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17

universe v

noncomputable section

/-! ## Ring maps and module functors -/

/-- The map of sheaves of rings on the source space corresponding to the sharp
map of a ringed-space morphism. -/
noncomputable def ringedSpacePullbackRingMap {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    (moduleRingSheafPullback f.continuous).obj Y.structureSheaf ⟶
      X.structureSheaf :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f.continuous).homEquiv
    Y.structureSheaf X.structureSheaf |>.symm f.sharp

/-- The inverse-image module underlying the pullback module. -/
noncomputable def ringedSpaceInverseImageModule {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (moduleSheafPullbackUnit f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    Mod Y.structureSheaf ⥤
      Mod ((moduleRingSheafPullback f.continuous).obj Y.structureSheaf) := by
  exact moduleSheafPullbackAlong f.continuous
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

/-- The source's formula for the pullback module as a tensor product over the
inverse-image structure sheaf. -/
theorem ringedSpaceModulePullback_formula {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (moduleSheafPullbackUnit f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    Nonempty
      ((ringedSpaceModulePullback f).obj G ≅
        Formalization.Books.Sheaves.Unit17.tensorProductSheaf
          (ringedSpacePullbackRingMap f)
          ((ringedSpaceInverseImageModule f).obj G)) := by
  sorry

/-! ## Stalk tensor formula -/

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
      (Formalization.Books.Sheaves.Unit17.tensorProductSheaf
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

/-! ## Adjunction, composition, and `f`-maps -/

/-- The pullback/pushforward adjunction for modules on a ringed-space
morphism. -/
noncomputable def ringedSpaceModuleAdjunction {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    ringedSpaceModulePullback f ⊣ ringedSpaceModulePushforward f := by
  exact SheafOfModules.pullbackPushforwardAdjunction
    (F := Opens.map f.continuous) f.sharp

/-- The canonical module Hom correspondence for a ringed-space morphism. -/
noncomputable abbrev ringedSpaceModuleHomEquiv {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    (F : Mod X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    ((ringedSpaceModulePullback f).obj G ⟶ F) ≃
      (G ⟶ (ringedSpaceModulePushforward f).obj F) :=
  (ringedSpaceModuleAdjunction f).homEquiv G F

/-- Pushforward of modules is compatible with composition of ringed-space
morphisms. -/
theorem exists_ringedSpaceModulePushforwardCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) :
    Nonempty
      (ringedSpaceModulePushforward f ⋙ ringedSpaceModulePushforward g ≅
        ringedSpaceModulePushforward (RingedSpaceHom.comp f g)) := by
  sorry

noncomputable def ringedSpaceModulePushforwardCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) :
    ringedSpaceModulePushforward f ⋙ ringedSpaceModulePushforward g ≅
      ringedSpaceModulePushforward (RingedSpaceHom.comp f g) :=
  SheafOfModules.pushforwardComp g.sharp f.sharp

/-- Pullback of modules is canonically compatible with composition. -/
theorem exists_ringedSpaceModulePullbackCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward
      (F := Opens.map (RingedSpaceHom.comp f g).continuous)
      (RingedSpaceHom.comp f g).sharp).IsRightAdjoint)] :
    Nonempty
      (ringedSpaceModulePullback (RingedSpaceHom.comp f g) ≅
        ringedSpaceModulePullback g ⋙ ringedSpaceModulePullback f) := by
  sorry

noncomputable def ringedSpaceModulePullbackCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward
      (F := Opens.map (RingedSpaceHom.comp f g).continuous)
      (RingedSpaceHom.comp f g).sharp).IsRightAdjoint)] :
    ringedSpaceModulePullback (RingedSpaceHom.comp f g) ≅
      ringedSpaceModulePullback g ⋙ ringedSpaceModulePullback f :=
  (SheafOfModules.pullbackComp g.sharp f.sharp).symm

/-- A module `f`-map is a morphism to the module pushforward. -/
abbrev RingedSpaceModuleFMap {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    (F : Mod X.structureSheaf) : Type _ :=
  G ⟶ (ringedSpaceModulePushforward f).obj F

/-- The module `f`-map/pullback Hom correspondence. -/
noncomputable abbrev ringedSpaceModuleFMapPullbackHomEquiv
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (F : Mod X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    ((ringedSpaceModulePullback f).obj G ⟶ F) ≃ RingedSpaceModuleFMap f G F :=
  ringedSpaceModuleHomEquiv f G F

/-- Composition of module `f`-maps. -/
noncomputable def ringedSpaceModuleFMapComp
    {X Y Z : RingedSpace.{v}} {f : RingedSpaceHom X Y}
    {g : RingedSpaceHom Y Z} {F : Mod X.structureSheaf}
    {G : Mod Y.structureSheaf} {H : Mod Z.structureSheaf}
    (φ : RingedSpaceModuleFMap f G F)
    (ψ : RingedSpaceModuleFMap g H G) :
    RingedSpaceModuleFMap (RingedSpaceHom.comp f g) H F := by
  exact ψ ≫ (ringedSpaceModulePushforward g).map φ ≫
    (ringedSpaceModulePushforwardCompIso f g).hom.app F

/-- The stalk map of a module `f`-map, regarded as a map of modules after
restricting scalars along the stalk of `f^sharp`. -/
noncomputable def ringedSpaceModuleFMapStalkMap
    {X Y : RingedSpace.{v}} {f : RingedSpaceHom X Y}
    {G : Mod Y.structureSheaf} {F : Mod X.structureSheaf}
    (φ : RingedSpaceModuleFMap f G F) (x : X) :
    ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v})
        Y.structureSheaf.obj (f.continuous x))
        (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          G.val.presheaf (f.continuous x))) ⟶
      moduleSheafFMapStalkTarget f.sharp F x :=
  moduleSheafFMapStalkMap f.sharp φ x

end

end Formalization.Books.Sheaves.Unit22
