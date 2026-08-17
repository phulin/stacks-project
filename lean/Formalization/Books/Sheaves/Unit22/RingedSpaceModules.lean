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
    (f : RingedSpaceHom X Y) :
    Mod Y.structureSheaf ⥤
      Mod ((moduleRingSheafPullback f.continuous).obj Y.structureSheaf) := by
  sorry

/-- Pushforward of modules along a morphism of ringed spaces. -/
noncomputable def ringedSpaceModulePushforward {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    Mod X.structureSheaf ⥤ Mod Y.structureSheaf :=
  moduleSheafPushforwardAlong f.continuous f.sharp

/-- Pullback of modules along a morphism of ringed spaces. -/
noncomputable def ringedSpaceModulePullback {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    Mod Y.structureSheaf ⥤ Mod X.structureSheaf where
  obj G := tensorProductSheaf (ringedSpacePullbackRingMap f)
    ((ringedSpaceInverseImageModule f).obj G)
  map φ := by
    sorry
  map_id := by
    intros
    sorry
  map_comp := by
    intros
    sorry

/-- The source's formula for the pullback module as a tensor product over the
inverse-image structure sheaf. -/
theorem ringedSpaceModulePullback_formula {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf) :
    Nonempty
      ((ringedSpaceModulePullback f).obj G ≅
        Formalization.Books.Sheaves.Unit17.tensorProductSheaf
          (ringedSpacePullbackRingMap f)
          ((ringedSpaceInverseImageModule f).obj G)) := by
  sorry

/-! ## Adjunction, composition, and `f`-maps -/

/-- The pullback/pushforward adjunction for modules on a ringed-space
morphism. -/
noncomputable def ringedSpaceModuleAdjunction {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    ringedSpaceModulePullback f ⊣ ringedSpaceModulePushforward f := by
  sorry

/-- The canonical module Hom correspondence for a ringed-space morphism. -/
noncomputable abbrev ringedSpaceModuleHomEquiv {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    (F : Mod X.structureSheaf) :
    ((ringedSpaceModulePullback f).obj G ⟶ F) ≃
      (G ⟶ (ringedSpaceModulePushforward f).obj F) :=
  (ringedSpaceModuleAdjunction f).homEquiv G F

/-- Pushforward of modules is compatible with composition of ringed-space
morphisms. -/
noncomputable def ringedSpaceModulePushforwardCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) :
    ringedSpaceModulePushforward f ⋙ ringedSpaceModulePushforward g ≅
      ringedSpaceModulePushforward (RingedSpaceHom.comp f g) := by
  sorry

/-- Pullback of modules is canonically compatible with composition. -/
noncomputable def ringedSpaceModulePullbackCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) :
    ringedSpaceModulePullback (RingedSpaceHom.comp f g) ≅
      ringedSpaceModulePullback g ⋙ ringedSpaceModulePullback f := by
  sorry

/-- A module `f`-map is a morphism to the module pushforward. -/
abbrev RingedSpaceModuleFMap {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    (F : Mod X.structureSheaf) : Type _ :=
  G ⟶ (ringedSpaceModulePushforward f).obj F

/-- The module `f`-map/pullback Hom correspondence. -/
noncomputable abbrev ringedSpaceModuleFMapPullbackHomEquiv
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (F : Mod X.structureSheaf) :
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
  sorry

/-! ## Stalks -/

/-- The stalk tensor product appearing in the source's pullback formula. -/
noncomputable def ringedSpaceStalkPullbackModule
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (x : X) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v})
      X.structureSheaf.obj x) := by
  sorry

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

/-- The stalk of a pullback module is the tensor product of the source stalk
with the target stalk, using the stalk map induced by `f^sharp`. -/
theorem ringedSpaceModulePullback_stalk_formula
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (x : X) :
    Nonempty
      (ringedSpaceStalkPullbackModule f G x ≅
        ModuleCat.of
          (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
            ((ringedSpaceModulePullback f).obj G).val.presheaf x))) := by
  sorry

end

end Formalization.Books.Sheaves.Unit22
