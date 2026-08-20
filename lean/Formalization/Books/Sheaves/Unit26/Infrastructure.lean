import Formalization.Books.Sheaves.Unit25.Infrastructure
import Formalization.Books.Sheaves.Unit24.Infrastructure
import Formalization.Books.Sheaves.Unit20.SheafificationOfPresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Shared infrastructure for Chapter 26: Morphisms of ringed spaces and modules

The scalar map on a ringed-space morphism is converted by the sheaf
pullback/pushforward adjunction.  Pushforward is the canonical module
pushforward along that map; pullback is the corresponding inverse-image module
followed by extension of scalars.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

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
  let β := ringedSpacePullbackRingMap f
  let adj₂ :
      Formalization.Books.Sheaves.Unit17.sheafChangeOfRings β ⊣
        SheafOfModules.pushforward (F := 𝟭 (Opens X)) β := by
    exact (Formalization.Books.Sheaves.Unit17.sheafChangeOfRingsAdjunction β).ofNatIsoRight
      (Iso.refl _)
  have hβ :
      (moduleSheafPullbackUnit f.continuous Y.structureSheaf) ≫
        (moduleRingSheafPushforward f.continuous).map β = f.sharp := by
    change
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f.continuous).homEquiv
        Y.structureSheaf X.structureSheaf) β = f.sharp
    exact ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f.continuous).homEquiv
      Y.structureSheaf X.structureSheaf).apply_symm_apply f.sharp
  have eR :
      SheafOfModules.pushforward (F := 𝟭 (Opens X)) β ⋙
          SheafOfModules.pushforward (F := Opens.map f.continuous)
            (moduleSheafPullbackUnit f.continuous Y.structureSheaf) ≅
        SheafOfModules.pushforward (F := Opens.map f.continuous) f.sharp := by
    exact
      (SheafOfModules.pushforwardComp
        (F := Opens.map f.continuous) (G := 𝟭 (Opens X))
        (moduleSheafPullbackUnit f.continuous Y.structureSheaf) β) ≪≫
        SheafOfModules.pushforwardCongr hβ
  have eL :
      (SheafOfModules.pullback
        (moduleSheafPullbackUnit f.continuous Y.structureSheaf) ⋙
        Formalization.Books.Sheaves.Unit17.sheafChangeOfRings β) ≅
        ringedSpaceModulePullback f :=
    Adjunction.leftAdjointCompIso
      (SheafOfModules.pullbackPushforwardAdjunction
        (moduleSheafPullbackUnit f.continuous Y.structureSheaf))
      adj₂
      (SheafOfModules.pullbackPushforwardAdjunction f.sharp)
      eR
  exact ⟨(eL.app G).symm⟩

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

private theorem moduleStalkIso_of_sheafModuleIso
    {X : TopCat.{v}} {O : RingSheaf X} {F T : Mod O}
    (e : F ≅ T) (x : X) :
    Nonempty
      (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x)) ≅
        ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) T.val.presheaf x))) := by
  classical
  let R := TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x
  let M : ModuleCat R := ModuleCat.of R
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))
  let N : ModuleCat R := ModuleCat.of R
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) T.val.presheaf x))
  change Nonempty (M ≅ N)
  let eVal : F.val ≅ T.val :=
    (SheafOfModules.forget O).mapIso e
  let eAddIso :
      (forget₂ (ModuleCat R) AddCommGrpCat).obj M ≅
        (forget₂ (ModuleCat R) AddCommGrpCat).obj N :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapIso
      ((PresheafOfModules.toPresheaf O.obj).mapIso eVal)
  have hsmul (r : R) : eAddIso.hom ≫ N.smul r = M.smul r ≫ eAddIso.hom := by
    apply TopCat.Presheaf.stalk_hom_ext F.val.presheaf
    intro U hxU
    apply ConcreteCategory.hom_ext
    intro m
    obtain ⟨V, hxV, rV, hr⟩ :=
      TopCat.Presheaf.exists_germ_eq O.obj r
    let W : Opens X := U ⊓ V
    let hxW : x ∈ W := ⟨hxU, hxV⟩
    let rW : O.obj.obj (Opposite.op W) :=
      O.obj.map (homOfLE (show W ≤ V from inf_le_right)).op rV
    have hrW :
        TopCat.Presheaf.germ O.obj W x hxW rW = r := by
      dsimp [rW]
      rw [TopCat.Presheaf.germ_res_apply]
      simpa using hr
    let mU : F.val.obj (Opposite.op U) := m
    let mW : F.val.obj (Opposite.op W) :=
      F.val.map (homOfLE (show W ≤ U from inf_le_left)).op mU
    let mW0 : F.val.presheaf.obj (Opposite.op W) :=
      F.val.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op m
    have hmW0 : mW0 = mW := by
      dsimp [mW0, mW, mU]
      rfl
    have hmW :
        TopCat.Presheaf.germ F.val.presheaf W x hxW mW0 =
          TopCat.Presheaf.germ F.val.presheaf U x hxU m := by
      simpa only [mW0] using
        (TopCat.Presheaf.germ_res_apply F.val.presheaf
          (homOfLE (show W ≤ U from inf_le_left)) x hxW m)
    rw [← hrW]
    simp only [ConcreteCategory.comp_apply]
    rw [← hmW]
    rw [hmW0]
    let φAdd : F.val.presheaf ⟶ T.val.presheaf :=
      (PresheafOfModules.toPresheaf O.obj).map e.hom.val
    have hmap_section (n : F.val.obj (Opposite.op W)) :
        eAddIso.hom
            (TopCat.Presheaf.germ F.val.presheaf W x hxW n) =
          TopCat.Presheaf.germ T.val.presheaf W x hxW
            (e.hom.val.app (Opposite.op W) n) := by
      let n0 : F.val.presheaf.obj (Opposite.op W) := n
      let p0 : T.val.presheaf.obj (Opposite.op W) :=
        e.hom.val.app (Opposite.op W) n
      change
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φAdd
            (TopCat.Presheaf.germ F.val.presheaf W x hxW n0) =
          TopCat.Presheaf.germ T.val.presheaf W x hxW p0
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rfl
    have hsmulF :
        (M.smul (TopCat.Presheaf.germ O.obj W x hxW rW)).hom
            (TopCat.Presheaf.germ F.val.presheaf W x hxW mW) =
          TopCat.Presheaf.germ F.val.presheaf W x hxW (rW • mW) := by
      change
        (TopCat.Presheaf.germ O.obj W x hxW rW) •
            TopCat.Presheaf.germ F.val.presheaf W x hxW mW =
          TopCat.Presheaf.germ F.val.presheaf W x hxW (rW • mW)
      exact (PresheafOfModules.germ_ringCat_smul F.val x W hxW rW mW).symm
    have hsmulT :
        (N.smul (TopCat.Presheaf.germ O.obj W x hxW rW)).hom
            (TopCat.Presheaf.germ T.val.presheaf W x hxW
              (e.hom.val.app (Opposite.op W) mW)) =
          TopCat.Presheaf.germ T.val.presheaf W x hxW
            (rW • e.hom.val.app (Opposite.op W) mW) := by
      change
        (TopCat.Presheaf.germ O.obj W x hxW rW) •
            TopCat.Presheaf.germ T.val.presheaf W x hxW
              (e.hom.val.app (Opposite.op W) mW) =
          TopCat.Presheaf.germ T.val.presheaf W x hxW
            (rW • e.hom.val.app (Opposite.op W) mW)
      exact (PresheafOfModules.germ_ringCat_smul T.val x W hxW rW
        (e.hom.val.app (Opposite.op W) mW)).symm
    rw [hmap_section mW, hsmulT]
    have hsection_smul :
        rW • e.hom.val.app (Opposite.op W) mW =
          e.hom.val.app (Opposite.op W) (rW • mW) := by
      exact ((e.hom.val.app (Opposite.op W)).hom.map_smul rW mW).symm
    rw [hsection_smul]
    rw [hsmulF, hmap_section (rW • mW)]
  exact ⟨ModuleCat.isoMk eAddIso hsmul⟩

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
  simpa [ringedSpaceModulePullbackStalkTensor] using
    (moduleStalkIso_of_sheafModuleIso
      (Classical.choice (ringedSpaceModulePullback_formula f G)) x)

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
  exact ⟨SheafOfModules.pushforwardComp g.sharp f.sharp⟩

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
  exact ⟨(SheafOfModules.pullbackComp g.sharp f.sharp).symm⟩

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

/-! ## Stalks of sheaves of modules -/

/-- The additive map on stalks induced by a morphism of sheaves of modules. -/
noncomputable def moduleStalkAddMap {X : TopCat.{v}} {O : RingSheaf X}
    {F G : Mod O} (φ : F ⟶ G) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
    ((PresheafOfModules.toPresheaf O.obj).map φ.val)

theorem moduleStalkAddMap_smul {X : TopCat.{v}} {O : RingSheaf X}
    {F G : Mod O} (φ : F ⟶ G) (x : X)
    (r : TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) :
    moduleStalkAddMap φ x ≫
        (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf x))).smul r =
        (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))).smul r ≫
        moduleStalkAddMap φ x := by
  classical
  apply TopCat.Presheaf.stalk_hom_ext F.val.presheaf
  intro U hxU
  apply ConcreteCategory.hom_ext
  intro m
  obtain ⟨V, hxV, rV, hr⟩ :=
    TopCat.Presheaf.exists_germ_eq O.obj r
  let W : Opens X := U ⊓ V
  let hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : O.obj.obj (Opposite.op W) :=
    O.obj.map (homOfLE (show W ≤ V from inf_le_right)).op rV
  have hrW :
      TopCat.Presheaf.germ O.obj W x hxW rW = r := by
    dsimp [rW]
    rw [TopCat.Presheaf.germ_res_apply]
    simpa using hr
  let mU : F.val.obj (Opposite.op U) := m
  let mW : F.val.obj (Opposite.op W) :=
    F.val.map (homOfLE (show W ≤ U from inf_le_left)).op mU
  let mW0 : F.val.presheaf.obj (Opposite.op W) :=
    F.val.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op m
  have hmW0 : mW0 = mW := by
    dsimp [mW0, mW, mU]
    rfl
  have hmW :
      TopCat.Presheaf.germ F.val.presheaf W x hxW mW0 =
        TopCat.Presheaf.germ F.val.presheaf U x hxU m := by
    simpa only [mW0] using
      (TopCat.Presheaf.germ_res_apply F.val.presheaf
        (homOfLE (show W ≤ U from inf_le_left)) x hxW m)
  rw [← hrW]
  simp only [ConcreteCategory.comp_apply]
  rw [← hmW]
  rw [hmW0]
  change
    (TopCat.Presheaf.germ O.obj W x hxW rW) •
        moduleStalkAddMap φ x
          (TopCat.Presheaf.germ F.val.presheaf W x hxW mW) =
      moduleStalkAddMap φ x
        ((TopCat.Presheaf.germ O.obj W x hxW rW) •
          TopCat.Presheaf.germ F.val.presheaf W x hxW mW)
  let φAdd : F.val.presheaf ⟶ G.val.presheaf :=
    (PresheafOfModules.toPresheaf O.obj).map φ.val
  have hmap_section (n : F.val.obj (Opposite.op W)) :
      moduleStalkAddMap φ x
          (TopCat.Presheaf.germ F.val.presheaf W x hxW n) =
        TopCat.Presheaf.germ G.val.presheaf W x hxW
          (φ.val.app (Opposite.op W) n) := by
    let n0 : F.val.presheaf.obj (Opposite.op W) := n
    let p0 : G.val.presheaf.obj (Opposite.op W) :=
      φ.val.app (Opposite.op W) n
    change
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φAdd
          (TopCat.Presheaf.germ F.val.presheaf W x hxW n0) =
        TopCat.Presheaf.germ G.val.presheaf W x hxW p0
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  have hsmulF :
      (TopCat.Presheaf.germ O.obj W x hxW rW) •
          TopCat.Presheaf.germ F.val.presheaf W x hxW mW =
        TopCat.Presheaf.germ F.val.presheaf W x hxW (rW • mW) := by
    exact (PresheafOfModules.germ_ringCat_smul F.val x W hxW rW mW).symm
  have hsmulG :
      (TopCat.Presheaf.germ O.obj W x hxW rW) •
          TopCat.Presheaf.germ G.val.presheaf W x hxW
            (φ.val.app (Opposite.op W) mW) =
        TopCat.Presheaf.germ G.val.presheaf W x hxW
          (rW • φ.val.app (Opposite.op W) mW) := by
    exact (PresheafOfModules.germ_ringCat_smul G.val x W hxW rW
      (φ.val.app (Opposite.op W) mW)).symm
  rw [hmap_section mW, hsmulF, hmap_section (rW • mW)]
  rw [(φ.val.app (Opposite.op W)).hom.map_smul]
  rw [← hsmulG]

/-- The stalk functor on sheaves of `O`-modules, with its canonical stalk
module structure. -/
noncomputable def moduleStalkFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Mod O ⥤ ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) where
  obj F :=
    ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))
  map φ := ModuleCat.homMk (moduleStalkAddMap φ x) (moduleStalkAddMap_smul φ x)
  map_id := by
    intro F
    apply ModuleCat.hom_ext
    ext m
    let φAdd :
        (PresheafOfModules.toPresheaf O.obj).obj F.val ⟶
          (PresheafOfModules.toPresheaf O.obj).obj F.val :=
      (PresheafOfModules.toPresheaf O.obj).map (𝟙 F : F ⟶ F).val
    have hφ : φAdd = 𝟙 ((PresheafOfModules.toPresheaf O.obj).obj F.val) := by
      dsimp [φAdd]
      simpa only [SheafOfModules.id_val] using
        (PresheafOfModules.toPresheaf O.obj).map_id F.val
    change
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φAdd)) m = m
    rw [hφ]
    have hstalk :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_id
        ((PresheafOfModules.toPresheaf O.obj).obj F.val)
    exact congrArg (fun q => (ConcreteCategory.hom q) m) hstalk
  map_comp := by
    intro F G H f g
    apply ModuleCat.hom_ext
    ext m
    let φAdd :
        (PresheafOfModules.toPresheaf O.obj).obj F.val ⟶
          (PresheafOfModules.toPresheaf O.obj).obj G.val :=
      (PresheafOfModules.toPresheaf O.obj).map f.val
    let ψAdd :
        (PresheafOfModules.toPresheaf O.obj).obj G.val ⟶
          (PresheafOfModules.toPresheaf O.obj).obj H.val :=
      (PresheafOfModules.toPresheaf O.obj).map g.val
    let θAdd :
        (PresheafOfModules.toPresheaf O.obj).obj F.val ⟶
          (PresheafOfModules.toPresheaf O.obj).obj H.val :=
      (PresheafOfModules.toPresheaf O.obj).map (f ≫ g).val
    have hcomp : θAdd = φAdd ≫ ψAdd := by
      dsimp [θAdd, φAdd, ψAdd]
      exact (PresheafOfModules.toPresheaf O.obj).map_comp f.val g.val
    change
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map θAdd)) m =
        (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ψAdd))
          ((ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φAdd)) m)
    rw [hcomp, (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_comp]
    rfl

end

end Formalization.Books.Sheaves.Unit22
