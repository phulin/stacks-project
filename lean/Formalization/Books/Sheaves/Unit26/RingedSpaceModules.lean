import Formalization.Books.Sheaves.Unit20.SheafificationOfPresheavesOfModules
import Formalization.Books.Sheaves.Unit22.Modules
import Formalization.Books.Sheaves.Unit24.Modules
import Formalization.Books.Sheaves.Unit25.RingedSpaces
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Sheaves on Spaces, Chapter 26: Morphisms of ringed spaces and modules

This file formalizes `books/sheaves.tex:3108-3268`.  The constructions reuse
the canonical module and ringed-space interfaces from Chapters 24 and 25;
the declarations below add only the ringed-space-specific source interface.

The literal equality of functors in the source is represented by Mathlib's
canonical natural isomorphism.  Equalities of module objects are stated as
usable `ModuleCat` isomorphisms, retaining the scalar structure.
-/

namespace Formalization.Books.Sheaves.Unit26

open CategoryTheory TopologicalSpace
open Formalization.Books.Sheaves.Unit10

universe v

noncomputable section

/-! ## Ringed spaces and module functors -/

abbrev RingedSpace := Formalization.Books.Sheaves.Unit25.RingedSpace

abbrev RingedSpaceHom := Formalization.Books.Sheaves.Unit25.RingedSpaceHom

/-! The ringed-space scalar map and module functors. -/

/-- The sheaf-of-rings map corresponding to `f♯`. -/
noncomputable def ringedSpacePullbackRingMap {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    (Formalization.Books.Sheaves.Unit24.sheafRingPullback f.continuous).obj
      Y.structureSheaf ⟶
      X.structureSheaf :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f.continuous).homEquiv
    Y.structureSheaf X.structureSheaf |>.symm f.sharp

/-- The inverse-image module over the pulled-back structure sheaf. -/
noncomputable def ringedSpaceInverseImageModule {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (Formalization.Books.Sheaves.Unit24.sheafRingUnit
        f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    Mod Y.structureSheaf ⥤
      Mod ((Formalization.Books.Sheaves.Unit24.sheafRingPullback
        f.continuous).obj Y.structureSheaf) :=
  Formalization.Books.Sheaves.Unit24.sheafModulePullbackAlong f.continuous
    (Formalization.Books.Sheaves.Unit24.sheafRingUnit
      f.continuous Y.structureSheaf)

/-- Pushforward of modules along a morphism of ringed spaces. -/
noncomputable def ringedSpaceModulePushforward {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    Mod X.structureSheaf ⥤ Mod Y.structureSheaf :=
  Formalization.Books.Sheaves.Unit24.sheafModulePushforwardAlong
    f.continuous f.sharp

/-- Pullback of modules along a morphism of ringed spaces. -/
noncomputable def ringedSpaceModulePullback {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    Mod Y.structureSheaf ⥤ Mod X.structureSheaf :=
  Formalization.Books.Sheaves.Unit24.sheafModulePullbackAlong
    f.continuous f.sharp

/-- The source's tensor description of the pullback module. -/
theorem ringedSpaceModulePullback_formula {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (G : Mod Y.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (Formalization.Books.Sheaves.Unit24.sheafRingUnit
        f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    Nonempty
      ((ringedSpaceModulePullback f).obj G ≅
        Formalization.Books.Sheaves.Unit20.tensorProductSheaf
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
        (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g) :=
  SheafOfModules.pushforwardComp g.sharp f.sharp

/-- The pushforward comparison as a source-facing existence statement. -/
theorem exists_ringedSpaceModulePushforwardCompIso
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) :
    Nonempty
      (ringedSpaceModulePushforward f ⋙ ringedSpaceModulePushforward g ≅
        ringedSpaceModulePushforward
          (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g)) := by
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
        (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g).continuous)
      (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g).sharp).IsRightAdjoint)] :
    ringedSpaceModulePullback
        (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g) ≅
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
        (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g).continuous)
      (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g).sharp).IsRightAdjoint)] :
    Nonempty
      (ringedSpaceModulePullback
          (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g) ≅
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
        (Formalization.Books.Sheaves.Unit25.RingedSpaceHom.comp f g) H F := by
  exact ψ ≫ (ringedSpaceModulePushforward g).map φ ≫
    (ringedSpaceModulePushforwardCompIso f g).hom.app F

/-! ## Stalk maps and the stalk pullback formula -/

/-- The scalar map on stalks of a ringed-space morphism. -/
noncomputable abbrev ringedSpaceModuleStalkScalarMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (x : X) :
    TopCat.Presheaf.stalk (C := RingCat.{v}) Y.structureSheaf.obj
        (f.continuous x) ⟶
      TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x :=
  Formalization.Books.Sheaves.Unit22.moduleSheafFMapStalkScalarMap f.sharp x

/-- The target stalk module with scalars restricted along `f♯_x`. -/
noncomputable abbrev ringedSpaceModuleStalkTarget
    {X Y : RingedSpace.{v}} {f : RingedSpaceHom X Y}
    (F : Mod X.structureSheaf) (x : X) :=
  Formalization.Books.Sheaves.Unit22.moduleSheafFMapStalkTarget f.sharp F x

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
  Formalization.Books.Sheaves.Unit22.moduleSheafFMapStalkMap f.sharp φ x

/-! The source's stalk tensor is represented by the stalk of the canonical
sheaf tensor product.  This is the project-wide `RingCat` representation of
the tensor expression while retaining its full `O_{X,x}`-module structure. -/

/-- The stalk-level extension of scalars in the source's pullback formula. -/
noncomputable def ringedSpaceModulePullbackStalkTensor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (x : X)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (Formalization.Books.Sheaves.Unit24.sheafRingUnit
        f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    ModuleCat (↑(TopCat.Presheaf.stalk (C := RingCat.{v})
      X.structureSheaf.obj x)) :=
  ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v})
      X.structureSheaf.obj x)
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
      (Formalization.Books.Sheaves.Unit20.tensorProductSheaf
        (ringedSpacePullbackRingMap f)
        ((ringedSpaceInverseImageModule f).obj G)).val.presheaf x))

/-- The stalk of the pullback module is the source's stalk tensor module. -/
theorem ringedSpaceModulePullback_stalk_formula
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (x : X)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      (Formalization.Books.Sheaves.Unit24.sheafRingUnit
        f.continuous Y.structureSheaf)).IsRightAdjoint)] :
    Nonempty
      (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v})
          X.structureSheaf.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
            ((ringedSpaceModulePullback f).obj G).val.presheaf x)) ≅
        ringedSpaceModulePullbackStalkTensor f G x) := by
  sorry

end

end Formalization.Books.Sheaves.Unit26
