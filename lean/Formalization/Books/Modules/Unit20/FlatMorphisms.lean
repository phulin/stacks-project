import Formalization.Books.Modules.Unit16.TensorProduct
import Formalization.Books.Injectives.Unit08.ModulesOnRingedSite
import Formalization.Books.Sheaves.Unit26.RingedSpaceModules
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.RingTheory.Flat.Basic

/-!
# Sheaves of Modules, Chapter 20, Section 1: Flat morphisms of ringed spaces

This file records the pointwise and global flatness definitions, the standard
open-immersion example, and the exactness statements from the source section.
The stalk module is Mathlib's canonical scalar restriction along the stalk map
of the structure sheaves.
-/

namespace Formalization.Books.Modules.Unit20

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Sheaves.Unit25
open Formalization.Books.Sheaves.Unit26

universe v

noncomputable section

/-! ## Flat morphisms -/

abbrev RingedSpace := Formalization.Books.Sheaves.Unit25.RingedSpace

abbrev RingedSpaceHom := Formalization.Books.Sheaves.Unit25.RingedSpaceHom

/-- The stalk of the target structure sheaf at the image of `x`. -/
abbrev targetStalk {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (x : X) :=
  TopCat.Presheaf.stalk (C := RingCat.{v}) Y.structureSheaf.obj
    (f.continuous x)

/-- The source structure-sheaf stalk, regarded as a module over the target
stalk through the stalk map induced by `f`. -/
noncomputable abbrev sourceStalkAsTargetModule
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (x : X) :
    ModuleCat (targetStalk f x) :=
  Formalization.Books.Sheaves.Unit22.moduleSheafFMapStalkTarget f.sharp
    (SheafOfModules.unit X.structureSheaf) x

/-- A morphism of ringed spaces is flat at `x` when its map on structure-sheaf
stalks makes the source stalk a flat module over the target stalk. -/
def flatAt {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (x : X) : Prop :=
  Nonempty (Formalization.Books.Injectives.Unit08.PointwiseFlatModule
    (targetStalk f x) (sourceStalkAsTargetModule f x))

/-- A morphism of ringed spaces is flat when it is flat at every point of its
source. -/
def flat {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) : Prop :=
  ∀ x : X, flatAt f x

/-- The pointwise definition unfolds to flatness of the scalar-restricted
source stalk module. -/
theorem flatAt_iff_stalkModule {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (x : X) :
    flatAt f x ↔ Nonempty (Formalization.Books.Injectives.Unit08.PointwiseFlatModule
      (targetStalk f x) (sourceStalkAsTargetModule f x)) :=
  Iff.rfl

/-- The global definition unfolds to pointwise flatness. -/
theorem flat_iff_forall_flatAt {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    flat f ↔ ∀ x : X, flatAt f x :=
  Iff.rfl

/-! ## Open immersions -/

/-- The canonical morphism from an open ringed subspace is flat. -/
theorem ringedOpenInclusion_flat (X : RingedSpace.{v}) (U : Opens X.carrier) :
    flat (Formalization.Books.Sheaves.Unit22.ringedOpenInclusion X U) := by
  sorry

/-! ## Pullback exactness -/

/-- Pullback along a flat morphism of ringed spaces is exact. -/
theorem pullback_isExact {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hf : flat f)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    Formalization.Books.Categories.Unit23.IsExact
      (Formalization.Books.Sheaves.Unit26.ringedSpaceModulePullback f) := by
  sorry

/-! ## Flat modules over a base -/

/-- An `O_X`-module is flat over `Y` at `x` when its stalk is flat over the
stalk of `O_Y` at the image of `x`. -/
def flatOverAt {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (x : X) : Prop :=
  Nonempty (Formalization.Books.Injectives.Unit08.PointwiseFlatModule
    (targetStalk f x)
    (Formalization.Books.Sheaves.Unit22.moduleSheafFMapStalkTarget f.sharp F x))

/-- An `O_X`-module is flat over `Y` when it is flat over `Y` at every point
of `X`. -/
def flatOver {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, flatOverAt f F x

/-- The pointwise definition of flatness over a base. -/
theorem flatOverAt_iff_stalkModule {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (F : Mod X.structureSheaf) (x : X) :
    flatOverAt f F x ↔
      Nonempty (Formalization.Books.Injectives.Unit08.PointwiseFlatModule
        (targetStalk f x)
        (Formalization.Books.Sheaves.Unit22.moduleSheafFMapStalkTarget f.sharp F x)) :=
  Iff.rfl

/-- The global definition of flatness over a base. -/
theorem flatOver_iff_forall_flatOverAt {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (F : Mod X.structureSheaf) :
    flatOver f F ↔ ∀ x : X, flatOverAt f F x :=
  Iff.rfl

/-! ## Exactness after tensoring -/

/-! ## The tensor-pullback functor in the commutative model -/

/-
The source's final functor uses tensor products over the structure sheaf.  The
project's canonical tensor construction is the commutative-ring-sheaf model
from Chapter 16.  The following declarations expose that construction without
introducing a second tensor-product implementation for the weaker `RingCat`
ringed-space interface.
-/

noncomputable def commutativePullbackTensorFunctor
    {X Y : TopCat.{v}} {OX : Formalization.Books.Sheaves.Unit17.CommRingSheaf X}
    {OY : Formalization.Books.Sheaves.Unit17.CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf OY ⟶
      (Formalization.Books.Sheaves.Unit24.sheafRingPushforward f).obj
        (Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    (F : Formalization.Books.Sheaves.Unit17.CommRingSheafModule OX) :
    Formalization.Books.Sheaves.Unit17.CommRingSheafModule OY ⥤
      Formalization.Books.Sheaves.Unit17.CommRingSheafModule OX where
  obj G := Formalization.Books.Modules.Unit16.tensorProductSheaf OX
    ((Formalization.Books.Modules.Unit16.pullbackModule f α).obj G) F
  map φ := Formalization.Books.Modules.Unit16.tensorProductMap
    ((Formalization.Books.Modules.Unit16.pullbackModule f α).map φ) (𝟙 F)
  map_id G := by
    rw [(Formalization.Books.Modules.Unit16.pullbackModule f α).map_id]
    exact Formalization.Books.Modules.Unit16.tensorProductMap_id
  map_comp φ ψ := by
    rw [(Formalization.Books.Modules.Unit16.pullbackModule f α).map_comp]
    simpa using (Formalization.Books.Modules.Unit16.tensorProductMap_comp
      ((Formalization.Books.Modules.Unit16.pullbackModule f α).map φ)
      ((Formalization.Books.Modules.Unit16.pullbackModule f α).map ψ) (𝟙 F) (𝟙 F))

/-- Flatness over `Y` for a module in the commutative sheaf model. -/
def commutativeFlatOverAt
    {X Y : TopCat.{v}} {OX : Formalization.Books.Sheaves.Unit17.CommRingSheaf X}
    {OY : Formalization.Books.Sheaves.Unit17.CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf OY ⟶
      (Formalization.Books.Sheaves.Unit24.sheafRingPushforward f).obj
        (Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf OX))
    (F : Formalization.Books.Sheaves.Unit17.CommRingSheafModule OX) (x : X) : Prop :=
  Nonempty (Formalization.Books.Injectives.Unit08.PointwiseFlatModule
    (TopCat.Presheaf.stalk (C := RingCat.{v})
      (Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf OY).obj (f x))
      (Formalization.Books.Sheaves.Unit22.moduleSheafFMapStalkTarget α F x))

/-- The commutative sheaf-model form of the source's final exactness lemma. -/
theorem commutativePullbackTensor_flatOver_isExact
    {X Y : TopCat.{v}} {OX : Formalization.Books.Sheaves.Unit17.CommRingSheaf X}
    {OY : Formalization.Books.Sheaves.Unit17.CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf OY ⟶
      (Formalization.Books.Sheaves.Unit24.sheafRingPushforward f).obj
        (Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    (F : Formalization.Books.Sheaves.Unit17.CommRingSheafModule OX)
    (hF : ∀ x, commutativeFlatOverAt f α F x) :
    Formalization.Books.Categories.Unit23.IsExact
      (commutativePullbackTensorFunctor f α F) := by
  sorry

end

end Formalization.Books.Modules.Unit20
