import Formalization.Books.Cohomology.Unit13
import Formalization.Books.Topology.Unit17
import Formalization.Books.Sheaves.Unit21.ContinuousMaps
import Formalization.Books.Sheaves.Unit23.Infrastructure
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cohomology of Sheaves, Chapter 14: proper base change in topology

This file records the fibre comparison, the derived-category base-change
interface, the proper base-change isomorphism, and the set-valued statement
from the source section.  The categorical objects are the existing Mathlib
sheaf and derived-category constructions; the difficult comparison proofs are
left as theorem interfaces for the proof stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Set
open TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit13
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit17
open Formalization.Books.Homology.Unit03
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit21
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Topology.Unit17

universe v u

namespace Formalization.Books.Cohomology.Unit14

/-! ## Fibres and cartesian squares -/

/-- The fibre of a continuous map over a point, with its subspace topology. -/
def topologicalFiber {X Y : TopCat.{v}} (f : X ⟶ Y) (y : Y) : TopCat.{v} :=
  TopCat.of (f ⁻¹' ({y} : Set Y))

/-- The canonical inclusion of a fibre into the source. -/
def topologicalFiberInclusion {X Y : TopCat.{v}} (f : X ⟶ Y) (y : Y) :
    topologicalFiber f y ⟶ X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

/-- A cartesian square of topological spaces, with the source's notation. -/
structure TopologicalBaseChangeSquare where
  X' : TopCat.{v}
  X : TopCat.{v}
  Y' : TopCat.{v}
  Y : TopCat.{v}
  g' : X' ⟶ X
  f' : X' ⟶ Y'
  g : Y' ⟶ Y
  f : X ⟶ Y
  comm : g' ≫ f = f' ≫ g
  isPullback : IsPullback g' f' f g

/-- The map between fibres induced by a cartesian square. -/
def topologicalFiberMap (S : TopologicalBaseChangeSquare) (y' : S.Y') :
    topologicalFiber S.f' y' ⟶ topologicalFiber S.f (S.g y') :=
  TopCat.ofHom
    { toFun := fun x =>
        ⟨S.g' x,
          by
            have hcomm := congrArg (fun h => h x) S.comm
            change S.f (S.g' x) = S.g (S.f' x) at hcomm
            have hx : S.f' (x : S.X') = y' := by
              have hxmem := x.property
              change S.f' (x : S.X') ∈ ({y'} : Set S.Y') at hxmem
              simpa only [mem_singleton_iff] using hxmem
            exact hcomm.trans (congrArg S.g hx)⟩
      continuous_toFun :=
        (S.g'.hom.continuous.comp continuous_subtype_val).subtype_mk (by
          intro x
          have hcomm := congrArg (fun h => h x) S.comm
          change S.f (S.g' x) = S.g (S.f' x) at hcomm
          have hx : S.f' (x : S.X') = y' := by
            have hxmem := x.property
            change S.f' (x : S.X') ∈ ({y'} : Set S.Y') at hxmem
            simpa only [mem_singleton_iff] using hxmem
          exact hcomm.trans (congrArg S.g hx)) }

/-- The fibre homeomorphism supplied by the cartesian-square property. -/
structure TopologicalFiberHomeomorphData
    (S : TopologicalBaseChangeSquare) (y' : S.Y') where
  homeomorph : Homeomorph (S.f' ⁻¹' ({y'} : Set S.Y'))
    (S.f ⁻¹' ({S.g y'} : Set S.Y))
  induced_map : homeomorph.toFun = topologicalFiberMap S y'

theorem exists_topologicalFiberHomeomorphData
    (S : TopologicalBaseChangeSquare) (y' : S.Y') :
    Nonempty (TopologicalFiberHomeomorphData S y') := by
  sorry

/-! ## The ringed-space stalk and fibre interfaces -/

/-- The ring of functions at a point of a ringed space. -/
abbrev ringedSpaceStalkRing (Y : RingedSpace.{v}) (y : Y) : Type v :=
  TopCat.Presheaf.stalk (C := RingCat.{v}) Y.structureSheaf.obj y

/-- Taking a stalk is exact for sheaves of modules. -/
theorem sheafModuleStalk_isExact (Y : RingedSpace.{v}) (y : Y) :
    IsExact (sheafModuleStalkFunctor Y.structureSheaf y) := by
  sorry

/-- The exact stalk functor used to interpret the stalk of a derived
pushforward. -/
noncomputable def ringedSpaceModuleStalkExactFunctor
    (Y : RingedSpace.{v}) (y : Y) :
    Mod Y.structureSheaf ⥤ₑ ModuleCat.{v} (ringedSpaceStalkRing Y y) :=
  ⟨sheafModuleStalkFunctor Y.structureSheaf y,
    sheafModuleStalk_isExact Y y⟩

/-- The derived stalk functor on the bounded-below derived category. -/
noncomputable def ringedSpaceModuleDerivedStalk
    (Y : RingedSpace.{v}) (y : Y) :
    DPlus (Mod Y.structureSheaf) ⥤
      DPlus (ModuleCat.{v} (ringedSpaceStalkRing Y y)) :=
  ObjectProperty.lift
    (derivedPlusProperty (ModuleCat.{v} (ringedSpaceStalkRing Y y)))
    (DerivedCategory.Plus.ι (C := Mod Y.structureSheaf) ⋙
      exactDerivedFunctor (ringedSpaceModuleStalkExactFunctor Y y))
    (exactDerivedFunctor_preserves_derivedPlus
      (ringedSpaceModuleStalkExactFunctor Y y))

/-- The topological fibre of a morphism of ringed spaces, endowed with the
pullback of the structure sheaf. -/
def ringedSpaceFiber {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (y : Y) : RingedSpace :=
  { carrier := topologicalFiber f.continuous y
    structureSheaf :=
      (algebraicSheafPullback RingCat
        (topologicalFiberInclusion f.continuous y)).obj X.structureSheaf }

/-- The canonical morphism from a ringed-space fibre to the original space. -/
noncomputable def ringedSpaceFiberInclusion
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (y : Y) :
    RingedSpaceHom (ringedSpaceFiber f y) X :=
  { continuous := topologicalFiberInclusion f.continuous y
    sharp := algebraicSheafUnit (C := RingCat)
      (topologicalFiberInclusion f.continuous y) X.structureSheaf }

/-- The restriction of a module complex to the fibre, expressed by the
canonical ringed-space pullback. -/
noncomputable def ringedSpaceModuleFiberRestriction
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (y : Y)
    [((SheafOfModules.pushforward
      (F := Opens.map (ringedSpaceFiberInclusion f y).continuous)
      (ringedSpaceFiberInclusion f y).sharp).IsRightAdjoint)] :
    Mod X.structureSheaf ⥤ Mod (ringedSpaceFiber f y).structureSheaf :=
  ringedSpaceModulePullback (ringedSpaceFiberInclusion f y)

/-- Derived sections on the fibre after restricting a sheaf of modules. -/
structure RingedSpaceModuleFiberDerivedSectionsData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (y : Y) where
  functor : DPlus (Mod X.structureSheaf) ⥤
      DPlus (ModuleCat.{v} (ringedSpaceStalkRing Y y))

theorem exists_ringedSpaceModuleFiberDerivedSectionsData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (y : Y) :
    Nonempty (RingedSpaceModuleFiberDerivedSectionsData f y) := by
  sorry

noncomputable def ringedSpaceModuleFiberDerivedSections
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (y : Y) :
    DPlus (Mod X.structureSheaf) ⥤
      DPlus (ModuleCat.{v} (ringedSpaceStalkRing Y y)) :=
  (Classical.choice (exists_ringedSpaceModuleFiberDerivedSectionsData f y)).functor

/-! ## The ringed-space proper base-change lemma -/

theorem proper_base_change_stalk_iso
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (y : Y)
    (hclosed : IsClosedMap f.continuous)
    (hseparated : IsSeparatedMap f.continuous)
    (hfiber : IsCompact (f.continuous ⁻¹' ({y} : Set Y)))
    (E : DPlus (Mod X.structureSheaf))
    [((SheafOfModules.pushforward
      (F := Opens.map (ringedSpaceFiberInclusion f y).continuous)
      (ringedSpaceFiberInclusion f y).sharp).IsRightAdjoint)] :
    Nonempty
      ((ringedSpaceModuleDerivedStalk Y y).obj
        ((ringedSpaceModuleDerivedPushforward f).obj E) ≅
        (ringedSpaceModuleFiberDerivedSections f y).obj E) := by
  sorry

/-! ## Derived base change for topological spaces -/

/-- Pullback of abelian sheaves is exact. -/
theorem abelianSheafPullback_isExact {X Y : TopCat.{v}} (g : X ⟶ Y) :
    IsExact (abelianSheafPullback g) := by
  sorry

noncomputable def abelianSheafPullbackExactFunctor
    {X Y : TopCat.{v}} (g : X ⟶ Y) : Ab Y ⥤ₑ Ab X :=
  ⟨abelianSheafPullback g, abelianSheafPullback_isExact g⟩

/-- The derived inverse-image functor on bounded-below derived categories of
abelian sheaves. -/
noncomputable def abelianSheafDerivedPullback
    {X Y : TopCat.{v}} (g : X ⟶ Y) :
    DPlus (Ab Y) ⥤ DPlus (Ab X) :=
  ObjectProperty.lift (derivedPlusProperty (Ab X))
    (DerivedCategory.Plus.ι (C := Ab Y) ⋙
      exactDerivedFunctor (abelianSheafPullbackExactFunctor g))
    (exactDerivedFunctor_preserves_derivedPlus
      (abelianSheafPullbackExactFunctor g))

/-- The derived direct image of abelian sheaves. -/
noncomputable def abelianSheafDerivedPushforward
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    DPlus (Ab X) ⥤ DPlus (Ab Y) :=
  rightDerivedFunctorOfLeftExact
    (Formalization.Books.Cohomology.Unit02.abelianSheafPushforward f)
    (Formalization.Books.Cohomology.Unit02.abelianSheafPushforward_isLeftExact f)

/-- Source and target of the derived proper-base-change map. -/
noncomputable def properBaseChangeSourceFunctor
    (S : TopologicalBaseChangeSquare) :
    DPlus (Ab S.X) ⥤ DPlus (Ab S.Y') :=
  abelianSheafDerivedPushforward S.f ⋙
    abelianSheafDerivedPullback S.g

noncomputable def properBaseChangeTargetFunctor
    (S : TopologicalBaseChangeSquare) :
    DPlus (Ab S.X) ⥤ DPlus (Ab S.Y') :=
  abelianSheafDerivedPullback S.g' ⋙
    abelianSheafDerivedPushforward S.f'

/-- The canonical derived base-change transformation for a topological
cartesian square. -/
structure TopologicalBaseChangeMapData
    (S : TopologicalBaseChangeSquare) where
  transformation :
    properBaseChangeSourceFunctor S ⟶ properBaseChangeTargetFunctor S

theorem exists_topologicalBaseChangeMap
    (S : TopologicalBaseChangeSquare) :
    Nonempty (TopologicalBaseChangeMapData S) := by
  sorry

noncomputable def topologicalBaseChangeMap
    (S : TopologicalBaseChangeSquare) :
    properBaseChangeSourceFunctor S ⟶ properBaseChangeTargetFunctor S :=
  (Classical.choice (exists_topologicalBaseChangeMap S)).transformation

/-- Proper base change for bounded-below complexes of abelian sheaves. -/
theorem proper_base_change
    (S : TopologicalBaseChangeSquare)
    (hproper : IsProperTopologicalMap (S.f : S.X → S.Y))
    (E : DPlus (Ab S.X)) :
    IsIso ((topologicalBaseChangeMap S).app E) := by
  sorry

/-! ## Proper base change for sheaves of sets -/

abbrev SetSheaf (X : TopCat.{v}) := TopCat.Sheaf (Type v) X

/-- The sheaf-level comparison in the set-valued proper base-change theorem. -/
structure SetSheafProperBaseChangeData
    (S : TopologicalBaseChangeSquare) (F : SetSheaf S.X) where
  iso :
    (pullbackSheaf S.g).obj ((pushforwardSheaf S.f).obj F) ≅
      (pushforwardSheaf S.f').obj ((pullbackSheaf S.g').obj F)

theorem exists_setSheafProperBaseChangeData
    (S : TopologicalBaseChangeSquare)
    (hproper : IsProperTopologicalMap (S.f : S.X → S.Y))
    (F : SetSheaf S.X) :
    Nonempty (SetSheafProperBaseChangeData S F) := by
  sorry

noncomputable def setSheafProperBaseChangeIso
    (S : TopologicalBaseChangeSquare)
    (hproper : IsProperTopologicalMap (S.f : S.X → S.Y))
    (F : SetSheaf S.X) :
    (pullbackSheaf S.g).obj ((pushforwardSheaf S.f).obj F) ≅
      (pushforwardSheaf S.f').obj ((pullbackSheaf S.g').obj F) :=
  (Classical.choice (exists_setSheafProperBaseChangeData S hproper F)).iso

end Formalization.Books.Cohomology.Unit14
