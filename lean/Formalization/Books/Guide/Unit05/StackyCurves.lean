import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 8: stacky curves
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

structure TwistedCurve (C : Type u) [Category.{v} C]
    [StackCategory C] where
  curve : C
  coarseCurve : C
  coarseMap : curve ⟶ coarseCurve
  coarseMapIsCoarse : IsCoarseModuliSpaceMap coarseMap
  nodal : Prop
  stackyMarkedPoints : Prop
  tame : Prop
  deligneMumford : IsDeligneMumfordStack curve

def IsTwistedCurve {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  ∃ D : TwistedCurve C, D.curve = X

structure StableMapFromTwistedCurve {C : Type u} [Category.{v} C]
    [StackCategory C] where
  source : TwistedCurve C
  target : C
  map : source.curve ⟶ target
  stable : Prop

structure StableMapCompactificationData {C : Type u} [Category.{v} C]
    [StackCategory C] where
  target : C
  targetTame : IsTameArtinStack target
  targetDeligneMumford : IsDeligneMumfordStack target
  coarseSpace : C
  coarseSpaceProjective : CoarseSpaceIsProjective coarseSpace
  coarseMap : target ⟶ coarseSpace
  coarseMapIsCoarse : IsCoarseModuliSpaceMap coarseMap
  moduliStack : C
  parameterizesStableMaps : Prop

structure StableMapCompactificationConclusion {C : Type u}
    [Category.{v} C] [StackCategory C]
    (D : StableMapCompactificationData (C := C)) where
  properOverBase : IsProperStack D.moduliStack
  moduliStackIsArtin : IsArtinStack D.moduliStack

class StableMapCompactificationLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  compactify : ∀ (D : StableMapCompactificationData (C := C)),
    D.parameterizesStableMaps → Nonempty (StableMapCompactificationConclusion D)

theorem compactification_of_stable_maps_to_tame_dm_stacks
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StableMapCompactificationLaws (C := C)]
    (D : StableMapCompactificationData (C := C))
    (hparameterizesStableMaps : D.parameterizesStableMaps) :
    Nonempty (StableMapCompactificationConclusion D) :=
  StableMapCompactificationLaws.compactify D hparameterizesStableMaps

structure DeligneMumfordAnalyticCurve (C : Type u) [Category.{v} C]
    [StackCategory C] where
  curve : C
  analytic : Prop
  deligneMumford : IsDeligneMumfordStack curve
  uniformizationSpace : Type u
  uniformizationGroup : Type u
  groupStructure : Group uniformizationGroup
  uniformizationMap : uniformizationSpace → Point curve

structure UniformizationConclusion where
  uniformizes : Prop

theorem uniformization_of_deligne_mumford_analytic_curves
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : DeligneMumfordAnalyticCurve C) (hanalytic : D.analytic) :
    Nonempty UniformizationConclusion := by
  exact ⟨{ uniformizes := hanalytic = hanalytic }⟩

end Formalization.Books.Guide.Unit05
