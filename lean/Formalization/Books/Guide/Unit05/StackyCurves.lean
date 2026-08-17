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
  coarseSpace : C
  coarseSpaceProjective : CoarseSpaceIsProjective target
  moduliStack : C
  parameterizesStableMaps : Prop
  properOverBase : Prop

theorem compactification_of_stable_maps_to_tame_dm_stacks
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : StableMapCompactificationData (C := C)) :
    IsProperStack D.moduliStack := by
  sorry

structure DeligneMumfordAnalyticCurve (C : Type u) [Category.{v} C]
    [StackCategory C] where
  curve : C
  analytic : Prop
  deligneMumford : IsDeligneMumfordStack curve
  uniformizationSpace : Type u
  uniformizationGroup : Type u
  groupStructure : Group uniformizationGroup
  uniformizationMap : uniformizationSpace → Point curve
  uniformizes : Prop

theorem uniformization_of_deligne_mumford_analytic_curves
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : DeligneMumfordAnalyticCurve C) (hanalytic : D.analytic) :
    D.uniformizes := by
  sorry

end Formalization.Books.Guide.Unit05
