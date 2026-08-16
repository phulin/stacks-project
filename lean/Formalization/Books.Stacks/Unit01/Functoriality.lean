import Formalization.«Books.Stacks».Unit01.StackificationGroupoids
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Over

/-!
# Stacks, Chapter 1, Section 12: functoriality for stacks

The reindexing construction is expressed using Mathlib's pseudofunctor
composition.  The localization construction is recorded by data structures
whose fields expose the mathematical properties used by the chapter.
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe v' v u' u w' w

abbrev FixedFiberedCategory (C : Type u) [Category.{v} C] :=
  Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}

def pushforwardFiberedCategory {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory D) : FixedFiberedCategory C :=
  Pseudofunctor.comp u.op.toPseudofunctor S

theorem pushforward_fibre {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory D) (U : C) :
    Fiber (pushforwardFiberedCategory u S) U = Fiber S (u.obj U) := by
  sorry

def PushforwardStack {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory D) (J : GrothendieckTopology C) : Prop :=
  Stack (pushforwardFiberedCategory u S) J

theorem stack_pushforward {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (u : C ⥤ D)
    (S : FixedFiberedCategory D) (hS : Stack S K)
    (hu : u.IsContinuous J K) :
    PushforwardStack u S J := by
  sorry

theorem stack_in_groupoids_pushforward {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (u : C ⥤ D)
    (S : FixedFiberedCategory D) (hS : StackInGroupoids S K)
    (hu : u.IsContinuous J K) :
    StackInGroupoids (pushforwardFiberedCategory u S) J := by
  sorry

structure PullbackPrecategoryObject {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) where
  object : Pseudofunctor.CoGrothendieck S
  base : D
  anchor : base ⟶ u.obj object.base

structure PullbackPrecategoryMorphism {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (x y : PullbackPrecategoryObject u S) where
  base : x.base ⟶ y.base
  object : x.object ⟶ y.object
  commutes : x.anchor ≫ u.map object.base = base ≫ y.anchor

def rightCartesianSystem {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) {x y : PullbackPrecategoryObject u S}
    (f : PullbackPrecategoryMorphism u S x y) : Prop :=
  (∃ h : x.base = y.base, f.base = eqToHom h) ∧
    IsStronglyCartesian (Pseudofunctor.CoGrothendieck.forget S)
      f.object.base f.object

structure RightMultiplicativeSystem {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) where
  member : ∀ {x y : PullbackPrecategoryObject u S},
    PullbackPrecategoryMorphism u S x y → Prop
  member_iff : ∀ {x y : PullbackPrecategoryObject u S}
    (f : PullbackPrecategoryMorphism u S x y),
    member f ↔ rightCartesianSystem u S f
  identities : Prop
  composition : Prop
  rightOre : Prop
  rightCancellation : Prop

theorem right_multiplicative_system {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) [HasFiniteProducts C] [HasEqualizers C]
    [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (RightMultiplicativeSystem u S) := by
  sorry

structure PullbackFiberedData {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) where
  value : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{w, w}
  projection : Prop
  isLocalization : Prop

theorem fibred_category_pullback {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) [HasFiniteProducts C] [HasEqualizers C]
    [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (PullbackFiberedData u S) := by
  sorry

theorem fibred_groupoids_category_pullback
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (u : C ⥤ D) (S : FixedFiberedCategory C) (hS : FiberwiseGroupoid S)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    ∃ P : PullbackFiberedData u S, FiberwiseGroupoid P.value := by
  sorry

structure PullbackStackData {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (K : GrothendieckTopology D) where
  value : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{w, w}
  isStack : Stack value K
  isStackification : Prop

noncomputable def pullbackStackification {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (K : GrothendieckTopology D)
    (h : Nonempty (PullbackStackData u S K)) : FixedFiberedCategory D :=
  (Classical.choice h).value

theorem adjunction_pullback_pushforward
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (u : C ⥤ D) (S : FixedFiberedCategory C) (T : FixedFiberedCategory D)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Nonempty (PullbackFiberedData u S)) :
    Nonempty
      ((S ⟶ pushforwardFiberedCategory u T) ≃
        ((Classical.choice h).value ⟶ T)) := by
  sorry

theorem pullback_stack_exists {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (K : GrothendieckTopology D)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (PullbackStackData u S K) := by
  sorry

theorem adjunction_pullback_pushforward_stacks
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) (S : FixedFiberedCategory C) (T : FixedFiberedCategory D)
    (hS : Stack S J) (hT : Stack T K) (hu : u.IsContinuous J K)
    [HasFiniteProducts C] [HasEqualizers C] [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (PullbackStackData u S K) := by
  sorry

theorem technical_pullback_stackification
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) (S S' : FixedFiberedCategory C)
    (hS : Stack S J) (hS' : Stack S' J)
    (η : S ⟶ S') :
    Nonempty (PullbackStackData u S' K) →
      Nonempty (PullbackStackData u S K) := by
  sorry

structure BiggerSiteAssumptions {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) where
  fullyFaithful : u.FullyFaithful
  continuous : u.IsContinuous J K
  cocontinuous : u.IsCocontinuous J K

structure BiggerSiteResult {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (S : FixedFiberedCategory C) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) where
  pullback : PullbackStackData u S K
  canonical : S ⟶ pushforwardFiberedCategory u pullback.value
  equivalence : FiberwiseEquivalence canonical
  fullOnMorphisms : Prop

theorem bigger_site {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (h : BiggerSiteAssumptions u J K) (S : FixedFiberedCategory C)
    (hS : Stack S J) [HasFiniteProducts C] [HasEqualizers C]
    [PreservesFiniteProducts u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    Nonempty (BiggerSiteResult u S J K) := by
  sorry

end Formalization.«Books.Stacks».Unit01
