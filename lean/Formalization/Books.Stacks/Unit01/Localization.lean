import Formalization.«Books.Stacks».Unit01.Functoriality
import Mathlib.CategoryTheory.Sites.Over

/-!
# Stacks, Chapter 1, Section 13: stacks and localization
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory
open Opposite

universe v' v u' u w

def RepresentableIsSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) : Prop :=
  Presheaf.IsSheaf J (CategoryTheory.yoneda.obj U)

structure LocalizationStackData {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) where
  value : FixedFiberedCategory C
  isStack : Stack value J
  localizationProjection : Prop

theorem when_localization_stack {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) :
    RepresentableIsSheaf J U ↔ Nonempty (LocalizationStackData J U) := by
  sorry

structure ConstructionAData {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    (S : FixedFiberedCategory (Over C U)) where
  value : FixedFiberedCategory C
  isStack : Stack value J
  underlyingCategory : Prop
  mapToLocalization : Prop

structure ConstructionBData {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    (T : FixedFiberedCategory C) where
  isStack : Stack T J
  mapToLocalization : Prop

def IsStackOverLocalization {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    {T : FixedFiberedCategory C} (B : ConstructionBData J U T) : Prop :=
  B.isStack ∧ B.mapToLocalization

theorem construction_b_is_stack_over_localization
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {U : C} {T : FixedFiberedCategory C}
    (B : ConstructionBData J U T) :
    IsStackOverLocalization J U B := by
  exact ⟨B.isStack, B.mapToLocalization⟩

structure LocalizationConstructionsEquivalence
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    (S : FixedFiberedCategory (Over C U)) where
  fromA : ConstructionAData J U S →
    Σ T : FixedFiberedCategory C, ConstructionBData J U T
  fromB : (Σ T : FixedFiberedCategory C, ConstructionBData J U T) →
    ConstructionAData J U S
  leftInverse : Prop
  rightInverse : Prop

theorem localize_stacks {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    (hU : RepresentableIsSheaf J U)
    (S : FixedFiberedCategory (Over C U))
    (hS : Stack S (J.over U)) :
    Nonempty (LocalizationConstructionsEquivalence J U S) := by
  sorry

end Formalization.«Books.Stacks».Unit01
