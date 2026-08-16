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
  value : FixedFiberedCategory.{v, u, w} C
  isStack : Stack value J
  localizationProjection :
    Pseudofunctor.CoGrothendieck value ⥤ Over C U
  localizationProjection_over :
    localizationProjection ⋙ Over.forget U =
      Pseudofunctor.CoGrothendieck.forget value
  localizationProjection_isEquivalence : localizationProjection.IsEquivalence

theorem when_localization_stack {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) :
    RepresentableIsSheaf J U ↔ Nonempty (LocalizationStackData J U) := by
  sorry

structure ConstructionAData {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    (S : FixedFiberedCategory.{v, max u v, w} (Over C U)) where
  isStackOverLocalization : Stack S (J.over U)
  value : FixedFiberedCategory.{v, u, w} C
  isStack : Stack value J
  underlyingEquivalence :
    Pseudofunctor.CoGrothendieck value ≌ Pseudofunctor.CoGrothendieck S
  mapToLocalization :
    Pseudofunctor.CoGrothendieck value ⥤ Over C U
  mapToLocalization_eq :
    mapToLocalization =
      underlyingEquivalence.functor ⋙ Pseudofunctor.CoGrothendieck.forget S
  mapOver :
    mapToLocalization ⋙ Over.forget U =
      Pseudofunctor.CoGrothendieck.forget value

structure ConstructionBData {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    (T : FixedFiberedCategory.{v, u, w} C) where
  isStack : Stack T J
  mapToLocalization :
    Pseudofunctor.CoGrothendieck T ⥤ Over C U
  mapOver :
    mapToLocalization ⋙ Over.forget U =
      Pseudofunctor.CoGrothendieck.forget T
  localizedValue : FixedFiberedCategory.{v, max u v, w} (Over C U)
  localizedStack : Stack localizedValue (J.over U)
  localizedEquivalence :
    Pseudofunctor.CoGrothendieck localizedValue ≌
      Pseudofunctor.CoGrothendieck T
  localizedIdentification :
    Pseudofunctor.CoGrothendieck.forget localizedValue =
      localizedEquivalence.functor ⋙ mapToLocalization

def IsStackOverLocalization {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    {T : FixedFiberedCategory C} (_B : ConstructionBData J U T) : Prop :=
  Stack _B.localizedValue (J.over U)

theorem construction_b_is_stack_over_localization
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {U : C} {T : FixedFiberedCategory C}
    (B : ConstructionBData J U T) :
    IsStackOverLocalization J U B := by
  exact B.localizedStack

structure LocalizationConstructionsEquivalence
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    (S : FixedFiberedCategory.{v, max u v, w} (Over C U)) where
  equivalence :
    ConstructionAData J U S ≃
      (Σ T : FixedFiberedCategory.{v, u, w} C, ConstructionBData J U T)

theorem localize_stacks {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    (hU : RepresentableIsSheaf J U)
    (S : FixedFiberedCategory.{v, max u v, w} (Over C U))
    (hS : Stack S (J.over U)) :
    Nonempty (LocalizationConstructionsEquivalence J U S) := by
  sorry

end Formalization.«Books.Stacks».Unit01
