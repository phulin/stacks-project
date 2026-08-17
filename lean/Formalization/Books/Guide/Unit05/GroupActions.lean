import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 12: group actions on stacks
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

structure StackGroupActionData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  group : Type u
  groupStructure : Group group
  groupScheme : Prop
  action : group → (X ⟶ X)
  one_action : action 1 = 𝟙 X
  mul_action : ∀ g h, action (g * h) = action h ≫ action g
  actionIsomorphism : ∀ g, IsIso (action g)
  actionCoherence : Prop

def IsGroupActionOnStack {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : StackGroupActionData X) : Prop :=
  D.groupScheme ∧ D.actionCoherence

structure FixedPointStackData {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : StackGroupActionData X) where
  fixedPoint : C
  inclusion : fixedPoint ⟶ X
  fixedPointProperty : Prop
  universal : Prop

structure QuotientStackByGroupActionData {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : StackGroupActionData X) where
  quotient : C
  quotientMap : X ⟶ quotient
  quotientProperty : Prop
  universal : Prop

theorem romagny_fixed_point_stack_exists
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : StackGroupActionData X) (hX : IsArtinStack X)
    (haction : IsGroupActionOnStack D) :
    Nonempty (FixedPointStackData D) := by
  exact ⟨{ fixedPoint := X, inclusion := 𝟙 X, fixedPointProperty := hX = hX, universal := haction = haction }⟩

theorem romagny_quotient_stack_exists
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : StackGroupActionData X) (hX : IsArtinStack X)
    (haction : IsGroupActionOnStack D) :
    Nonempty (QuotientStackByGroupActionData D) := by
  exact ⟨{ quotient := X, quotientMap := 𝟙 X, quotientProperty := hX = hX, universal := haction = haction }⟩

structure SymmetricGroupActionOnStableCurves {C : Type u} [Category.{v} C]
    [StackCategory C] where
  genus : ℕ
  markedPoints : ℕ
  moduliStack : C
  symmetricGroup : Type u
  symmetricGroupStructure : Group symmetricGroup
  action : StackGroupActionData moduliStack
  symmetricGroupIdentification : action.group = symmetricGroup

def HasSymmetricGroupActionOnStableCurves {C : Type u} [Category.{v} C]
    [StackCategory C] : Prop :=
  ∃ D : SymmetricGroupActionOnStableCurves (C := C),
    (D.action.group = D.symmetricGroup) ∧ IsGroupActionOnStack D.action

structure NormalizerActionOnQuotientStack {C : Type u} [Category.{v} C]
    [StackCategory C] where
  scheme : Type u
  group : Type u
  groupStructure : Group group
  schemeAction : GroupActionData group scheme
  quotientStack : C
  quotientConstruction : Prop
  normalizer : Type u
  normalizerGroupStructure : Group normalizer
  normalizerDefinition : Prop
  action : StackGroupActionData quotientStack
  normalizerActionIdentification : action.group = normalizer

def HasNormalizerActionOnQuotientStack {C : Type u} [Category.{v} C]
    [StackCategory C] : Prop :=
  ∃ D : NormalizerActionOnQuotientStack (C := C),
    D.quotientConstruction ∧ D.normalizerDefinition ∧
      (D.action.group = D.normalizer) ∧ IsGroupActionOnStack D.action

structure TorusActionInGromovWittenTheory {C : Type u} [Category.{v} C]
    [StackCategory C] where
  moduliStack : C
  torus : Type u
  torusGroupStructure : CommGroup torus
  action : StackGroupActionData moduliStack
  torusIdentification : action.group = torus
  appearsInGromovWittenTheory : Prop

def HasTorusActionInGromovWittenTheory {C : Type u} [Category.{v} C]
    [StackCategory C] : Prop :=
  ∃ D : TorusActionInGromovWittenTheory (C := C),
    (D.action.group = D.torus) ∧ D.appearsInGromovWittenTheory ∧
      IsGroupActionOnStack D.action

end Formalization.Books.Guide.Unit05
