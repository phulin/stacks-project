import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 7: rigidification
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

structure RigidificationInput {C : Type u} [Category.{v} C]
    [StackCategory C] (X S : C) where
  subgroupPoints : C → Type u
  subgroupGroup : ∀ T, Group (subgroupPoints T)
  overBase : Prop
  flat : Prop
  finitelyPresented : Prop
  separated : Prop
  objectsOver : C → Type u
  automorphisms : ∀ T : C, objectsOver T → Type u
  embedding : ∀ (T : C) (ξ : objectsOver T),
    subgroupPoints T → automorphisms T ξ
  embeddingInjective : ∀ (T : C) (ξ : objectsOver T),
    Function.Injective (embedding T ξ)
  compatibleWithPullback : Prop

structure RigidificationWitness {C : Type u} [Category.{v} C]
    [StackCategory C] {X S : C} (D : RigidificationInput X S) where
  quotient : C
  rigidificationMap : X ⟶ quotient
  quotientIsAlgebraicStack : IsArtinStack quotient
  isFppfGerbe : Prop
  rigidifiedAutomorphisms : ∀ T : C, D.objectsOver T → Type u
  automorphismMap : ∀ (T : C) (ξ : D.objectsOver T),
    D.automorphisms T ξ → rigidifiedAutomorphisms T ξ
  automorphismMapSurjective : ∀ (T : C) (ξ : D.objectsOver T),
    Function.Surjective (automorphismMap T ξ)
  automorphismKernel : ∀ (T : C) (ξ : D.objectsOver T),
    Set (D.automorphisms T ξ)
  automorphismKernelIsImageOfSubgroup :
    ∀ (T : C) (ξ : D.objectsOver T) (a : D.automorphisms T ξ),
      a ∈ automorphismKernel T ξ ↔
        ∃ h : D.subgroupPoints T, D.embedding T ξ h = a

theorem rigidification_exists
    {C : Type u} [Category.{v} C] [StackCategory C] {X S : C}
    (D : RigidificationInput X S) :
    Nonempty (RigidificationWitness D) := by
  sorry

structure RigidificationGroupActionData {C : Type u} [Category.{v} C]
    [StackCategory C] (X S : C) where
  group : Type u
  groupStructure : Group group
  action : group → C → C
  actionOne : ∀ Y : C, action 1 Y = Y
  actionMul : ∀ (g h : group) (Y : C), action (g * h) Y = action g (action h Y)
  rigidification : RigidificationInput X S

structure RigidificationActionCompatibility {C : Type u} [Category.{v} C]
    [StackCategory C] {X S : C}
    (D : RigidificationGroupActionData X S) where
  inducedActionOnRigidification : D.group → C → C
  commutesWithRigidification : Prop

theorem group_actions_compatible_with_rigidification
    {C : Type u} [Category.{v} C] [StackCategory C] {X S : C}
    (D : RigidificationGroupActionData X S) :
    Nonempty (RigidificationActionCompatibility D) := by
  sorry

structure RigidificationAlternativeInterpretations {C : Type u}
    [Category.{v} C] [StackCategory C] where
  rigidification : Prop

structure RigidificationApplications where
  alternativeInterpretationOne : Prop
  alternativeInterpretationTwo : Prop
  gluingAlongClosedSubstacks : Prop
  takingRootsOfLineBundles : Prop

theorem rigidification_alternative_interpretations_and_applications
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : RigidificationAlternativeInterpretations (C := C)) :
    Nonempty RigidificationApplications := by
  sorry

structure NormalFlatInertiaSubgroup {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  subgroupStack : C
  subgroupOfInertia : Prop
  flat : Prop
  finitelyPresented : Prop
  separated : Prop
  normal : Prop
  rigidification : C
  quotientMap : X ⟶ rigidification

structure NormalNoncentralRigidificationConclusion {C : Type u}
    [Category.{v} C] [StackCategory C] {X : C}
    (D : NormalFlatInertiaSubgroup X) where
  quotientMap : X ⟶ D.rigidification
  isFppfGerbe : Prop
  handlesNoncentralCase : Prop

theorem tame_stack_normal_noncentral_rigidification
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : NormalFlatInertiaSubgroup X) (htame : IsTameArtinStack X)
    (hnormal : D.normal) :
    Nonempty (NormalNoncentralRigidificationConclusion D) := by
  sorry

end Formalization.Books.Guide.Unit05
