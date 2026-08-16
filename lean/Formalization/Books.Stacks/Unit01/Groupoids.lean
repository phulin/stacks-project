import Formalization.«Books.Stacks».Unit01.Stacks

/-!
# Stacks, Chapter 1, Section 5: stacks in groupoids
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory

universe t v' v u' u

def StackInGroupoids {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  FiberwiseGroupoid F ∧ Stack F J

structure GroupoidificationData {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  map : FiberedMorphism F value
  isStackInGroupoids : StackInGroupoids value J

structure StackInGroupoidsObject (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  value : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u}
  isStackInGroupoids : StackInGroupoids value J

theorem stack_in_groupoids_iff {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C} :
    StackInGroupoids F J ↔ FiberwiseGroupoid F ∧ Stack F J := Iff.rfl

theorem stack_groupoidification {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : Stack F J) : Nonempty (GroupoidificationData F J) := by
  sorry

theorem equivalent_stacks_in_groupoids_preserve
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) :
    StackInGroupoids F J ↔ StackInGroupoids G J := by
  sorry

def IsGroupoidTwoMorphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X Y : StackInGroupoidsObject C J}
    (f g : FiberedMorphism X.value Y.value) : Prop :=
  ∀ U : C, Nonempty ((f.app (.mk (Opposite.op U))).toFunctor ⟶
    (g.app (.mk (Opposite.op U))).toFunctor)

theorem two_fibre_product_of_stacks_in_groupoids
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C}
    (hF : StackInGroupoids F J) (hG : StackInGroupoids G J)
    (hH : StackInGroupoids H J) (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H, StackInGroupoids P.apex J := by
  sorry

end Formalization.«Books.Stacks».Unit01
