import Formalization.«Books.Stacks».Unit01.Descent

/-!
# Stacks, Chapter 1, Section 4: stacks
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory
open CategoryTheory.Pseudofunctor
open Opposite

universe t v u

structure StackObject (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  value : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u}
  isStack : Stack value J

structure StackMorphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (X Y : StackObject C J) where
  map : FiberedMorphism X.value Y.value

def IsStack2Morphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X Y : StackObject C J}
    (f g : StackMorphism X Y) : Prop :=
  ∀ U : C, Nonempty ((f.map.app (.mk (op U))).toFunctor ⟶
    (g.map.app (.mk (op U))).toFunctor)

def HasFibrewiseRepresentatives {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) : Prop :=
  ∀ U : C, ∃ representatives : Set (Fiber F U),
    ∀ X : Fiber F U, ∃ Y, Y ∈ representatives ∧ Nonempty (X ≅ Y)

theorem stack_iff_effective_descent {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) :
    Stack F J ↔
      ∀ (ι : Type t) (U : C) (X : ι → C) (f : ∀ i, X i ⟶ U),
        CoveringFamily J f → (F.toDescentData f).IsEquivalence := by
  sorry

theorem substack_is_stack {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    [F.IsStack J] (S : Substack F J) :
    ∃ G : FiberedCategory C, Stack G J := by
  sorry

theorem equivalent_fibred_categories_preserve_stack
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) :
    Stack F J ↔ Stack G J := by
  sorry

theorem two_fibre_product_of_stacks {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G H : FiberedCategory C}
    (hF : Stack F J) (hG : Stack G J) (hH : Stack H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H, Stack P.apex J := by
  sorry

theorem characterize_fully_faithful {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {F G : FiberedCategory C}
    (η : FiberedMorphism F G) [F.IsStack J] [G.IsStack J] :
    FiberwiseFullyFaithful η ↔
      ∀ (U : C) (x y : Fiber F U),
        Nonempty
          (F.presheafHom x y ≅
            G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
              ((η.app (.mk (op U))).toFunctor.obj y)) := by
  sorry

theorem characterize_essentially_surjective_when_fully_faithful
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseFullyFaithful η) :
    FiberwiseEssentiallySurjective η ↔
      ∀ (U : C) (y : Fiber G U),
        ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
          CoveringFamily J f ∧
            ∀ i, ∃ x : Fiber F (X i),
              Nonempty
                ((G.map (f i).op.toLoc).toFunctor.obj y ≅
                  (η.app (.mk (op (X i)))).toFunctor.obj x) := by
  sorry

end Formalization.«Books.Stacks».Unit01
