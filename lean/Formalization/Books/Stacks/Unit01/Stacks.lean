import Formalization.Books.Stacks.Unit01.Descent

/-!
# Stacks, Chapter 1, Section 4: stacks
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v u

structure StackObject (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  value : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}
  isStack : Stack value J

structure StackMorphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (X Y : StackObject C J) where
  map : FiberedMorphism X.value Y.value

def IsStack2Morphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X Y : StackObject C J}
    (f g : StackMorphism X Y) : Prop :=
  Nonempty (f.map ⟶ g.map)

def HasFibrewiseRepresentatives {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) : Prop :=
    ∀ U : C, ∃ representatives : Set (Fiber F U),
    ∀ X : Fiber F U, ∃ Y, Y ∈ representatives ∧ Nonempty (X ≅ Y)

structure SmallSubstackData {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  inclusion : FiberedMorphism value F
  isStack : Stack value J
  fullyFaithful : FiberwiseFullyFaithful inclusion
  essentiallySurjective : FiberwiseEssentiallySurjective inclusion
  hasFibrewiseRepresentatives : HasFibrewiseRepresentatives value

theorem small_stack_substack_exists {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : Stack F J) (hrepresentatives : HasFibrewiseRepresentatives F) :
    Nonempty (SmallSubstackData F J) := by
  refine ⟨⟨F, 𝟙 F, hF, ?_, ?_, hrepresentatives⟩⟩
  · intro U
    change Nonempty ((𝟭 _).FullyFaithful)
    exact ⟨Functor.FullyFaithful.id _⟩
  · intro U
    change Functor.EssSurj (𝟭 _)
    infer_instance

theorem stack_morphism_presheaves_are_sheaves {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C} [F.IsStack J]
    {U : C} (x y : Fiber F U) :
    Presheaf.IsSheaf (J.over U) (F.presheafHom x y) := by
  exact IsPrestack.isSheaf J x y

theorem stack_iff_effective_descent {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) :
    Stack F J ↔
      ∀ (U : C) (R : Sieve U), R ∈ J U →
        (F.toDescentData (fun f : R.arrows.category ↦ f.obj.hom)).IsEquivalence := by
  constructor
  · intro h U R hR
    let : F.IsStack J := h
    exact (F.isStackFor' R hR).isEquivalence
  · intro h
    -- TODO: apply `Pseudofunctor.IsStack.of_isStackFor`; this sieve-indexed
    -- formulation deliberately matches its universe, unlike the former fixed
    -- `Type t` family quantifier.
    sorry

theorem substack_is_stack {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    [F.IsStack J] (S : Substack F J) :
    Stack S.value J := by
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
    ∃ P : TwoFiberProductCone F G H f g, Stack P.apex J := by
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
    [F.IsStack J] [G.IsStack J]
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

end Formalization.Books.Stacks.Unit01
