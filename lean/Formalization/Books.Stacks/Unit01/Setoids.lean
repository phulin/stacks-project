import Formalization.«Books.Stacks».Unit01.Groupoids

/-!
# Stacks, Chapter 1, Section 6: stacks in setoids
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t v' v u' u

def StackInSetoids {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  FiberwiseSetoid F ∧ Stack F J

def StackInSets {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  FiberwiseSet F ∧ Stack F J

def ObjectIsoSetoid (K : Type u) [Category.{v} K] : Setoid K where
  r X Y := Nonempty (X ≅ Y)
  iseqv := {
    refl := fun X => ⟨Iso.refl X⟩
    symm := by
      intro X Y h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro X Y Z h₁ h₂
      rcases h₁ with ⟨e₁⟩
      rcases h₂ with ⟨e₂⟩
      exact ⟨e₁.trans e₂⟩ }

def ObjectIsomorphismClasses {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (U : C) :=
  Quotient (ObjectIsoSetoid (Fiber F U))

def RelativePair {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) (U : C)
    (y : Fiber G U) :=
  Σ x : Fiber F U, (η.app (.mk (op U))).toFunctor.obj x ⟶ y

structure TwoCartesianSquare {C : Type u} [Category.{v} C]
    (A B C' D : FiberedCategory C) where
  left : FiberedMorphism A B
  right : FiberedMorphism A C'
  top : FiberedMorphism B D
  bottom : FiberedMorphism C' D
  commutes : left ≫ top = right ≫ bottom
  isTwoPullback : Prop

def FiberwiseFaithful {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) : Prop :=
  ∀ U : C, (η.app (.mk (op U))).toFunctor.Faithful

structure RelativeSheafCondition {C : Type u} [Category.{v} C]
    (F G : FiberedCategory C) (J : GrothendieckTopology C) where
  map : FiberedMorphism F G
  targetIsGroupoidStack : StackInGroupoids G J
  fibresFaithful : FiberwiseFaithful map
  pairPresheavesAreSheaves : Prop

theorem stack_in_sets_iff_sheaf_condition {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) :
    StackInSets F J ↔ FiberwiseSet F ∧ Stack F J := Iff.rfl

theorem stack_in_setoids_characterization {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : FiberwiseSetoid F) :
    StackInSetoids F J ↔ Stack F J := by
  simp [StackInSetoids, hF]

theorem equivalent_stacks_in_setoids_preserve
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) :
    StackInSetoids F J ↔ StackInSetoids G J := by
  sorry

theorem two_fibre_product_of_stacks_in_setoids
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (hF : StackInSetoids F J)
    (hG : StackInSetoids G J) (hH : StackInSetoids H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H, StackInSetoids P.apex J := by
  sorry

theorem two_fibre_product_setoids_over_groupoid_stack
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (hF : StackInSetoids F J)
    (hG : StackInSetoids G J) (hH : StackInGroupoids H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H, StackInSetoids P.apex J := by
  sorry

theorem faithful_descent_for_stacks_in_groupoids
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A B C' D : FiberedCategory C} (sq : TwoCartesianSquare A B C' D)
    (hleft : FiberwiseEssentiallySurjective sq.left)
    (hright : FiberwiseFaithful sq.right) :
    FiberwiseFaithful sq.bottom := by
  sorry

theorem setoid_stack_descent
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A B C' D : FiberedCategory C} (sq : TwoCartesianSquare A B C' D)
    (hleft : FiberwiseFullyFaithful sq.left)
    (hlocal : Prop) (hB : StackInSetoids B J) :
    StackInSetoids A J := by
  sorry

theorem relative_sheaf_over_groupoid_stack_is_stack
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (h : RelativeSheafCondition F G J) :
    StackInGroupoids F J := by
  sorry

end Formalization.«Books.Stacks».Unit01
