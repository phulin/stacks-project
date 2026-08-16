import Formalization.«Books.Stacks».Unit01.Stackification

/-!
# Stacks, Chapter 1, Section 9: stackification in groupoids
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t v' v u' u

structure GroupoidStackification {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  map : FiberedMorphism F value
  isStackInGroupoids : StackInGroupoids value J
  locallyFromMap : Prop

theorem groupoid_stackification_exists {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) :
    Nonempty (GroupoidStackification F J) := by
  sorry

theorem groupoid_stackification_universal_property
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C} (S : GroupoidStackification F J)
    {X : FiberedCategory C} (hX : StackInGroupoids X J)
    (η : FiberedMorphism F X) :
    ∃ θ : FiberedMorphism S.value X, η = S.map ≫ θ := by
  sorry

theorem groupoid_stackification_commutes_two_fibre_products
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H,
      Nonempty (GroupoidStackification P.apex J) := by
  sorry

end Formalization.«Books.Stacks».Unit01
