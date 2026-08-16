import Formalization.«Books.Stacks».Unit01.Inertia

/-!
# Stacks, Chapter 1, Section 8: stackification of fibred categories
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t v' v u' u

def AreEquivalentFibredCategories {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} : Prop :=
  ∃ η : FiberedMorphism F G, FiberwiseEquivalence η

theorem stackification_exists {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) :
    Nonempty (Stackification F J) := by
  sorry

theorem stackification_map_preserves_cartesian
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C} (S : Stackification F J) :
    ∀ U : C, Nonempty (Fiber F U ⥤ Fiber S.value U) := by
  intro U
  exact ⟨(S.map.app (.mk (Opposite.op U))).toFunctor⟩

theorem stackification_unique {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C}
    (S T : Stackification F J) :
    AreEquivalentFibredCategories (F := S.value) (G := T.value) := by
  sorry

theorem stackification_universal_property
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C} (S : Stackification F J)
    {X : FiberedCategory C} (hX : Stack X J) (η : FiberedMorphism F X) :
    ∃ θ : FiberedMorphism S.value X, η = S.map ≫ θ := by
  sorry

theorem stackification_universal_property_equivalence
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C} (S : Stackification F J)
    {X : FiberedCategory C} (hX : Stack X J) :
    Nonempty ((F ⟶ X) ≃ (S.value ⟶ X)) := by
  sorry

theorem stackification_commutes_two_fibre_products
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H, Nonempty (Stackification P.apex J) := by
  sorry

theorem stackification_commutes_with_inertia
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G : FiberedCategory C} (η : FiberedMorphism F G) :
    ∃ I : FiberedCategory C, StackInGroupoids I J := by
  sorry

end Formalization.«Books.Stacks».Unit01
