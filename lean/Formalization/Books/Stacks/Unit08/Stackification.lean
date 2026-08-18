import Formalization.Books.Stacks.Unit07.Inertia
import Formalization.Books.Stacks.Unit02.FoundationPresheaves
import Formalization.Books.Stacks.Unit08.Foundation
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

/-!
# Stacks, Chapter 1, Section 8: stackification of fibred categories
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v u

def Unique2Isomorphism {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η θ : FiberedMorphism F G) : Prop :=
  ∃ α : η ≅ θ, ∀ β : η ≅ θ, β = α

noncomputable def morphismPresheafMap {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U) :
    F.presheafHom x y ⟶
      G.presheafHom ((η.app (.mk (Opposite.op U))).toFunctor.obj x)
        ((η.app (.mk (Opposite.op U))).toFunctor.obj y) :=
  presheaf_mor_map_fibred_categories η x y

theorem stackification_exists {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) :
    Nonempty (Stackification.{t, v, u, w} F J) := by
  sorry

theorem stackification_map_preserves_strongly_cartesian
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C}
    (S : Stackification.{t, v, u, w} F J) :
    Nonempty (FiberedMorphism F S.value) :=
  ⟨S.map⟩

theorem stackification_morphism_presheaves_are_sheaves
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C}
    (S : Stackification.{t, v, u, w} F J)
    {U : C} (x y : Fiber F U) :
    Presheaf.IsSheaf (J.over U)
      (S.value.presheafHom ((S.map.app (.mk (Opposite.op U))).toFunctor.obj x)
        ((S.map.app (.mk (Opposite.op U))).toFunctor.obj y)) :=
  (S.morphismSheafification U x y).1

theorem stackification_unique {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C}
    (S T : Stackification.{t, v, u, w} F J) :
    ∃ η : FiberedMorphism S.value T.value,
      FiberwiseEquivalence η ∧
        Nonempty (S.map ≫ η ≅ T.map) ∧
        ∀ θ : FiberedMorphism S.value T.value,
          FiberwiseEquivalence θ →
            Nonempty (S.map ≫ θ ≅ T.map) → Unique2Isomorphism η θ := by
  sorry

theorem stackification_universal_property
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C}
    (S : Stackification.{t, v, u, w} F J)
    {X : FiberedCategory C} (hX : Stack X J) (η : FiberedMorphism F X) :
    ∃ θ : FiberedMorphism S.value X,
      Nonempty (η ≅ S.map ≫ θ) := by
  sorry

theorem stackification_universal_property_equivalence
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C}
    (S : Stackification.{t, v, u, w} F J)
    {X : FiberedCategory C} (hX : Stack X J) :
    Nonempty ((F ⟶ X) ≌ (S.value ⟶ X)) := by
  sorry

structure StackificationTwoFiberProductComparison
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H)
    (SF : Stackification.{t, v, u, w} F J)
    (SG : Stackification.{t, v, u, w} G J)
    (SH : Stackification.{t, v, u, w} H J) where
  rawProduct : TwoFiberProductCone F G H f g
  rawStackification : Stackification.{t, v, u, w} rawProduct.apex J
  leftMap : FiberedMorphism rawStackification.value SF.value
  rightMap : FiberedMorphism rawStackification.value SG.value
  leftMapExtension : Nonempty
    (rawStackification.map ≫ leftMap ≅ rawProduct.left ≫ SF.map)
  rightMapExtension : Nonempty
    (rawStackification.map ≫ rightMap ≅ rawProduct.right ≫ SG.map)
  stackifiedLeft : FiberedMorphism SF.value SH.value
  stackifiedRight : FiberedMorphism SG.value SH.value
  stackifiedLeftExtension : Nonempty
    (SF.map ≫ stackifiedLeft ≅ f ≫ SH.map)
  stackifiedRightExtension : Nonempty
    (SG.map ≫ stackifiedRight ≅ g ≫ SH.map)
  stackifiedProduct :
    TwoFiberProductCone SF.value SG.value SH.value stackifiedLeft stackifiedRight
  comparison : FiberedMorphism rawStackification.value stackifiedProduct.apex
  comparisonIsEquivalence : FiberwiseEquivalence comparison
  leftCompatibility : Nonempty
    (comparison ≫ stackifiedProduct.left ≅ leftMap)
  rightCompatibility : Nonempty
    (comparison ≫ stackifiedProduct.right ≅ rightMap)

structure StackificationInertiaComparison
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F : FiberedCategory C} (I : AbsoluteInertiaPresentation F)
    (S : Stackification.{t, v, u, w} F J) where
  inertiaStackification : Stackification.{t, v, u, w} I.value J
  inertiaOfStack : AbsoluteInertiaStackData S.value J
  comparison : FiberedMorphism inertiaStackification.value inertiaOfStack.value
  comparisonIsEquivalence : FiberwiseEquivalence comparison

theorem stackification_commutes_two_fibre_products
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H)
    (SF : Stackification.{t, v, u, w} F J)
    (SG : Stackification.{t, v, u, w} G J)
    (SH : Stackification.{t, v, u, w} H J) :
    Nonempty (StackificationTwoFiberProductComparison J f g SF SG SH) := by
  sorry

theorem stackification_commutes_with_inertia
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F : FiberedCategory C} (I : AbsoluteInertiaPresentation F)
    (S : Stackification.{t, v, u, w} F J) :
    Nonempty (StackificationInertiaComparison J I S) := by
  sorry

end Formalization.Books.Stacks.Unit01
