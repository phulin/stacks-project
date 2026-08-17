import Formalization.Books.Stacks.Unit01.Stackification

/-!
# Stacks, Chapter 1, Section 9: stackification in groupoids
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v u

structure GroupoidStackification {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  map : FiberedMorphism F value
  isStackInGroupoids : StackInGroupoids value J
  locallyFromMap : ∀ (U : C) (x' : Fiber value U),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ x : Fiber F (X i), Nonempty
          ((value.map (f i).op.toLoc).toFunctor.obj x' ≅
            (map.app (.mk (Opposite.op (X i)))).toFunctor.obj x)
  morphismPresheafMap : ∀ (U : C) (x y : Fiber F U),
    F.presheafHom x y ⟶
      value.presheafHom ((map.app (.mk (Opposite.op U))).toFunctor.obj x)
        ((map.app (.mk (Opposite.op U))).toFunctor.obj y)
  morphismPresheafMap_is_induced : ∀ (U : C) (x y : Fiber F U),
    IsInducedMorphismPresheafMap map x y (morphismPresheafMap U x y)
  morphismSheafification : ∀ (U : C) (x y : Fiber F U),
    IsSheafification (J.over U) (morphismPresheafMap U x y)

theorem groupoid_stackification_exists {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : FiberwiseGroupoid F) :
    Nonempty (GroupoidStackification.{t, v, u, w} F J) := by
  sorry

theorem groupoid_stackification_unique {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C}
    (S T : GroupoidStackification.{t, v, u, w} F J) :
    ∃ η : FiberedMorphism S.value T.value,
      FiberwiseEquivalence η ∧
        Nonempty (S.map ≫ η ≅ T.map) ∧
        ∀ θ : FiberedMorphism S.value T.value,
          FiberwiseEquivalence θ →
            Nonempty (S.map ≫ θ ≅ T.map) → Unique2Isomorphism η θ := by
  sorry

theorem groupoid_stackification_universal_property
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {J : GrothendieckTopology C}
    (S : GroupoidStackification.{t, v, u, w} F J)
    {X : FiberedCategory C} (hF : FiberwiseGroupoid F)
    (hX : StackInGroupoids X J)
    (η : FiberedMorphism F X) :
    ∃ θ : FiberedMorphism S.value X,
      Nonempty (η ≅ S.map ≫ θ) := by
  sorry

structure GroupoidStackificationTwoFiberProductComparison
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) (hF : FiberwiseGroupoid F)
    (hG : FiberwiseGroupoid G) (hH : FiberwiseGroupoid H)
    (SF : GroupoidStackification.{t, v, u, w} F J)
    (SG : GroupoidStackification.{t, v, u, w} G J)
    (SH : GroupoidStackification.{t, v, u, w} H J) where
  rawProduct : TwoFiberProductCone F G H f g
  rawStackification : GroupoidStackification.{t, v, u, w} rawProduct.apex J
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
  stackifiedProductIsGroupoidStack :
    StackInGroupoids stackifiedProduct.apex J
  comparison : FiberedMorphism rawStackification.value stackifiedProduct.apex
  comparisonIsEquivalence : FiberwiseEquivalence comparison
  leftCompatibility : Nonempty
    (comparison ≫ stackifiedProduct.left ≅ leftMap)
  rightCompatibility : Nonempty
    (comparison ≫ stackifiedProduct.right ≅ rightMap)

theorem groupoid_stackification_commutes_two_fibre_products
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H)
    (hF : FiberwiseGroupoid F) (hG : FiberwiseGroupoid G)
    (hH : FiberwiseGroupoid H)
    (SF : GroupoidStackification.{t, v, u, w} F J)
    (SG : GroupoidStackification.{t, v, u, w} G J)
    (SH : GroupoidStackification.{t, v, u, w} H J) :
    Nonempty
      (GroupoidStackificationTwoFiberProductComparison J f g hF hG hH SF SG SH) := by
  sorry

end Formalization.Books.Stacks.Unit01
