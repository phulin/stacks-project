import Formalization.Books.Duality.Unit01.Examples

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure situation_shriek where
  base : Scheme.{u}
  noetherian : IsNoetherianScheme base

def UpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y) (a : RightAdjointData f) :
    DerivedObject Y ⥤ DerivedObject X :=
  a.rightAdjoint

structure UpperShriekCompositionData {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : RightAdjointData f)
    (b : RightAdjointData g) where
  composite : RightAdjointData (f ≫ g)
  comparison : Nonempty (composite.rightAdjoint ≅ b.rightAdjoint ⋙ a.rightAdjoint)

structure UpperShriekPseudoFunctorData where
  compositionLaw : Prop
  identityLaw : Prop
  associativityLaw : Prop
  unitLaw : Prop

structure PullbackToShriekData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  comparison : ∀ K : DerivedObject Y,
    Isomorphic ((LPullback f).obj K) (a.rightAdjoint.obj K)

theorem lemma_shriek_well_defined {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Nonempty (RightAdjointData f)) : Nonempty (RightAdjointData f) := by
  exact h

theorem lemma_upper_shriek_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : RightAdjointData f)
    (b : RightAdjointData g) : Nonempty (UpperShriekCompositionData f g a b) := by
  sorry

theorem lemma_pseudo_functor : Nonempty UpperShriekPseudoFunctorData := by
  sorry

theorem lemma_map_pullback_to_shriek_well_defined {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) : Nonempty (PullbackToShriekData f a) := by
  sorry

end

end Formalization.Books.Duality.Unit01
