import Formalization.Books.Duality.Unit13.PerfectProper

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure EffectiveCartierData {X Z : Scheme.{u}} (i : Z ⟶ X) where
  normal : DerivedObject Z
  regularImmersion : IsClosedImmersionMorphism i
  comparison : ∀ K : DerivedObject X,
    Isomorphic (Tensor ((LPullback i).obj K) (Shift normal (-1)))
      (ExactSupportOnSource i K)

def EffectiveCartierComparison {X Z : Scheme.{u}} (i : Z ⟶ X)
    (K : DerivedObject X) : Prop :=
  ∃ d : EffectiveCartierData i,
    Isomorphic (Tensor ((LPullback i).obj K) (Shift d.normal (-1)))
      (ExactSupportOnSource i K)

theorem lemma_compute_for_effective_Cartier {X Z : Scheme.{u}} (i : Z ⟶ X)
    (hi : IsClosedImmersionMorphism i) : Nonempty (EffectiveCartierData i) := by
  sorry

theorem lemma_sheaf_with_exact_support_effective_Cartier {X Z : Scheme.{u}}
    (i : Z ⟶ X) (hi : IsClosedImmersionMorphism i) :
    ∀ K : DerivedObject X, EffectiveCartierComparison i K := by
  sorry

theorem equation_map_effective_Cartier {X Z : Scheme.{u}} (i : Z ⟶ X)
    (K : DerivedObject X) :
    ∃ d : EffectiveCartierData i,
      Isomorphic (Tensor ((LPullback i).obj K) (Shift d.normal (-1)))
        (ExactSupportOnSource i K) := by
  sorry

end

end Formalization.Books.Duality.Unit01
