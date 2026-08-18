import Formalization.Books.Duality.Unit01.ClosedImmersions

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def ExactSupportBaseChangeMap {X X' Z Z' : Scheme.{u}}
    (i : Z ⟶ X) (_i' : Z' ⟶ X') (K : DerivedObject X) :
    DerivedObject X :=
  ExactSupport i K

def equation_base_change_exact_support {S : Type u}
    [CategoryTheory.Category.{u, u} S] [CategoryTheory.Limits.HasPullbacks S]
    [SchemeDerivedContext S] [SchemeDerivedOperations S]
    {square : CartesianSquare S} {a : RightAdjointData square.f}
    {a' : RightAdjointData square.f'} (b : BaseChangeData square a a')
    (K : DerivedObject square.Y) :=
  BaseChangeMap b K

theorem lemma_check_base_change_is_iso {X Z : Scheme.{u}}
    (i : Z ⟶ X) (K : DerivedObject X)
    (c : ExactSupport i K ⟶ ExactSupport i K) (hcartesian : Prop) :
    IsIso c := by
  sorry

theorem lemma_flat_bc_sheaf_with_exact_support {X X' Z Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (K : DerivedObject X)
    (hflat : Prop) (hi : Prop) :
    ∃ c : ExactSupport i K ⟶ ExactSupport i K, IsIso c := by
  sorry

theorem lemma_sheaf_with_exact_support_tensor {X Z : Scheme.{u}}
    (i : Z ⟶ X) (M K : DerivedObject X) (hM : IsBoundedBelow M)
    (hK : IsBoundedBelow K) :
    Nonempty (ExactSupport i (Tensor K M) ≅ ExactSupport i (Tensor K M)) := by
  sorry

end

end Formalization.Books.Duality.Unit01
