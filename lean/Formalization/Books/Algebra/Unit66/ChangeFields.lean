import Formalization.Books.Algebra.Unit66.ChangeFieldsTensor

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct
noncomputable section

/-- Weakly associated primes descend along extension of the coefficient
field. -/
theorem weaklyAssociatedPrimes_change_fields
    {k K R M : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R]
    [AddCommGroup M] [Module R M] :
    letI : Algebra k R := (algebraMap k R).toAlgebra
    letI : Algebra k K := (algebraMap k K).toAlgebra
    ∀ (q : PrimeSpectrum (R ⊗[k] K)) (p : PrimeSpectrum R),
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            R →+* R ⊗[k] K) q = p →
        q ∈ weaklyAssociatedPrimes (R ⊗[k] K)
          (Formalization.Books.Algebra.Unit14.baseChangeModule
            (M := M) (algebraMap k R) (algebraMap k K)) →
        p ∈ weaklyAssociatedPrimes R M := by
  classical
  let oldAlgR : Algebra k R := inferInstance
  let oldAlgK : Algebra k K := inferInstance
  have hAlgR : oldAlgR = (algebraMap k R).toAlgebra := by
    exact Algebra.algebra_ext _ _ (fun r => rfl)
  have hAlgK : oldAlgK = (algebraMap k K).toAlgebra := by
    exact Algebra.algebra_ext _ _ (fun r => rfl)
  let : Algebra k R := (algebraMap k R).toAlgebra
  let : Algebra k K := (algebraMap k K).toAlgebra
  let B := R ⊗[k] K
  let Pobj :=
    (ModuleCat.extendScalars (Unit14.baseChangeAlgebraMap
      (algebraMap k R) (algebraMap k K))).obj (ModuleCat.of R M)
  let : AddCommGroup (Pobj : Type _) := Pobj.isAddCommGroup
  let : AddCommMonoid (Pobj : Type _) := Pobj.isAddCommGroup.toAddCommMonoid
  let : Module B (Pobj : Type _) := Pobj.isModule
  change ∀ (q : PrimeSpectrum B) (p : PrimeSpectrum R),
    PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* B) q = p →
      q ∈ weaklyAssociatedPrimes B (Pobj : Type _) →
        p ∈ weaklyAssociatedPrimes R M
  intro q p hpq hq
  let Bobj :=
    (ModuleCat.restrictScalars (Unit14.baseChangeAlgebraMap
      (algebraMap k R) (algebraMap k K))).obj
      (ModuleCat.of B B)
  let : IsScalarTower R B (Bobj : Type _) :=
    IsScalarTower.of_compHom R B (Bobj : Type _)
  let eU : B ≃ₗ[B] (Bobj : Type _) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  let eP : TensorProduct R B M ≃ₗ[B] (Pobj : Type _) :=
    TensorProduct.AlgebraTensorModule.congr eU (LinearEquiv.refl R M)
  have hqstd : q ∈ weaklyAssociatedPrimes B (TensorProduct R B M) :=
    (weaklyAssociatedPrimes_linearEquiv eP q).2 hq
  exact weaklyAssociatedPrimes_change_fields_tensor q p hpq hqstd

end
end Formalization.Books.Algebra.Unit66
