import Formalization.Books.Algebra.Unit66.WitnessDescent

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct

noncomputable section

-- The generic linter pass is disproportionately expensive on the large
-- scalar-tower type below; the proof itself elaborates quickly.
set_option linter.all false
theorem weaklyAssociatedPrime_contract_intermediate_preimage
    {k K R M : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
    (L : IntermediateField k K) (q : PrimeSpectrum (R ⊗[k] K))
    (z : TensorProduct R (R ⊗[k] K) M)
    (zL : TensorProduct R (R ⊗[k] L) M)
    (hzmap : (intermediateFieldTensorMapLinear L).rTensor M zL = z)
    (hz : q.asIdeal ∈
      ((⊥ : Submodule (R ⊗[k] K) (TensorProduct R (R ⊗[k] K) M)).colon
        ({z} : Set _)).minimalPrimes) :
    let f := Algebra.TensorProduct.map (AlgHom.id k R) L.val
    letI : Module (R ⊗[k] L) (TensorProduct R (R ⊗[k] K) M) :=
      Module.compHom _ f.toRingHom
    PrimeSpectrum.comap f.toRingHom q ∈
      weaklyAssociatedPrimes (R ⊗[k] L)
        (TensorProduct R (R ⊗[k] L) M) := by
  let f := Algebra.TensorProduct.map (AlgHom.id k R) L.val
  letI : Algebra L (R ⊗[k] L) :=
    (Algebra.TensorProduct.includeRight : L →ₐ[k] R ⊗[k] L).toRingHom.toAlgebra
  letI : Algebra (R ⊗[k] L) (R ⊗[k] K) := f.toRingHom.toAlgebra
  letI : Module (R ⊗[k] L) (R ⊗[k] K) :=
    Module.compHom (R ⊗[k] K) f.toRingHom
  letI : IsScalarTower (R ⊗[k] L) (R ⊗[k] L) (R ⊗[k] K) :=
    IsScalarTower.left (R ⊗[k] L)
  letI : IsScalarTower (R ⊗[k] L) (R ⊗[k] L)
      (TensorProduct R (R ⊗[k] L) M) := IsScalarTower.left (R ⊗[k] L)
  letI : IsScalarTower R (R ⊗[k] L) (R ⊗[k] K) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := R ⊗[k] L)
      (A := R ⊗[k] K) (by
        ext r
        change r ⊗ₜ[k] (1 : K) =
          (Algebra.TensorProduct.map (AlgHom.id k R) L.val) (r ⊗ₜ[k] (1 : L))
        simp)
  haveI : Module.Flat (R ⊗[k] L) (R ⊗[k] K) := by
    exact tensorProduct_flat_intermediateField L
  let eCancel : TensorProduct R (R ⊗[k] K) M ≃ₗ[R ⊗[k] K]
      TensorProduct (R ⊗[k] L) (R ⊗[k] K)
        (TensorProduct R (R ⊗[k] L) M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⊗[k] L)
      (R ⊗[k] K) (R ⊗[k] K) M).symm
  have hemap (t : TensorProduct R (R ⊗[k] L) M) :
      eCancel ((intermediateFieldTensorMapLinear L).rTensor M t) =
        (1 : R ⊗[k] K) ⊗ₜ[R ⊗[k] L] t := by
    induction t with
    | zero => simp
    | tmul b m =>
        change eCancel (f b ⊗ₜ[R] m) =
          (1 : R ⊗[k] K) ⊗ₜ[R ⊗[k] L] (b ⊗ₜ[R] m)
        change f b ⊗ₜ[R ⊗[k] L] ((1 : R ⊗[k] L) ⊗ₜ[R] m) =
          (1 : R ⊗[k] K) ⊗ₜ[R ⊗[k] L] (b ⊗ₜ[R] m)
        have hf : f b = b • (1 : R ⊗[k] K) := by
          change f b = f b * 1
          simp
        have hinner : b ⊗ₜ[R] m =
            b • ((1 : R ⊗[k] L) ⊗ₜ[R] m) := by
          simp [TensorProduct.smul_tmul']
        rw [hf, hinner]
        exact TensorProduct.smul_tmul (R := R ⊗[k] L) (R' := R ⊗[k] L)
          b (1 : R ⊗[k] K) ((1 : R ⊗[k] L) ⊗ₜ[R] m)
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy, TensorProduct.tmul_add]
  have hez : eCancel z =
      (1 : R ⊗[k] K) ⊗ₜ[R ⊗[k] L] zL := by
    rw [← hzmap, hemap]
  have hziter : q.asIdeal ∈
      ((⊥ : Submodule (R ⊗[k] K)
          (TensorProduct (R ⊗[k] L) (R ⊗[k] K)
            (TensorProduct R (R ⊗[k] L) M))).colon
        ({(1 : R ⊗[k] K) ⊗ₜ[R ⊗[k] L] zL} : Set _)).minimalPrimes := by
    rw [← hez]
    exact (mem_minimalPrimes_colon_linearEquiv eCancel q z).2 hz
  exact weaklyAssociatedPrime_contract_tmul_of_flat
    (A := R ⊗[k] L) (S := R ⊗[k] K)
      (X := TensorProduct R (R ⊗[k] L) M) q zL hziter

end
end Formalization.Books.Algebra.Unit66
