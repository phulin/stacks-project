import Formalization.Books.Algebra.Unit66.WitnessDescent

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct

noncomputable section

set_option linter.style.haveILetI false in
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
  let BF := R ⊗[k] L
  let BK := R ⊗[k] K
  let f := Algebra.TensorProduct.map (AlgHom.id k R) L.val
  let fR : BF →ₗ[R] BK := intermediateFieldTensorMapLinear L
  have hzmap' : fR.rTensor M zL = z := by simpa [fR] using hzmap
  letI : Algebra L (R ⊗[k] L) :=
    (Algebra.TensorProduct.includeRight : L →ₐ[k] R ⊗[k] L).toRingHom.toAlgebra
  letI : Algebra (R ⊗[k] L) (R ⊗[k] K) := f.toRingHom.toAlgebra
  letI : Algebra BF BK := f.toRingHom.toAlgebra
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
  haveI : Module.Flat BF BK := by
    let e := tensorProduct_towerAlgEquiv
      (k := k) (F := L) (K := K) (R := R)
    exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let eCancel : TensorProduct R BK M ≃ₗ[BK]
      TensorProduct BF BK (TensorProduct R BF M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R BF BK BK M).symm
  have hemap (t : TensorProduct R BF M) :
      eCancel (fR.rTensor M t) = (1 : BK) ⊗ₜ[BF] t := by
    induction t with
    | zero => simp
    | tmul b m =>
        change eCancel (f b ⊗ₜ[R] m) = (1 : BK) ⊗ₜ[BF] (b ⊗ₜ[R] m)
        change f b ⊗ₜ[BF] ((1 : BF) ⊗ₜ[R] m) =
          (1 : BK) ⊗ₜ[BF] (b ⊗ₜ[R] m)
        have hf : f b = b • (1 : BK) := by
          change f b = f b * 1
          simp
        have hinner : b ⊗ₜ[R] m = b • ((1 : BF) ⊗ₜ[R] m) := by
          simp [TensorProduct.smul_tmul']
        rw [hf, hinner]
        exact TensorProduct.smul_tmul (R := R ⊗[k] L) (R' := R ⊗[k] L)
          b (1 : R ⊗[k] K) ((1 : R ⊗[k] L) ⊗ₜ[R] m)
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy, TensorProduct.tmul_add]
  have hez : eCancel z = (1 : BK) ⊗ₜ[BF] zL := by rw [← hzmap', hemap]
  have hann :
      (⊥ : Submodule BK (TensorProduct BF BK (TensorProduct R BF M))).colon
          ({eCancel z} : Set _) =
        (⊥ : Submodule BK (TensorProduct R BK M)).colon ({z} : Set _) := by
    ext b
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
    constructor
    · intro hb
      apply eCancel.injective
      rw [map_zero, eCancel.map_smul]
      exact hb
    · intro hb
      rw [← eCancel.map_smul]
      simp [hb]
  have hziter : q.asIdeal ∈
      ((⊥ : Submodule BK (TensorProduct BF BK (TensorProduct R BF M))).colon
        ({(1 : BK) ⊗ₜ[BF] zL} : Set _)).minimalPrimes := by
    rw [← hez, hann]
    exact hz
  exact weaklyAssociatedPrime_contract_tmul_of_flat
    (A := BF) (S := BK) (X := TensorProduct R BF M) q zL hziter

end
end Formalization.Books.Algebra.Unit66
