import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free

namespace Formalization.Books.Algebra.Unit66

open scoped TensorProduct

noncomputable section

/-- Iterated scalar extension through a field tower agrees with direct scalar
extension and is linear over the first base-changed ring. -/
def tensorProduct_towerAlgEquiv
    {k F K R : Type*} [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K]
    [CommRing R] [Algebra k R] :
    let BF := R ⊗[k] F
    let BK := R ⊗[k] K
    let f := Algebra.TensorProduct.map (AlgHom.id k R)
      (IsScalarTower.toAlgHom k F K)
    letI : Algebra F BF :=
      (Algebra.TensorProduct.includeRight : F →ₐ[k] BF).toRingHom.toAlgebra
    letI : Algebra BF BK := f.toRingHom.toAlgebra
    ((BF ⊗[F] K) ≃ₐ[BF] BK) := by
  dsimp only
  let BF := R ⊗[k] F
  let BK := R ⊗[k] K
  let f := Algebra.TensorProduct.map (AlgHom.id k R)
    (IsScalarTower.toAlgHom k F K)
  letI : Algebra F BF :=
    (Algebra.TensorProduct.includeRight : F →ₐ[k] BF).toRingHom.toAlgebra
  letI : Algebra BF BK := f.toRingHom.toAlgebra
  letI : IsScalarTower k F BF := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul x)
  let eInner : BF ≃ₐ[F] (F ⊗[k] R) :=
    { (Algebra.TensorProduct.comm k R F).toRingEquiv with
      commutes' := by
        intro x
        change (Algebra.TensorProduct.comm k R F) (1 ⊗ₜ[k] x) = x ⊗ₜ[k] 1
        simp }
  let e : (BF ⊗[F] K) ≃+* BK :=
    (Algebra.TensorProduct.comm F BF K).toRingEquiv.trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[F] K) eInner).toRingEquiv.trans <|
        (Algebra.TensorProduct.cancelBaseChange k F K K R).toRingEquiv.trans <|
          (Algebra.TensorProduct.comm k K R).toRingEquiv
  have heInner (r : R) (x : F) : eInner (r ⊗ₜ[k] x) = x ⊗ₜ[k] r := rfl
  have hcongr (b : BF) :
      (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[F] K) eInner)
          (1 ⊗ₜ[F] b) = 1 ⊗ₜ[F] eInner b := by
    change (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl K K) eInner.toLinearEquiv) (1 ⊗ₜ[F] b) = _
    rw [TensorProduct.AlgebraTensorModule.congr_tmul]
    simp
  have hmap : e.toRingHom.comp (algebraMap BF (BF ⊗[F] K)) = f.toRingHom := by
    ext r
    · change e (algebraMap BF (BF ⊗[F] K)
          (Algebra.TensorProduct.includeLeftRingHom r)) =
        f (Algebra.TensorProduct.includeLeftRingHom r)
      rw [Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      change (Algebra.TensorProduct.comm k K R)
          (Algebra.TensorProduct.cancelBaseChange k F K K R
            ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[F] K) eInner)
              (1 ⊗ₜ[F] (r ⊗ₜ[k] 1)))) = f (r ⊗ₜ[k] 1)
      rw [hcongr, heInner]
      dsimp [f]
      rw [Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.comm_tmul]
      simp
    · change e (algebraMap BF (BF ⊗[F] K)
          (Algebra.TensorProduct.includeRight r)) =
        f (Algebra.TensorProduct.includeRight r)
      rw [Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      change (Algebra.TensorProduct.comm k K R)
          (Algebra.TensorProduct.cancelBaseChange k F K K R
            ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[F] K) eInner)
              (1 ⊗ₜ[F] (1 ⊗ₜ[k] r)))) = f (1 ⊗ₜ[k] r)
      rw [hcongr, heInner]
      dsimp [f]
      rw [Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.comm_tmul]
      simp [Algebra.smul_def]
  exact { e with commutes' := fun b => DFunLike.congr_fun hmap b }

/-- Over the first base-changed ring, the directly base-changed module is a
finite-support family of copies of the module at the intermediate field. -/
def tensorProduct_towerModuleEquiv
    {k F K R M : Type*} [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K]
    [CommRing R] [Algebra k R] [Module.Finite F K]
    [AddCommGroup M] [Module R M] :
    let BF := R ⊗[k] F
    let BK := R ⊗[k] K
    let f := Algebra.TensorProduct.map (AlgHom.id k R)
      (IsScalarTower.toAlgHom k F K)
    letI : Algebra F BF :=
      (Algebra.TensorProduct.includeRight : F →ₐ[k] BF).toRingHom.toAlgebra
    letI : Algebra BF BK := f.toRingHom.toAlgebra
    letI : IsScalarTower R BF BK := IsScalarTower.of_algebraMap_eq' (by
      ext r
      change r ⊗ₜ[k] (1 : K) = f (r ⊗ₜ[k] (1 : F))
      simp [f])
    TensorProduct R BK M ≃ₗ[BF]
      ((Module.Free.ChooseBasisIndex F K) →₀ TensorProduct R BF M) := by
  dsimp only
  let BF := R ⊗[k] F
  let BK := R ⊗[k] K
  let f := Algebra.TensorProduct.map (AlgHom.id k R)
    (IsScalarTower.toAlgHom k F K)
  letI : Algebra F BF :=
    (Algebra.TensorProduct.includeRight : F →ₐ[k] BF).toRingHom.toAlgebra
  letI : Algebra BF BK := f.toRingHom.toAlgebra
  letI : IsScalarTower R BF BK := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change r ⊗ₜ[k] (1 : K) = f (r ⊗ₜ[k] (1 : F))
    simp [f])
  let b := Module.Free.chooseBasis F K
  let eCoeff : (BF ⊗[F] K) ≃ₗ[BF]
      ((Module.Free.ChooseBasisIndex F K) →₀ BF) :=
    Algebra.TensorProduct.equivFinsuppOfBasis BF b
  let eBK : BK ≃ₗ[BF]
      ((Module.Free.ChooseBasisIndex F K) →₀ BF) :=
    (tensorProduct_towerAlgEquiv (k := k) (F := F) (K := K) (R := R)).symm.toLinearEquiv.trans
      eCoeff
  let MF := TensorProduct R BF M
  let eCancel : TensorProduct R BK M ≃ₗ[BF] TensorProduct BF BK MF :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R BF BF BK M).symm
  let eCongr : TensorProduct BF BK MF ≃ₗ[BF]
      TensorProduct BF ((Module.Free.ChooseBasisIndex F K) →₀ BF) MF :=
    TensorProduct.AlgebraTensorModule.congr eBK (LinearEquiv.refl BF MF)
  let eF : TensorProduct BF ((Module.Free.ChooseBasisIndex F K) →₀ BF) MF ≃ₗ[BF]
      ((Module.Free.ChooseBasisIndex F K) →₀ MF) :=
    TensorProduct.equivFinsuppOfBasisLeft
      (Finsupp.basisSingleOne
        (R := BF) (ι := Module.Free.ChooseBasisIndex F K))
  exact (eCancel.trans eCongr).trans eF

end

end Formalization.Books.Algebra.Unit66
