import Formalization.Books.Brauer.Unit01.BrauerGroup
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

open scoped TensorProduct

/-!
# Skolem--Noether

The source theorem is recorded with units, so the conjugating element is
invertible by construction rather than merely assumed to be a division-ring
element.
-/

namespace Formalization.Books.Brauer

theorem skolem_noether (k A B : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    [Ring B] [Algebra k B] [IsSimpleRing B]
    (f g : B →ₐ[k] A) :
    ∃ x : Aˣ, ∀ b : B,
      f b = (x : A) * g b * (x⁻¹ : Aˣ) := by
  classical
  obtain ⟨M, hM⟩ := finite_algebra_has_simple_submodule k A
  let : IsSimpleModule A M := hM
  let : Nontrivial M := IsSimpleModule.nontrivial A M
  let : Module.Finite k M :=
    simple_module_over_finite_algebra_is_finite_dimensional k A M
  let L := Module.End A M
  have hLfd : FiniteDimensional k L :=
    (simple_module_center_and_dimension k A M).2.1
  let : FiniteDimensional k L := hLfd
  let : FiniteDimensional k B :=
    FiniteDimensional.of_injective f.toLinearMap f.injective
  let eCenter : Subalgebra.center k A ≃ₐ[k] Subalgebra.center k L :=
    Classical.choice (simple_module_center_and_dimension k A M).1
  let : Algebra.IsCentral k L := by
    constructor
    intro z hz
    let z' : Subalgebra.center k A := eCenter.symm ⟨z, hz⟩
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out z'.property)
    refine ⟨r, ?_⟩
    let za : Subalgebra.center k A := ⟨algebraMap k A r, by
      simpa [hr] using z'.property⟩
    have hz' : z' = za := by
      apply Subtype.ext
      exact hr.symm
    have hz'' := congrArg (fun w : Subalgebra.center k A => (eCenter w : L)) hz'
    have hza : (eCenter za : L) = algebraMap k L r := by
      simp [za]
    calc
      algebraMap k L r = (eCenter za : L) := hza.symm
      _ = (eCenter z' : L) := hz''.symm
      _ = z := by simp [z']
  let module_f : Module B M := Module.compHom M f.toRingHom
  let module_g : Module B M := Module.compHom M g.toRingHom
  let tower_f : @IsScalarTower k B M _ module_f.toDistribMulAction.toSMul _ := by
    let : Module B M := module_f
    exact IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := M) (fun r m => by
      change f (algebraMap k B r) • m = r • m
      rw [f.commutes]
      exact IsScalarTower.algebraMap_smul A r m)
  let tower_g : @IsScalarTower k B M _ module_g.toDistribMulAction.toSMul _ := by
    let : Module B M := module_g
    exact IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := M) (fun r m => by
      change g (algebraMap k B r) • m = r • m
      rw [g.commutes]
      exact IsScalarTower.algebraMap_smul A r m)
  let tower_L : IsScalarTower k L M := Module.End.apply_isScalarTower
  let comm_f : @SMulCommClass B L M module_f.toDistribMulAction.toSMul _ := by
    let : Module B M := module_f
    exact ⟨by
      intro b l m
      change f b • (l • m) = l • (f b • m)
      exact (l.map_smul (f b) m).symm⟩
  let comm_g : @SMulCommClass B L M module_g.toDistribMulAction.toSMul _ := by
    let : Module B M := module_g
    exact ⟨by
      intro b l m
      change g b • (l • m) = l • (g b • m)
      exact (l.map_smul (g b) m).symm⟩
  let C : Type _ := (B ⊗[k] L)
  let module_fC : Module C M := by
    letI : Module B M := module_f
    letI : IsScalarTower k B M := tower_f
    letI : IsScalarTower k L M := tower_L
    letI : SMulCommClass B L M := comm_f
    exact TensorProduct.Algebra.module
  let module_gC : Module C M := by
    letI : Module B M := module_g
    letI : IsScalarTower k B M := tower_g
    letI : IsScalarTower k L M := tower_L
    letI : SMulCommClass B L M := comm_g
    exact TensorProduct.Algebra.module
  let tower_fC : @IsScalarTower k C M _ module_fC.toDistribMulAction.toSMul _ := by
    let : Module B M := module_f
    let : IsScalarTower k B M := tower_f
    let : IsScalarTower k L M := tower_L
    let : SMulCommClass B L M := comm_f
    let : Module C M := module_fC
    exact IsScalarTower.of_algebraMap_smul (R := k) (A := C) (M := M) (fun r m => by
      change (algebraMap k (B ⊗[k] L) r) • m = r • m
      rw [Algebra.TensorProduct.algebraMap_apply' (R := k) (A := B) (B := L) r]
      rw [TensorProduct.Algebra.smul_def, one_smul]
      exact IsScalarTower.algebraMap_smul L r m)
  let tower_gC : @IsScalarTower k C M _ module_gC.toDistribMulAction.toSMul _ := by
    let : Module B M := module_g
    let : IsScalarTower k B M := tower_g
    let : IsScalarTower k L M := tower_L
    let : SMulCommClass B L M := comm_g
    let : Module C M := module_gC
    exact IsScalarTower.of_algebraMap_smul (R := k) (A := C) (M := M) (fun r m => by
      change (algebraMap k (B ⊗[k] L) r) • m = r • m
      rw [Algebra.TensorProduct.algebraMap_apply' (R := k) (A := B) (B := L) r]
      rw [TensorProduct.Algebra.smul_def, one_smul]
      exact IsScalarTower.algebraMap_smul L r m)
  let finite_fC : @Module.Finite C M _ _ module_fC := by
    let : Module C M := module_fC
    let : IsScalarTower k C M := tower_fC
    exact Module.Finite.of_restrictScalars_finite k C M
  let finite_gC : @Module.Finite C M _ _ module_gC := by
    let : Module C M := module_gC
    let : IsScalarTower k C M := tower_gC
    exact Module.Finite.of_restrictScalars_finite k C M
  let : Ring C := inferInstance
  let : Semiring C := (inferInstance : Ring C).toSemiring
  let : IsSimpleRing C := tensor_product_simple_of_simple_algebras k B L
  let : FiniteDimensional k C := inferInstance
  obtain ⟨T⟩ :=
    (@finite_simple_algebra_modules_classified_by_dimension k C M M
      _ _ _ _ _ _ module_gC _ tower_gC finite_gC _ module_fC _ tower_fC finite_fC).2 rfl
  let T_L : M →ₗ[L] M :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := by
        intro l m
        let : Module B M := module_g
        let : IsScalarTower k B M := tower_g
        let : IsScalarTower k L M := tower_L
        let : SMulCommClass B L M := comm_g
        let : Module C M := module_gC
        have hs : ((1 : B) ⊗ₜ[k] l) • m = l • m := by
          change (1 : B) • (l • m) = l • m
          simp
        have h := T.map_smul (1 ⊗ₜ[k] l) m
        let : Module B M := module_f
        let : IsScalarTower k B M := tower_f
        let : SMulCommClass B L M := comm_f
        let : Module C M := module_fC
        have ht : ((1 : B) ⊗ₜ[k] l) • T m = l • T m := by
          change (1 : B) • (l • T m) = l • T m
          simp
        rw [hs, ht] at h
        exact h }
  let TLe : M ≃ₗ[L] M := LinearEquiv.ofBijective T_L T.bijective
  let uT : (Module.End L M)ˣ :=
    { val := TLe.toLinearMap
      inv := TLe.symm.toLinearMap
      val_inv := by
        apply LinearMap.ext
        intro m
        simp [Module.End.mul_eq_comp]
      inv_val := by
        apply LinearMap.ext
        intro m
        simp [Module.End.mul_eq_comp] }
  let comm_A_L : @SMulCommClass A L M _ _ :=
    ⟨fun a l m => (l.map_smul a m).symm⟩
  let : SMulCommClass A L M := comm_A_L
  let rho : A →ₐ[k] Module.End L M :=
    { toRingHom := Module.toModuleEnd L (S := A) M
      commutes' := by
        intro r
        ext m
        rw [Module.algebraMap_end_apply]
        exact congrArg Subtype.val (IsScalarTower.algebraMap_smul A r m) }
  have hAnn : Module.annihilator A M = ⊥ := by
    have h := (isSimpleRing_iff_isTwoSided_imp.mp (inferInstance : IsSimpleRing A)).2
      (Module.annihilator A M) inferInstance
    exact h.resolve_right (by
      intro htop
      exact (not_subsingleton M)
        (Module.annihilator_eq_top_iff.mp htop))
  let : FaithfulSMul A M := Module.annihilator_eq_bot.mp hAnn
  have hrho : Function.Injective rho := by
    intro a b h
    apply (Module.toModuleEnd L (S := A) M).injective
    simpa [rho] using h
  obtain ⟨eA⟩ := simple_module_double_commutant k A M
  let alpha : A →ₐ[k] A := eA.symm.toAlgHom.comp rho
  have halpha_injective : Function.Injective alpha := eA.symm.injective.comp hrho
  have halpha_surjective : Function.Surjective alpha :=
    LinearMap.surjective_of_injective (f := alpha.toLinearMap) halpha_injective
  let alphaE : A ≃ₐ[k] A := AlgEquiv.ofBijective alpha
    ⟨halpha_injective, halpha_surjective⟩
  have hTend (b : B) :
      T_L * rho (g b) = rho (f b) * T_L := by
    apply LinearMap.ext
    intro m
    let : Module B M := module_g
    let : IsScalarTower k B M := tower_g
    let : IsScalarTower k L M := tower_L
    let : SMulCommClass B L M := comm_g
    let : Module C M := module_gC
    have hs : ((b : B) ⊗ₜ[k] (1 : L)) • m = g b • m := by
      change g b • ((1 : L) • m) = g b • m
      simp
    have h := T.map_smul (b ⊗ₜ[k] (1 : L)) m
    let : Module B M := module_f
    let : IsScalarTower k B M := tower_f
    let : SMulCommClass B L M := comm_f
    let : Module C M := module_fC
    have ht : ((b : B) ⊗ₜ[k] (1 : L)) • T m = f b • T m := by
      change f b • ((1 : L) • T m) = f b • T m
      simp
    rw [hs, ht] at h
    simpa [Module.End.mul_eq_comp, T_L, rho] using h
  let y : Aˣ := Units.map eA.symm.toRingEquiv.toMonoidHom uT
  have hval : (uT : Module.End L M) = T_L := by
    apply LinearMap.ext
    intro m
    rfl
  have hAend (b : B) :
      (y : A) * (alpha (g b)) = (alpha (f b)) * (y : A) := by
    have h := congrArg eA.symm (hTend b)
    rw [map_mul, map_mul] at h
    rw [← hval] at h
    simpa [y, alpha, uT, TLe, T_L, rho] using h
  have hconj_alpha (b : B) :
      alpha (f b) = (y : A) * alpha (g b) * (y⁻¹ : Aˣ) := by
    calc
      alpha (f b) = alpha (f b) * 1 := by simp
      _ = alpha (f b) * ((y : A) * (y⁻¹ : Aˣ)) := by simp
      _ = (alpha (f b) * (y : A)) * (y⁻¹ : Aˣ) := by rw [mul_assoc]
      _ = ((y : A) * alpha (g b)) * (y⁻¹ : Aˣ) := by rw [hAend b]
      _ = (y : A) * alpha (g b) * (y⁻¹ : Aˣ) := by rfl
  let x : Aˣ := Units.map alphaE.symm.toRingEquiv.toMonoidHom y
  refine ⟨x, ?_⟩
  intro b
  have halphaE (a : A) : alphaE.symm (alpha a) = a := by
    change (AlgEquiv.ofBijective alpha
      ⟨halpha_injective, halpha_surjective⟩).symm (alpha a) = a
    exact AlgEquiv.ofBijective_symm_apply_apply alpha
      ⟨halpha_injective, halpha_surjective⟩ a
  have h := congrArg alphaE.symm (hconj_alpha b)
  rw [map_mul, map_mul] at h
  rw [halphaE (f b), halphaE (g b)] at h
  simpa [x] using h

theorem finite_central_simple_automorphism_inner (k A : Type*) [Field k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A] (f : A ≃ₐ[k] A) :
    ∃ x : Aˣ, ∀ a : A,
      f a = (x : A) * a * (x⁻¹ : Aˣ) := by
  simpa using (skolem_noether k A A f (AlgEquiv.refl : A ≃ₐ[k] A))

theorem matrix_automorphism_inner (k : Type*) (n : ℕ) [Field k] [NeZero n]
    (f : Matrix (Fin n) (Fin n) k ≃ₐ[k] Matrix (Fin n) (Fin n) k) :
    ∃ x : (Matrix (Fin n) (Fin n) k)ˣ, ∀ a,
      f a = (x : Matrix (Fin n) (Fin n) k) * a * (x⁻¹ : _) := by
  classical
  let V := Fin n → k
  let e : Module.End k V ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
    LinearMap.toMatrixAlgEquiv (Pi.basisFun k (Fin n))
  let h : Module.End k V ≃ₐ[k] Module.End k V :=
    e.trans (f.trans e.symm)
  obtain ⟨T, hT⟩ := h.eq_linearEquivConjAlgEquiv
  let u : (Module.End k V)ˣ :=
    { val := T.toLinearMap
      inv := T.symm.toLinearMap
      val_inv := by
        apply LinearMap.ext
        intro v
        simp [Module.End.mul_eq_comp]
      inv_val := by
        apply LinearMap.ext
        intro v
        simp [Module.End.mul_eq_comp] }
  let x : (Matrix (Fin n) (Fin n) k)ˣ :=
    Units.map e.toRingEquiv.toMonoidHom u
  refine ⟨x, ?_⟩
  intro a
  have hTa := DFunLike.congr_fun hT (e.symm a)
  have hTa' := congrArg e hTa
  have hTa'' : f a =
      e (T.toLinearMap ∘ₗ e.symm a ∘ₗ T.symm.toLinearMap) := by
    calc
      f a = e (h (e.symm a)) := by simp [h]
      _ = e (T.toLinearMap ∘ₗ e.symm a ∘ₗ T.symm.toLinearMap) := by
        simpa [LinearEquiv.conjAlgEquiv_apply] using hTa'
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp] at hTa''
  simpa [h, x, u, mul_assoc] using hTa''

end Formalization.Books.Brauer
