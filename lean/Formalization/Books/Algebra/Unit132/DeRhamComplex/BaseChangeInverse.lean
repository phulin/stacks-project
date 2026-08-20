import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeForward

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section

variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

@[instance_reducible]
noncomputable def exteriorAlgebraA :
    Algebra A (ExteriorAlgebra B (ModuleOfDifferentials A B)) :=
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let f : A →+* EB := (algebraMap B EB).comp (algebraMap A B)
  f.toAlgebra' (fun a x => Algebra.commutes (algebraMap A B a) x)

theorem exteriorAlgebraTower :
    let : Algebra A (ExteriorAlgebra B (ModuleOfDifferentials A B)) :=
      exteriorAlgebraA (A := A) (B := B)
    IsScalarTower A B (ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rfl

noncomputable def baseChangeExteriorScalarMap :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    T →ₐ[A'] A' ⊗[A] EB := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let bToEB : B →ₐ[A] EB :=
    { toRingHom := algebraMap B EB
      commutes' := fun _ => rfl }
  exact Algebra.TensorProduct.map (AlgHom.id A' A') bToEB

@[simp]
theorem baseChangeExteriorScalarMap_tmul (a : A') (b : B) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    baseChangeExteriorScalarMap (A := A) (A' := A') (B := B) (a ⊗ₜ[A] b) =
      a ⊗ₜ[A] algebraMap B EB b := by
  exact Algebra.TensorProduct.map_tmul _ _ _ _

theorem baseChangeExteriorScalarMap_commutes :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    ∀ (t : T) (x : A' ⊗[A] EB),
      baseChangeExteriorScalarMap (A := A) (A' := A') (B := B) t * x =
        x * baseChangeExteriorScalarMap (A := A) (A' := A') (B := B) t := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  dsimp only
  intro t x
  refine TensorProduct.induction_on t (by simp) (fun a b => ?_)
    (fun u v hu hv => by simpa [add_mul, mul_add] using congrArg₂ (· + ·) hu hv)
  refine TensorProduct.induction_on x (by simp) (fun c y => ?_)
    (fun u v hu hv => by simpa [mul_add, add_mul] using congrArg₂ (· + ·) hu hv)
  rw [baseChangeExteriorScalarMap_tmul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  change (a * c) ⊗ₜ[A] ((algebraMap B EB b) * y) =
    (c * a) ⊗ₜ[A] (y * algebraMap B EB b)
  rw [mul_comm a c, Algebra.commutes]

@[instance_reducible]
noncomputable def baseChangeExteriorAlgebra :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    Algebra T (A' ⊗[A] EB) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  exact (baseChangeExteriorScalarMap (A := A) (A' := A') (B := B)).toAlgebra'
    (baseChangeExteriorScalarMap_commutes (A := A) (A' := A') (B := B))

theorem baseChangeExteriorTower :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    IsScalarTower A' T (A' ⊗[A] EB) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  apply IsScalarTower.of_algebraMap_smul
  intro a x
  rw [Algebra.smul_def, Algebra.smul_def]
  change baseChangeExteriorScalarMap (A := A) (A' := A') (B := B)
      (algebraMap A' T a) * x = algebraMap A' (A' ⊗[A] EB) a * x
  rw [(baseChangeExteriorScalarMap (A := A) (A' := A') (B := B)).commutes]

noncomputable def exteriorGeneratorA :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    ModuleOfDifferentials A B →ₗ[A] EB := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  exact
    { toFun := ExteriorAlgebra.ι B
      map_add' := (ExteriorAlgebra.ι B).map_add
      map_smul' := by
        intro a m
        rw [← IsScalarTower.algebraMap_smul B a m,
          (ExteriorAlgebra.ι B).map_smul]
        rfl }

noncomputable def baseChangeExteriorGeneratorA' :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    A' ⊗[A] ModuleOfDifferentials A B →ₗ[A'] A' ⊗[A] EB :=
  LinearMap.baseChange A' (exteriorGeneratorA (A := A) (B := B))

@[simp]
theorem baseChangeExteriorGeneratorA'_tmul
    (a : A') (m : ModuleOfDifferentials A B) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
        (a ⊗ₜ[A] m) =
      a ⊗ₜ[A] ExteriorAlgebra.ι B m :=
  LinearMap.baseChange_tmul _ _ _

private theorem baseChangeExteriorGenerator_smul
    (t : deRhamBaseChangeRing A A' B)
    (x : A' ⊗[A] ModuleOfDifferentials A B) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B) (t • x) =
      t • baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B) x := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  change baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B) (t • x) =
    t • baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B) x
  induction t using (inferInstance : Algebra.IsPushout A A' B T).1.inductionOn with
  | zero => simp
  | smul a t ht =>
      rw [smul_assoc,
        (baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)).map_smul,
        ht, smul_assoc]
  | add u v hu hv => simp only [add_smul, map_add, hu, hv]
  | tmul b =>
      change baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
          ((algebraMap B T b) • x) =
        (algebraMap B T b) •
          baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B) x
      refine TensorProduct.induction_on x (by simp) (fun a m => ?_)
        (fun u v hu hv => by simpa [smul_add] using congrArg₂ (· + ·) hu hv)
      rw [show (algebraMap B T b) • (a ⊗ₜ[A] m) =
          b • (a ⊗ₜ[A] m) by
        exact IsScalarTower.algebraMap_smul T b (a ⊗ₜ[A] m)]
      rw [KaehlerDifferential.mulActionBaseChange_smul_tmul,
        baseChangeExteriorGeneratorA'_tmul,
        baseChangeExteriorGeneratorA'_tmul]
      change a ⊗ₜ[A] ExteriorAlgebra.ι B (b • m) =
        baseChangeExteriorScalarMap (A := A) (A' := A') (B := B)
            (algebraMap B T b) *
          (a ⊗ₜ[A] ExteriorAlgebra.ι B m)
      change a ⊗ₜ[A] ExteriorAlgebra.ι B (b • m) =
        (1 ⊗ₜ[A] algebraMap B EB b) *
          (a ⊗ₜ[A] ExteriorAlgebra.ι B m)
      rw [Algebra.TensorProduct.tmul_mul_tmul,
        (ExteriorAlgebra.ι B).map_smul, Algebra.smul_def]
      simp only [one_mul]
      rfl

noncomputable def deRhamBaseChangeInverseGenerator :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    ModuleOfDifferentials A' T →ₗ[T] A' ⊗[A] EB := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  exact
    { toFun := fun x =>
        baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
          ((baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)).symm x)
      map_add' := by simp
      map_smul' := by
        intro t x
        rw [(baseChangeDifferentialsEquiv
          (R := A) (R' := A') (S := B)).symm.map_smul]
        exact baseChangeExteriorGenerator_smul
          (A := A) (A' := A') (B := B) t _ }

private theorem baseChangeExteriorGenerator_anticomm
    (x y : A' ⊗[A] ModuleOfDifferentials A B) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let h := baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
    h x * h y + h y * h x = 0 := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let h := baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
  refine TensorProduct.induction_on x (by simp) (fun a m => ?_)
    (fun u v hu hv => ?_)
  · refine TensorProduct.induction_on y (by simp) (fun c n => ?_)
      (fun u v hu hv => ?_)
    · simp only [baseChangeExteriorGeneratorA'_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_comm c a, ← TensorProduct.tmul_add,
        ExteriorAlgebra.ι_add_mul_swap]
      simp
    · change h (a ⊗ₜ[A] m) * h (u + v) +
        h (u + v) * h (a ⊗ₜ[A] m) = 0
      simp only [h.map_add, mul_add, add_mul]
      calc
        h (a ⊗ₜ[A] m) * h u + h (a ⊗ₜ[A] m) * h v +
            (h u * h (a ⊗ₜ[A] m) + h v * h (a ⊗ₜ[A] m)) =
          (h (a ⊗ₜ[A] m) * h u + h u * h (a ⊗ₜ[A] m)) +
            (h (a ⊗ₜ[A] m) * h v + h v * h (a ⊗ₜ[A] m)) := by abel
        _ = 0 := by rw [hu, hv, add_zero]
  · change h (u + v) * h y + h y * h (u + v) = 0
    simp only [h.map_add, add_mul, mul_add]
    calc
      h u * h y + h v * h y + (h y * h u + h y * h v) =
          (h u * h y + h y * h u) + (h v * h y + h y * h v) := by abel
      _ = 0 := by rw [hu, hv, add_zero]

private theorem baseChangeExteriorGenerator_sq_zero
    (x : A' ⊗[A] ModuleOfDifferentials A B) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let h := baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
    h x * h x = 0 := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let h := baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
  refine TensorProduct.induction_on x (by simp) (fun a m => ?_)
    (fun u v hu hv => ?_)
  · simp only [baseChangeExteriorGeneratorA'_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    rw [ExteriorAlgebra.ι_sq_zero]
    simp
  · change h (u + v) * h (u + v) = 0
    simp only [h.map_add, add_mul, mul_add]
    calc
      h u * h u + h v * h u + (h u * h v + h v * h v) =
          h u * h u + (h u * h v + h v * h u) + h v * h v := by abel
      _ = 0 := by
        rw [hu, baseChangeExteriorGenerator_anticomm, hv, zero_add, add_zero]

private theorem deRhamBaseChangeInverseGenerator_sq_zero
    (x : ModuleOfDifferentials A' (deRhamBaseChangeRing A A' B)) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    deRhamBaseChangeInverseGenerator (A := A) (A' := A') (B := B) x *
      deRhamBaseChangeInverseGenerator (A := A) (A' := A') (B := B) x = 0 := by
  exact baseChangeExteriorGenerator_sq_zero (A := A) (A' := A') (B := B)
    ((baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)).symm x)

noncomputable def deRhamBaseChangeInverse :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    ExteriorAlgebra T (ModuleOfDifferentials A' T) →ₐ[T] A' ⊗[A] EB := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  exact ExteriorAlgebra.lift T
    ⟨deRhamBaseChangeInverseGenerator (A := A) (A' := A') (B := B),
      deRhamBaseChangeInverseGenerator_sq_zero
        (A := A) (A' := A') (B := B)⟩

@[simp]
theorem deRhamBaseChangeInverse_ι
    (x : ModuleOfDifferentials A' (deRhamBaseChangeRing A A' B)) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
        (ExteriorAlgebra.ι T x) =
      deRhamBaseChangeInverseGenerator (A := A) (A' := A') (B := B) x := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  change (ExteriorAlgebra.lift T
      ⟨deRhamBaseChangeInverseGenerator (A := A) (A' := A') (B := B),
        deRhamBaseChangeInverseGenerator_sq_zero
          (A := A) (A' := A') (B := B)⟩) (ExteriorAlgebra.ι T x) = _
  exact ExteriorAlgebra.lift_ι_apply T
    (deRhamBaseChangeInverseGenerator (A := A) (A' := A') (B := B))
    (deRhamBaseChangeInverseGenerator_sq_zero
      (A := A) (A' := A') (B := B)) x

end
end Formalization.Books.Algebra.Unit132
