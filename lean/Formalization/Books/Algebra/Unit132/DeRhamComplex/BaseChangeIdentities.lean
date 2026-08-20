import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeAlgebraEquiv

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section

variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

theorem deRhamBaseChangeForwardBase_generator
    (y : A' ⊗[A] ModuleOfDifferentials A B) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)
        (baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B) y) =
      ExteriorAlgebra.ι T
        (baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B) y) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  refine TensorProduct.induction_on y (by simp) (fun a m => ?_)
    (fun u v hu hv => by simpa only [map_add] using congrArg₂ (· + ·) hu hv)
  rw [baseChangeExteriorGeneratorA'_tmul, deRhamBaseChangeForwardBase_tmul,
    deRhamBaseChangeForward_ι]
  have ht : (algebraMap A' T a) • (1 ⊗ₜ[A] m) = a ⊗ₜ[A] m := by
    rw [IsScalarTower.algebraMap_smul T a, TensorProduct.smul_tmul']
    simp
  calc
    a • ExteriorAlgebra.ι T
        (baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)
          (1 ⊗ₜ[A] m)) =
      ExteriorAlgebra.ι T
        ((algebraMap A' T a) •
          baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)
            (1 ⊗ₜ[A] m)) := by
        rw [(ExteriorAlgebra.ι T).map_smul,
          IsScalarTower.algebraMap_smul T a]
    _ = ExteriorAlgebra.ι T
        (baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)
          ((algebraMap A' T a) • (1 ⊗ₜ[A] m))) := by
        rw [(baseChangeDifferentialsEquiv
          (R := A) (R' := A') (S := B)).map_smul]
    _ = _ := congrArg (fun z => ExteriorAlgebra.ι T
      (baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B) z)) ht

theorem deRhamBaseChangeForward_inverse :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    (deRhamBaseChangeForwardT (A := A) (A' := A') (B := B)).comp
        (deRhamBaseChangeInverse (A := A) (A' := A') (B := B)) =
      AlgHom.id T ET := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  change deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)
      (deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
        (ExteriorAlgebra.ι T x)) = ExteriorAlgebra.ι T x
  rw [deRhamBaseChangeInverse_ι]
  change deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)
      (baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
        ((baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)).symm x)) =
    ExteriorAlgebra.ι T x
  rw [deRhamBaseChangeForwardBase_generator,
    (baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)).apply_symm_apply]

theorem deRhamBaseChangeInverse_forward
    (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
        (deRhamBaseChangeForward (A := A) (A' := A') (B := B) x) =
      1 ⊗ₜ[A] x := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  change deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
      (deRhamBaseChangeForward (A := A) (A' := A') (B := B) x) =
    1 ⊗ₜ[A] x
  refine ExteriorAlgebra.induction (fun b => ?_) (fun m => ?_)
    (fun u v hu hv => by
      rw [map_mul, map_mul, hu, hv, Algebra.TensorProduct.tmul_mul_tmul]
      simp)
    (fun u v hu hv => by
      rw [map_add, map_add, hu, hv, TensorProduct.tmul_add]) x
  · rw [(deRhamBaseChangeForward (A := A) (A' := A') (B := B)).commutes]
    change deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
        (algebraMap T (ExteriorAlgebra T (ModuleOfDifferentials A' T))
          (algebraMap B T b)) = _
    rw [(deRhamBaseChangeInverse (A := A) (A' := A') (B := B)).commutes]
    change baseChangeExteriorScalarMap (A := A) (A' := A') (B := B)
        (algebraMap B T b) = 1 ⊗ₜ[A] algebraMap B EB b
    change baseChangeExteriorScalarMap (A := A) (A' := A') (B := B)
        (1 ⊗ₜ[A] b) = _
    rw [baseChangeExteriorScalarMap_tmul]
  · rw [deRhamBaseChangeForward_ι, deRhamBaseChangeInverse_ι]
    change baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
        ((baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)).symm
          (baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)
            (1 ⊗ₜ[A] m))) = _
    rw [(baseChangeDifferentialsEquiv
      (R := A) (R' := A') (S := B)).symm_apply_apply]
    exact baseChangeExteriorGeneratorA'_tmul
      (A := A) (A' := A') (B := B) 1 m

theorem deRhamBaseChangeInverse_forwardT :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    ((deRhamBaseChangeInverse (A := A) (A' := A') (B := B)).restrictScalars A').comp
        (deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)) =
      AlgHom.id A' (A' ⊗[A] EB) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  change ((deRhamBaseChangeInverse (A := A) (A' := A') (B := B)).restrictScalars A').comp
      (deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)) =
    AlgHom.id A' (A' ⊗[A] EB)
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro x
  change deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
      (deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)
        (1 ⊗ₜ[A] x)) = 1 ⊗ₜ[A] x
  rw [deRhamBaseChangeForwardBase_tmul, one_smul]
  exact deRhamBaseChangeInverse_forward (A := A) (A' := A') (B := B)
    x

noncomputable def deRhamBaseChangeAlgebraEquiv :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    A' ⊗[A] EB ≃ₐ[A'] ET := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  exact AlgEquiv.ofAlgHom
    (deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B))
    ((deRhamBaseChangeInverse (A := A) (A' := A') (B := B)).restrictScalars A')
    (by
      apply AlgHom.ext
      intro z
      change deRhamBaseChangeForwardT (A := A) (A' := A') (B := B)
          (deRhamBaseChangeInverse (A := A) (A' := A') (B := B) z) = z
      exact congrArg (fun f => f z)
        (deRhamBaseChangeForward_inverse (A := A) (A' := A') (B := B)))
    (deRhamBaseChangeInverse_forwardT (A := A) (A' := A') (B := B))

end
end Formalization.Books.Algebra.Unit132
