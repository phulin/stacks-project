import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeInverseGraded

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section


variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

noncomputable def deRhamBaseChangeHomogeneousForward (p : ℕ) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    deRhamBaseChangeGrading (A := A) (A' := A') (B := B) p →ₗ[A']
      deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B) p := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : GradedAlgebra (deRhamBaseChangeTargetGrading
      (A := A) (A' := A') (B := B)) := by infer_instance
  let : GradedAlgebra (deRhamBaseChangeGrading
      (A := A) (A' := A') (B := B)) := by infer_instance
  exact ((deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)).toLinearMap.comp
    (Submodule.subtype _)).codRestrict _ fun x =>
      (deRhamBaseChangeForwardBaseGraded
        (A := A) (A' := A') (B := B)).map_mem x.property

noncomputable def deRhamBaseChangeHomogeneousInverse (p : ℕ) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B) p →ₗ[A']
      deRhamBaseChangeGrading (A := A) (A' := A') (B := B) p := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  let : GradedAlgebra (deRhamBaseChangeTargetGrading
      (A := A) (A' := A') (B := B)) := by infer_instance
  let : GradedAlgebra (deRhamBaseChangeGrading
      (A := A) (A' := A') (B := B)) := by infer_instance
  let gA' := (deRhamBaseChangeInverse
    (A := A) (A' := A') (B := B)).restrictScalars A'
  exact (gA'.toLinearMap.comp (Submodule.subtype _)).codRestrict _ fun x =>
    (deRhamBaseChangeInverseGraded
      (A := A) (A' := A') (B := B)).map_mem x.property

theorem deRhamBaseChangeHomogeneous_forward_inverse (p : ℕ) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    (deRhamBaseChangeHomogeneousForward (A := A) (A' := A') (B := B) p).comp
      (deRhamBaseChangeHomogeneousInverse (A := A) (A' := A') (B := B) p) =
      LinearMap.id := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)
      (deRhamBaseChangeInverse (A := A) (A' := A') (B := B) x) = x
  exact congrArg (fun q => q x)
    (deRhamBaseChangeForward_inverse (A := A) (A' := A') (B := B))

theorem deRhamBaseChangeHomogeneous_inverse_forward (p : ℕ) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    (deRhamBaseChangeHomogeneousInverse (A := A) (A' := A') (B := B) p).comp
      (deRhamBaseChangeHomogeneousForward (A := A) (A' := A') (B := B) p) =
      LinearMap.id := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
      (deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B) x) = x
  exact congrArg (fun q => q x)
    (deRhamBaseChangeInverse_forwardT (A := A) (A' := A') (B := B))

noncomputable def deRhamBaseChangeHomogeneousEquiv (p : ℕ) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    let : IsScalarTower A' T (A' ⊗[A] EB) :=
      baseChangeExteriorTower (A := A) (A' := A') (B := B)
    deRhamBaseChangeGrading (A := A) (A' := A') (B := B) p ≃ₗ[A']
      deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B) p := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  let : RingHomInvPair (RingHom.id A') (RingHom.id A') := RingHomInvPair.ids
  exact LinearEquiv.ofLinear (σ₁₂ := RingHom.id A') (σ₂₁ := RingHom.id A')
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids)
    (deRhamBaseChangeHomogeneousForward (A := A) (A' := A') (B := B) p)
    (deRhamBaseChangeHomogeneousInverse (A := A) (A' := A') (B := B) p)
    (deRhamBaseChangeHomogeneous_forward_inverse (A := A) (A' := A') (B := B) p)
    (deRhamBaseChangeHomogeneous_inverse_forward (A := A) (A' := A') (B := B) p)

end
end Formalization.Books.Algebra.Unit132
