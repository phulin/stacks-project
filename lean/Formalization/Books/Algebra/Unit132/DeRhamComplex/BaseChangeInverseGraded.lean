import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeDegree

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section


variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

theorem deRhamBaseChangeInverse_scalar_mem_degree_zero
    (t : deRhamBaseChangeRing A A' B) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    algebraMap T (A' ⊗[A] EB) t ∈
      deRhamBaseChangeGrading (A := A) (A' := A') (B := B) 0 := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  change baseChangeExteriorScalarMap (A := A) (A' := A') (B := B) t ∈
    (deRhamBaseChangeSourceGrading (A := A) (B := B) 0).baseChange A'
  refine TensorProduct.induction_on t (by simp) (fun a b => ?_)
    (fun u v hu hv => by simpa only [map_add] using add_mem hu hv)
  rw [baseChangeExteriorScalarMap_tmul]
  apply Submodule.tmul_mem_baseChange_of_mem
  change algebraMap B EB b ∈ exteriorPower B (ModuleOfDifferentials A B) 0
  have hzero : (1 : EB) ∈ exteriorPower B (ModuleOfDifferentials A B) 0 :=
    SetLike.one_mem_graded _
  simpa only [Algebra.algebraMap_eq_smul_one] using
    Submodule.smul_mem _ b hzero

theorem baseChangeExteriorGenerator_mem_degree_one
    (y : A' ⊗[A] ModuleOfDifferentials A B) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B) y ∈
      deRhamBaseChangeGrading (A := A) (A' := A') (B := B) 1 := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  refine TensorProduct.induction_on y (by simp) (fun a m => ?_)
    (fun u v hu hv => by simpa only [map_add] using add_mem hu hv)
  rw [baseChangeExteriorGeneratorA'_tmul]
  apply Submodule.tmul_mem_baseChange_of_mem
  change ExteriorAlgebra.ι B m ∈
    exteriorPower B (ModuleOfDifferentials A B) 1
  change ExteriorAlgebra.ι B m ∈ (LinearMap.range (ExteriorAlgebra.ι B)) ^ 1
  rw [pow_one]
  exact LinearMap.mem_range_self _ _

theorem deRhamBaseChangeInverse_generator_mem_degree_one
    (x : ModuleOfDifferentials A' (deRhamBaseChangeRing A A' B)) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
        (ExteriorAlgebra.ι T x) ∈
      deRhamBaseChangeGrading (A := A) (A' := A') (B := B) 1 := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  change deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
      (ExteriorAlgebra.ι T x) ∈
    deRhamBaseChangeGrading (A := A) (A' := A') (B := B) 1
  rw [deRhamBaseChangeInverse_ι]
  exact baseChangeExteriorGenerator_mem_degree_one
    ((baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)).symm x)

noncomputable def deRhamBaseChangeInverseGraded :
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
    deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B) →ₐᵍ[A']
      deRhamBaseChangeGrading (A := A) (A' := A') (B := B) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  let target := deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B)
  let V := deRhamBaseChangeGrading (A := A) (A' := A') (B := B)
  let : GradedAlgebra target := by infer_instance
  let : GradedAlgebra V := by infer_instance
  let gA' := (deRhamBaseChangeInverse
    (A := A) (A' := A') (B := B)).restrictScalars A'
  exact
    { gA' with
      map_mem := by
        intro n x hx
        induction hx using Submodule.pow_induction_on_left' with
        | algebraMap t =>
            change deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
                (algebraMap T (ExteriorAlgebra T (ModuleOfDifferentials A' T)) t) ∈ V 0
            rw [(deRhamBaseChangeInverse (A := A) (A' := A') (B := B)).commutes]
            exact deRhamBaseChangeInverse_scalar_mem_degree_zero t
        | add x y n hx hy ihx ihy =>
            simpa only [map_add] using add_mem ihx ihy
        | mem_mul _ hm n x hx ih =>
            obtain ⟨m, rfl⟩ := hm
            rw [gA'.map_mul]
            change deRhamBaseChangeInverse (A := A) (A' := A') (B := B)
                (ExteriorAlgebra.ι T m) *
              deRhamBaseChangeInverse (A := A) (A' := A') (B := B) x ∈ V (n + 1)
            rw [deRhamBaseChangeInverse_ι]
            change baseChangeExteriorGeneratorA' (A := A) (A' := A') (B := B)
                ((baseChangeDifferentialsEquiv
                  (R := A) (R' := A') (S := B)).symm m) *
              deRhamBaseChangeInverse (A := A) (A' := A') (B := B) x ∈ V (n + 1)
            simpa [Nat.one_add, gA'] using SetLike.mul_mem_graded (A := V)
              (baseChangeExteriorGenerator_mem_degree_one
                ((baseChangeDifferentialsEquiv
                  (R := A) (R' := A') (S := B)).symm m)) ih }

end
end Formalization.Books.Algebra.Unit132
