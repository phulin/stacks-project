import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeIdentities

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section


variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

noncomputable abbrev deRhamBaseChangeSourceGrading (n : ℕ) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    Submodule A EB :=
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let sourceTower : IsScalarTower A B EB := inferInstance
  @Submodule.restrictScalars A B EB _ _ _ _ _ _
    sourceTower
    (exteriorPower B (ModuleOfDifferentials A B) n)

noncomputable abbrev deRhamBaseChangeTargetGrading (n : ℕ) :
    let T := deRhamBaseChangeRing A A' B
    Submodule A' (ExteriorAlgebra T (ModuleOfDifferentials A' T)) :=
  (exteriorPower (deRhamBaseChangeRing A A' B)
    (ModuleOfDifferentials A' (deRhamBaseChangeRing A A' B)) n).restrictScalars A'

noncomputable abbrev deRhamBaseChangeGrading (n : ℕ) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    Submodule A' (A' ⊗[A] EB) :=
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  (deRhamBaseChangeSourceGrading (A := A) (B := B) n).baseChange A'

noncomputable instance deRhamBaseChangeSourceGradedAlgebra :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    GradedAlgebra (deRhamBaseChangeSourceGrading (A := A) (B := B)) := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let sourceTower : IsScalarTower A B EB := inferInstance
  change GradedAlgebra (fun n => @Submodule.restrictScalars A B EB _ _ _ _ _ _
    sourceTower
    (exteriorPower B (ModuleOfDifferentials A B) n))
  let i : GradedAlgebra
      (fun n => exteriorPower B (ModuleOfDifferentials A B) n) := inferInstance
  exact { i with }

noncomputable def deRhamBaseChangeForwardGraded :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : GradedAlgebra (deRhamBaseChangeSourceGrading (A := A) (B := B)) := by
      infer_instance
    let : GradedAlgebra (deRhamBaseChangeTargetGrading
        (A := A) (A' := A') (B := B)) := by
      infer_instance
    (deRhamBaseChangeSourceGrading (A := A) (B := B)) →ₐᵍ[A]
      (fun n => (deRhamBaseChangeTargetGrading
        (A := A) (A' := A') (B := B) n).restrictScalars A) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let source := deRhamBaseChangeSourceGrading (A := A) (B := B)
  let target := deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B)
  let : GradedAlgebra source := by
    infer_instance
  let : GradedAlgebra target := by
    infer_instance
  let f := deRhamBaseChangeForwardA (A := A) (A' := A') (B := B)
  have hgen (m : ModuleOfDifferentials A B) :
      f (ExteriorAlgebra.ι B m) ∈ target 1 := by
    change deRhamBaseChangeForward (A := A) (A' := A') (B := B)
        (ExteriorAlgebra.ι B m) ∈ exteriorPower T (ModuleOfDifferentials A' T) 1
    rw [deRhamBaseChangeForward_ι]
    change ExteriorAlgebra.ι T _ ∈ (LinearMap.range (ExteriorAlgebra.ι T)) ^ 1
    rw [pow_one]
    exact LinearMap.mem_range_self _ _
  have hscalar (b : B) : f (algebraMap B EB b) ∈ target 0 := by
    change deRhamBaseChangeForward (A := A) (A' := A') (B := B)
        (algebraMap B EB b) ∈ exteriorPower T (ModuleOfDifferentials A' T) 0
    rw [(deRhamBaseChangeForward (A := A) (A' := A') (B := B)).commutes]
    change algebraMap T ET (algebraMap B T b) ∈
      exteriorPower T (ModuleOfDifferentials A' T) 0
    have hzero : (1 : ET) ∈ exteriorPower T (ModuleOfDifferentials A' T) 0 :=
      SetLike.one_mem_graded _
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Submodule.smul_mem _ (algebraMap B T b) hzero
  exact
    { f with
      map_mem := by
        intro n x hx
        induction hx using Submodule.pow_induction_on_left' with
        | algebraMap b => exact hscalar b
        | add x y n hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
        | mem_mul _ hm n x hx ih =>
            obtain ⟨m, rfl⟩ := hm
            rw [map_mul]
            change f (ExteriorAlgebra.ι B m) * f x ∈ target (n + 1)
            simpa [Nat.one_add] using
              SetLike.mul_mem_graded (A := target) (hgen m) ih }

noncomputable def deRhamBaseChangeForwardBaseGraded :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : GradedAlgebra (deRhamBaseChangeSourceGrading (A := A) (B := B)) := by
      infer_instance
    let : GradedAlgebra (deRhamBaseChangeTargetGrading
        (A := A) (A' := A') (B := B)) := by
      infer_instance
    let : GradedAlgebra (deRhamBaseChangeGrading
        (A := A) (A' := A') (B := B)) := by
      infer_instance
    (deRhamBaseChangeGrading (A := A) (A' := A') (B := B)) →ₐᵍ[A']
      (deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B)) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : GradedAlgebra (deRhamBaseChangeSourceGrading (A := A) (B := B)) := by
    infer_instance
  let : GradedAlgebra (deRhamBaseChangeTargetGrading
      (A := A) (A' := A') (B := B)) := by
    infer_instance
  let : GradedAlgebra (deRhamBaseChangeGrading
      (A := A) (A' := A') (B := B)) := by
    infer_instance
  exact GradedAlgHom.liftEquiv
    (deRhamBaseChangeSourceGrading (A := A) (B := B))
    (deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B))
    (deRhamBaseChangeForwardGraded (A := A) (A' := A') (B := B))

end
end Formalization.Books.Algebra.Unit132
