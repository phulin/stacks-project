import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeDefs

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section

variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

private noncomputable def includeBaseChangeDifferentials :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    ModuleOfDifferentials A B →ₗ[B]
      A' ⊗[A] ModuleOfDifferentials A B := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  exact
    { toFun := fun m => 1 ⊗ₜ[A] m
      map_add' := fun m n => TensorProduct.tmul_add 1 m n
      map_smul' := by
        intro b m
        change 1 ⊗ₜ[A] (b • m) = b • (1 ⊗ₜ[A] m)
        rw [KaehlerDifferential.mulActionBaseChange_smul_tmul] }

private noncomputable def deRhamBaseChangeForwardGeneratorT :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange A A' B
    let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
      KaehlerDifferential.moduleBaseChange' A A' B T
    A' ⊗[A] ModuleOfDifferentials A B →ₗ[T]
      ExteriorAlgebra T (ModuleOfDifferentials A' T) := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  exact (ExteriorAlgebra.ι T).comp
    (baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)).toLinearMap

private noncomputable def deRhamBaseChangeForwardGenerator :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    ModuleOfDifferentials A B →ₗ[B]
      ExteriorAlgebra T (ModuleOfDifferentials A' T) := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  exact
    ((deRhamBaseChangeForwardGeneratorT (A := A) (A' := A') (B := B)
      ).restrictScalars B).comp
      (includeBaseChangeDifferentials (A := A) (A' := A') (B := B))

private theorem deRhamBaseChangeForwardGenerator_sq_zero
    (m : ModuleOfDifferentials A B) :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    deRhamBaseChangeForwardGenerator (A := A) (A' := A') (B := B) m *
      deRhamBaseChangeForwardGenerator (A := A) (A' := A') (B := B) m = 0 := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Module B (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange A A' B
  let : Module T (A' ⊗[A] ModuleOfDifferentials A B) :=
    KaehlerDifferential.moduleBaseChange' A A' B T
  apply ExteriorAlgebra.ι_sq_zero

noncomputable def deRhamBaseChangeForward :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    ExteriorAlgebra B (ModuleOfDifferentials A B) →ₐ[B]
      ExteriorAlgebra T (ModuleOfDifferentials A' T) := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  exact ExteriorAlgebra.lift B
    ⟨deRhamBaseChangeForwardGenerator (A := A) (A' := A') (B := B),
      deRhamBaseChangeForwardGenerator_sq_zero (A := A) (A' := A') (B := B)⟩

@[simp]
theorem deRhamBaseChangeForward_ι (m : ModuleOfDifferentials A B) :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    deRhamBaseChangeForward (A := A) (A' := A') (B := B)
        (ExteriorAlgebra.ι B m) =
      ExteriorAlgebra.ι T
        (baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)
          (1 ⊗ₜ[A] m)) := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  rw [deRhamBaseChangeForward, ExteriorAlgebra.lift_ι_apply]
  simp [deRhamBaseChangeForwardGenerator,
    deRhamBaseChangeForwardGeneratorT, includeBaseChangeDifferentials]

theorem deRhamBaseChangeForward_ιMulti
    (p : ℕ) (m : Fin p → ModuleOfDifferentials A B) :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    deRhamBaseChangeForward (A := A) (A' := A') (B := B)
        (exteriorPower.ιMulti B p m :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      ExteriorAlgebra.ιMulti T p (fun i =>
        baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)
          (1 ⊗ₜ[A] m i)) := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  change deRhamBaseChangeForward (A := A) (A' := A') (B := B)
      (List.ofFn (fun i => ExteriorAlgebra.ι B (m i))).prod = _
  rw [map_list_prod, ExteriorAlgebra.ιMulti_apply]
  simp only [List.map_ofFn]
  congr 1
  congr 1
  funext i
  change deRhamBaseChangeForward (A := A) (A' := A') (B := B)
      (ExteriorAlgebra.ι B (m i)) = _
  exact deRhamBaseChangeForward_ι (A := A) (A' := A') (B := B) (m i)

end
end Formalization.Books.Algebra.Unit132
