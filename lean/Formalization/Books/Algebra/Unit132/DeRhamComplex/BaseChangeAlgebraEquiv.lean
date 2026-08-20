import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeInverse

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section

variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

noncomputable def deRhamBaseChangeForwardA :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    EB →ₐ[A] ExteriorAlgebra T (ModuleOfDifferentials A' T) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let f := deRhamBaseChangeForward (A := A) (A' := A') (B := B)
  exact
    { toRingHom := f.toRingHom
      commutes' := by
        intro a
        change f (algebraMap B EB (algebraMap A B a)) =
          algebraMap A (ExteriorAlgebra T (ModuleOfDifferentials A' T)) a
        rw [f.commutes]
        calc
          algebraMap T (ExteriorAlgebra T (ModuleOfDifferentials A' T))
              (algebraMap B T (algebraMap A B a)) =
              algebraMap T (ExteriorAlgebra T (ModuleOfDifferentials A' T))
                (algebraMap A T a) := by
            apply congrArg (algebraMap T
              (ExteriorAlgebra T (ModuleOfDifferentials A' T)))
            exact congrArg (fun q : A →+* T => q a)
              (IsScalarTower.algebraMap_eq A B T).symm
          _ = algebraMap A (ExteriorAlgebra T (ModuleOfDifferentials A' T)) a := by
            exact congrArg (fun q : A →+* ExteriorAlgebra T
              (ModuleOfDifferentials A' T) => q a)
              (IsScalarTower.algebraMap_eq A T
                (ExteriorAlgebra T (ModuleOfDifferentials A' T))).symm }

noncomputable def deRhamBaseChangeForwardBase :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    A' ⊗[A] EB →ₐ[A'] ExteriorAlgebra T (ModuleOfDifferentials A' T) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  exact AlgHom.liftEquiv A A' EB
    (ExteriorAlgebra T (ModuleOfDifferentials A' T))
    (deRhamBaseChangeForwardA (A := A) (A' := A') (B := B))

@[simp]
theorem deRhamBaseChangeForwardBase_tmul (a : A')
    (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B) (a ⊗ₜ[A] x) =
      a • deRhamBaseChangeForward (A := A) (A' := A') (B := B) x := by
  rw [deRhamBaseChangeForwardBase, AlgHom.liftEquiv_tmul]
  rfl

theorem deRhamBaseChangeForwardBase_scalar
    (t : deRhamBaseChangeRing A A' B) :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)
        (algebraMap T (A' ⊗[A] EB) t) =
      algebraMap T ET t := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  change deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)
      (baseChangeExteriorScalarMap (A := A) (A' := A') (B := B) t) =
    algebraMap T ET t
  refine TensorProduct.induction_on t (by simp) (fun a b => ?_)
    (fun u v hu hv => by simpa only [map_add] using congrArg₂ (· + ·) hu hv)
  rw [baseChangeExteriorScalarMap_tmul, deRhamBaseChangeForwardBase_tmul]
  change a • deRhamBaseChangeForward (A := A) (A' := A') (B := B)
      (algebraMap B EB b) = algebraMap T ET (a ⊗ₜ[A] b)
  rw [(deRhamBaseChangeForward (A := A) (A' := A') (B := B)).commutes]
  change algebraMap A' ET a * algebraMap T ET (algebraMap B T b) =
    algebraMap T ET (a ⊗ₜ[A] b)
  change algebraMap T ET (algebraMap A' T a) *
      algebraMap T ET (algebraMap B T b) = _
  rw [← map_mul]
  congr 1
  exact (Algebra.TensorProduct.tmul_mul_tmul a 1 1 b).trans (by simp)

noncomputable def deRhamBaseChangeForwardT :
    let T := deRhamBaseChangeRing A A' B
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    let : Algebra T (A' ⊗[A] EB) :=
      baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
    A' ⊗[A] EB →ₐ[T] ET := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  exact
    { toRingHom :=
        (deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)).toRingHom
      commutes' := deRhamBaseChangeForwardBase_scalar
        (A := A) (A' := A') (B := B) }

end
end Formalization.Books.Algebra.Unit132
