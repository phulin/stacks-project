import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeSplit

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section


variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

noncomputable def deRhamTargetGradeTermEquiv (p : ℕ) :
    let T := deRhamBaseChangeRing A A' B
    deRhamBaseChangeTargetGrading (A := A) (A' := A') (B := B) p ≃ₗ[A']
      deRhamTerm A' T p := by
  let T := deRhamBaseChangeRing A A' B
  exact
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; apply Subtype.ext; rfl
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }

noncomputable def deRhamBaseChangeRawEquiv (p : ℕ) :
    deRhamBaseChangeTerm A A' B p ≃ₗ[A']
      deRhamTerm A' (deRhamBaseChangeRing A A' B) p := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  exact (LinearEquiv.baseChange A A' _ _
    (deRhamTermSourceGradeEquiv (A := A) (B := B) p)).trans
      ((deRhamBaseChangeGradeEquiv (A := A) (A' := A') (B := B) p).trans
        ((deRhamBaseChangeHomogeneousEquiv
          (A := A) (A' := A') (B := B) p).trans
          (deRhamTargetGradeTermEquiv (A := A) (A' := A') (B := B) p)))

theorem deRhamBaseChangeRawEquiv_tmul (p : ℕ) (a : A')
    (x : deRhamTerm A B p) :
    let T := deRhamBaseChangeRing A A' B
    ((deRhamBaseChangeRawEquiv (A := A) (A' := A') (B := B) p
      (a ⊗ₜ[A] x) : deRhamTerm A' T p) :
        ExteriorAlgebra T (ModuleOfDifferentials A' T)) =
      a • deRhamBaseChangeForward (A := A) (A' := A') (B := B)
        (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  let T := deRhamBaseChangeRing A A' B
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : Algebra T (A' ⊗[A] EB) :=
    baseChangeExteriorAlgebra (A := A) (A' := A') (B := B)
  let : IsScalarTower A' T (A' ⊗[A] EB) :=
    baseChangeExteriorTower (A := A) (A' := A') (B := B)
  simp only [deRhamBaseChangeRawEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul]
  change deRhamBaseChangeForwardBase (A := A) (A' := A') (B := B)
      ((deRhamBaseChangeSourceGrading (A := A) (B := B) p).toBaseChange A'
        (a ⊗ₜ[A] deRhamTermSourceGradeEquiv (A := A) (B := B) p x)) =
    a • deRhamBaseChangeForward (A := A) (A' := A') (B := B) x
  rw [Submodule.coe_toBaseChange_tmul, deRhamBaseChangeForwardBase_tmul]
  rfl

end
end Formalization.Books.Algebra.Unit132
