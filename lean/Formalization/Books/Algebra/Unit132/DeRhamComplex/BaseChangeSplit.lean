import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeHomogeneous

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section


variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

noncomputable def deRhamSourceGradeProjection (p : ℕ) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    EB →ₗ[A] deRhamBaseChangeSourceGrading (A := A) (B := B) p := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : GradedAlgebra (deRhamBaseChangeSourceGrading
      (A := A) (B := B)) := deRhamBaseChangeSourceGradedAlgebra
  exact (DirectSum.component A ℕ
    (fun n => ↥(deRhamBaseChangeSourceGrading (A := A) (B := B) n)) p).comp
      (DirectSum.decomposeAlgEquiv
        (deRhamBaseChangeSourceGrading (A := A) (B := B))).toLinearMap

@[simp]
theorem deRhamSourceGradeProjection_subtype (p : ℕ)
    (x : deRhamBaseChangeSourceGrading (A := A) (B := B) p) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    deRhamSourceGradeProjection (A := A) (B := B) p (x : EB) = x := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : GradedAlgebra (deRhamBaseChangeSourceGrading
      (A := A) (B := B)) := deRhamBaseChangeSourceGradedAlgebra
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same
    (deRhamBaseChangeSourceGrading (A := A) (B := B)) x.property

noncomputable def deRhamBaseChangeGradeProjection (p : ℕ) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    (A' ⊗[A] EB) →ₗ[A']
      (A' ⊗[A] deRhamBaseChangeSourceGrading (A := A) (B := B) p) := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  exact LinearMap.baseChange A'
    (deRhamSourceGradeProjection (A := A) (B := B) p)

theorem deRhamBaseChangeGradeProjection_toBaseChange (p : ℕ)
    (x : A' ⊗[A] deRhamBaseChangeSourceGrading (A := A) (B := B) p) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    deRhamBaseChangeGradeProjection (A := A) (A' := A') (B := B) p
      ((deRhamBaseChangeSourceGrading (A := A) (B := B) p).toBaseChange A' x :
        A' ⊗[A] EB) = x := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  refine TensorProduct.induction_on x (by simp) (fun a y => ?_)
    (fun u v hu hv => by
      rw [((deRhamBaseChangeSourceGrading
        (A := A) (B := B) p).toBaseChange A').map_add]
      change deRhamBaseChangeGradeProjection (A := A) (A' := A') (B := B) p
          (↑((deRhamBaseChangeSourceGrading
            (A := A) (B := B) p).toBaseChange A' u) +
            ↑((deRhamBaseChangeSourceGrading
              (A := A) (B := B) p).toBaseChange A' v)) = u + v
      rw [(deRhamBaseChangeGradeProjection
        (A := A) (A' := A') (B := B) p).map_add, hu, hv])
  rw [Submodule.coe_toBaseChange_tmul]
  change (LinearMap.baseChange A'
      (deRhamSourceGradeProjection (A := A) (B := B) p))
        (a ⊗ₜ[A] (y : EB)) = a ⊗ₜ[A] y
  rw [LinearMap.baseChange_tmul, deRhamSourceGradeProjection_subtype]

noncomputable def deRhamBaseChangeGradeRetraction (p : ℕ) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    deRhamBaseChangeGrading (A := A) (A' := A') (B := B) p →ₗ[A']
      (A' ⊗[A] deRhamBaseChangeSourceGrading (A := A) (B := B) p) := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  exact (deRhamBaseChangeGradeProjection
    (A := A) (A' := A') (B := B) p).comp (Submodule.subtype _)

noncomputable def deRhamBaseChangeGradeEquiv (p : ℕ) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    (A' ⊗[A] deRhamBaseChangeSourceGrading (A := A) (B := B) p) ≃ₗ[A']
      deRhamBaseChangeGrading (A := A) (A' := A') (B := B) p := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  let : RingHomInvPair (RingHom.id A') (RingHom.id A') := RingHomInvPair.ids
  exact LinearEquiv.ofLinear (σ₁₂ := RingHom.id A') (σ₂₁ := RingHom.id A')
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids)
    ((deRhamBaseChangeSourceGrading
      (A := A) (B := B) p).toBaseChange A')
    (deRhamBaseChangeGradeRetraction (A := A) (A' := A') (B := B) p)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := (deRhamBaseChangeSourceGrading
        (A := A) (B := B) p).toBaseChange_surjective A' x
      apply congrArg ((deRhamBaseChangeSourceGrading
        (A := A) (B := B) p).toBaseChange A')
      exact deRhamBaseChangeGradeProjection_toBaseChange
        (A := A) (A' := A') (B := B) p y)
    (by
      apply LinearMap.ext
      intro x
      exact deRhamBaseChangeGradeProjection_toBaseChange
        (A := A) (A' := A') (B := B) p x)

noncomputable def deRhamTermSourceGradeEquiv (p : ℕ) :
    let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
    let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
    let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
    deRhamTerm A B p ≃ₗ[A]
      deRhamBaseChangeSourceGrading (A := A) (B := B) p := by
  let EB := ExteriorAlgebra B (ModuleOfDifferentials A B)
  let : Algebra A EB := exteriorAlgebraA (A := A) (B := B)
  let : IsScalarTower A B EB := exteriorAlgebraTower (A := A) (B := B)
  exact
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; apply Subtype.ext; rfl
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }

end
end Formalization.Books.Algebra.Unit132
