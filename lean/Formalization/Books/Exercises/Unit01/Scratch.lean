import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section

open CategoryTheory
open CategoryTheory.ShortComplex
open scoped TensorProduct

universe u w

example {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R S := Algebra.toModule
    ∃ (r : (S ⊗[R] ULift.{w} S) →ₗ[S] (S ⊗[R] ULift.{w} R)),
      r.comp (LinearMap.baseChange S
        (ULift.moduleEquiv.symm.toLinearMap.comp
          ((Algebra.linearMap R S).comp ULift.moduleEquiv.toLinearMap))) =
        LinearMap.id := by
  letI : Algebra R S := f.toAlgebra
  letI : Module R S := Algebra.toModule
  let i' : ULift.{w} R →ₗ[R] ULift.{w} S :=
    ULift.moduleEquiv.symm.toLinearMap.comp
      ((Algebra.linearMap R S).comp ULift.moduleEquiv.toLinearMap)
  let r : (S ⊗[R] ULift.{w} S) →ₗ[S] (S ⊗[R] ULift.{w} R) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun b =>
          { toFun := fun x => (b * x.down) ⊗ₜ[R] ULift.up (1 : R)
            map_add' := by
              intro x y
              change (b * (x.down + y.down)) ⊗ₜ[R] ULift.up (1 : R) = _
              rw [mul_add, TensorProduct.add_tmul]
            map_smul' := by
              intro a x
              simp [Algebra.smul_def, TensorProduct.smul_tmul', mul_assoc,
                mul_comm, mul_left_comm] }
        map_add' := by
          intro b c
          apply LinearMap.ext
          intro x
          change ((b + c) * x.down) ⊗ₜ[R] ULift.up (1 : R) =
            (b * x.down) ⊗ₜ[R] ULift.up (1 : R) +
              (c * x.down) ⊗ₜ[R] ULift.up (1 : R)
          rw [add_mul, TensorProduct.add_tmul]
        map_smul' := by
          intro c b
          apply LinearMap.ext
          intro x
          simp [Algebra.smul_def, TensorProduct.smul_tmul', mul_assoc] }
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ (fun b x => ?_) (fun x y hx hy => ?_)
  · simp
  · dsimp [r, i']
    change (b * algebraMap R S x.down) ⊗ₜ[R] ULift.up (1 : R) =
      b ⊗ₜ[R] x
    apply (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl S S) ULift.moduleEquiv).injective
    apply (TensorProduct.AlgebraTensorModule.rid R S S).injective
    simp [Algebra.smul_def, mul_comm]
  · simp only [map_add, hx, hy]

open scoped ModuleCat.Algebra

example {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : True := by
  letI : Algebra R S := f.toAlgebra
  let M := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)
  let N := ModuleCat.of R (ULift.{w} R)
  letI : Module S M := inferInstanceAs (Module S S)
  letI : Module R M := Module.compHom S f
  letI : SMulCommClass R S M := by
    constructor
    intro r s x
    change r • (s * (show S from x)) =
      s * (r • (show S from x))
    simpa [← Int.cast_smul_eq_zsmul S, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc]
  letI : Module S (M ⊗[R] N) := TensorProduct.leftModule
  trivial

example {S : Type u} [CommRing S] (n : ℤ) (b x : S) :
    b * x * (n : S) = b * (n • x) := by
  rw [← Int.cast_smul_eq_zsmul S n x]
  simp [smul_eq_mul, mul_comm, mul_assoc]
