import Formalization.Books.Algebra.Unit132.DeRhamComplex.Functoriality
import Formalization.Books.Algebra.Unit132.DeRhamComplex.BaseChangeRawEquiv

namespace Formalization.Books.Algebra.Unit132

open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section


variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]

private noncomputable def deRhamBaseChangeComponent (p : ℕ) :
    deRhamBaseChangeTerm A A' B p →ₗ[A']
      deRhamTerm A' (deRhamBaseChangeRing A A' B) p := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Module A (deRhamTerm A' T p) :=
    Module.restrictScalars A A' (deRhamTerm A' T p)
  let : IsScalarTower A A' (deRhamTerm A' T p) :=
    IsScalarTower.restrictScalars A A' (deRhamTerm A' T p)
  let f : deRhamTerm A B p →ₗ[A] deRhamTerm A' T p :=
    { toFun := deRhamMapComponent (A := A) (A' := A')
        (B := B) (B' := T) p
      map_add' := (deRhamMapComponent (A := A) (A' := A')
        (B := B) (B' := T) p).map_add
      map_smul' := by
        intro r x
        rw [(deRhamMapComponent (A := A) (A' := A')
          (B := B) (B' := T) p).map_smul]
        change (algebraMap A T r) • deRhamMapComponent
            (A := A) (A' := A') (B := B) (B' := T) p x =
          (algebraMap A' T (algebraMap A A' r)) • deRhamMapComponent
            (A := A) (A' := A') (B := B) (B' := T) p x
        rw [show algebraMap A T r = algebraMap A' T (algebraMap A A' r) by
          exact congrArg (fun g : A →+* T => g r)
            (IsScalarTower.algebraMap_eq A A' T)] }
  exact @LinearMap.liftBaseChange A (deRhamTerm A B p)
    (deRhamTerm A' T p) A' _ _ _ _ _ _
    (Module.restrictScalars A A' (deRhamTerm A' T p)) _
    (IsScalarTower.restrictScalars A A' (deRhamTerm A' T p)) f

private theorem deRhamBaseChangeComponent_tmul (p : ℕ) (a : A')
    (x : deRhamTerm A B p) :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    deRhamBaseChangeComponent (A := A) (A' := A') (B := B) p (a ⊗ₜ[A] x) =
      a • deRhamMapComponent
        (A := A) (A' := A') (B := B) (B' := T) p x := by
  rfl

theorem deRhamBaseChangeDifferentials_universal (b : B) :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    baseChangeDifferentialsEquiv (R := A) (R' := A') (S := B)
        (1 ⊗ₜ[A] universalDifferentialLinearMap A B b) =
      universalDifferentialLinearMap A' T (algebraMap B T b) := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  change KaehlerDifferential.tensorKaehlerEquivBase A A' B T
      (1 ⊗ₜ[A] universalDifferentialLinearMap A B b) = _
  rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul, one_smul]
  exact mapOfDifferentials_apply_universalDifferential
    (R := A) (T := A') (A := B) (B := T) b

theorem deRhamBaseChangeForward_component (p : ℕ) (x : deRhamTerm A B p) :
    let T := deRhamBaseChangeRing A A' B
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    deRhamBaseChangeForward (A := A) (A' := A') (B := B)
        (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      (deRhamMapComponent
        (A := A) (A' := A') (B := B) (B' := T) p x :
          ExteriorAlgebra T (ModuleOfDifferentials A' T)) := by
  let T := deRhamBaseChangeRing A A' B
  let ET := ExteriorAlgebra T (ModuleOfDifferentials A' T)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  have hx : x ∈ Submodule.span A (deRhamGenerators (A := A) (B := B) p) := by
    rw [deRhamGenerators_span (A := A) (B := B) p]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun (x : deRhamTerm A B p) _ =>
      deRhamBaseChangeForward (A := A) (A' := A') (B := B)
          (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (deRhamMapComponent
          (A := A) (A' := A') (B := B) (B' := T) p x : ET))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, rfl⟩
    rcases z with ⟨b₀, b⟩
    rw [deRhamMapComponent_on_generator]
    simp only [deRhamGenerator, Submodule.coe_smul, Algebra.smul_def]
    rw [map_mul,
      (deRhamBaseChangeForward (A := A) (A' := A') (B := B)).commutes]
    rw [show algebraMap B ET b₀ = algebraMap T ET (algebraMap B T b₀) by
      exact congrArg (fun q : B →+* ET => q b₀)
        (IsScalarTower.algebraMap_eq B T ET)]
    rw [deRhamBaseChangeForward_ιMulti]
    have hm :
        (fun i => baseChangeDifferentialsEquiv
          (R := A) (R' := A') (S := B)
            (1 ⊗ₜ[A] universalDifferentialLinearMap A B (b i))) =
        (fun i => universalDifferentialLinearMap A' T
          (algebraMap B T (b i))) := by
      funext i
      exact deRhamBaseChangeDifferentials_universal (A := A) (A' := A') (B := B) (b i)
    rw [hm]
    exact (IsScalarTower.algebraMap_smul T b₀ _).symm
  · simp
  · intro u v hu hv ihu ihv
    simp only [map_add, Submodule.coe_add, ihu, ihv]
  · intro a u hu ihu
    change deRhamBaseChangeForwardA (A := A) (A' := A') (B := B)
        (a • (u : ExteriorAlgebra B (ModuleOfDifferentials A B))) =
      (deRhamMapComponent (A := A) (A' := A')
        (B := B) (B' := T) p) (a • u)
    have hc := congrArg (fun y : deRhamTerm A' T p => (y : ET))
      ((deRhamMapComponent (A := A) (A' := A')
        (B := B) (B' := T) p).map_smul a u)
    calc
      deRhamBaseChangeForwardA (A := A) (A' := A') (B := B)
          (a • (u : ExteriorAlgebra B (ModuleOfDifferentials A B))) =
        a • deRhamBaseChangeForwardA (A := A) (A' := A') (B := B)
          (u : ExteriorAlgebra B (ModuleOfDifferentials A B)) :=
            (deRhamBaseChangeForwardA
              (A := A) (A' := A') (B := B)).toLinearMap.map_smul a _
      _ = a • (deRhamMapComponent (A := A) (A' := A')
          (B := B) (B' := T) p u : ET) := congrArg (a • ·) ihu
      _ = (deRhamMapComponent (A := A) (A' := A')
          (B := B) (B' := T) p (a • u) : ET) := hc.symm

private theorem deRhamBaseChangeRawEquiv_toLinearMap (p : ℕ) :
    (deRhamBaseChangeRawEquiv (A := A) (A' := A') (B := B) p).toLinearMap =
      deRhamBaseChangeComponent (A := A) (A' := A') (B := B) p := by
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x (by simp) (fun a y => ?_)
    (fun u v hu hv => by simpa only [map_add] using congrArg₂ (· + ·) hu hv)
  apply Subtype.ext
  rw [LinearEquiv.coe_toLinearMap, deRhamBaseChangeRawEquiv_tmul,
    deRhamBaseChangeComponent_tmul, deRhamBaseChangeForward_component]
  rfl

theorem deRhamBaseChangeRawEquiv_commutes (p : ℕ)
    (x : deRhamBaseChangeTerm A A' B p) :
    deRhamBaseChangeRawEquiv (A := A) (A' := A') (B := B) (p + 1)
        (deRhamBaseChangeDifferential (A := A) (A' := A') (B := B) p x) =
      deRhamDifferential (A := A') (B := deRhamBaseChangeRing A A' B) p
        (deRhamBaseChangeRawEquiv (A := A) (A' := A') (B := B) p x) := by
  let T := deRhamBaseChangeRing A A' B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  rw [show deRhamBaseChangeRawEquiv (A := A) (A' := A') (B := B) (p + 1)
      (deRhamBaseChangeDifferential (A := A) (A' := A') (B := B) p x) =
        deRhamBaseChangeComponent (A := A) (A' := A') (B := B) (p + 1)
          (deRhamBaseChangeDifferential (A := A) (A' := A') (B := B) p x) by
      exact LinearMap.congr_fun
        (deRhamBaseChangeRawEquiv_toLinearMap
          (A := A) (A' := A') (B := B) (p + 1)) _]
  rw [show deRhamBaseChangeRawEquiv (A := A) (A' := A') (B := B) p x =
        deRhamBaseChangeComponent (A := A) (A' := A') (B := B) p x by
      exact LinearMap.congr_fun
        (deRhamBaseChangeRawEquiv_toLinearMap
          (A := A) (A' := A') (B := B) p) _]
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a y
    simp only [deRhamBaseChangeDifferential,
      TensorProduct.AlgebraTensorModule.lTensor_tmul]
    rw [deRhamBaseChangeComponent_tmul, deRhamBaseChangeComponent_tmul,
      deRhamMapComponent_commutes]
    exact ((deRhamDifferential (A := A') (B := T) p).map_smul a _).symm
  · intro u v hu hv
    simp only [map_add, hu, hv]

end
end Formalization.Books.Algebra.Unit132
