import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Epi
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exercises, Chapter 5: Flat ring maps

This file records the two explicit witnesses requested for the failure of
flatness over `k[x,y]`.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit05

open scoped TensorProduct

/-! ## The polynomial ring and the ideal `(x,y)` -/

/-- The two-variable polynomial ring used in both examples. -/
abbrev twoVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The ideal `(x,y)` in `k[x,y]`. -/
def polynomialXYIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (twoVariablePolynomialRing k))

/-- The inclusion of `(x,y)` into `k[x,y]`. -/
def polynomialXYIdealInclusion (k : Type u) [Field k] :
    (polynomialXYIdeal k : Type u) →ₗ[twoVariablePolynomialRing k]
      twoVariablePolynomialRing k :=
  (polynomialXYIdeal k).subtype

/-- The map obtained by tensoring the ideal inclusion with `(x,y)`. -/
def polynomialXYIdealTensorInclusion (k : Type u) [Field k] :
    ((polynomialXYIdeal k : Type u) ⊗[twoVariablePolynomialRing k]
        (polynomialXYIdeal k : Type u)) →ₗ[twoVariablePolynomialRing k]
      (twoVariablePolynomialRing k ⊗[twoVariablePolynomialRing k]
        (polynomialXYIdeal k : Type u)) :=
  (polynomialXYIdeal k).subtype.rTensor (polynomialXYIdeal k)

/-- For `N = (x,y)`, the ideal inclusion is an injection whose tensor with
`N` is not injective. -/
theorem polynomialXYIdeal_tensor_counterexample (k : Type u) [Field k] :
    Function.Injective (polynomialXYIdealInclusion k) ∧
      ¬ Function.Injective (polynomialXYIdealTensorInclusion k) := by
  constructor
  · exact Submodule.injective_subtype (polynomialXYIdeal k)
  · let ev : twoVariablePolynomialRing k →+* k :=
      MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
    letI : Algebra (twoVariablePolynomialRing k) k := ev.toAlgebra
    let f₀ : (polynomialXYIdeal k : Type u) →ₗ[twoVariablePolynomialRing k] k :=
      { toFun := fun p => MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1) p.1
        map_add' := by
          intro p q
          simp
        map_smul' := by
          intro r p
          change MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1)
              (r * p.1) = ev r * MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1) p.1
          have hp : p.1 ∈ Ideal.span
              ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
                Set (twoVariablePolynomialRing k)) := p.2
          rcases (Ideal.mem_span_pair.mp hp) with ⟨a, b, hab⟩
          have hcoeff (q s : twoVariablePolynomialRing k) :
              MvPolynomial.coeff 0 (q * s) = MvPolynomial.constantCoeff q *
                MvPolynomial.coeff 0 s := by
            simpa only [MvPolynomial.constantCoeff_eq] using
              (map_mul (MvPolynomial.constantCoeff : twoVariablePolynomialRing k →+*
                k) q s)
          rw [← hab, mul_add, ← mul_assoc r a, ← mul_assoc r b, MvPolynomial.coeff_add]
          simp [ev, MvPolynomial.eval₂Hom_zero_apply, MvPolynomial.coeff_mul_X', hcoeff] }
    let f₁ : (polynomialXYIdeal k : Type u) →ₗ[twoVariablePolynomialRing k] k :=
      { toFun := fun p => MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) p.1
        map_add' := by
          intro p q
          simp
        map_smul' := by
          intro r p
          change MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)
              (r * p.1) = ev r * MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) p.1
          have hp : p.1 ∈ Ideal.span
              ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
                Set (twoVariablePolynomialRing k)) := p.2
          rcases (Ideal.mem_span_pair.mp hp) with ⟨a, b, hab⟩
          have hcoeff (q s : twoVariablePolynomialRing k) :
              MvPolynomial.coeff 0 (q * s) = MvPolynomial.constantCoeff q *
                MvPolynomial.coeff 0 s := by
            simpa only [MvPolynomial.constantCoeff_eq] using
              (map_mul (MvPolynomial.constantCoeff : twoVariablePolynomialRing k →+* k) q s)
          rw [← hab, mul_add, ← mul_assoc r a, ← mul_assoc r b, MvPolynomial.coeff_add]
          simp [ev, MvPolynomial.eval₂Hom_zero_apply, MvPolynomial.coeff_mul_X', hcoeff] }
    have hev : Function.Surjective (algebraMap (twoVariablePolynomialRing k) k) := by
      intro c
      refine ⟨MvPolynomial.C c, ?_⟩
      change ev (MvPolynomial.C c) = c
      simp [ev]
    letI : Algebra.IsEpi (twoVariablePolynomialRing k) k :=
      Algebra.isEpi_of_surjective_algebraMap _ _ hev
    let xI : (polynomialXYIdeal k : Type u) :=
      ⟨MvPolynomial.X (0 : Fin 2), Ideal.subset_span (by simp)⟩
    let yI : (polynomialXYIdeal k : Type u) :=
      ⟨MvPolynomial.X (1 : Fin 2), Ideal.subset_span (by simp)⟩
    let z : (polynomialXYIdeal k : Type u) ⊗[twoVariablePolynomialRing k]
        (polynomialXYIdeal k : Type u) := xI ⊗ₜ yI - yI ⊗ₜ xI
    have hz : z ≠ 0 := by
      intro hz
      have hm : TensorProduct.map f₀ f₁ z = 0 := by
        rw [hz]
        simp
      have hm' := congrArg (TensorProduct.lid' (twoVariablePolynomialRing k) k k) hm
      have : (1 : k) = 0 := by
        simpa [z, xI, yI, f₀, f₁] using hm'
      exact one_ne_zero this
    have hzmap : polynomialXYIdealTensorInclusion k z = 0 := by
      apply (TensorProduct.lid (twoVariablePolynomialRing k) (polynomialXYIdeal k)).injective
      apply Subtype.ext
      simp [z, xI, yI, polynomialXYIdealTensorInclusion, mul_comm]
    intro hinj
    apply hz
    apply hinj
    simpa [hzmap]

/-! ## The quotient `k[x,y]/(x,y)` -/

/-- The residue-field quotient at `(x,y)`. -/
abbrev polynomialXYQuotient (k : Type u) [Field k] :=
  twoVariablePolynomialRing k ⧸ polynomialXYIdeal k

/-- Multiplication by `x` on `k[x,y]`. -/
def multiplicationByFirstVariable (k : Type u) [Field k] :
    twoVariablePolynomialRing k →ₗ[twoVariablePolynomialRing k]
      twoVariablePolynomialRing k :=
  LinearMap.mulLeft _ (MvPolynomial.X (0 : Fin 2))

/-- The tensor of multiplication by `x` with the quotient `k[x,y]/(x,y)`. -/
def multiplicationByFirstVariableTensorQuotient (k : Type u) [Field k] :
    (twoVariablePolynomialRing k ⊗[twoVariablePolynomialRing k]
        polynomialXYQuotient k) →ₗ[twoVariablePolynomialRing k]
      (twoVariablePolynomialRing k ⊗[twoVariablePolynomialRing k]
        polynomialXYQuotient k) :=
  (multiplicationByFirstVariable k).rTensor (polynomialXYQuotient k)

/-- For `N = k[x,y]/(x,y)`, multiplication by `x` is an injection before
tensoring but becomes non-injective after tensoring with `N`. -/
theorem polynomialXYQuotient_tensor_counterexample (k : Type u) [Field k] :
    Function.Injective (multiplicationByFirstVariable k) ∧
      ¬ Function.Injective (multiplicationByFirstVariableTensorQuotient k) := by
  constructor
  · intro f g h
    change (MvPolynomial.X (0 : Fin 2)) * f = (MvPolynomial.X (0 : Fin 2)) * g at h
    exact mul_left_cancel₀ (by simp) h
  · intro hinj
    let e := TensorProduct.lid (twoVariablePolynomialRing k) (polynomialXYQuotient k)
    let u : twoVariablePolynomialRing k ⊗[twoVariablePolynomialRing k]
        polynomialXYQuotient k := (1 : twoVariablePolynomialRing k) ⊗ₜ (1 : polynomialXYQuotient k)
    have hx : algebraMap (twoVariablePolynomialRing k) (polynomialXYQuotient k)
        (MvPolynomial.X (0 : Fin 2)) = 0 := by
      change Ideal.Quotient.mk (polynomialXYIdeal k) (MvPolynomial.X (0 : Fin 2)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    have hmap : multiplicationByFirstVariableTensorQuotient k u = 0 := by
      apply e.injective
      simp [u, e, multiplicationByFirstVariableTensorQuotient, multiplicationByFirstVariable,
        LinearMap.mulLeft, hx]
      calc
        (MvPolynomial.X (0 : Fin 2) : twoVariablePolynomialRing k) •
            (1 : polynomialXYQuotient k) =
            (MvPolynomial.X (0 : Fin 2) : twoVariablePolynomialRing k) •
              (polynomialXYIdeal k).mkQ (1 : twoVariablePolynomialRing k) := by rfl
        _ = (polynomialXYIdeal k).mkQ
              ((MvPolynomial.X (0 : Fin 2) : twoVariablePolynomialRing k) •
                (1 : twoVariablePolynomialRing k)) := by
          exact ((polynomialXYIdeal k).mkQ.map_smul _ _).symm
        _ = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact Ideal.subset_span (by simp)
    have hu : u ≠ 0 := by
      intro hu
      have : (1 : polynomialXYQuotient k) = 0 := by
        rw [← e.apply_symm_apply (1 : polynomialXYQuotient k)]
        have hsymm : e.symm (1 : polynomialXYQuotient k) = u := by
          simp [e, u]
        rw [hsymm, hu]
        simp
      let ev : twoVariablePolynomialRing k →+* k :=
        MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
      have hsubset : polynomialXYIdeal k ≤ RingHom.ker ev := by
        rw [polynomialXYIdeal]
        refine Ideal.span_le.2 ?_
        intro z hz
        rcases hz with (rfl | rfl)
        · change ev (MvPolynomial.X (0 : Fin 2)) = 0
          simp [ev]
        · change ev (MvPolynomial.X (1 : Fin 2)) = 0
          simp [ev]
      have hone : (1 : polynomialXYQuotient k) ≠ 0 := by
        intro h
        have hmem : (1 : twoVariablePolynomialRing k) ∈ polynomialXYIdeal k := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          exact h
        have hevone : ev (1 : twoVariablePolynomialRing k) = 0 := by
          change (1 : twoVariablePolynomialRing k) ∈ RingHom.ker ev
          exact hsubset hmem
        simpa [ev] using hevone
      exact hone this
    exact hu (hinj (by simpa [hmap]))

end Formalization.Books.Exercises.Unit05
