import Mathlib.Algebra.Algebra.Pi
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Fields, Chapter 13: Linear independence of characters

The source's characters are Mathlib's `MonoidHom`s, and morphisms of field
extensions are Mathlib's `AlgHom`s.  The finite tensor-product statement uses
the canonical `Algebra.TensorProduct` and pointwise `Pi` algebra structures.
-/

namespace Formalization.Books.Fields.Unit13

noncomputable section

open scoped BigOperators TensorProduct

universe u v w

/-! ## Linear independence of characters -/

/- Mathlib's theorem for all monoid homomorphisms is stronger than the finite
   family in the source.  Restricting it along an injective finite family gives
   the source statement without introducing a parallel notion of character. -/
/- The coefficient formulation in the source is exactly the usual meaning of
   `LinearIndependent`, so no separate theorem is needed for that paraphrase. -/
/- A monoid homomorphism from a field-valued monoid is represented by
   `MonoidHom`, whose coercion gives the corresponding function. -/
/- The source assumes a field; Mathlib's stronger `CommRing`/`IsDomain`
   hypotheses are discharged by that field assumption. -/
/- The family is indexed by `Fin n`; `Function.Injective` is the finite-family
   form of pairwise distinctness. -/
/- The resulting declaration is the exact finite restriction of the canonical
   Mathlib result. -/
/- The proof is intentionally short because all mathematics is already in
   `linearIndependent_monoidHom`. -/
/- The `Monoid` assumption includes the identity used in the source proof. -/
/- No choice of an ordering beyond the `Fin n` indexing is needed. -/
/- This is the first source lemma. -/
theorem linearIndependent_of_distinct_monoid_homs
    {G L : Type*} [Monoid G] [Field L] {n : ℕ}
    (χ : Fin n → G →* L) (hχ : Function.Injective χ) :
    LinearIndependent L (fun i => (χ i : G → L)) := by
  exact (linearIndependent_monoidHom G L).comp χ hχ

/- The source's “not all zero coefficients” formulation is subsumed by the
   preceding stronger linear-independence statement. -/

/-! ## Sums of powers -/

/- The source's powers are indexed by the additive monoid `ℕ`, so the result
   is stated with a natural exponent and a finite sum over `Fin n`. -/
theorem exists_nat_sum_pow_ne_zero
    {L : Type*} [Field L] {n : ℕ} (hn : 1 ≤ n)
    (α : Fin n → L) (hα : Function.Injective α) :
    ∃ e : ℕ, ∑ i : Fin n, α i ^ e ≠ 0 := by
  classical
  let χ : Fin n → Multiplicative ℕ →* L := fun i =>
    { toFun := fun e => α i ^ e.toAdd
      map_one' := by simp
      map_mul' := by
        intro e f
        simp [pow_add] }
  have hχ : Function.Injective χ := by
    intro i j hij
    apply hα
    have h := congrArg (fun f : Multiplicative ℕ →* L => f (Multiplicative.ofAdd 1)) hij
    simpa [χ] using h
  have hli : LinearIndependent L (fun i => (χ i : Multiplicative ℕ → L)) :=
    linearIndependent_of_distinct_monoid_homs χ hχ
  by_contra h
  push Not at h
  have hzero : ∑ i : Fin n, (1 : L) • (χ i : Multiplicative ℕ → L) = 0 := by
    funext e
    simpa [χ] using h e.toAdd
  have hcoeff := (Fintype.linearIndependent_iff.mp hli (fun _ => (1 : L))) hzero
  exact one_ne_zero (hcoeff ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩)

/-! ## Independence of embeddings -/

/- A morphism of `F`-extensions is Mathlib's `AlgHom`.  Mathlib already proves
   the stronger linear independence of all such maps, so this is its finite
   restriction along the injective family of pairwise distinct embeddings. -/
theorem linearIndependent_of_distinct_extension_embeddings
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] {n : ℕ}
    (σ : Fin n → K →ₐ[F] L) (hσ : Function.Injective σ) :
    LinearIndependent L (fun i => (σ i).toLinearMap) := by
  exact (linearIndependent_algHom_toLinearMap F K L).comp σ hσ

/- The source's coefficient/evaluation formulation is subsumed by this
   stronger `LinearIndependent` declaration. -/

/-! ## Finite separable tensor products over an algebraically closed field -/

/- `rightAlgebra` is deliberately not a global instance in Mathlib because a
   tensor product can carry two natural scalar structures.  This chapter uses
   the source's scalar field `L`, acting through the right tensor factor. -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- The canonical `F`-algebra map that evaluates the first tensor factor at
   every `F`-algebra embedding into `L`. -/
def finiteSeparableEvaluation
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] :
    K →ₐ[F] ((K →ₐ[F] L) → L) :=
  AlgHom.pi (fun σ => σ)

/- The source's displayed map is obtained from the base-change adjunction,
   followed by the canonical commutation of the two tensor factors. -/
def finiteSeparableTensorProductMap
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] :
    (K ⊗[F] L) →ₐ[L] ((K →ₐ[F] L) → L) :=
  let f : L ⊗[F] K →ₐ[L] ((K →ₐ[F] L) → L) :=
    AlgHom.liftEquiv F L K ((K →ₐ[F] L) → L) (finiteSeparableEvaluation (F := F) (K := K) (L := L))
  f.comp (Algebra.TensorProduct.commRight F L K).symm.toAlgHom

/- The formula on pure tensors is the source's displayed identity. -/
@[simp]
theorem finiteSeparableTensorProductMap_tmul
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (α : K) (β : L) :
    finiteSeparableTensorProductMap (F := F) (K := K) (L := L) (α ⊗ₜ[F] β) =
      fun σ => σ α * β := by
  classical
  funext σ
  simp [finiteSeparableTensorProductMap, finiteSeparableEvaluation, mul_comm]

/- The source's finite-separable and algebraically-closed hypotheses are
   Mathlib's `FiniteDimensional`, `Algebra.IsSeparable`, and `IsAlgClosed`. -/
theorem finite_separable_tensor_product_map_bijective
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [FiniteDimensional F K]
    [Algebra.IsSeparable F K] [IsAlgClosed L] :
    Function.Bijective
      (finiteSeparableTensorProductMap (F := F) (K := K) (L := L)) := by
  classical
  let f : (L ⊗[F] K) →ₐ[L] ((K →ₐ[F] L) → L) :=
    AlgHom.liftEquiv F L K ((K →ₐ[F] L) → L)
      (finiteSeparableEvaluation (F := F) (K := K) (L := L))
  have hσli : LinearIndependent L
      (fun σ : K →ₐ[F] L => σ.toLinearMap) :=
    linearIndependent_algHom_toLinearMap F K L
  have hcard : Fintype.card (K →ₐ[F] L) = Module.finrank L (K →ₗ[F] L) := by
    rw [Module.finrank_linearMap_self, AlgHom.card F K L]
  let bσ : Module.Basis (K →ₐ[F] L) L (K →ₗ[F] L) :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun σ : K →ₐ[F] L => σ.toLinearMap) hσli hcard
  let evalTensor (φ : K →ₗ[F] L) : L ⊗[F] K →ₗ[L] L :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.smulRight (LinearMap.id : L →ₗ[L] L) φ)
  let T : (K →ₗ[F] L) →ₗ[L] (L ⊗[F] K →ₗ[L] L) :=
    { toFun := evalTensor
      map_add' := by
        intro φ ψ
        apply TensorProduct.AlgebraTensorModule.ext
        intro l k
        simp [evalTensor]
      map_smul' := by
        intro c φ
        apply TensorProduct.AlgebraTensorModule.ext
        intro l k
        simp [evalTensor, mul_left_comm] }
  have hT (σ : K →ₐ[F] L) :
      T σ.toLinearMap =
        (LinearMap.proj (R := L) σ).comp f.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro l k
    simp [T, evalTensor, f, finiteSeparableEvaluation]
  let bK : Module.Basis (Fin (Module.finrank F K)) F K := Module.finBasis F K
  let coordMap (i : Fin (Module.finrank F K)) : K →ₗ[F] L :=
    (Algebra.linearMap F L).comp (bK.coord i)
  let coordTensor (i : Fin (Module.finrank F K)) : L ⊗[F] K →ₗ[L] L :=
    (TensorProduct.AlgebraTensorModule.rid F L L).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor L L (bK.coord i))
  have hcoord (i : Fin (Module.finrank F K)) :
      T (coordMap i) = coordTensor i := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro l k
    simp [T, evalTensor, coordMap, coordTensor, Algebra.smul_def, mul_comm]
  have hf_zero : ∀ x : L ⊗[F] K, f x = 0 → x = 0 := by
    intro x hx
    have hTzero (σ : K →ₐ[F] L) : T σ.toLinearMap x = 0 := by
      rw [hT σ]
      simp [hx]
    have hTzero' (σ : K →ₐ[F] L) : T (bσ σ) x = 0 := by
      simpa [bσ] using hTzero σ
    have hcoord_zero (i : Fin (Module.finrank F K)) : T (coordMap i) x = 0 := by
      rw [← bσ.sum_repr (coordMap i), map_sum]
      simp only [map_smul]
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
      simp_rw [hTzero']
      simp
    have hxcoeff (i : Fin (Module.finrank F K)) :
        (TensorProduct.equivFinsuppOfBasisRight bK x) i = 0 := by
      have hi := hcoord_zero i
      rw [hcoord i] at hi
      simpa [coordTensor, TensorProduct.equivFinsuppOfBasisRight_apply] using hi
    have hxzero : TensorProduct.equivFinsuppOfBasisRight bK x = 0 := by
      ext i
      exact hxcoeff i
    exact (TensorProduct.equivFinsuppOfBasisRight bK).injective hxzero
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hf_zero
    rw [map_sub, hxy, sub_self]
  have hdim : Module.finrank L (L ⊗[F] K) =
      Module.finrank L ((K →ₐ[F] L) → L) := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul,
      Module.finrank_pi L, AlgHom.card F K L]
  have hf_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf_inj
  have hf_bij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  exact hf_bij.comp (Algebra.TensorProduct.commRight F L K).symm.bijective

/- A bijective algebra homomorphism is the canonical Mathlib representation of
   the source's “isomorphism of `L`-algebras”. -/
noncomputable def finiteSeparableTensorProductAlgEquiv
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [FiniteDimensional F K]
    [Algebra.IsSeparable F K] [IsAlgClosed L] :
    (K ⊗[F] L) ≃ₐ[L] ((K →ₐ[F] L) → L) :=
  AlgEquiv.ofBijective
    (finiteSeparableTensorProductMap (F := F) (K := K) (L := L))
    finite_separable_tensor_product_map_bijective

end

end Formalization.Books.Fields.Unit13
