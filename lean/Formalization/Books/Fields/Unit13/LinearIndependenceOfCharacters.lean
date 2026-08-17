import Formalization.Books.Fields.Unit12.SeparableAlgebraicExtensions
import Mathlib.Algebra.Algebra.Pi
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
  sorry

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
  sorry

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
