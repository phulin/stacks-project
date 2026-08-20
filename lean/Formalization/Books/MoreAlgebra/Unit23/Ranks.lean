import Formalization.Books.MoreAlgebra.Unit22.TorsionFree
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# More on Algebra, Chapter 23: Ranks of modules

The source's rank is the dimension after passage to a fraction field.  The
definition below uses Mathlib's cardinal-valued `Module.rank`; the tensor
product is written with the fraction field on the left so that its canonical
`K`-module structure is available.  This is the symmetric form of the
source's `M ⊗_R K`.
-/

namespace Formalization.Books.MoreAlgebra.Unit23

open scoped TensorProduct

universe u v

noncomputable section

/-! ## The rank -/

/-- The rank of an `R`-module after extension to the fraction field `K`. -/
def rank
    (R K M : Type*) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] : Cardinal :=
  Module.rank K (K ⊗[R] M)

private theorem rank_eq_lift_module_rank
    {R K : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] :
    rank R K M = Cardinal.lift.{u} (Module.rank R M) := by
  unfold rank
  rw [IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl]
  apply Cardinal.lift_injective.{v}
  simpa using IsLocalizedModule.lift_rank_eq (nonZeroDivisors R)
    (TensorProduct.mk R K M 1) le_rfl

/- The source's remark that this agrees with locally free rank is a
   compatibility observation, not a separate mathematical assertion: the
   canonical `Module.Free`/basis APIs remain the interfaces for freeness. -/

/-! ## Invariance and additivity -/

/-- A map with torsion kernel and cokernel does not change rank. -/
theorem rank_torsion_invariant
    {R K : Type u} {M M' : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M')
    (hker : Module.IsTorsion R (LinearMap.ker f))
    (hcoker : Module.IsTorsion R (M' ⧸ LinearMap.range f)) :
    rank R K M = rank R K M' := by
  rw [rank_eq_lift_module_rank, rank_eq_lift_module_rank]
  have hk : Module.rank R (LinearMap.ker f) = 0 := hker.rank_eq_zero
  have hc : Module.rank R (M' ⧸ LinearMap.range f) = 0 := hcoker.rank_eq_zero
  have hM : Module.rank R (LinearMap.range f) = Module.rank R M := by
    rw [← LinearMap.rank_range_add_rank_ker f, hk, add_zero]
  have hM' : Module.rank R (LinearMap.range f) = Module.rank R M' := by
    rw [← Submodule.rank_quotient_add_rank f.range, hc, zero_add]
  exact congrArg (Cardinal.lift.{u}) (hM.symm.trans hM')

/-- Rank is additive in a short exact sequence of modules. -/
theorem rank_additive
    {R K : Type u} {M M' M'' : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : Function.Injective f)
    (h_exact : Function.Exact (f : M → M') (g : M' → M''))
    (hg : Function.Surjective g) :
    rank R K M' = rank R K M + rank R K M'' := by
  rw [rank_eq_lift_module_rank, rank_eq_lift_module_rank, rank_eq_lift_module_rank]
  have hrg : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp h_exact).symm
  have hdim := LinearMap.rank_range_add_rank_ker g
  rw [rank_range_of_surjective g hg, ← hrg, rank_range_of_injective f hf] at hdim
  have hbase : Module.rank R M' = Module.rank R M + Module.rank R M'' :=
    hdim.symm.trans (add_comm _ _)
  simpa only [Cardinal.lift_add] using congrArg (Cardinal.lift.{u}) hbase

/-! ## Tensor products and Hom -/

/-- Rank is multiplicative for tensor products. -/
theorem rank_tensor
    {R K : Type u} {M N : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    rank R K (M ⊗[R] N) = rank R K M * rank R K N := by
  unfold rank
  let e₁ := (TensorProduct.isBaseChange R N K).tensorEquiv (K ⊗[R] M)
  let e₂ := TensorProduct.AlgebraTensorModule.assoc R R K K M N
  rw [← (e₁.trans e₂).rank_eq, rank_tensorProduct']

/-- Rank is multiplicative for `Hom` when the source is finitely presented. -/
theorem rank_hom
    {R K : Type u} {M N : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] :
    rank R K (M →ₗ[R] N) = rank R K M * rank R K N := by
  unfold rank
  let _ : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hbc := Module.FinitePresentation.isBaseChange_map R M N K
  rw [hbc.equiv.rank_eq, Module.rank_linearMap]
  simp

/-! ## Pullback along a domain extension -/

/-- Extending scalars along an inclusion of domains preserves rank. -/
theorem rank_baseChange
    {R R' K K' : Type u} {M : Type v}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R']
    [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra R R']
    (hRR' : Function.Injective (algebraMap R R'))
    [AddCommGroup M] [Module R M] :
    rank R K M = rank R' K' (R' ⊗[R] M) := by
  sorry

/-! ## Finite modules -/

/- The source's generator/basis choices and the common-denominator
   normalization are proof-only intermediate claims.  The four resulting
   assertions are recorded together below. -/

/-- A finite module over a domain has finite rank and admits the four
source constructions: a torsion-isomorphism to a finite free module, a
free localization of that rank, and a torsion quotient from a finite free
submodule. -/
theorem finite_module_rank
    {R K : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ r : ℕ,
      rank R K M = (r : Cardinal) ∧
        (∃ f : M →ₗ[R] (Fin r →₀ R),
          Module.IsTorsion R (LinearMap.ker f) ∧
            Module.IsTorsion R ((Fin r →₀ R) ⧸ LinearMap.range f)) ∧
        (∃ f : R, f ≠ 0 ∧
          Nonempty
            (Module.Basis (Fin r) (Localization.Away f)
              (LocalizedModule.Away f M))) ∧
        (∃ f : (Fin r →₀ R) →ₗ[R] M,
          Function.Injective f ∧
            Module.IsTorsion R (M ⧸ LinearMap.range f)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit23
