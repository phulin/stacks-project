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
  sorry

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
  sorry

/-! ## Tensor products and Hom -/

/-- Rank is multiplicative for tensor products. -/
theorem rank_tensor
    {R K : Type u} {M N : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    rank R K (M ⊗[R] N) = rank R K M * rank R K N := by
  sorry

/-- Rank is multiplicative for `Hom` when the source is finitely presented. -/
theorem rank_hom
    {R K : Type u} {M N : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] :
    rank R K (M →ₗ[R] N) = rank R K M * rank R K N := by
  sorry

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
