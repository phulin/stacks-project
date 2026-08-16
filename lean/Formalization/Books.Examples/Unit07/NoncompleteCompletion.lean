import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Noncomplete completion

This file formalizes the precise statements in Section 7 of `books/examples.tex`.
The completion used throughout is Mathlib's inverse-limit construction
`AdicCompletion`; proposition proofs are left for the proving stage.
-/

namespace Formalization.«Books.Examples».Unit07

open scoped BigOperators

open Ideal Submodule

universe u v

section Completion

variable {R : Type u} [CommRing R] (m : Ideal R)

/-- The kernel of the zeroth residue map of the adic completion. -/
noncomputable def completionMaximalIdeal : Ideal (AdicCompletion m R) :=
  RingHom.ker (AdicCompletion.evalOneₐ m).toRingHom

/-- The kernel of the projection of the completion to the `n`th quotient. -/
noncomputable def completionKernel (n : ℕ) : Ideal (AdicCompletion m R) :=
  RingHom.ker (AdicCompletion.evalₐ m n).toRingHom

/-- The assertion that the completion's maximal ideal is extended from `m`. -/
def maximalIdealIsExtended : Prop :=
  m.map (algebraMap R (AdicCompletion m R)) = completionMaximalIdeal m

/-- Completeness of the completion as a module over its own local ring. -/
def completionIsCompleteAsCompletionModule : Prop :=
  IsAdicComplete (completionMaximalIdeal m) (AdicCompletion m R)

/-- Completeness of the completion as an `R`-module for the original ideal. -/
def completionIsCompleteAsOriginalModule : Prop :=
  IsAdicComplete m (AdicCompletion m R)

/-- Every element of the inverse-limit completion is represented by an adic Cauchy sequence. -/
theorem adicCompletion_is_complete_in_inverse_limit_topology :
    Function.Surjective (AdicCompletion.mk m R) := by
  exact AdicCompletion.mk_surjective m R

/-- An element outside the kernel-defined maximal ideal is a unit. -/
theorem completion_unit_of_not_mem_maximalIdeal
    (x : AdicCompletion m R) (hx : x ∉ completionMaximalIdeal m) :
    ∃ y : AdicCompletion m R, x * y = 1 := by
  sorry

/-- The completion is local when the defining ideal is maximal. -/
theorem adicCompletion_isLocalRing [m.IsMaximal] :
    IsLocalRing (AdicCompletion m R) := by
  sorry

/-- The kernel-defined maximal ideal is maximal. -/
theorem completionMaximalIdeal_isMaximal [m.IsMaximal] :
    (completionMaximalIdeal m).IsMaximal := by
  sorry

/-- Completeness for the original ideal forces the maximal ideal to be extended. -/
theorem completion_original_complete_implies_extended :
    completionIsCompleteAsOriginalModule m → maximalIdealIsExtended m := by
  sorry

theorem completionMaximalIdeal_pow_le_kernel (n : ℕ) :
    completionMaximalIdeal m ^ n ≤ completionKernel m n := by
  sorry

theorem completionKernel_succ_le (n : ℕ) :
    completionKernel m (n + 1) ≤ completionKernel m n := by
  sorry

/-- The projection sends `(m')ⁿ` onto `mⁿ/mⁿ⁺¹`. -/
theorem completion_projection_pow_image (n : ℕ) :
    (completionMaximalIdeal m ^ n).map
        (AdicCompletion.evalₐ m (n + 1)).toRingHom =
      (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
  sorry

/-- The additive quotient `Kₙ/(m')ⁿ` from the exact sequence in the source. -/
noncomputable abbrev completionKernelQuotient (n : ℕ) :=
  (completionKernel m n : Type _) ⧸
    (Submodule.comap
      (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
      (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R)))

/-- The additive quotient `R̂/(m')ⁿ` from the exact sequence in the source. -/
noncomputable abbrev completionQuotient (n : ℕ) :=
  AdicCompletion m R ⧸
    (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R))

/-- The projection `Kₙ₊₁ → Kₙ/(m')ⁿ`. -/
noncomputable def completionKernelTransition (n : ℕ) :
    completionKernel m (n + 1) →ₗ[AdicCompletion m R] completionKernelQuotient m n :=
  let i := (completionKernel m (n + 1) : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype.codRestrict
    (completionKernel m n)
    (fun x => completionKernel_succ_le m n x.property)
  (Submodule.comap
    (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
    (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R))).mkQ.comp i

/-- The transition maps on the kernels are surjective. -/
theorem completionKernelTransition_surjective (n : ℕ) :
    Function.Surjective (completionKernelTransition m n) := by
  sorry

/-- The map from `Kₙ/(m')ⁿ` into `R̂/(m')ⁿ`. -/
noncomputable def completionKernelQuotientMap (m : Ideal R) (n : ℕ) :
    completionKernelQuotient m n →ₗ[AdicCompletion m R] completionQuotient m n :=
  Submodule.mapQ
    (Submodule.comap
      (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
      (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R)))
    (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R))
    (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
    (by
      intro x hx
      exact hx)

/-- The map from `R̂/(m')ⁿ` to `R/mⁿ`. -/
noncomputable def completionQuotientToResidue (n : ℕ) :
    completionQuotient m n →+* R ⧸ m ^ n :=
  Ideal.Quotient.lift (completionMaximalIdeal m ^ n)
    (AdicCompletion.evalₐ m n).toRingHom
    (fun a ha => by
      exact completionMaximalIdeal_pow_le_kernel m n ha)

/-- The short exact sequence
`0 → Kₙ/(m')ⁿ → R̂/(m')ⁿ → R/mⁿ → 0`. -/
theorem completion_kernel_quotient_short_exact (n : ℕ) :
    Function.Injective (completionKernelQuotientMap m n) ∧
      Function.Exact (completionKernelQuotientMap m n).toAddMonoidHom
        (completionQuotientToResidue m n).toAddMonoidHom ∧
      Function.Surjective (completionQuotientToResidue m n) := by
  sorry

/-- The inverse-limit/Mittag--Leffler criterion for completeness in the maximal-ideal topology. -/
theorem completion_is_completeAsCompletionModule_iff_kernel_eq_pow :
    completionIsCompleteAsCompletionModule m ↔
      ∀ n : ℕ, 1 ≤ n → completionKernel m n = completionMaximalIdeal m ^ n := by
  sorry

end Completion

section InfinitePolynomialExample

variable (k : Type u) [Field k]

/-- The countably generated polynomial ring used in the example. -/
abbrev infinitePolynomialRing := MvPolynomial ℕ k

/-- Its ideal generated by all variables. -/
noncomputable abbrev infinitePolynomialMaximalIdeal : Ideal (infinitePolynomialRing k) :=
  MvPolynomial.idealOfVars ℕ k

/-- The ideal generated by all variables is maximal, with residue field `k`. -/
theorem infinitePolynomialMaximalIdeal_isMaximal :
    (infinitePolynomialMaximalIdeal k).IsMaximal := by
  sorry

/-- The finite partial sums of `x₁ + x₂² + x₃³ + ⋯`. -/
noncomputable def infiniteVariableSeriesPartial (n : ℕ) : infinitePolynomialRing k :=
  Finset.sum (Finset.range n) (fun i =>
    (MvPolynomial.X i : infinitePolynomialRing k) ^ (i + 1))

/-- The formal infinite sum `x₁ + x₂² + x₃³ + ⋯` in the adic completion. -/
noncomputable def infiniteVariableSeries :
    AdicCompletion (infinitePolynomialMaximalIdeal k) (infinitePolynomialRing k) :=
  AdicCompletion.mk _ _
    (AdicCompletion.AdicCauchySequence.mk _ _ (infiniteVariableSeriesPartial k) (by
      intro n
      apply (SModEq.sub_mem).2
      have hmem :
          (MvPolynomial.X n : infinitePolynomialRing k) ^ (n + 1) ∈
            infinitePolynomialMaximalIdeal k ^ n := by
        rw [MvPolynomial.X_pow_eq_monomial]
        apply (MvPolynomial.monomial_mem_pow_idealOfVars_iff n
          (Finsupp.single n (n + 1)) (by simp)).2
        simp
      have hneg :
          -(MvPolynomial.X n : infinitePolynomialRing k) ^ (n + 1) ∈
            infinitePolynomialMaximalIdeal k ^ n :=
        (infinitePolynomialMaximalIdeal k ^ n).neg_mem hmem
      simpa [infiniteVariableSeriesPartial, Finset.sum_range_succ, sub_eq_add_neg,
        add_assoc, smul_eq_mul, Ideal.mul_top] using hneg))

/-- Coordinates of the formal infinite sum are its finite partial sums. -/
theorem infiniteVariableSeries_coordinate (n : ℕ) :
    AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) n
        (infiniteVariableSeries k) =
      Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ n)
        (infiniteVariableSeriesPartial k n) := by
  sorry

/-- The series has zero constant term. -/
theorem infiniteVariableSeries_mem_completionMaximalIdeal :
    infiniteVariableSeries k ∈
      Formalization.«Books.Examples».Unit07.completionMaximalIdeal
        (infinitePolynomialMaximalIdeal k) := by
  sorry

/-- The series is not a finite `R`-linear combination of elements of the completion. -/
theorem infiniteVariableSeries_not_mem_extendedMaximalIdeal :
    infiniteVariableSeries k ∉
      (infinitePolynomialMaximalIdeal k).map
        (algebraMap (infinitePolynomialRing k)
          (AdicCompletion (infinitePolynomialMaximalIdeal k) (infinitePolynomialRing k))) := by
  sorry

theorem infinitePolynomial_maximalIdeal_not_extended :
    ¬ Formalization.«Books.Examples».Unit07.maximalIdealIsExtended
        (infinitePolynomialMaximalIdeal k) := by
  sorry

/-- The series lies in `K₂` but not in the square of the completion's maximal ideal. -/
theorem infiniteVariableSeries_mem_completionKernel_two :
    infiniteVariableSeries k ∈
      Formalization.«Books.Examples».Unit07.completionKernel
        (infinitePolynomialMaximalIdeal k) 2 := by
  sorry

theorem infiniteVariableSeries_not_mem_completionMaximalIdeal_sq :
    infiniteVariableSeries k ∉
      Formalization.«Books.Examples».Unit07.completionMaximalIdeal
        (infinitePolynomialMaximalIdeal k) ^ 2 := by
  sorry

theorem infinitePolynomial_completion_not_complete_as_completionModule :
    ¬ Formalization.«Books.Examples».Unit07.completionIsCompleteAsCompletionModule
        (infinitePolynomialMaximalIdeal k) := by
  sorry

theorem infinitePolynomial_completion_not_complete_as_originalModule :
    ¬ Formalization.«Books.Examples».Unit07.completionIsCompleteAsOriginalModule
        (infinitePolynomialMaximalIdeal k) := by
  sorry

end InfinitePolynomialExample

section DerivativeObstruction

variable (k : Type u) [Field k]

/-- A finite sum of products with both factors having zero constant term. -/
def IsFiniteProductSum {n : ℕ} (t : ℕ) (p : MvPolynomial (Fin n) k) : Prop :=
  ∃ f g : Fin t → MvPowerSeries (Fin n) k,
    (∀ i, MvPowerSeries.constantCoeff (f i) = 0 ∧
      MvPowerSeries.constantCoeff (g i) = 0) ∧
      (p : MvPowerSeries (Fin n) k) = ∑ i, f i * g i

/-- The homogeneous polynomial `x₁ᵈ + ⋯ + xₙᵈ`. -/
noncomputable def powerSumPolynomial (n d : ℕ) : MvPolynomial (Fin n) k :=
  ∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) k) ^ d

/-- The ideal generated by the formal partial derivatives of a polynomial. -/
noncomputable def polynomialDerivativeIdeal {n : ℕ} (p : MvPolynomial (Fin n) k) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span (Set.range (fun i : Fin n => MvPolynomial.pderiv i p))

/-- The ideal generated by the formal partial derivatives of a power series. -/
noncomputable def powerSeriesDerivativeIdeal {n t : ℕ}
    (f g : Fin t → MvPowerSeries (Fin n) k) :
    Ideal (MvPowerSeries (Fin n) k) :=
  Ideal.span (Set.range (fun i : Fin n =>
    MvPowerSeries.pderiv k i (∑ j, f j * g j)))

/-- The ideal generated by the factors in a finite product sum. -/
noncomputable def powerSeriesFactorIdeal {n t : ℕ}
    (f g : Fin t → MvPowerSeries (Fin n) k) :
    Ideal (MvPowerSeries (Fin n) k) :=
  Ideal.span (Set.range f ∪ Set.range g)

/-- The Krull dimension of the closed locus defined by an ideal. -/
noncomputable def zeroLocusKrullDimension {A : Type v} [CommRing A] (I : Ideal A) : WithBot ℕ∞ :=
  ringKrullDim (A ⧸ I)

theorem powerSumPolynomial_isHomogeneous (n d : ℕ) :
    MvPolynomial.IsHomogeneous (powerSumPolynomial k n d) d := by
  sorry

theorem powerSumPolynomial_derivative_ideal (n d : ℕ) (hd : (d : k) ≠ 0) :
    polynomialDerivativeIdeal k (powerSumPolynomial k n d) =
      Ideal.span (Set.range (fun i : Fin n =>
        (d : k) • (MvPolynomial.X i : MvPolynomial (Fin n) k) ^ (d - 1))) := by
  sorry

theorem powerSumPolynomial_derivative_zeroLocus_is_singleton
    (n d : ℕ) (hn : 0 < n) (hd : (d : k) ≠ 0) :
    ∃ x : PrimeSpectrum (MvPolynomial (Fin n) k),
      PrimeSpectrum.zeroLocus (polynomialDerivativeIdeal k (powerSumPolynomial k n d)) = {x} := by
  sorry

theorem finiteProductSum_derivative_mem_factorIdeal
    {n t : ℕ} (f g : Fin t → MvPowerSeries (Fin n) k) (i : Fin n) :
    MvPowerSeries.pderiv k i (∑ j, f j * g j) ∈ powerSeriesFactorIdeal k f g := by
  sorry

theorem finiteProductSum_factor_locus_dimension
    {n t : ℕ} (f g : Fin t → MvPowerSeries (Fin n) k) :
    ((n - 2 * t : ℕ) : WithBot ℕ∞) ≤
      zeroLocusKrullDimension (powerSeriesFactorIdeal k f g) := by
  sorry

theorem finiteProductSum_derivative_locus_contains_factor_locus
    {n t : ℕ} (f g : Fin t → MvPowerSeries (Fin n) k) :
      PrimeSpectrum.zeroLocus (powerSeriesFactorIdeal k f g : Set (MvPowerSeries (Fin n) k)) ⊆
      PrimeSpectrum.zeroLocus (powerSeriesDerivativeIdeal k f g : Set (MvPowerSeries (Fin n) k)) := by
  sorry

theorem powerSumPolynomial_not_finiteProductSum
    (n d t : ℕ) (hnt : 2 * t < n) (hd : 1 < d) (hchar : (d : k) ≠ 0) :
    ¬ IsFiniteProductSum k t (powerSumPolynomial k n d) := by
  sorry

theorem exists_powerSum_obstruction (t : ℕ) (ht : 0 < t) :
    ∃ (n d : ℕ), 2 * t < n ∧ 1 < d ∧ (d : k) ≠ 0 ∧
      ¬ IsFiniteProductSum k t (powerSumPolynomial k n d) := by
  sorry

/-- A block-by-block sequence of homogeneous polynomials with the required obstruction. -/
structure HomogeneousBlockSeries where
  degree : ℕ → ℕ
  blockStart : ℕ → ℕ
  block : ∀ i, MvPolynomial (Fin (blockStart (i + 1) - blockStart i)) k
  degree_strict : StrictMono degree
  block_start_strict : StrictMono blockStart
  positive_block_start : ∀ i, 0 < blockStart i
  degree_gt_one : ∀ i, 1 < degree i
  homogeneous : ∀ i, MvPolynomial.IsHomogeneous (block i) (degree i)
  obstruction : ∀ i t, t ≤ i → ¬ IsFiniteProductSum k t (block i)

theorem exists_homogeneousBlockSeries :
    Nonempty (HomogeneousBlockSeries k) := by
  sorry

theorem exists_completion_kernel_not_square :
    ∃ z : AdicCompletion (MvPolynomial.idealOfVars ℕ k) (MvPolynomial ℕ k),
      z ∈ Formalization.«Books.Examples».Unit07.completionKernel
          (MvPolynomial.idealOfVars ℕ k) 2 ∧
        z ∉ Formalization.«Books.Examples».Unit07.completionMaximalIdeal
          (MvPolynomial.idealOfVars ℕ k) ^ 2 := by
  sorry

end DerivativeObstruction

section FinalStatement

variable (k : Type u) [Field k]

/-- The local-ring counterexample supplied by the infinite polynomial construction. -/
theorem lemma_noncomplete_completion :
    ∃ (R : CommRingCat.{u}) (m : Ideal (R : Type u)),
      m.IsMaximal ∧
        IsLocalRing (R : Type u) ∧
        IsLocalRing (AdicCompletion m (R : Type u)) ∧
        completionMaximalIdeal m ≠
          m.map (algebraMap (R : Type u) (AdicCompletion m (R : Type u))) ∧
        ¬ completionIsCompleteAsCompletionModule m ∧
        ¬ completionIsCompleteAsOriginalModule m := by
  sorry

end FinalStatement

/- The chapter-level result packages the local, nonextended, and two distinct
completeness failures established by the preceding declarations. -/
end Formalization.«Books.Examples».Unit07
