import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Examples, Chapter 9: Completion is not exact

The source section is expressed using Mathlib's canonical `AdicCompletion`
and its functorial map.  The first example uses a positive indexing shift, so
the component indexed by `n` is the source summand `R/(t^(n + 1))`.
-/

open scoped DirectSum
open scoped BigOperators
open DirectSum

namespace Formalization.«Books.Examples».Unit09

universe u

noncomputable section

section FirstCounterexample

variable (k : Type u) [Field k]

/-- The polynomial ring in the first completion counterexample. -/
abbrev polynomialRing := Polynomial k

/-- The `(t)`-adic ideal, with `Polynomial.X` playing the role of `t`. -/
def polynomialAdicIdeal : Ideal (polynomialRing k) :=
  Ideal.span {Polynomial.X}

/-- The direct sum `K = ⨁ R` in the first example. -/
abbrev firstKernel := ⨁ _n : ℕ, polynomialRing k

/-- The direct sum `P = ⨁ R` in the first example. -/
abbrev firstMiddle := ⨁ _n : ℕ, polynomialRing k

/-- The direct sum `M = ⨁ R/(t^(n + 1))` in the first example. -/
abbrev firstCokernel :=
  ⨁ n : ℕ, polynomialRing k ⧸ (polynomialAdicIdeal k) ^ (n + 1)

/-- Multiplication by the power assigned to the `n`th summand. -/
def firstKernelComponentMap (n : ℕ) :
    polynomialRing k →ₗ[polynomialRing k] polynomialRing k :=
  LinearMap.mulLeft (polynomialRing k) (Polynomial.X ^ (n + 1))

/-- The quotient map on the `n`th summand. -/
def firstQuotientComponentMap (n : ℕ) :
    polynomialRing k →ₗ[polynomialRing k]
      polynomialRing k ⧸ (polynomialAdicIdeal k) ^ (n + 1) :=
  ((polynomialAdicIdeal k) ^ (n + 1)).mkQ

/-- The componentwise multiplication map `K → P`. -/
def firstKernelMap : firstKernel k →ₗ[polynomialRing k] firstMiddle k :=
  DirectSum.toModule (polynomialRing k) ℕ (firstMiddle k) (fun n ↦
    (DirectSum.lof (polynomialRing k) ℕ (fun _ : ℕ ↦ polynomialRing k) n) ∘ₗ
      firstKernelComponentMap k n)

/-- The componentwise quotient map `P → M`. -/
def firstQuotientMap : firstMiddle k →ₗ[polynomialRing k] firstCokernel k :=
  DirectSum.toModule (polynomialRing k) ℕ (firstCokernel k) (fun n ↦
    (DirectSum.lof (polynomialRing k) ℕ
      (fun n : ℕ ↦ polynomialRing k ⧸ (polynomialAdicIdeal k) ^ (n + 1)) n) ∘ₗ
      firstQuotientComponentMap k n)

/-- The finite truncation of the element `(t^2, t^3, t^4, ...)`. -/
def firstXiTruncation (m : ℕ) : firstMiddle k :=
  ∑ n ∈ Finset.range m,
    DirectSum.lof (polynomialRing k) ℕ (fun _ : ℕ ↦ polynomialRing k) n
      (Polynomial.X ^ (n + 2))

/-- The completion-level meaning of the displayed element `ξ`. -/
def IsFirstXi
    (ξ : AdicCompletion (polynomialAdicIdeal k) (firstMiddle k)) : Prop :=
  ∀ m : ℕ,
    AdicCompletion.eval (polynomialAdicIdeal k) (firstMiddle k) m ξ =
      ((polynomialAdicIdeal k) ^ m •
        (⊤ : Submodule (polynomialRing k) (firstMiddle k))).mkQ
        (firstXiTruncation k m)

/-- The completion of the componentwise multiplication map. -/
def firstCompletedKernelMap :
    AdicCompletion (polynomialAdicIdeal k) (firstKernel k) →ₗ[
      AdicCompletion (polynomialAdicIdeal k) (polynomialRing k)]
      AdicCompletion (polynomialAdicIdeal k) (firstMiddle k) :=
  AdicCompletion.map (polynomialAdicIdeal k) (firstKernelMap k)

/-- The completion of the componentwise quotient map. -/
def firstCompletedQuotientMap :
    AdicCompletion (polynomialAdicIdeal k) (firstMiddle k) →ₗ[
      AdicCompletion (polynomialAdicIdeal k) (polynomialRing k)]
      AdicCompletion (polynomialAdicIdeal k) (firstCokernel k) :=
  AdicCompletion.map (polynomialAdicIdeal k) (firstQuotientMap k)

/-- The finite truncations of the putative constant vector `(t, t, t, ...)`. -/
def firstConstantTruncation (m : ℕ) : firstKernel k :=
  ∑ n ∈ Finset.range m,
    DirectSum.lof (polynomialRing k) ℕ (fun _ : ℕ ↦ polynomialRing k) n Polynomial.X

/-- A completion element with all components equal to `t`, if one existed. -/
def IsFirstConstantVector
    (x : AdicCompletion (polynomialAdicIdeal k) (firstKernel k)) : Prop :=
  ∀ m : ℕ,
    AdicCompletion.eval (polynomialAdicIdeal k) (firstKernel k) m x =
      ((polynomialAdicIdeal k) ^ m •
        (⊤ : Submodule (polynomialRing k) (firstKernel k))).mkQ
        (firstConstantTruncation k m)

/-- The displayed constant vector is not an element of the completed direct sum. -/
theorem first_constant_vector_not_in_completion :
    ¬ ∃ x : AdicCompletion (polynomialAdicIdeal k) (firstKernel k),
      IsFirstConstantVector k x := by
  sorry

/-- The first completed direct sum contains the displayed obstruction. -/
theorem firstXi_exists :
    ∃ ξ : AdicCompletion (polynomialAdicIdeal k) (firstMiddle k),
      IsFirstXi k ξ ∧
        firstCompletedQuotientMap k ξ = 0 ∧
          ξ ∉ LinearMap.range (firstCompletedKernelMap k) := by
  sorry

/-- A named choice of the obstruction `ξ`. -/
noncomputable def firstXi :
    AdicCompletion (polynomialAdicIdeal k) (firstMiddle k) :=
  Classical.choose (firstXi_exists k)

/-- The defining properties of the chosen obstruction. -/
theorem firstXi_spec :
    IsFirstXi k (firstXi k) ∧
      firstCompletedQuotientMap k (firstXi k) = 0 ∧
        firstXi k ∉ LinearMap.range (firstCompletedKernelMap k) :=
  Classical.choose_spec (firstXi_exists k)

/-- The uncompleted sequence `0 → K → P → M → 0` is short exact. -/
theorem first_sequence_short_exact :
    Function.Injective (firstKernelMap k) ∧
      Function.Exact (firstKernelMap k) (firstQuotientMap k) ∧
        Function.Surjective (firstQuotientMap k) := by
  sorry

/-- The completed sequence fails exactness in the middle. -/
theorem first_completed_sequence_not_exact :
    ¬ Function.Exact (firstCompletedKernelMap k) (firstCompletedQuotientMap k) := by
  intro h
  exact (firstXi_spec k).2.2 ((h (firstXi k)).mp (firstXi_spec k).2.1)

end FirstCounterexample

section PrincipalQuotientCounterexample

variable {R : Type u} [CommRing R]

/-- Multiplication by a generator, with codomain restricted to its ideal. -/
def principalMultiplicationMap (J : Ideal R) (f : R) (hf : f ∈ J) : R →ₗ[R] J :=
  (LinearMap.mulLeft R f).codRestrict J (fun x ↦ J.mul_mem_right x hf)

/-- The inclusion of an ideal into its ambient ring. -/
def idealInclusionMap (J : Ideal R) : J →ₗ[R] R :=
  J.subtype

/-- The quotient map by an ideal, viewed as an `R`-linear map. -/
def idealQuotientMap (J : Ideal R) : R →ₗ[R] R ⧸ J :=
  J.mkQ

/-- The completed map from the ambient ring to the completed ideal. -/
def completedPrincipalMultiplicationMap (I J : Ideal R) (f : R) (hf : f ∈ J) :
    AdicCompletion I R →ₗ[AdicCompletion I R] AdicCompletion I J :=
  AdicCompletion.map I (principalMultiplicationMap J f hf)

/-- The completed inclusion of the ideal. -/
def completedIdealInclusionMap (I J : Ideal R) :
    AdicCompletion I J →ₗ[AdicCompletion I R] AdicCompletion I R :=
  AdicCompletion.map I (idealInclusionMap J)

/-- The completed quotient map. -/
def completedIdealQuotientMap (I J : Ideal R) :
    AdicCompletion I R →ₗ[AdicCompletion I R] AdicCompletion I (R ⧸ J) :=
  AdicCompletion.map I (idealQuotientMap J)

/-- The quotient map from `R` into the completion of `R/J`. -/
def idealQuotientCompletionFromRing (I J : Ideal R) :
    R →ₗ[R] AdicCompletion I (R ⧸ J) :=
  (completedIdealQuotientMap I J).restrictScalars R ∘ₗ AdicCompletion.of I R

/-- Multiplication by `f` on `R`. -/
def principalEndomorphism (f : R) : R →ₗ[R] R :=
  LinearMap.mulLeft R f

/-- The quotient map `R → R/(f)`. -/
def principalQuotientMap (f : R) : R →ₗ[R] R ⧸ Ideal.span {f} :=
  (Ideal.span {f}).mkQ

/-- The completed multiplication-by-`f` map. -/
def completedPrincipalEndomorphism (I : Ideal R) (f : R) :
    AdicCompletion I R →ₗ[AdicCompletion I R] AdicCompletion I R :=
  AdicCompletion.map I (principalEndomorphism f)

/-- The completed quotient map `R^ → (R/(f))^`. -/
def completedPrincipalQuotientMap (I : Ideal R) (f : R) :
    AdicCompletion I R →ₗ[AdicCompletion I R]
      AdicCompletion I (R ⧸ Ideal.span {f}) :=
  AdicCompletion.map I (principalQuotientMap f)

/-- The ordinary ideal inclusion has image exactly `J`. -/
theorem ideal_inclusion_range (J : Ideal R) :
    LinearMap.range (idealInclusionMap J) = J := by
  sorry

/-- The principal-ideal quotient example fails after completion. -/
theorem principal_quotient_completion_failure
    (a f : R) (I J : Ideal R)
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {f}) (hf : f ∈ J)
    (hR : IsAdicComplete I R)
    (hquot : ¬ IsAdicComplete I (R ⧸ J)) :
    Function.Surjective (completedPrincipalMultiplicationMap I J f hf) ∧
      Function.Surjective (completedIdealQuotientMap I J) ∧
        Set.range (completedIdealInclusionMap I J) =
          Set.range (AdicCompletion.of I R ∘ₗ idealInclusionMap J) ∧
          J < LinearMap.ker (idealQuotientCompletionFromRing I J) ∧
            ¬ Function.Exact (completedIdealInclusionMap I J)
              (completedIdealQuotientMap I J) := by
  sorry

/-- The same quotient phenomenon gives failure for the sequence
`R → R → R/(f) → 0`. -/
theorem principal_right_completion_failure
    (a f : R) (I : Ideal R) (hI : I = Ideal.span {a})
    (hR : IsAdicComplete I R)
    (hquot : ¬ IsAdicComplete I (R ⧸ Ideal.span {f})) :
    Function.Surjective (completedPrincipalQuotientMap I f) ∧
      ¬ Function.Exact (completedPrincipalEndomorphism I f)
        (completedPrincipalQuotientMap I f) := by
  sorry

end PrincipalQuotientCounterexample

section ExactnessPredicates

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- Preservation of short exact sequences by the `I`-adic completion maps. -/
def CompletionPreservesExactness : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
      Function.Injective (AdicCompletion.map I f) ∧
        Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
          Function.Surjective (AdicCompletion.map I g)

/-- Preservation of left exact sequences by completion. -/
def CompletionPreservesLeftExactness : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Exact f g →
      Function.Injective (AdicCompletion.map I f) ∧
        Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g)

/-- Preservation of right exact sequences by completion. -/
def CompletionPreservesRightExactness : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Exact f g → Function.Surjective g →
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
        Function.Surjective (AdicCompletion.map I g)

/-- The left exactness predicate restricted to finitely presented modules. -/
def CompletionPreservesLeftExactnessOnFinitelyPresentedModules : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    [Module.FinitePresentation R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Exact f g →
      Function.Injective (AdicCompletion.map I f) ∧
        Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g)

/-- The right exactness predicate restricted to finitely presented modules. -/
def CompletionPreservesRightExactnessOnFinitelyPresentedModules : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    [Module.FinitePresentation R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Exact f g → Function.Surjective g →
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
        Function.Surjective (AdicCompletion.map I g)

/-- Completion is neither left nor right exact in general, including on
finitely presented modules with a finitely generated ideal. -/
theorem completion_not_exact :
    (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
      CompletionPreservesExactness R I) ∧
      (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
        CompletionPreservesLeftExactness R I) ∧
        (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
          CompletionPreservesRightExactness R I) ∧
          (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R), I.FG →
            CompletionPreservesLeftExactnessOnFinitelyPresentedModules R I) ∧
            (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R), I.FG →
              CompletionPreservesRightExactnessOnFinitelyPresentedModules R I) := by
  sorry

end ExactnessPredicates

end

end Formalization.«Books.Examples».Unit09
