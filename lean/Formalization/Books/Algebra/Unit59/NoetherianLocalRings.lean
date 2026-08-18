import Formalization.Books.Algebra.Unit51.MoreNoetherianRings
import Formalization.Books.Algebra.Unit52.Length
import Formalization.Books.Algebra.Unit58.NoetherianGradedRings
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Operations

/-!
# Commutative Algebra, Chapter 59: Noetherian local rings

The source's Hilbert functions use the canonical `Module.length` and
submodule quotients.  Numerical-polynomial assertions are phrased using the
integer-valued interface from Chapter 58; the functions on `ℕ` are extended
by zero to `ℤ` only to match that interface.
-/

namespace Formalization.Books.Algebra.Unit59

open Formalization.Books.Algebra.Unit58
open scoped BigOperators

universe u v w

noncomputable section

/-! ## Powers and lengths -/

/- The quotient of successive powers of an ideal acting on a module. -/
abbrev idealPowerPiece
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : Type v :=
  let N : Submodule R M := I ^ n • (⊤ : Submodule R M)
  N ⧸ Submodule.comap N.subtype (I ^ (n + 1) • (⊤ : Submodule R M))

/- The quotient occurring in the cumulative Hilbert function. -/
abbrev idealPowerCumulativeQuotient
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : Type v :=
  M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))

/- Mathlib's length is extended-natural-valued; under the finite-length
   hypotheses in the source, this is its ordinary natural-number value. -/
def moduleLengthNat
    {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] : ℕ :=
  (Module.length R M).toNat

private theorem finiteLength_of_maximalIdeal_pow_smul_top_eq_bot
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : ∃ s : ℕ,
      (IsLocalRing.maximalIdeal R) ^ s • (⊤ : Submodule R M) = ⊥) :
    IsFiniteLength R M := by
  obtain ⟨s, hs⟩ := hM
  let K : Ideal R := (IsLocalRing.maximalIdeal R) ^ s
  have hkill : K • (⊤ : Submodule R M) = ⊥ := by
    simpa [K] using hs
  by_cases hK : K = ⊤
  · let : Subsingleton M := by
      constructor
      intro x y
      apply sub_eq_zero.mp
      have hx : x - y ∈ K • (⊤ : Submodule R M) := by
        rw [hK]
        simp
      rw [hkill] at hx
      simpa using hx
    exact IsFiniteLength.of_subsingleton
  · let S := R ⧸ K
    let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hK
    let : IsLocalRing S :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective
    let : IsNoetherianRing S :=
      isNoetherianRing_of_surjective R S (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective
    have hmap :
        (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk K) =
          IsLocalRing.maximalIdeal S :=
      IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective
    let : IsSemiprimaryRing S :=
      { isSemisimpleRing := by
          have hJac : Ring.jacobson S = IsLocalRing.maximalIdeal S :=
            IsLocalRing.ringJacobson_eq_maximalIdeal S
          let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal S)
          exact (Ideal.quotEquivOfEq hJac).symm.isSemisimpleRing
        isNilpotent := by
          rw [IsLocalRing.ringJacobson_eq_maximalIdeal S, ← hmap]
          refine ⟨s, ?_⟩
          rw [← Ideal.map_pow, Ideal.zero_eq_bot,
            Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] }
    have htors : Module.IsTorsionBySet R M K := by
      rw [Module.isTorsionBySet_iff_subset_annihilator]
      change K ≤ Module.annihilator R M
      rw [← Submodule.annihilator_top, Submodule.le_annihilator_iff]
      exact hkill
    let : Module S M := htors.module
    let : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
    have hfinS : IsNoetherian S M := inferInstance
    have hArtS : IsArtinian S M :=
      (IsSemiprimaryRing.isNoetherian_iff_isArtinian (R := S) (M := M)).mp hfinS
    have hArtR : IsArtinian R M :=
      (LinearMap.isArtinian_iff_of_bijective htors.semilinearMap
        Function.bijective_id).mpr hArtS
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hArtR⟩

/-! ## The maximal-ideal Hilbert functions -/

def hilbertFunction
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  moduleLengthNat (R := R)
    (M := idealPowerPiece (IsLocalRing.maximalIdeal R) M n)

def cumulativeHilbertFunction
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  moduleLengthNat (R := R)
    (M := idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M n)

theorem cumulativeHilbertFunction_eq_sum
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) :
    cumulativeHilbertFunction R M n =
      ∑ i ∈ Finset.range (n + 1), hilbertFunction R M i := by
  sorry

/-! ## Ideals of definition and their Hilbert functions -/

/-- An ideal whose radical is the maximal ideal of a local ring. -/
def IsIdealOfDefinition
    (R : Type u) [CommRing R] [IsLocalRing R] (I : Ideal R) : Prop :=
  I.radical = IsLocalRing.maximalIdeal R

theorem maximalIdeal_isIdealOfDefinition
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsIdealOfDefinition R (IsLocalRing.maximalIdeal R) := by
  unfold IsIdealOfDefinition
  exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical

theorem exists_pow_maximalIdeal_le_of_isIdealOfDefinition
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : IsIdealOfDefinition R I) :
    ∃ r : ℕ, (IsLocalRing.maximalIdeal R) ^ r ≤ I := by
  unfold IsIdealOfDefinition at hI
  have hrad : IsLocalRing.maximalIdeal R ≤ I.radical := by
    simp [hI]
  have hfg : (IsLocalRing.maximalIdeal R).FG :=
    Ideal.FG.of_isNoetherianRing _
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg

theorem finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (hM : ∃ r : ℕ, I ^ r • (⊤ : Submodule R M) = ⊥) :
    IsFiniteLength R M := by
  obtain ⟨r, hr⟩ := exists_pow_maximalIdeal_le_of_isIdealOfDefinition I hI
  obtain ⟨s, hs⟩ := hM
  have hmax :
      (IsLocalRing.maximalIdeal R) ^ (r * s) • (⊤ : Submodule R M) = ⊥ := by
    apply le_antisymm
    · have hpow :
          (IsLocalRing.maximalIdeal R) ^ (r * s) ≤ I ^ s := by
        simpa [pow_mul] using Ideal.pow_right_mono hr s
      exact (Submodule.smul_mono_left hpow).trans_eq hs
    · exact bot_le
  exact finiteLength_of_maximalIdeal_pow_smul_top_eq_bot ⟨r * s, hmax⟩

def idealHilbertFunction
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  moduleLengthNat (R := R) (M := idealPowerPiece I M n)

def idealCumulativeHilbertFunction
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  moduleLengthNat (R := R)
    (M := idealPowerCumulativeQuotient I M n)

theorem idealPowerPiece_isFiniteLength
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (n : ℕ) :
    IsFiniteLength R (idealPowerPiece I M n) := by
  sorry

theorem idealPowerCumulativeQuotient_isFiniteLength
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (n : ℕ) :
    IsFiniteLength R (idealPowerCumulativeQuotient I M n) := by
  sorry

theorem hilbertPowerPiece_isFiniteLength
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) :
    IsFiniteLength R
      (idealPowerPiece (IsLocalRing.maximalIdeal R) M n) := by
  sorry

theorem hilbertPowerCumulativeQuotient_isFiniteLength
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) :
    IsFiniteLength R
      (idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M n) := by
  sorry

theorem idealCumulativeHilbertFunction_eq_sum
    {R : Type u} {M : Type v} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (n : ℕ) :
    idealCumulativeHilbertFunction I M n =
      ∑ i ∈ Finset.range (n + 1), idealHilbertFunction I M i := by
  sorry

/- The numerical-polynomial API is indexed by `ℤ`, whereas the source only
   defines these functions for nonnegative integers. -/
def natFunctionToInteger (f : ℕ → ℕ) (n : ℤ) : ℤ :=
  if 0 ≤ n then (f n.toNat : ℤ) else 0

def hilbertFunctionInteger
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℤ → ℤ :=
  natFunctionToInteger (hilbertFunction R M)

def cumulativeHilbertFunctionInteger
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℤ → ℤ :=
  natFunctionToInteger (cumulativeHilbertFunction R M)

def idealHilbertFunctionInteger
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : ℤ → ℤ :=
  natFunctionToInteger (idealHilbertFunction I M)

def idealCumulativeHilbertFunctionInteger
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : ℤ → ℤ :=
  natFunctionToInteger (idealCumulativeHilbertFunction I M)

/-! ## Comparison of finite-colength modules -/

/-- A submodule has finite colength when its quotient has finite length. -/
def Submodule.HasFiniteColength
    {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] (N : Submodule R M) : Prop :=
  IsFiniteLength R (M ⧸ N)

theorem cumulative_hilbert_compare_of_finite_colength
    {R : Type u} {M' M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (f : M' →ₗ[R] M) (hf : Function.Injective f)
    (hquot : IsFiniteLength R (M ⧸ LinearMap.range f)) :
    ∃ c₁ c₂ : ℕ, ∀ n ≥ c₂,
      c₁ + idealCumulativeHilbertFunction I M' (n - c₂) ≤
          idealCumulativeHilbertFunction I M n ∧
        idealCumulativeHilbertFunction I M n ≤
          c₁ + idealCumulativeHilbertFunction I M' n := by
  sorry

theorem hilbert_functions_of_short_exact
    {R : Type u} {M' M M'' : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    ∃ N : Submodule R M', ∃ l c : ℕ,
      Submodule.HasFiniteColength N ∧
        l = moduleLengthNat (R := R) (M := M' ⧸ N) ∧
        (∀ n ≥ c,
          idealCumulativeHilbertFunction I M n =
              idealCumulativeHilbertFunction I M'' n +
                idealCumulativeHilbertFunction I N (n - c) + l) ∧
        (∀ n ≥ c,
          idealHilbertFunction I M n =
              idealHilbertFunction I M'' n +
                idealHilbertFunction I N (n - c)) := by
  sorry

theorem hilbert_cumulative_change_of_ideal
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I I' : Ideal R)
    (hI : IsIdealOfDefinition R I) (hI' : IsIdealOfDefinition R I') :
    ∃ a : ℕ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      idealCumulativeHilbertFunction I M n ≤
        idealCumulativeHilbertFunction I' M (a * n) := by
  sorry

/-! ## Numerical polynomials and the Hilbert polynomial -/

theorem ideal_hilbert_functions_are_numerical
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I) :
    IsNumericalPolynomial (idealHilbertFunctionInteger I M) ∧
      IsNumericalPolynomial (idealCumulativeHilbertFunctionInteger I M) := by
  sorry

theorem hilbert_functions_are_numerical
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    IsNumericalPolynomial (hilbertFunctionInteger R M) ∧
      IsNumericalPolynomial (cumulativeHilbertFunctionInteger R M) := by
  sorry

def IsEventuallyRationalPolynomial (f : ℤ → ℤ) (P : Polynomial ℚ) : Prop :=
  ∀ᶠ n : ℤ in Filter.atTop, P.eval (n : ℚ) = (f n : ℚ)

theorem exists_eventually_rational_polynomial_of_isNumericalPolynomial
    (f : ℤ → ℤ) (hf : IsNumericalPolynomial f) :
    ∃ P : Polynomial ℚ, IsEventuallyRationalPolynomial f P := by
  sorry

noncomputable def eventuallyRationalPolynomial (f : ℤ → ℤ) : Polynomial ℚ :=
  by
    classical
    exact if h : ∃ P : Polynomial ℚ, IsEventuallyRationalPolynomial f P then
      Classical.choose h
    else 0

def numericalPolynomialDegree (f : ℤ → ℤ) : WithBot ℕ :=
  (eventuallyRationalPolynomial f).degree

theorem eventuallyRationalPolynomial_spec
    (f : ℤ → ℤ) (hf : IsNumericalPolynomial f) :
    IsEventuallyRationalPolynomial f (eventuallyRationalPolynomial f) := by
  sorry

noncomputable def hilbertPolynomial
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Polynomial ℚ :=
  eventuallyRationalPolynomial (hilbertFunctionInteger R M)

theorem hilbertPolynomial_spec
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∀ᶠ n : ℕ in Filter.atTop,
      (hilbertPolynomial R M).eval (n : ℚ) =
        (hilbertFunction R M n : ℚ) := by
  sorry

theorem hilbertPolynomial_unique
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (P : Polynomial ℚ)
    (hP : ∀ᶠ n : ℕ in Filter.atTop,
      P.eval (n : ℚ) = (hilbertFunction R M n : ℚ)) :
    P = hilbertPolynomial R M := by
  sorry

theorem ideal_hilbert_function_degree_independent
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I I' : Ideal R)
    (hI : IsIdealOfDefinition R I) (hI' : IsIdealOfDefinition R I') :
    numericalPolynomialDegree (idealHilbertFunctionInteger I M) =
        numericalPolynomialDegree (idealHilbertFunctionInteger I' M) ∧
      numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M) =
        numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I' M) := by
  sorry

/-- The dimension invariant `d(M)` from the source. -/
def d
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] : WithBot ℕ :=
  by
    classical
    exact if Nontrivial M then
      numericalPolynomialDegree (cumulativeHilbertFunctionInteger R M)
    else ⊥

theorem d_eq_hilbertPolynomial_degree_add_one
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : ∀ n : ℕ,
      (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R M) ≠ ⊥) :
    d R M = (hilbertPolynomial R M).degree + 1 := by
  sorry

/-! ## Finite-colength differences -/

theorem cumulative_hilbert_difference_of_finite_colength
    {R : Type u} {M' M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (f : M' →ₗ[R] M) (hf : Function.Injective f)
    (hquot : IsFiniteLength R (M ⧸ LinearMap.range f))
    (hM : ¬ IsFiniteLength R M) :
    let Δ := fun n : ℤ =>
      idealCumulativeHilbertFunctionInteger I M n -
        idealCumulativeHilbertFunctionInteger I M' n
    IsNumericalPolynomial Δ ∧
      numericalPolynomialDegree Δ <
        numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M) ∧
      numericalPolynomialDegree Δ <
        numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M') := by
  sorry

/-! ## Exact sequences and degrees -/

theorem hilbert_short_exact_degree_statements
    {R : Type u} {M' M M'' : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    (¬ IsFiniteLength R M' →
        let Δ := fun n : ℤ =>
          idealCumulativeHilbertFunctionInteger I M n -
            idealCumulativeHilbertFunctionInteger I M'' n -
            idealCumulativeHilbertFunctionInteger I M' n
        IsNumericalPolynomial Δ ∧
          numericalPolynomialDegree Δ <
            numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M')) ∧
      max
          (numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M'))
          (numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M'')) =
        numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M) ∧
      max (d R M') (d R M'') = d R M := by
  sorry

end

end Formalization.Books.Algebra.Unit59
