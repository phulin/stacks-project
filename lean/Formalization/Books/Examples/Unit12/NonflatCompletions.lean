import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Examples, Chapter 12: Nonflat completions

This file records the definitions and theorem interfaces in the source
section.  The mathematical proofs belong to the proof stage.
-/

noncomputable section

open scoped TensorProduct
open scoped BigOperators

namespace Formalization.Books.Examples.Unit12

universe u v

/-! ## The tensor-product criterion -/

/-
The source's canonical map is Mathlib's `TensorProduct.piScalarRightHom` with
the coefficient ring used as both scalar rings.  Its codomain is the product
`ℕ → M`, and on a pure tensor it sends `m ⊗ a` to `n ↦ a n • m`.
-/

@[simp]
theorem countableTensorToPi_tmul (R : Type u) (M : Type v)
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    (m : M) (a : ℕ → R) :
    TensorProduct.piScalarRightHom R R M ℕ (m ⊗ₜ[R] a) = fun n => a n • m := by
  exact TensorProduct.piScalarRightHom_tmul R R M ℕ m a

theorem countable_finite_iff_tensor_surjective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Countable M] :
    Module.Finite R M ↔
      Function.Surjective (TensorProduct.piScalarRightHom R R M ℕ) := by
  sorry

theorem countable_finitePresentation_iff_tensor_bijective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Countable R] [Countable M] :
    Module.FinitePresentation R M ↔
      Function.Bijective (TensorProduct.piScalarRightHom R R M ℕ) := by
  sorry

/-! ## Coherence and power series -/

/-
Mathlib has the module-level notion of finite presentation but no separate
`Coherent` ring predicate.  The following is the standard commutative-ring
definition used by the source: every finitely generated ideal is finitely
presented as a module.
-/
def IsCoherent (R : Type u) [CommRing R] : Prop :=
  ∀ I : Ideal R, I.FG → Module.FinitePresentation R I

theorem coherent_iff_pi_flat (R : Type u) [CommRing R] [Countable R] :
    IsCoherent R ↔ Module.Flat R (ℕ → R) := by
  sorry

/-
The coefficient map is the module isomorphism used in the observation that
`R[[x]]` is `R^ℕ` as an `R`-module.
-/
def powerSeriesCoeffEquiv (R : Type u) [Semiring R] :
    PowerSeries R ≃ₗ[R] (ℕ → R) where
  toFun p n := PowerSeries.coeff n p
  invFun := PowerSeries.mk
  left_inv p := by
    apply PowerSeries.ext
    intro n
    simp
  right_inv f := by
    funext n
    simp
  map_add' p q := by
    funext n
    simp
  map_smul' r p := by
    funext n
    simp

theorem powerSeriesCoeffEquiv_apply (R : Type u) [Semiring R]
    (p : PowerSeries R) (n : ℕ) :
    powerSeriesCoeffEquiv R p n = PowerSeries.coeff n p :=
  rfl

theorem powerSeries_flat_iff_isCoherent
    (R : Type u) [CommRing R] [Countable R] :
    Module.Flat R (PowerSeries R) ↔ IsCoherent R := by
  sorry

theorem powerSeries_algebraMap_flat_iff_isCoherent
    (R : Type u) [CommRing R] [Countable R] :
    RingHom.Flat (algebraMap R (PowerSeries R)) ↔ IsCoherent R := by
  rw [RingHom.flat_algebraMap_iff]
  exact powerSeries_flat_iff_isCoherent R

/-! ## The explicitly displayed noncoherent ring -/

abbrev NoncoherentExampleVariables := Fin 2 ⊕ (ℕ × Bool)

def noncoherentExampleYVar : NoncoherentExampleVariables := Sum.inl 0

def noncoherentExampleZVar : NoncoherentExampleVariables := Sum.inl 1

def noncoherentExampleAVar (n : ℕ) : NoncoherentExampleVariables :=
  Sum.inr (n, false)

def noncoherentExampleBVar (n : ℕ) : NoncoherentExampleVariables :=
  Sum.inr (n, true)

def noncoherentExampleRelation (k : Type u) [CommSemiring k] (n : ℕ) :
    MvPolynomial NoncoherentExampleVariables k :=
  MvPolynomial.X (noncoherentExampleAVar n) * MvPolynomial.X noncoherentExampleYVar +
    MvPolynomial.X (noncoherentExampleBVar n) * MvPolynomial.X noncoherentExampleZVar

def noncoherentExampleRelationsIdeal (k : Type u) [CommSemiring k] :
    Ideal (MvPolynomial NoncoherentExampleVariables k) :=
  Ideal.span (Set.range (noncoherentExampleRelation k))

abbrev noncoherentExampleRing (k : Type u) [CommRing k] :=
  MvPolynomial NoncoherentExampleVariables k ⧸ noncoherentExampleRelationsIdeal k

def noncoherentExampleY (k : Type u) [CommRing k] : noncoherentExampleRing k :=
  Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k)
    (MvPolynomial.X noncoherentExampleYVar)

def noncoherentExampleZ (k : Type u) [CommRing k] : noncoherentExampleRing k :=
  Ideal.Quotient.mk (noncoherentExampleRelationsIdeal k)
    (MvPolynomial.X noncoherentExampleZVar)

def noncoherentExampleIdeal (k : Type u) [CommRing k] :
    Ideal (noncoherentExampleRing k) :=
  Ideal.span {noncoherentExampleY k, noncoherentExampleZ k}

theorem noncoherentExample_countable
    (k : Type u) [Field k] [Countable k] :
    Countable (noncoherentExampleRing k) := by
  sorry

instance noncoherentExample_countable_inst
    (k : Type u) [Field k] [Countable k] :
    Countable (noncoherentExampleRing k) :=
  noncoherentExample_countable k

theorem noncoherentExample_ideal_not_finitePresented
    (k : Type u) [Field k] [Countable k] :
    ¬ Module.FinitePresentation (noncoherentExampleRing k)
        (noncoherentExampleIdeal k) := by
  sorry

theorem noncoherentExample_not_coherent
    (k : Type u) [Field k] [Countable k] :
    ¬ IsCoherent (noncoherentExampleRing k) := by
  sorry

theorem noncoherentExample_powerSeries_not_flat
    (k : Type u) [Field k] [Countable k] :
    ¬ Module.Flat (noncoherentExampleRing k)
        (PowerSeries (noncoherentExampleRing k)) := by
  rw [powerSeries_flat_iff_isCoherent]
  exact noncoherentExample_not_coherent k

/-! ## Completion of a polynomial ring -/

def polynomialXIdeal (R : Type u) [CommRing R] : Ideal (Polynomial R) :=
  Ideal.span {(Polynomial.X : Polynomial R)}

abbrev polynomialRingCompletion (R : Type u) [CommRing R] :=
  AdicCompletion (polynomialXIdeal R) (Polynomial R)

def IsPowerSeriesCompletion (R : Type u) [CommRing R] : Prop :=
  Nonempty
    (PowerSeries R ≃ₐ[Polynomial R]
      polynomialRingCompletion R)

theorem powerSeries_is_completion (R : Type u) [CommRing R] :
    IsPowerSeriesCompletion R := by
  sorry

theorem completion_polynomial_ring_not_flat :
    ∃ (R : Type u) (_ : CommRing R),
      IsPowerSeriesCompletion R ∧
        ¬ Module.Flat R (PowerSeries R) ∧
        ¬ Module.Flat (Polynomial R) (PowerSeries R) := by
  sorry

/-! ## Valuation rings and almost integral elements -/

theorem valuationRing_is_coherent (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] :
    IsCoherent R := by
  sorry

theorem valuationRing_is_normal (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] :
    IsIntegrallyClosed R := by
  sorry

theorem valuationRing_powerSeries_flat (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] :
    Module.Flat R (PowerSeries R) := by
  sorry

theorem exists_valuationRing_dimension_gt_one_not_flat_over_polynomial :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : ValuationRing R),
      ¬ Ring.KrullDimLE 1 R ∧
        Module.Flat R (PowerSeries R) ∧
          ¬ Module.Flat (Polynomial R) (PowerSeries R) := by
  sorry

def IsCompletelyNormal (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Prop :=
  ∀ {x : K}, IsAlmostIntegral R x → ∃ r : R, algebraMap R K r = x

/-
The series used in the almost-integral argument is represented by its
coefficient data.  The source writes the coefficient of `x ^ n` as
`r * α ^ (n - 1)` but displays the identity `(a x - b) f = -r b`.
That identity uses the shifted coefficients `r * α ^ n`, including the
constant term `r`, so that is the convention used here.
-/
structure AlmostIntegralSeriesData (R : Type u) (K : Type v)
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (α : K) (r : R) where
  coefficient : ℕ → R
  coefficient_spec :
    ∀ n, algebraMap R K (coefficient n) = algebraMap R K r * α ^ n

def almostIntegralSeries {R : Type u} {K : Type v}
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {α : K} {r : R} (d : AlmostIntegralSeriesData R K α r) : PowerSeries R :=
  PowerSeries.mk d.coefficient

theorem exists_almostIntegralSeriesData
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (α : K) (r : R) (hr : r ≠ 0)
    (hpow : ∀ n : ℕ, 1 ≤ n →
      ∃ c : R, algebraMap R K c = algebraMap R K r * α ^ n) :
    Nonempty (AlmostIntegralSeriesData R K α r) := by
  sorry

theorem almostIntegralSeries_factorization
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (α : K) (r a b : R)
    (d : AlmostIntegralSeriesData R K α r) (hb : b ≠ 0)
    (hα : algebraMap R K a = α * algebraMap R K b) :
    (PowerSeries.C a * PowerSeries.X - PowerSeries.C b) *
        almostIntegralSeries d = PowerSeries.C (-r * b) := by
  sorry

/-
The multiplicative subset used in the proof consists of polynomials whose
constant coefficient is one.  It is represented by the canonical preimage
construction for submonoids.
-/
def almostIntegralDenominatorSubmonoid (R : Type u) [CommRing R] :
    Submonoid (Polynomial R) :=
  Submonoid.comap Polynomial.constantCoeff (Submonoid.powers (1 : R))

abbrev almostIntegralPolynomialLocalization (R : Type u) [CommRing R] :=
  Localization (almostIntegralDenominatorSubmonoid R)

noncomputable def almostIntegralPolynomialLocalizationMap
    (R : Type u) [CommRing R] :
    almostIntegralPolynomialLocalization R →+* PowerSeries R :=
  IsLocalization.lift (M := almostIntegralDenominatorSubmonoid R)
    (S := almostIntegralPolynomialLocalization R)
    (g := Polynomial.coeToPowerSeries.ringHom) (by
      intro h
      rw [PowerSeries.isUnit_iff_constantCoeff]
      change IsUnit (Polynomial.constantCoeff (h : Polynomial R))
      rcases (Submonoid.mem_powers_iff _ _).mp h.property with ⟨n, hn⟩
      rw [← hn]
      simp)

noncomputable instance almostIntegralPolynomialLocalizationPowerSeriesAlgebra
    (R : Type u) [CommRing R] :
    Algebra (almostIntegralPolynomialLocalization R) (PowerSeries R) :=
  RingHom.toAlgebra (almostIntegralPolynomialLocalizationMap R)

theorem almostIntegralPolynomialLocalization_faithfullyFlat
    (R : Type u) [CommRing R] [IsDomain R]
    (hflat : Module.Flat (Polynomial R) (PowerSeries R)) :
    RingHom.FaithfullyFlat (almostIntegralPolynomialLocalizationMap R) := by
  sorry

def almostIntegralPrincipalPolynomial (R : Type u) [CommRing R]
    (a b : R) : Ideal (Polynomial R) :=
  Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b}

abbrev almostIntegralLocalizedPrincipalIdeal
    (R : Type u) [CommRing R] (a b : R) :
    Ideal (almostIntegralPolynomialLocalization R) :=
  Ideal.map (algebraMap (Polynomial R)
    (almostIntegralPolynomialLocalization R))
    (almostIntegralPrincipalPolynomial R a b)

abbrev almostIntegralPowerSeriesPrincipalIdeal
    (R : Type u) [CommRing R] (a b : R) : Ideal (PowerSeries R) :=
  Ideal.map (almostIntegralPolynomialLocalizationMap R)
    (almostIntegralLocalizedPrincipalIdeal R a b)

noncomputable def almostIntegralPrincipalQuotientMap
    (R : Type u) [CommRing R] (a b : R) :
    (almostIntegralPolynomialLocalization R ⧸
        almostIntegralLocalizedPrincipalIdeal R a b) →+*
      (PowerSeries R ⧸ almostIntegralPowerSeriesPrincipalIdeal R a b) :=
  Ideal.Quotient.lift (almostIntegralLocalizedPrincipalIdeal R a b)
    ((Ideal.Quotient.mk (almostIntegralPowerSeriesPrincipalIdeal R a b)).comp
      (almostIntegralPolynomialLocalizationMap R))
    (fun _ hh => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (almostIntegralPolynomialLocalizationMap R) hh))

theorem almostIntegralPrincipalQuotientMap_injective
    (R : Type u) [CommRing R] [IsDomain R]
    (hflat : Module.Flat (Polynomial R) (PowerSeries R)) (a b : R) :
    Function.Injective (almostIntegralPrincipalQuotientMap R a b) := by
  sorry

theorem flat_powerSeries_normal_iff_completelyNormal
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (hflat : Module.Flat (Polynomial R) (PowerSeries R)) :
    IsIntegrallyClosed R ↔ IsCompletelyNormal R K := by
  sorry

theorem valuationRing_dimension_gt_one_not_completelyNormal
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (hdim : ¬ Ring.KrullDimLE 1 R) :
    ¬ IsCompletelyNormal R (FractionRing R) := by
  sorry

theorem valuationRing_dimension_gt_one_not_flat_over_polynomial
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (hdim : ¬ Ring.KrullDimLE 1 R) :
    Module.Flat R (PowerSeries R) ∧
      ¬ Module.Flat (Polynomial R) (PowerSeries R) := by
  sorry

/-! ## The nonflat localized completion

The source leaves the coefficient ring `k` implicit.  The Noetherian step in
the argument uses that `k[z][[x]]` is Noetherian, so the field hypothesis is
attached to the kernel characterization and the nonflatness conclusions below.
-/

abbrev NonflatLocalizationVariables := Fin 2 ⊕ ℕ

def nonflatLocalizationYVar : NonflatLocalizationVariables := Sum.inl 0

def nonflatLocalizationZVar : NonflatLocalizationVariables := Sum.inl 1

def nonflatLocalizationAVar (n : ℕ) : NonflatLocalizationVariables := Sum.inr n

def nonflatLocalizationYRelation (n : ℕ) (k : Type u) [CommSemiring k] :
    MvPolynomial NonflatLocalizationVariables k :=
  MvPolynomial.X nonflatLocalizationYVar * MvPolynomial.X (nonflatLocalizationAVar n)

def nonflatLocalizationARelation (p : ℕ × ℕ) (k : Type u) [CommSemiring k] :
    MvPolynomial NonflatLocalizationVariables k :=
  MvPolynomial.X (nonflatLocalizationAVar p.1) *
    MvPolynomial.X (nonflatLocalizationAVar p.2)

def nonflatLocalizationRelationsIdeal (k : Type u) [CommSemiring k] :
    Ideal (MvPolynomial NonflatLocalizationVariables k) :=
  Ideal.span
    (Set.range (fun n => nonflatLocalizationYRelation n k) ∪
      Set.range (fun p => nonflatLocalizationARelation p k))

abbrev nonflatLocalizationRing (k : Type u) [CommRing k] :=
  MvPolynomial NonflatLocalizationVariables k ⧸ nonflatLocalizationRelationsIdeal k

def nonflatLocalizationF (k : Type u) [CommRing k] : nonflatLocalizationRing k :=
  Ideal.Quotient.mk (nonflatLocalizationRelationsIdeal k)
    (MvPolynomial.X nonflatLocalizationZVar)

def nonflatLocalizationA (k : Type u) [CommRing k] (n : ℕ) : nonflatLocalizationRing k :=
  Ideal.Quotient.mk (nonflatLocalizationRelationsIdeal k)
    (MvPolynomial.X (nonflatLocalizationAVar n))

def nonflatLocalizationY (k : Type u) [CommRing k] : nonflatLocalizationRing k :=
  Ideal.Quotient.mk (nonflatLocalizationRelationsIdeal k)
    (MvPolynomial.X nonflatLocalizationYVar)

abbrev nonflatLocalizationPowerSeries (k : Type u) [CommRing k] :=
  PowerSeries (Localization.Away (nonflatLocalizationF k))

noncomputable def nonflatLocalizationCompletionMap
    (k : Type u) [CommRing k] :
    PowerSeries (nonflatLocalizationRing k) →+*
      nonflatLocalizationPowerSeries k :=
  PowerSeries.map (algebraMap (nonflatLocalizationRing k)
    (Localization.Away (nonflatLocalizationF k)))

def powerSeriesMultiplication (R : Type u) [CommRing R] (r : R) :
    PowerSeries R →ₗ[PowerSeries R] PowerSeries R :=
  LinearMap.mulLeft (PowerSeries R) (PowerSeries.C r)

def powerSeriesMulKernel (R : Type u) [CommRing R] (r : R) : Ideal (PowerSeries R) :=
  (LinearMap.ker (powerSeriesMultiplication R r) : Ideal (PowerSeries R))

theorem powerSeriesMulKernel_exact (R : Type u) [CommRing R] (r : R) :
    Function.Exact (powerSeriesMulKernel R r).subtype
      (powerSeriesMultiplication R r) :=
  by
  sorry

def nonflatLocalizationKernel (k : Type u) [CommRing k] :
    Ideal (nonflatLocalizationPowerSeries k) :=
  powerSeriesMulKernel (Localization.Away (nonflatLocalizationF k))
    (algebraMap (nonflatLocalizationRing k)
      (Localization.Away (nonflatLocalizationF k))
      (nonflatLocalizationY k))

def nonflatLocalizationSourceKernel (k : Type u) [CommRing k] :
    Ideal (PowerSeries (nonflatLocalizationRing k)) :=
  powerSeriesMulKernel (nonflatLocalizationRing k)
    (nonflatLocalizationY k)

/-!
The source describes elements of the kernel coefficientwise as finite sums
of the `a_m` with coefficients in `k[z]`.  `Polynomial k` is the canonical
Lean model for `k[z]`, and a finitely supported family records the finite
support required separately at each power of `x`.
-/

def nonflatLocalizationZPolynomialMap (k : Type u) [CommRing k] :
    Polynomial k →+* nonflatLocalizationRing k :=
  Polynomial.eval₂RingHom (algebraMap k (nonflatLocalizationRing k))
    (nonflatLocalizationF k)

def NonflatLocalizationKernelExpansion (k : Type u) [CommRing k]
    (g : PowerSeries (nonflatLocalizationRing k)) : Prop :=
  ∃ c : ℕ → (ℕ →₀ Polynomial k),
    ∀ n, PowerSeries.coeff n g =
      ∑ m ∈ (c n).support,
        nonflatLocalizationZPolynomialMap k (c n m) * nonflatLocalizationA k m

theorem nonflatLocalizationSourceKernel_iff_expansion
    (k : Type u) [Field k] (g : PowerSeries (nonflatLocalizationRing k)) :
    g ∈ nonflatLocalizationSourceKernel k ↔
      NonflatLocalizationKernelExpansion k g := by
  sorry

def nonflatLocalizationTargetMultiplication (k : Type u) [CommRing k] :
    nonflatLocalizationPowerSeries k →ₗ[nonflatLocalizationPowerSeries k]
      nonflatLocalizationPowerSeries k :=
  powerSeriesMultiplication (Localization.Away (nonflatLocalizationF k))
    (algebraMap (nonflatLocalizationRing k)
      (Localization.Away (nonflatLocalizationF k)) (nonflatLocalizationY k))

def nonflatLocalizationSourceMultiplication (k : Type u) [CommRing k] :
    PowerSeries (nonflatLocalizationRing k) →ₗ[PowerSeries (nonflatLocalizationRing k)]
      PowerSeries (nonflatLocalizationRing k) :=
  powerSeriesMultiplication (nonflatLocalizationRing k) (nonflatLocalizationY k)

theorem nonflatLocalizationSource_exact (k : Type u) [CommRing k] :
    Function.Exact (nonflatLocalizationSourceKernel k).subtype
      (nonflatLocalizationSourceMultiplication k) :=
  by
  sorry

theorem nonflatLocalizationTarget_exact (k : Type u) [CommRing k] :
    Function.Exact (nonflatLocalizationKernel k).subtype
      (nonflatLocalizationTargetMultiplication k) :=
  by
  sorry

def nonflatLocalizationWitness (k : Type u) [CommRing k] :
    nonflatLocalizationPowerSeries k :=
  PowerSeries.mk fun n =>
    (Localization.Away.invSelf (nonflatLocalizationF k)) ^ n *
      algebraMap (nonflatLocalizationRing k)
        (Localization.Away (nonflatLocalizationF k))
        (nonflatLocalizationA k n)

@[simp]
theorem nonflatLocalizationWitness_coeff
    (k : Type u) [CommRing k] (n : ℕ) :
    PowerSeries.coeff n (nonflatLocalizationWitness k) =
      (Localization.Away.invSelf (nonflatLocalizationF k)) ^ n *
        algebraMap (nonflatLocalizationRing k)
          (Localization.Away (nonflatLocalizationF k))
          (nonflatLocalizationA k n) := by
  simp [nonflatLocalizationWitness]

theorem nonflatLocalizationWitness_mem_kernel
    (k : Type u) [Field k] :
    nonflatLocalizationWitness k ∈ nonflatLocalizationKernel k := by
  sorry

theorem nonflatLocalizationWitness_not_mem_mapped_kernel
    (k : Type u) [Field k] :
    nonflatLocalizationWitness k ∉
      Ideal.map (algebraMap (PowerSeries (nonflatLocalizationRing k))
        (nonflatLocalizationPowerSeries k))
        (nonflatLocalizationSourceKernel k) := by
  sorry

theorem nonflatLocalizationKernel_ne_mapped_kernel
    (k : Type u) [Field k] :
    nonflatLocalizationKernel k ≠
      Ideal.map (algebraMap (PowerSeries (nonflatLocalizationRing k))
        (nonflatLocalizationPowerSeries k))
        (nonflatLocalizationSourceKernel k) := by
  intro h
  exact nonflatLocalizationWitness_not_mem_mapped_kernel k
    (h ▸ nonflatLocalizationWitness_mem_kernel k)

theorem nonflatLocalizationCompletionMap_flat_implies_kernel_eq
    (k : Type u) [CommRing k]
    (hflat : RingHom.Flat (nonflatLocalizationCompletionMap k)) :
    nonflatLocalizationKernel k =
      Ideal.map (algebraMap (PowerSeries (nonflatLocalizationRing k))
        (nonflatLocalizationPowerSeries k))
        (nonflatLocalizationSourceKernel k) := by
  sorry

theorem nonflatLocalizationCompletionMap_not_flat
    (k : Type u) [Field k] :
    ¬ RingHom.Flat (nonflatLocalizationCompletionMap k) := by
  intro hflat
  exact nonflatLocalizationKernel_ne_mapped_kernel k
    (nonflatLocalizationCompletionMap_flat_implies_kernel_eq k hflat)

/-! ## Completion after localization -/

abbrev localizedAdicCompletion
    (A : Type u) [CommRing A] (I : Ideal A) (f : A) : Type u :=
  AdicCompletion (Ideal.map (algebraMap A (Localization.Away f)) I)
    (Localization.Away f)

def nonflatLocalizationAdicIdeal (k : Type u) [CommRing k] :
    Ideal (PowerSeries (nonflatLocalizationRing k)) :=
  Ideal.span {(PowerSeries.X : PowerSeries (nonflatLocalizationRing k))}

abbrev nonflatLocalizationAdicCompletion (k : Type u) [CommRing k] :=
  localizedAdicCompletion (PowerSeries (nonflatLocalizationRing k))
    (nonflatLocalizationAdicIdeal k)
    (algebraMap (nonflatLocalizationRing k)
      (PowerSeries (nonflatLocalizationRing k)) (nonflatLocalizationF k))

theorem nonflatLocalizationAdicIdeal_isPrincipal
    (k : Type u) [CommRing k] :
    (nonflatLocalizationAdicIdeal k).IsPrincipal := by
  sorry

theorem nonflatLocalizationPowerSeries_completion_equiv
    (k : Type u) [CommRing k] :
    Nonempty
      (nonflatLocalizationPowerSeries k ≃+*
        nonflatLocalizationAdicCompletion k) := by
  sorry

theorem nonflatLocalizationAdicCompletion_not_flat
    (k : Type u) [Field k] :
    ¬ Module.Flat (PowerSeries (nonflatLocalizationRing k))
      (nonflatLocalizationAdicCompletion k) := by
  sorry

theorem exists_nonflat_localized_adic_completion :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A) (f : A),
      I.IsPrincipal ∧ IsAdicComplete I A ∧
        ¬ Module.Flat A (localizedAdicCompletion A I f) := by
  sorry

end Formalization.Books.Examples.Unit12
