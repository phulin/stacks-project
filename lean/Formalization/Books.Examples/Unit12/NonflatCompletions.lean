import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Examples, Chapter 12: Nonflat completions

This file records the definitions and theorem interfaces in the source
section.  The mathematical proofs belong to the proof stage.
-/

noncomputable section

open scoped TensorProduct

namespace Formalization.«Books.Examples».Unit12

universe u v

/-! ## The tensor-product criterion -/

/-
The source uses the canonical map
`M ⊗[R] (ℕ → R) → (ℕ → M)`, sending `m ⊗ a` to the sequence
`n ↦ a n • m`.  Mathlib supplies the tensor-product universal property, so
we define this map directly from `TensorProduct.lift`.
-/
def countableTensorToPi (R : Type u) (M : Type v)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    M ⊗[R] (ℕ → R) →ₗ[R] (ℕ → M) :=
  TensorProduct.lift
    { toFun := fun m =>
        { toFun := fun a n => a n • m
          map_add' := by
            intro a b
            funext n
            change (a n + b n) • m = a n • m + b n • m
            exact add_smul (a n) (b n) m
          map_smul' := by
            intro r a
            funext n
            rw [Pi.smul_apply, Pi.smul_apply]
            exact mul_smul r (a n) m }
      map_add' := by
        intro m₁ m₂
        ext a n
        change a n • (m₁ + m₂) = a n • m₁ + a n • m₂
        exact smul_add (a n) m₁ m₂
      map_smul' := by
        intro r m
        ext a n
        change a n • (r • m) = r • (a n • m)
        exact smul_comm _ _ _ }

@[simp]
theorem countableTensorToPi_tmul (R : Type u) (M : Type v)
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    (m : M) (a : ℕ → R) :
    countableTensorToPi R M (m ⊗ₜ[R] a) = fun n => a n • m :=
  rfl

theorem countable_finite_iff_tensor_surjective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Countable M] :
    Module.Finite R M ↔ Function.Surjective (countableTensorToPi R M) := by
  sorry

theorem countable_finitePresentation_iff_tensor_bijective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Countable R] [Countable M] :
    Module.FinitePresentation R M ↔
      Function.Bijective (countableTensorToPi R M) := by
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

theorem powerSeries_flat_iff_isCoherent
    (R : Type u) [CommRing R] [Countable R] :
    Module.Flat R (PowerSeries R) ↔ IsCoherent R := by
  sorry

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

theorem noncoherentExample_ideal_not_finitePresented
    (k : Type u) [Field k] [Countable k] :
    ¬ Module.FinitePresentation (noncoherentExampleRing k)
        (noncoherentExampleIdeal k) := by
  sorry

theorem noncoherentExample_not_coherent
    (k : Type u) [Field k] [Countable k] :
    ¬ IsCoherent (noncoherentExampleRing k) := by
  sorry

/-! ## Completion of a polynomial ring -/

def IsPowerSeriesCompletion (R : Type u) [CommRing R] : Prop :=
  Nonempty
    (PowerSeries R ≃ₐ[Polynomial R]
      AdicCompletion (Ideal.span {(Polynomial.X : Polynomial R)}) (Polynomial R))

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

def IsCompletelyNormal (R K : Type*) [CommRing R] [CommRing K]
    [Algebra R K] : Prop :=
  ∀ {x : K}, IsAlmostIntegral R x → ∃ r : R, algebraMap R K r = x

theorem flat_powerSeries_normal_iff_completelyNormal
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (hflat : Module.Flat (Polynomial R) (PowerSeries R)) :
    IsIntegrallyClosed R ↔ IsCompletelyNormal R K := by
  sorry

theorem valuationRing_dimension_gt_one_not_flat_over_polynomial
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (hdim : ¬ Ring.KrullDimLE 1 R) :
    Module.Flat R (PowerSeries R) ∧
      ¬ Module.Flat (Polynomial R) (PowerSeries R) := by
  sorry

/-! ## The nonflat localized completion -/

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

abbrev nonflatLocalizationPowerSeries (k : Type u) [CommRing k] :=
  PowerSeries (Localization.Away (nonflatLocalizationF k))

noncomputable def nonflatLocalizationCompletionMap
    (k : Type u) [CommRing k] :
    PowerSeries (nonflatLocalizationRing k) →+*
      nonflatLocalizationPowerSeries k :=
  PowerSeries.map (algebraMap (nonflatLocalizationRing k)
    (Localization.Away (nonflatLocalizationF k)))

def powerSeriesMulKernel (R : Type u) [CommRing R] (r : R) : Ideal (PowerSeries R) :=
  LinearMap.ker (LinearMap.mulLeft (PowerSeries R) (PowerSeries.C r))

def nonflatLocalizationKernel (k : Type u) [CommRing k] :
    Ideal (nonflatLocalizationPowerSeries k) :=
  powerSeriesMulKernel (Localization.Away (nonflatLocalizationF k))
    (algebraMap (nonflatLocalizationRing k)
      (Localization.Away (nonflatLocalizationF k))
      (Ideal.Quotient.mk (nonflatLocalizationRelationsIdeal k)
        (MvPolynomial.X nonflatLocalizationYVar)))

def nonflatLocalizationSourceKernel (k : Type u) [CommRing k] :
    Ideal (PowerSeries (nonflatLocalizationRing k)) :=
  powerSeriesMulKernel (nonflatLocalizationRing k)
    (Ideal.Quotient.mk (nonflatLocalizationRelationsIdeal k)
      (MvPolynomial.X nonflatLocalizationYVar))

def nonflatLocalizationWitness (k : Type u) [CommRing k] :
    nonflatLocalizationPowerSeries k :=
  PowerSeries.mk fun n =>
    (Localization.Away.invSelf (nonflatLocalizationF k)) ^ n *
      algebraMap (nonflatLocalizationRing k)
        (Localization.Away (nonflatLocalizationF k))
        (nonflatLocalizationA k n)

theorem nonflatLocalizationWitness_mem_kernel
    (k : Type u) [Field k] [Countable k] :
    nonflatLocalizationWitness k ∈ nonflatLocalizationKernel k := by
  sorry

theorem nonflatLocalizationWitness_not_mem_mapped_kernel
    (k : Type u) [Field k] [Countable k] :
    nonflatLocalizationWitness k ∉
      Ideal.map (algebraMap (PowerSeries (nonflatLocalizationRing k))
        (nonflatLocalizationPowerSeries k))
        (nonflatLocalizationSourceKernel k) := by
  sorry

theorem nonflatLocalizationKernel_ne_mapped_kernel
    (k : Type u) [Field k] [Countable k] :
    nonflatLocalizationKernel k ≠
      Ideal.map (algebraMap (PowerSeries (nonflatLocalizationRing k))
        (nonflatLocalizationPowerSeries k))
        (nonflatLocalizationSourceKernel k) := by
  intro h
  exact nonflatLocalizationWitness_not_mem_mapped_kernel k
    (h ▸ nonflatLocalizationWitness_mem_kernel k)

theorem nonflatLocalizationCompletionMap_not_flat
    (k : Type u) [Field k] [Countable k] :
    ¬ Module.Flat (PowerSeries (nonflatLocalizationRing k))
      (nonflatLocalizationPowerSeries k) := by
  sorry

/-! ## Completion after localization -/

abbrev localizedAdicCompletion
    (A : Type u) [CommRing A] (I : Ideal A) (f : A) : Type u :=
  AdicCompletion (Ideal.map (algebraMap A (Localization.Away f)) I)
    (Localization.Away f)

theorem exists_nonflat_localized_adic_completion :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A) (f : A),
      I.IsPrincipal ∧ IsAdicComplete I A ∧
        ¬ Module.Flat A (localizedAdicCompletion A I f) := by
  sorry

end Formalization.«Books.Examples».Unit12
