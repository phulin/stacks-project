import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Formalization.«Books.Examples».Unit19.NonCatenary
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Existence of bad local Noetherian rings

This file records the source-facing interfaces and examples from Chapter 20.
The cited existence theorems are deliberately theorem interfaces: their proofs
belong to the proof stage of the formalization.
-/

namespace Formalization.«Books.Examples».Unit20

universe u

open scoped TensorProduct
noncomputable section

/-!
## Complete local rings and coefficient hypotheses

Mathlib has the adic completion and regular-sequence APIs, but no numerical
depth predicate.  `DepthAtLeast` is the standard regular-sequence
characterization for the only depth bounds used in this section.
-/

def DepthAtLeast (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Prop :=
  ∃ rs : List A,
    rs.length = n ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal A) ∧
        RingTheory.Sequence.IsRegular A rs

def ContainsRationalsOrPrimeField (A : Type*) [CommRing A] : Prop :=
  (∃ f : ℚ →+* A, Function.Injective f) ∨
    (∃ p : ℕ, Nat.Prime p ∧
      ∃ f : ZMod p →+* A, Function.Injective f)

def LechCoefficientHypotheses (A : Type*) [CommRing A] : Prop :=
  ContainsRationalsOrPrimeField A ∨
    ((∃ f : ℤ →+* A, Function.Injective f) ∧ Module.IsTorsionFree ℤ A)

/- The local-ring witness is included in this predicate so the completion
   relation remains usable without making a proposition-valued local-ring
   hypothesis an ambient instance. -/
def IsCompletionOf (A R : Type*) [CommRing A] [CommRing R] : Prop :=
  ∃ hR : IsLocalRing R,
    letI : IsLocalRing R := hR
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* A)

def IsNormalDomain (R : Type*) [CommRing R] : Prop :=
  IsDomain R ∧ IsIntegrallyClosed R

theorem lech_completion_exists
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : DepthAtLeast A 1 ∧ LechCoefficientHypotheses A) :
    ∃ R : CommRingCat,
      IsNoetherianRing R ∧ IsLocalRing R ∧ IsDomain R ∧
        IsCompletionOf A R := by
  sorry

/-!
## The first completed example
-/

abbrev ComplexPowerSeries2 := MvPowerSeries (Fin 2) ℂ

def complexPowerSeries2SquareIdeal : Ideal ComplexPowerSeries2 :=
  Ideal.span {MvPowerSeries.X (1 : Fin 2) ^ 2}

abbrev ComplexPowerSeries2SquareQuotient :=
  ComplexPowerSeries2 ⧸ complexPowerSeries2SquareIdeal

theorem complexPowerSeries2SquareQuotient_is_complete_local_noetherian :
    ∃ hA : IsLocalRing ComplexPowerSeries2SquareQuotient,
      letI : IsLocalRing ComplexPowerSeries2SquareQuotient := hA
      IsNoetherianRing ComplexPowerSeries2SquareQuotient ∧
        IsAdicComplete
          (IsLocalRing.maximalIdeal ComplexPowerSeries2SquareQuotient)
          ComplexPowerSeries2SquareQuotient := by
  sorry

theorem complexPowerSeries2SquareQuotient_is_not_reduced :
    ¬ IsReduced ComplexPowerSeries2SquareQuotient := by
  sorry

theorem lech_nonreduced_completion_example :
    ∃ R : CommRingCat,
      IsNoetherianRing R ∧ IsLocalRing R ∧ IsDomain R ∧
        IsCompletionOf ComplexPowerSeries2SquareQuotient R := by
  sorry

/- The source cites the LLPY characterization of reduced completions but does
   not state the conditions it characterizes, so there is no source-faithful
   theorem interface to add at this point. -/

/-!
## UFD completions and henselization
-/

theorem heitmann_ufd_completion_exists
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : DepthAtLeast A 2 ∧ LechCoefficientHypotheses A) :
    ∃ R : CommRingCat,
      IsNoetherianRing R ∧ IsLocalRing R ∧ IsDomain R ∧
        UniqueFactorizationMonoid R ∧ IsCompletionOf A R := by
  sorry

theorem unique_factorization_domain_is_normal
    (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] :
    IsNormalDomain R := by
  sorry

def IsHenselization
    (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) : Prop :=
  IsLocalHom f ∧ HenselianLocalRing B ∧
    ∀ (C : Type*) [CommRing C] [HenselianLocalRing C],
      ∀ (g : A →+* C), IsLocalHom g →
        ∃! h : B →+* C, IsLocalHom h ∧ h.comp f = g

def CompletionsAgree (R S : Type*) [CommRing R] [CommRing S] : Prop :=
  ∃ hR : IsLocalRing R, ∃ hS : IsLocalRing S,
    letI : IsLocalRing R := hR
    letI : IsLocalRing S := hS
    Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal S) S)

def IsHenselianNormalDomain (R : Type*) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ HenselianLocalRing R ∧ IsNormalDomain R

theorem henselization_of_normal_domain_is_normal
    (R Rh : Type*) [CommRing R] [CommRing Rh] [IsLocalRing R] [IsLocalRing Rh]
    (f : R →+* Rh) (hR : IsNormalDomain R)
    (hRh : IsHenselization R Rh f) :
    IsNormalDomain Rh := by
  sorry

theorem henselization_completion_agrees
    (R Rh : Type*) [CommRing R] [CommRing Rh] [IsNoetherianRing R]
    [IsNoetherianRing Rh] [IsLocalRing R] [IsLocalRing Rh]
    (f : R →+* Rh) (hRh : IsHenselization R Rh f) :
    CompletionsAgree R Rh := by
  sorry

theorem completion_of_equivalent_completions
    (A R S : Type*) [CommRing A] [CommRing R] [CommRing S]
    (hR : IsCompletionOf A R) (hRS : CompletionsAgree R S) :
    IsCompletionOf A S := by
  sorry

theorem heitmann_henselian_normal_completion_exists
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : DepthAtLeast A 2 ∧ LechCoefficientHypotheses A) :
    ∃ R : CommRingCat,
      IsHenselianNormalDomain R ∧ IsCompletionOf A R := by
  sorry

/-!
## Catenarity and the two-component completion

`IsCatenaryRing` uses saturated chains of prime ideals, the usual chain
formulation of catenarity.  `IsUniversallyCatenary` quantifies over finite-type
algebras, which is the ring-map formulation used in the source.
-/

abbrev IsCatenaryRing (R : Type*) [CommRing R] : Prop :=
  Formalization.«Books.Examples».Unit19.IsCatenaryRing R

def IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
    IsCatenaryRing S

/- The displayed blow-up morphism and the strict-transform point in the
   source are proof-level witnesses for the non-universal-catenarity result;
   the current Mathlib version has no blow-up construction to expose as a
   reusable declaration. -/

abbrev ComplexPowerSeries4 := MvPowerSeries (Fin 4) ℂ

def complexPowerSeries4TwoComponentIdeal : Ideal ComplexPowerSeries4 :=
  Ideal.span {
    MvPowerSeries.X (3 : Fin 4) * MvPowerSeries.X (0 : Fin 4),
    MvPowerSeries.X (3 : Fin 4) * MvPowerSeries.X (1 : Fin 4)
  }

abbrev ComplexPowerSeries4TwoComponentQuotient :=
  ComplexPowerSeries4 ⧸ complexPowerSeries4TwoComponentIdeal

def IsRegularComponentOfDimension {A : Type*} [CommRing A]
    (p : Ideal A) (d : ℕ) : Prop :=
  p ∈ minimalPrimes A ∧ IsRegularRing (A ⧸ p) ∧
    ringKrullDim (A ⧸ p) = d

theorem complexPowerSeries4_two_component_description :
    ∃ p₂ p₃ : Ideal ComplexPowerSeries4TwoComponentQuotient,
      p₂ ≠ p₃ ∧
        minimalPrimes ComplexPowerSeries4TwoComponentQuotient = {p₂, p₃} ∧
          IsRegularComponentOfDimension p₂ 2 ∧
            IsRegularComponentOfDimension p₃ 3 := by
  sorry

theorem heitmann_two_component_completion_example :
    ∃ R : CommRingCat,
      IsNoetherianRing R ∧ IsLocalRing R ∧ IsDomain R ∧
        UniqueFactorizationMonoid R ∧
          IsCompletionOf ComplexPowerSeries4TwoComponentQuotient R ∧
            ringKrullDim R = 3 ∧ ¬ IsUniversallyCatenary R := by
  sorry

theorem three_dimensional_local_noetherian_ufd_is_catenary
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] [UniqueFactorizationMonoid R]
    (hR : ringKrullDim R = 3) :
    IsCatenaryRing R := by
  sorry

theorem ogoma_non_catenary_normal_example :
    ∃ R : CommRingCat,
      IsNoetherianRing R ∧ IsLocalRing R ∧ IsNormalDomain R ∧
        IsCompletionOf ComplexPowerSeries4TwoComponentQuotient R ∧
          ¬ IsCatenaryRing R := by
  sorry

/-!
## Isolated singularities
-/

def IsRegularAtPrime {R : Type*} [CommRing R]
    (p : Ideal R) (hp : p.IsPrime) : Prop :=
  letI : p.IsPrime := hp
  IsRegularLocalRing (Localization.AtPrime p)

def HasIsolatedSingularity (R : Type*) [CommRing R] : Prop :=
  ∃ hR : IsLocalRing R,
    letI : IsLocalRing R := hR
    IsNoetherianRing R ∧
      ∀ (p : Ideal R) (hp : p.IsPrime),
        p ≠ IsLocalRing.maximalIdeal R → IsRegularAtPrime p hp

def IsIntegerRegularInProperLocalizations
    (A : Type*) [CommRing A] [IsLocalRing A] (p : ℕ) : Prop :=
  ∀ (q : Ideal A) (hq : q.IsPrime), q ≠ IsLocalRing.maximalIdeal A →
    letI : q.IsPrime := hq
    IsSMulRegular (Localization.AtPrime q)
      (algebraMap A (Localization.AtPrime q) (p : A))

def HeitmannIsolatedSingularityHypotheses (A : Type*) [CommRing A] : Prop :=
  ∃ hA : IsLocalRing A,
    letI : IsLocalRing A := hA
    ContainsRationalsOrPrimeField A ∨
      ∃ p : ℕ, 0 < p ∧ CharP (IsLocalRing.ResidueField A) p ∧
        IsIntegerRegularInProperLocalizations A p

theorem heitmann_isolated_singularity_completion_exists
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hA : HeitmannIsolatedSingularityHypotheses A) :
    ∃ R : CommRingCat,
      HasIsolatedSingularity R ∧ IsCompletionOf A R := by
  sorry

/-!
## Nishimura's Nagata normal domains

The Japanese condition in the source definition of a Nagata ring is written
using the canonical fraction-ring and integral-closure APIs.
-/

def IsJapaneseDomain (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L],
    letI : Algebra R L :=
      ((algebraMap (FractionRing R) L).comp
        (algebraMap R (FractionRing R))).toAlgebra
    Module.Finite R (integralClosure R L)

def IsNagataRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ p : Ideal R, ∀ hp : p.IsPrime,
      letI : p.IsPrime := hp
      IsJapaneseDomain (R ⧸ p)

abbrev ComplexPowerSeries3 := MvPowerSeries (Fin 3) ℂ

def complexPowerSeries3CrossingIdeal : Ideal ComplexPowerSeries3 :=
  Ideal.span {
    MvPowerSeries.X (1 : Fin 3) * MvPowerSeries.X (2 : Fin 3)
  }

abbrev ComplexPowerSeries3CrossingQuotient :=
  ComplexPowerSeries3 ⧸ complexPowerSeries3CrossingIdeal

def complexPowerSeries3CuspIdeal : Ideal ComplexPowerSeries3 :=
  Ideal.span {
    MvPowerSeries.X (1 : Fin 3) ^ 2 - MvPowerSeries.X (2 : Fin 3) ^ 3
  }

abbrev ComplexPowerSeries3CuspQuotient :=
  ComplexPowerSeries3 ⧸ complexPowerSeries3CuspIdeal

theorem nishimura_crossing_completion_exists :
    ∃ R : CommRingCat,
      IsNagataRing R ∧ IsLocalRing R ∧ IsNormalDomain R ∧
        ringKrullDim R = 2 ∧
          IsCompletionOf ComplexPowerSeries3CrossingQuotient R := by
  sorry

theorem nishimura_cusp_completion_exists :
    ∃ R : CommRingCat,
      IsNagataRing R ∧ IsLocalRing R ∧ IsNormalDomain R ∧
        ringKrullDim R = 2 ∧
          IsCompletionOf ComplexPowerSeries3CuspQuotient R := by
  sorry

/-!
## Loepp's excellent-domain criterion

Mathlib has no built-in excellent-ring predicate.  The standard decomposition
is recorded here: a quasi-excellent ring is a Noetherian J-2 G-ring, and an
excellent ring is quasi-excellent and universally catenary.  The regular
locus and formal fibers below use Mathlib's regular-local, adic-completion,
and tensor-product APIs.
-/

def IsGeometricallyRegularAlgebra
    (k B : Type u) [Field k] [CommRing B] [Algebra k B] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra k L],
    IsRegularRing (B ⊗[k] L)

abbrev FormalFiber (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] : Type u :=
  IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[Localization.AtPrime p]
    AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)

def IsGRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ p : Ideal R, ∀ hp : p.IsPrime,
      letI : p.IsPrime := hp
      IsGeometricallyRegularAlgebra
        (IsLocalRing.ResidueField (Localization.AtPrime p))
        (FormalFiber R p)

def IsJ2Ring (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
      IsOpen {p : PrimeSpectrum S | IsRegularAtPrime p.asIdeal p.isPrime}

def IsQuasiExcellentRing (R : Type u) [CommRing R] : Prop :=
  IsJ2Ring R ∧ IsGRing R

def IsExcellentRing (R : Type u) [CommRing R] : Prop :=
  IsQuasiExcellentRing R ∧ IsUniversallyCatenary R

def IsEquidimensional (A : Type*) [CommRing A] : Prop :=
  ∃ d : ℕ, ∀ p ∈ minimalPrimes A, ringKrullDim (A ⧸ p) = d

def NoIntegerZeroDivisors (A : Type*) [CommRing A] : Prop :=
  Module.IsTorsionFree ℤ A

theorem loepp_excellent_domain_completion_exists
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hred : IsReduced A) (hequidim : IsEquidimensional A)
    (hinteger : NoIntegerZeroDivisors A) :
    ∃ R : CommRingCat,
      IsExcellentRing R ∧ IsLocalRing R ∧ IsDomain R ∧ IsCompletionOf A R := by
  sorry

end

end Formalization.«Books.Examples».Unit20
