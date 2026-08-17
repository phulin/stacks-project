import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit62.SupportAndDimension
import Formalization.Books.Algebra.Unit63.AssociatedPrimes
import Formalization.Books.Algebra.Unit67.EmbeddedPrimes
import Formalization.Books.Algebra.Unit72.Depth
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Commutative Algebra, Chapter 157: Serre's criterion for normality

This file records the source's `(R_k)` and `(S_k)` conditions and the
equivalences and height-one localization statements that make up Serre's
criterion for normality.  The depth and support-dimension expressions use
the canonical interfaces from Chapters 62 and 72.
-/

namespace Formalization.Books.Algebra.Unit157

open Set
open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit67
open Formalization.Books.Algebra.Unit72

universe u v

noncomputable section

/-! ## The `(R_k)` and `(S_k)` conditions -/

/-- A ring has property `(R_k)` when every prime of height at most `k` has
regular localization.  The Noetherian hypothesis from the source is retained
on the theorems using this condition; the predicate itself is also useful as
a local property without that hypothesis. -/
def HasPropertyRk (R : Type u) [CommRing R] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    p.asIdeal.height ≤ (k : ℕ∞) →
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)

/-- The source's alternate name for property `(R_k)`. -/
abbrev IsRegularInCodimensionLe (R : Type u) [CommRing R] (k : ℕ) : Prop :=
  HasPropertyRk R k

/-- A Noetherian ring has property `(S_k)` when the depth at every prime is
at least the minimum of `k` and the dimension of the corresponding local
ring. -/
def HasPropertySk (R : Type u) [CommRing R] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    min ((k : ℕ∞) : WithBot ℕ∞)
        (ringKrullDim (Localization.AtPrime p.asIdeal)) ≤
      ((localDepth (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal) : ℕ∞) : WithBot ℕ∞)

/-- The module form of property `(S_k)`: the localized module has depth at
least the minimum of `k` and the dimension of its localized support. -/
def HasPropertySkModule
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    min ((k : ℕ∞) : WithBot ℕ∞)
        (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) ≤
      ((localDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M) : ℕ∞) : WithBot ℕ∞)

/-- Every Noetherian ring has property `(S_0)`. -/
theorem hasPropertySk_zero
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    HasPropertySk R 0 := by
  sorry

/-- Every finite module over a Noetherian ring has property `(S_0)`. -/
theorem hasPropertySkModule_zero
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasPropertySkModule R M 0 := by
  sorry

/-- A zero module has property `(S_k)` for every `k`.  A `Subsingleton`
module is the type-theoretic representation of the zero module. -/
theorem hasPropertySkModule_of_subsingleton
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Subsingleton M] (k : ℕ) :
    HasPropertySkModule R M k := by
  sorry

/-! ## The three main equivalences -/

/-- A finite module over a Noetherian ring has no embedded associated prime
exactly when it satisfies `(S_1)`. -/
theorem criterion_no_embedded_primes
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    embeddedAssociatedPrimes (R := R) (M := M) = ∅ ↔
      HasPropertySkModule R M 1 := by
  sorry

/-- Serre's reducedness criterion: reduced is equivalent to `(R_0)` plus
`(S_1)`. -/
theorem criterion_reduced
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsReduced R ↔ HasPropertyRk R 0 ∧ HasPropertySk R 1 := by
  sorry

/-- Serre's criterion for normality: normal is equivalent to `(R_1)` plus
`(S_2)`. -/
theorem criterion_normal
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsNormalRing R ↔ HasPropertyRk R 1 ∧ HasPropertySk R 2 := by
  sorry

/-- A regular ring is normal.  `IsRegularRing` is Mathlib's canonical
Noetherian regular-ring class, while `IsNormalRing` is the source-facing
normal-ring predicate from Chapter 37. -/
theorem regularRing_isNormal
    {R : Type u} [CommRing R] [IsRegularRing R] :
    IsNormalRing R := by
  sorry

/-! ## Height-one localizations of a normal domain -/

/-- For a nonzero element of a Noetherian normal domain, the quotient by the
principal ideal has no embedded associated primes and all its associated
primes have height one. -/
theorem normalDomain_principal_quotient_height_one
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsNormalDomain R) :
    ∀ {a : R}, a ≠ 0 →
      embeddedAssociatedPrimes (R := R)
          (M := R ⧸ Ideal.span ({a} : Set R)) = ∅ ∧
        ∀ p : PrimeSpectrum R,
          p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R
            (R ⧸ Ideal.span ({a} : Set R)) →
            p.asIdeal.height = 1 := by
  sorry

/-- The intersection of the height-one localizations, viewed inside a fixed
fraction field.  The explicit domain argument supplies the nonzerodivisor
condition needed to realize each localization as a subalgebra of the field. -/
noncomputable def heightOneLocalizationIntersection
    (R : Type u) (K : Type u) [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (hR : IsDomain R) : Set K := by
  letI : IsDomain R := hR
  exact ⋂ p : {p : PrimeSpectrum R // p.asIdeal.height = 1},
    (Localization.subalgebra.ofField K p.1.asIdeal.primeCompl
      p.1.asIdeal.primeCompl_le_nonZeroDivisors : Set K)

/-- The displayed intersection identity for a Noetherian normal domain,
written as equality of the image of `R` in its fraction field with the
intersection of the height-one localization subalgebras. -/
theorem normalDomain_eq_heightOneLocalizationIntersection
    (R : Type u) (K : Type u) [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsNormalDomain R) :
    Set.range (algebraMap R K) =
      heightOneLocalizationIntersection R K hR.1 := by
  sorry

/- The source's proof of the intersection identity uses the following
membership form: `b ∈ aR` exactly when `b` belongs to `aR_p` at every
height-one prime.  It is recorded separately because it is often the most
convenient form for applications and avoids choosing fraction representatives. -/
theorem principal_mem_iff_mem_all_heightOne_localizations
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R]
    {a b : R} (ha : a ≠ 0) :
    (∃ c : R, b = a * c) ↔
      ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
        ∃ z : Localization.AtPrime p.asIdeal,
          algebraMap R (Localization.AtPrime p.asIdeal) b =
            algebraMap R (Localization.AtPrime p.asIdeal) a * z := by
  sorry

/-- The fractional ideal `R ∩ xR`, represented as the comap of the
`R`-submodule generated by `x` in the fraction field. -/
def fractionIntersectionIdeal
    (R : Type u) (K : Type u) [CommRing R] [Field K]
    [Algebra R K] (x : K) : Ideal R :=
  Submodule.comap (Algebra.linearMap R K)
    (Submodule.span R ({x} : Set K))

/-- For a nonzero fraction `x`, the quotient by `R ∩ xR` has no embedded
associated primes and all of its associated primes have height one. -/
theorem fractionIntersection_criterion
    (R : Type u) (K : Type u) [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsNormalDomain R) :
    ∀ {x : K}, x ≠ 0 →
      embeddedAssociatedPrimes (R := R)
          (M := R ⧸ fractionIntersectionIdeal R K x) = ∅ ∧
        ∀ p : PrimeSpectrum R,
          p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R
            (R ⧸ fractionIntersectionIdeal R K x) →
          p.asIdeal.height = 1 := by
  sorry

end

end Formalization.Books.Algebra.Unit157
