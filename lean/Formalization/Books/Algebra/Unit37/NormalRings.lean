import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit36.FiniteIntegralRingExtensions
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Commutative Algebra, Chapter 37: Normal rings

The normal-domain and normal-ring predicates below are the source-facing
interfaces. Mathlib's canonical `IsIntegrallyClosed`, `IsIntegrallyClosedIn`,
`IsAlmostIntegral`, and `IsIntegralClosure` APIs are reused for their
integral-closure content; the earlier localization chapter supplies the
canonical total quotient ring.
-/

namespace Formalization.Books.Algebra.Unit37

universe u v w

noncomputable section

open Set
open scoped nonZeroDivisors Polynomial

/-! ## Normal domains and almost integral elements -/

/-- A commutative ring is a normal domain when it is a domain and is
integrally closed in its fraction ring. -/
def IsNormalDomain (R : Type*) [CommRing R] : Prop :=
  IsDomain R ∧ IsIntegrallyClosed R

/-- The integral closure of a ring in a normal domain is a normal domain. -/
theorem integralClosure_isNormalDomain
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hS : IsNormalDomain S) :
    IsNormalDomain (integralClosure R S) := by
  have hdomain : IsDomain S := hS.1
  have hclosed : IsIntegrallyClosed S := hS.2
  exact ⟨inferInstance,
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
      (integralClosure R S) S⟩

/- `IsAlmostIntegral R x` is Mathlib's canonical formulation of “almost
   integral over `R`; its witness is a non-zero-divisor scalar and its range
   condition is membership in the image of `algebraMap`. -/

/-- Every almost integral element of a fraction field belongs to the base
ring; this is the source's notion of complete normality. -/
def IsCompletelyNormal (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Prop :=
  ∀ {g : K}, IsAlmostIntegral R g →
    ∃ r : R, algebraMap R K r = g

/-- Almost integral elements in a fraction field are closed under addition and
multiplication. -/
theorem isAlmostIntegral_add_mul
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {u v : K} (hu : IsAlmostIntegral R u) (hv : IsAlmostIntegral R v) :
    IsAlmostIntegral R (u + v) ∧ IsAlmostIntegral R (u * v) := by
  exact ⟨(completeIntegralClosure R K).add_mem hu hv,
    (completeIntegralClosure R K).mul_mem hu hv⟩

/-- An element integral over a domain is almost integral in its fraction
field. -/
theorem isIntegral_isAlmostIntegral
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {g : K} (hg : IsIntegral R g) :
    IsAlmostIntegral R g := by
  exact hg.isAlmostIntegral

/-- Over a Noetherian domain, almost integral and integral elements of a
fraction field coincide. -/
theorem isAlmostIntegral_iff_isIntegral_of_noetherian
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R]
    {g : K} :
    IsAlmostIntegral R g ↔ IsIntegral R g := by
  constructor
  · exact IsAlmostIntegral.isIntegral
  · exact IsIntegral.isAlmostIntegral

/-- A Noetherian domain is normal exactly when it is completely normal. -/
theorem normalDomain_iff_completelyNormal
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R] :
    IsNormalDomain R ↔ IsCompletelyNormal R K := by
  constructor
  · rintro ⟨_, hclosed⟩ g hg
    exact (isIntegrallyClosed_iff K).mp hclosed
      ((isAlmostIntegral_iff_isIntegral_of_noetherian).mp hg)
  · intro hcomplete
    refine ⟨inferInstance, (isIntegrallyClosed_iff K).mpr ?_⟩
    intro g hg
    exact hcomplete (isIntegral_isAlmostIntegral hg)

/-! ## Permanence properties for normal domains -/

/-- A localization of a normal domain at non-zero-divisors is a normal
domain. -/
theorem localization_isNormalDomain
    {R : Type*} [CommRing R] (hR : IsNormalDomain R)
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) :
    IsNormalDomain (Localization M) := by
  letI : IsDomain R := hR.1
  letI : IsIntegrallyClosed R := hR.2
  refine ⟨IsLocalization.isDomain_localization hM, ?_⟩
  exact isIntegrallyClosed_of_isLocalization (Localization M) M hM

/-- A principal ideal domain is a normal domain. -/
theorem principalIdealDomain_isNormalDomain
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsNormalDomain R := by
  exact ⟨inferInstance, inferInstance⟩

/-! ## Polynomial and power-series rings -/

attribute [local instance] Polynomial.algebra

/-- Integrality of a polynomial over a polynomial ring can be checked on its
coefficients. -/
theorem polynomial_coeff_isIntegral
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : Polynomial K) (hf : IsIntegral (Polynomial R) f) (i : ℕ) :
    IsIntegral R (f.coeff i) := by
  exact hf.coeff i

/-- Almost integrality of a polynomial over a polynomial ring can be checked
on its coefficients. -/
theorem polynomial_coeff_isAlmostIntegral
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : Polynomial K) (hf : IsAlmostIntegral (Polynomial R) f) (i : ℕ) :
    IsAlmostIntegral R (f.coeff i) := by
  sorry

/-- The polynomial ring over a normal domain is a normal domain. -/
theorem polynomial_isNormalDomain
    {R : Type*} [CommRing R] (hR : IsNormalDomain R) :
    IsNormalDomain (Polynomial R) := by
  sorry

/-- A power-series ring over a Noetherian normal domain is Noetherian and is a
normal domain. -/
theorem powerSeries_isNoetherian_isNormalDomain
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (hR : IsNormalDomain R) :
    IsNoetherianRing (PowerSeries R) ∧ IsNormalDomain (PowerSeries R) := by
  sorry

/-! ## Locality and normal rings -/

/-- For a domain, normality can be checked at all prime localizations or at
all maximal localizations. -/
theorem normalDomain_local_iff
    {R : Type*} [CommRing R] [IsDomain R] :
    List.TFAE
      [ IsNormalDomain R,
        ∀ p : PrimeSpectrum R,
          IsNormalDomain (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R,
          IsNormalDomain (Localization.AtPrime m.asIdeal) ] := by
  sorry

/-- A commutative ring is normal when all of its prime localizations are
normal domains. -/
def IsNormalRing (R : Type*) [CommRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsNormalDomain (Localization.AtPrime p.asIdeal)

/-- A normal ring is reduced. -/
theorem normalRing_isReduced
    {R : Type*} [CommRing R] (hR : IsNormalRing R) :
    IsReduced R := by
  sorry

/-- A normal ring is integrally closed in its total ring of fractions. -/
theorem normalRing_isIntegrallyClosedIn_totalQuotientRing
    {R : Type*} [CommRing R] (hR : IsNormalRing R) :
    IsIntegrallyClosedIn R
      (Formalization.Books.Algebra.Unit09.totalQuotientRing R) := by
  sorry

/-- A localization of a normal ring is a normal ring. -/
theorem localization_isNormalRing
    {R S : Type*} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (hR : IsNormalRing R) :
    IsNormalRing S := by
  sorry

/-- A polynomial ring over a normal ring is a normal ring. -/
theorem polynomial_isNormalRing
    {R : Type*} [CommRing R] (hR : IsNormalRing R) :
    IsNormalRing (Polynomial R) := by
  sorry

/-- A finite product of normal rings is a normal ring. -/
theorem finite_product_isNormalRing
    {ι : Type u} [Fintype ι] {R : ι → Type v}
    [∀ i, CommRing (R i)] (hR : ∀ i, IsNormalRing (R i)) :
    IsNormalRing (∀ i, R i) := by
  sorry

/-- A ring is a finite product of normal domains when it is ring-isomorphic to
a finite product of commutative normal domains. -/
def IsFiniteProductOfNormalDomains (R : Type u) [CommRing R] : Prop :=
  ∃ (ι : Type u) (hι : Fintype ι) (S : ι → CommRingCat.{u}),
    letI : Fintype ι := hι
    (∀ i, IsNormalDomain (S i)) ∧
      Nonempty (R ≃+* (∀ i, (S i : Type u)))

/-- For a reduced ring with finitely many minimal primes, normality, integral
closure in the total quotient ring, and being a finite product of normal
domains are equivalent. -/
theorem normalRing_reduced_finite_minimalPrimes_TFAE
    {R : Type u} [CommRing R] [IsReduced R]
    (hfinite : (minimalPrimes R).Finite) :
    List.TFAE
      [ IsNormalRing R,
        IsIntegrallyClosedIn R
          (Formalization.Books.Algebra.Unit09.totalQuotientRing R),
        IsFiniteProductOfNormalDomains R ] := by
  sorry

/-! ## Directed colimits -/

/-- A directed colimit of normal rings is a normal ring. -/
theorem directLimit_isNormalRing
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {R : ι → Type v} [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (f · · ·)]
    (hR : ∀ i, IsNormalRing (R i)) :
    IsNormalRing (DirectLimit R f) := by
  sorry

end

end Formalization.Books.Algebra.Unit37
