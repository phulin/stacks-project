import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit25.ZerodivisorsAndTotalRingsOfFractions
import Formalization.Books.Algebra.Unit36.FiniteIntegralRingExtensions
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Ring
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.LocalProperties.Reduced

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
  let : IsDomain R := hR.1
  let : IsIntegrallyClosed R := hR.2
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
  exact hf.coeff i

private theorem polynomial_isNormalDomain_of_isDomain_of_isIntegrallyClosed
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalDomain (Polynomial R) := by
  exact ⟨inferInstance, inferInstance⟩

/-- The polynomial ring over a normal domain is a normal domain. -/
theorem polynomial_isNormalDomain
    {R : Type*} [CommRing R] (hR : IsNormalDomain R) :
    IsNormalDomain (Polynomial R) := by
  exact @polynomial_isNormalDomain_of_isDomain_of_isIntegrallyClosed R _ hR.1 hR.2

private theorem powerSeries_isNormalDomain_of_isDomain_of_isIntegrallyClosed
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] :
    IsNormalDomain (PowerSeries R) := by
  let : Field (FractionRing R) := IsFractionRing.toField R
  let K := FractionRing R
  let P := PowerSeries R
  let L := LaurentSeries K
  let φ : P →+* L :=
    (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (algebraMap R K))
  let : Algebra P L := φ.toAlgebra
  have hφ : Function.Injective φ := by
    intro x y h
    apply (PowerSeries.map_injective (algebraMap R K) (IsFractionRing.injective R K))
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    simpa [φ] using h
  have horder : ∀ a : P, a ≠ 0 → (algebraMap P L a).order = (a.order.toNat : ℤ) := by
    intro a ha
    have hcoeff : PowerSeries.coeff a.order.toNat a ≠ 0 := PowerSeries.coeff_order ha
    have hmap0 : algebraMap P L a ≠ 0 := by
      change φ a ≠ 0
      intro h
      apply ha
      apply (PowerSeries.map_injective (algebraMap R K) (IsFractionRing.injective R K))
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
      simpa [φ] using h
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      change ((PowerSeries.map (algebraMap R K) a : PowerSeries K) : L).coeff
        (a.order.toNat : ℤ) ≠ 0
      simp [PowerSeries.coeff_coe, hcoeff]
    · refine (HahnSeries.le_order_iff_forall (x := algebraMap P L a)
        (i := (a.order.toNat : ℤ)) hmap0).2 ?_
      intro i hi
      change ((PowerSeries.map (algebraMap R K) a : PowerSeries K) : L).coeff i = 0
      rw [PowerSeries.coeff_coe]
      by_cases hi0 : i < 0
      · simp [hi0]
      · rw [if_neg hi0, PowerSeries.coeff_map]
        have hz : PowerSeries.coeff i.natAbs a = 0 := by
          apply PowerSeries.coeff_of_lt_order_toNat
          omega
        simp [hz]
  have hlead : ∀ f : L, IsAlmostIntegral P f → f ≠ 0 →
      0 ≤ f.order ∧ IsAlmostIntegral R (f.coeff f.order) := by
    intro f hf hf0
    obtain ⟨a, ha, ha'⟩ := hf
    have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
    have ha_coeff : PowerSeries.coeff a.order.toNat a ≠ 0 := PowerSeries.coeff_order ha0
    have hf_coeff : f.coeff f.order ≠ 0 := fun h =>
      hf0 (HahnSeries.coeff_order_eq_zero.mp h)
    have hfa0 : algebraMap P L a ≠ 0 := by
      change φ a ≠ 0
      intro h
      apply ha0
      apply (PowerSeries.map_injective (algebraMap R K) (IsFractionRing.injective R K))
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
      simpa [φ] using h
    have hleadpow : ∀ n : ℕ, (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]
    have hnonneg : 0 ≤ f.order := by
      by_contra hneg
      let n : ℕ := a.order.toNat + 1
      obtain ⟨q, hq⟩ := ha' n
      have hindex : (a.order.toNat : ℤ) + n • f.order =
          (algebraMap P L a).order + (f ^ n).order := by
        rw [horder a ha0, HahnSeries.order_pow]
      have ht : (a.order.toNat : ℤ) + n • f.order < 0 := by
        have hneg' : f.order ≤ (-1 : ℤ) := by omega
        have hmul := nsmul_le_nsmul_right hneg' n
        calc
          (a.order.toNat : ℤ) + n • f.order ≤
              (a.order.toNat : ℤ) + n • (-1 : ℤ) := add_le_add_right hmul _
          _ < 0 := by simp [n]
      have hprod_coeff : (algebraMap P L a * f ^ n).coeff
          ((a.order.toNat : ℤ) + n • f.order) ≠ 0 := by
        rw [hindex, HahnSeries.coeff_mul_order_add_order]
        rw [HahnSeries.leadingCoeff_eq, hleadpow]
        rw [HahnSeries.leadingCoeff_eq, horder a ha0]
        change ((PowerSeries.map (algebraMap R K) a : PowerSeries K) : L).coeff
            (a.order.toNat : ℤ) * f.coeff f.order ^ n ≠ 0
        simp [PowerSeries.coeff_coe, ha_coeff, hf_coeff]
      have hcoeff_eq : (algebraMap P L q).coeff
          ((a.order.toNat : ℤ) + n • f.order) = 0 := by
        change ((PowerSeries.map (algebraMap R K) q : PowerSeries K) : L).coeff
          ((a.order.toNat : ℤ) + n • f.order) = 0
        simp only [PowerSeries.coeff_coe, if_pos ht]
      have hq' : algebraMap P L q = algebraMap P L a * f ^ n := by
        simpa [Algebra.smul_def] using hq
      exact hprod_coeff (by rw [← hq', hcoeff_eq])
    refine ⟨hnonneg, ?_⟩
    refine ⟨a.coeff a.order.toNat, mem_nonZeroDivisors_iff_ne_zero.mpr ha_coeff, ?_⟩
    intro n
    obtain ⟨q, hq⟩ := ha' n
    have hq' : algebraMap P L q = algebraMap P L a * f ^ n := by
      simpa [Algebra.smul_def] using hq
    have hindex : (a.order.toNat : ℤ) + n • f.order =
        (algebraMap P L a).order + (f ^ n).order := by
      rw [horder a ha0, HahnSeries.order_pow]
    have ht0 : 0 ≤ (a.order.toNat : ℤ) + n • f.order := by
      exact add_nonneg (by omega) (nsmul_nonneg hnonneg n)
    have hcoeffprod : (algebraMap P L a * f ^ n).coeff
        ((a.order.toNat : ℤ) + n • f.order) =
        algebraMap R K (a.coeff a.order.toNat) * (f.coeff f.order) ^ n := by
      rw [hindex, HahnSeries.coeff_mul_order_add_order]
      rw [HahnSeries.leadingCoeff_eq, hleadpow]
      rw [HahnSeries.leadingCoeff_eq, horder a ha0]
      change ((PowerSeries.map (algebraMap R K) a : PowerSeries K) : L).coeff
          (a.order.toNat : ℤ) * f.coeff f.order ^ n = _
      simp [PowerSeries.coeff_coe]
    have hqcoeff : (algebraMap P L q).coeff
        ((a.order.toNat : ℤ) + n • f.order) =
        algebraMap R K (q.coeff ((a.order.toNat : ℤ) + n • f.order).natAbs) := by
      change ((PowerSeries.map (algebraMap R K) q : PowerSeries K) : L).coeff
        ((a.order.toNat : ℤ) + n • f.order) = _
      rw [PowerSeries.coeff_coe, if_neg (not_lt.mpr ht0), PowerSeries.coeff_map]
    refine ⟨q.coeff ((a.order.toNat : ℤ) + n • f.order).natAbs, ?_⟩
    calc
      algebraMap R K (q.coeff ((a.order.toNat : ℤ) + (n : ℤ) • f.order).natAbs) =
          (algebraMap P L q).coeff ((a.order.toNat : ℤ) + n • f.order) := by
        symm
        simpa [nsmul_eq_mul] using hqcoeff
      _ = (algebraMap P L a * f ^ n).coeff ((a.order.toNat : ℤ) + n • f.order) := by
        rw [hq']
      _ = algebraMap R K (a.coeff a.order.toNat) * (f.coeff f.order) ^ n := hcoeffprod
      _ = (a.coeff a.order.toNat) • (f.coeff f.order) ^ n := by
        rw [Algebra.smul_def]
  let : Field (FractionRing P) := IsFractionRing.toField P
  let ψ : FractionRing P →ₐ[P] L :=
    IsFractionRing.liftAlgHom (R := P) (A := P) (K := FractionRing P) (L := L)
      (g := Algebra.ofId P L) hφ
  refine ⟨inferInstance, ?_⟩
  apply (isIntegrallyClosed_iff (FractionRing P)).2
  intro x hx
  obtain ⟨a, b, hxrep⟩ := IsLocalization.exists_mk'_eq P⁰ x
  have hψ : IsIntegral P (ψ x) := by
    exact IsIntegral.map (R := P) (A := P) ψ hx
  have hw : IsAlmostIntegral P (ψ x) :=
    hψ.isAlmostIntegral_of_exists_smul_mem_range ⟨b, b.2, by
      refine ⟨a, ?_⟩
      calc
        algebraMap P L a = ψ (algebraMap P (FractionRing P) a) := (ψ.commutes a).symm
        _ = ψ ((b : P) • IsLocalization.mk' (FractionRing P) a b) := by
          rw [IsLocalization.smul_mk'_self]
        _ = (b : P) • ψ x := by rw [map_smul, hxrep]⟩
  have hcoeff : ∀ n : ℕ, ∃ r : R, algebraMap R K r = (ψ x).coeff n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : (ψ x).coeff n = 0
      · exact ⟨0, by simp [hn]
        ⟩
      · let g : P := PowerSeries.mk (fun i =>
          if hi : i < n then Classical.choose (ih i hi) else 0)
        have hgcoeff : ∀ (i : ℕ) (hi : i < n),
            g.coeff i = Classical.choose (ih i hi) := by
          intro i hi
          simp [g, hi]
        let y : L := ψ x - algebraMap P L g
        have hmap_coeff : ∀ i : ℕ,
            (algebraMap P L g).coeff i = algebraMap R K (g.coeff i) := by
          intro i
          change ((PowerSeries.map (algebraMap R K) g : PowerSeries K) : L).coeff
            (i : ℤ) = _
          rw [PowerSeries.coeff_coe, if_neg (by omega), PowerSeries.coeff_map]
          congr 1
        have hy : IsAlmostIntegral P y := by
          exact (completeIntegralClosure P L).sub_mem hw
            ((completeIntegralClosure P L).algebraMap_mem g)
        have hycoeff : ∀ i < n, y.coeff i = 0 := by
          intro i hi
          rw [show y = ψ x - algebraMap P L g from rfl, HahnSeries.coeff_sub,
            hmap_coeff i]
          rw [hgcoeff i hi, Classical.choose_spec (ih i hi)]
          simp
        have hyn : y.coeff n = (ψ x).coeff n := by
          rw [show y = ψ x - algebraMap P L g from rfl, HahnSeries.coeff_sub,
            hmap_coeff n]
          simp [g]
        have hyn0 : y.coeff n ≠ 0 := by rwa [hyn]
        have hy0 : y ≠ 0 := by
          intro h
          exact hyn0 (by rw [h, HahnSeries.coeff_zero])
        have hynonneg : 0 ≤ y.order := (hlead y hy hy0).1
        have hyorder : y.order = n := by
          apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hyn0)
          apply (HahnSeries.le_order_iff_forall hy0).2
          intro i hi
          by_cases hi0 : i < 0
          · exact HahnSeries.coeff_eq_zero_of_lt_order
              (lt_of_lt_of_le hi0 hynonneg)
          · have hi' : i.natAbs < n := by omega
            have hi_eq : (i.natAbs : ℤ) = i := by omega
            rw [← hi_eq]
            exact hycoeff i.natAbs hi'
        have hyalmost : IsAlmostIntegral R (y.coeff n) := by
          simpa [hyorder] using (hlead y hy hy0).2
        have hyalmost' : IsAlmostIntegral R ((ψ x).coeff n) := by
          rw [← hyn]
          exact hyalmost
        exact (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed R›
          ((isAlmostIntegral_iff_isIntegral_of_noetherian).mp hyalmost')
  let f : P := PowerSeries.mk (fun n => Classical.choose (hcoeff n))
  have hfmap : algebraMap P L f = ψ x := by
    ext i
    change ((PowerSeries.map (algebraMap R K) f : PowerSeries K) : L).coeff i = (ψ x).coeff i
    rw [PowerSeries.coeff_coe]
    by_cases hi : i < 0
    · rw [if_pos hi]
      by_cases hx0 : ψ x = 0
      · simp [hx0]
      · exact (HahnSeries.coeff_eq_zero_of_lt_order
          (lt_of_lt_of_le hi (hlead (ψ x) hw hx0).1)).symm
    · rw [if_neg hi, PowerSeries.coeff_map]
      have hfcoeff : f.coeff i.natAbs = Classical.choose (hcoeff i.natAbs) := by
        simp [f]
      have hi_eq : (i.natAbs : ℤ) = i := by omega
      rw [hfcoeff, ← hi_eq]
      exact Classical.choose_spec (hcoeff i.natAbs)
  refine ⟨f, ?_⟩
  apply (RingHom.injective ψ.toRingHom)
  calc
    ψ (algebraMap P (FractionRing P) f) = algebraMap P L f := by
      change IsFractionRing.lift hφ (algebraMap P (FractionRing P) f) = φ f
      exact IsFractionRing.lift_algebraMap hφ f
    _ = ψ x := hfmap

/-- A power-series ring over a Noetherian normal domain is Noetherian and is a
normal domain. -/
theorem powerSeries_isNoetherian_isNormalDomain
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (hR : IsNormalDomain R) :
    IsNoetherianRing (PowerSeries R) ∧ IsNormalDomain (PowerSeries R) := by
  exact ⟨inferInstance,
    @powerSeries_isNormalDomain_of_isDomain_of_isIntegrallyClosed R _ hR.1 hR.2 _⟩

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
  tfae_have 1 → 2 := fun h p =>
    localization_isNormalDomain h p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors
  tfae_have 2 → 3 := fun h m =>
    h ⟨m.asIdeal, inferInstance⟩
  tfae_have 3 → 1 := fun h =>
    ⟨inferInstance,
      IsIntegrallyClosed.of_localization_maximal (fun p hp hpm =>
        (h ⟨p, hpm⟩).2)⟩
  tfae_finish

/-- A commutative ring is normal when all of its prime localizations are
normal domains. -/
def IsNormalRing (R : Type*) [CommRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsNormalDomain (Localization.AtPrime p.asIdeal)

/-- A normal ring is reduced. -/
theorem normalRing_isReduced
    {R : Type*} [CommRing R] (hR : IsNormalRing R) :
    IsReduced R := by
  apply isReduced_ofLocalizationMaximal
  intro m hm
  let : IsDomain (Localization.AtPrime m) := (hR ⟨m, hm.isPrime⟩).1
  infer_instance

/-- A normal ring is integrally closed in its total ring of fractions. -/
theorem normalRing_isIntegrallyClosedIn_totalQuotientRing
    {R : Type*} [CommRing R] (hR : IsNormalRing R) :
    IsIntegrallyClosedIn R
      (Formalization.Books.Algebra.Unit09.totalQuotientRing R) := by
  refine isIntegrallyClosedIn_iff.mpr ?_
  refine ⟨IsFractionRing.injective R _, ?_⟩
  intro x hx
  let I : Ideal R :=
    { carrier := {r | ∃ a : R, algebraMap R (FractionRing R) a =
          algebraMap R (FractionRing R) r * x}
      zero_mem' := by
        refine ⟨0, ?_⟩
        simp
      add_mem' := by
        intro a b ha hb
        obtain ⟨a', ha'⟩ := ha
        obtain ⟨b', hb'⟩ := hb
        refine ⟨a' + b', ?_⟩
        calc
          algebraMap R (FractionRing R) (a' + b') =
              algebraMap R (FractionRing R) a' +
                algebraMap R (FractionRing R) b' := map_add _ _ _
          _ = algebraMap R (FractionRing R) a * x +
              algebraMap R (FractionRing R) b * x := by rw [ha', hb']
          _ = algebraMap R (FractionRing R) (a + b) * x := by
            rw [← add_mul, ← map_add]
      smul_mem' := by
        intro c r hr
        obtain ⟨a, ha⟩ := hr
        refine ⟨c * a, ?_⟩
        simp only [smul_eq_mul, map_mul]
        rw [ha]
        ring }
  obtain ⟨c, d, hxrep⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have hlocal : ∀ (P : Ideal R) (_ : P.IsMaximal),
      ∃ r : R, r ∉ P ∧ r ∈ I := by
    intro P hP
    let Rp := Localization.AtPrime P
    let : IsDomain Rp := (hR ⟨P, hP.isPrime⟩).1
    let Kp := FractionRing Rp
    let : Field Kp := IsFractionRing.toField Rp
    have hM : nonZeroDivisors R ≤
        (nonZeroDivisors Rp).comap (algebraMap R Rp) := by
      intro s hs
      change algebraMap R Rp s ∈ nonZeroDivisors Rp
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hzero'
      obtain ⟨t, ht⟩ :=
        (IsLocalization.map_eq_zero_iff P.primeCompl Rp s).mp hzero'
      have ht0 : (t : R) = 0 :=
        (mem_nonZeroDivisors_iff.mp hs).2 t ht
      apply t.property
      rw [ht0]
      exact P.zero_mem
    let f : FractionRing R →+* Kp :=
      IsLocalization.map Kp (M := nonZeroDivisors R) (T := nonZeroDivisors Rp)
        (algebraMap R Rp) hM
    have hfx : IsIntegral Rp (f x) := by
      exact IsIntegral.map_of_comp_eq (R := R) (S := FractionRing R)
        (T := Rp) (U := Kp) (algebraMap R Rp) f
        (by
          change (algebraMap Rp Kp).comp (algebraMap R Rp) =
            f.comp (algebraMap R (FractionRing R))
          exact (IsLocalization.map_comp (Q := Kp) (g := algebraMap R Rp) hM).symm)
        hx
    obtain ⟨y, hy⟩ :=
      (isIntegrallyClosed_iff Kp).mp (hR ⟨P, hP.isPrime⟩).2 hfx
    have hycrossK :
        algebraMap Rp Kp y *
            algebraMap Rp Kp (algebraMap R Rp (d : R)) =
          algebraMap Rp Kp (algebraMap R Rp c) := by
      calc
        algebraMap Rp Kp y *
              algebraMap Rp Kp (algebraMap R Rp (d : R)) =
            f x *
              algebraMap Rp Kp (algebraMap R Rp (d : R)) := by rw [hy]
        _ = algebraMap Rp Kp (algebraMap R Rp c) := by
          rw [← hxrep]
          rw [show f (IsLocalization.mk' (FractionRing R) c d) =
              IsLocalization.mk' Kp (algebraMap R Rp c)
                ⟨algebraMap R Rp (d : R), hM d.property⟩ from
            IsLocalization.map_mk' (Q := Kp) hM c d]
          exact IsLocalization.mk'_spec Kp (algebraMap R Rp c)
            ⟨algebraMap R Rp (d : R), hM d.property⟩
    have hycross : y * algebraMap R Rp (d : R) =
        algebraMap R Rp c := by
      apply IsFractionRing.injective Rp Kp
      simpa only [map_mul] using hycrossK
    obtain ⟨⟨a, s⟩, hys⟩ := IsLocalization.surj P.primeCompl y
    have hcross' : algebraMap R Rp (a * (d : R)) =
        algebraMap R Rp (c * (s : R)) := by
      calc
        algebraMap R Rp (a * (d : R)) =
            algebraMap R Rp a * algebraMap R Rp (d : R) := map_mul _ _ _
        _ = (y * algebraMap R Rp (s : R)) *
              algebraMap R Rp (d : R) := by rw [hys]
        _ = (y * algebraMap R Rp (d : R)) *
              algebraMap R Rp (s : R) := by ring
        _ = algebraMap R Rp c * algebraMap R Rp (s : R) := by rw [hycross]
        _ = algebraMap R Rp (c * (s : R)) := by rw [map_mul]
    obtain ⟨t, ht⟩ :=
      (IsLocalization.eq_iff_exists (S := Rp) P.primeCompl).mp hcross'
    have hts : (t : R) * (s : R) ∉ P := by
      intro h
      exact (P.primeCompl.mul_mem t.property s.property) h
    refine ⟨(t : R) * (s : R), hts, ⟨(t : R) * a, ?_⟩⟩
    rw [← hxrep]
    have ht' : (t : R) * a * (d : R) =
        (t : R) * (s : R) * c := by
      calc
        (t : R) * a * (d : R) = (t : R) * (a * (d : R)) := by ring
        _ = (t : R) * ((c * (s : R))) := by rw [ht]
        _ = (t : R) * (s : R) * c := by ring
    rw [← IsLocalization.mk'_one (M := nonZeroDivisors R) (S := FractionRing R)]
    conv_rhs =>
      rw [← IsLocalization.mk'_one (M := nonZeroDivisors R) (S := FractionRing R)]
    rw [← IsLocalization.mk'_mul (M := nonZeroDivisors R) (S := FractionRing R)]
    rw [IsLocalization.mk'_eq_iff_eq']
    simpa only [map_mul, one_mul, mul_one, map_one, Submonoid.coe_one] using
      congrArg (algebraMap R (FractionRing R)) ht'
  have hIone : (1 : R) ∈ I := by
    apply Ideal.mem_of_localization_maximal
    intro P hP
    obtain ⟨r, hrP, hrI⟩ := hlocal P hP
    have hur : IsUnit (algebraMap R (Localization.AtPrime P) r) :=
      (IsLocalization.algebraMap_isUnit_iff P.primeCompl).2
        ⟨r, hrP, dvd_rfl⟩
    have hmem := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime P)) hrI
    have htop : Ideal.map (algebraMap R (Localization.AtPrime P)) I = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ hmem hur
    exact htop ▸ Set.mem_univ _
  change ∃ a : R, algebraMap R (FractionRing R) a =
    algebraMap R (FractionRing R) 1 * x at hIone
  obtain ⟨a, ha⟩ := hIone
  exact ⟨a, by simpa using ha⟩

/-- A localization of a normal ring is a normal ring. -/
theorem localization_isNormalRing
    {R S : Type*} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (hR : IsNormalRing R) :
    IsNormalRing S := by
  intro q
  have hloc : IsLocalization ((q.asIdeal.comap (algebraMap R S)).primeCompl)
      (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := M) (S := S) (T := Localization.AtPrime q.asIdeal)
      (Hp := q.2) q.asIdeal
  have hprime :
      (q.asIdeal.comap (algebraMap R S)).IsPrime :=
    (IsLocalization.isPrime_iff_isPrime_disjoint M S q.asIdeal).mp q.2 |>.1
  let p : PrimeSpectrum R := ⟨q.asIdeal.comap (algebraMap R S), hprime⟩
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime q.asIdeal := by
    letI := hloc
    exact IsLocalization.algEquiv (q.asIdeal.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
      (Localization.AtPrime q.asIdeal)
  have hdomain : IsDomain (Localization.AtPrime q.asIdeal) :=
    (e.toRingEquiv.isDomain_iff).mp (hR p).1
  exact ⟨hdomain, (hR p).2.of_equiv e.toRingEquiv⟩

/-- A polynomial ring over a normal ring is a normal ring. -/
theorem polynomial_isNormalRing
    {R : Type*} [CommRing R] (hR : IsNormalRing R) :
    IsNormalRing (Polynomial R) := by
  intro q
  let p : Ideal R := q.asIdeal.comap (Polynomial.C : R →+* Polynomial R)
  let : q.asIdeal.IsPrime := q.2
  have hp : p.IsPrime := by
    simpa [p] using
      (Ideal.comap_isPrime (Polynomial.C : R →+* Polynomial R) q.asIdeal)
  let pc : Submonoid (Polynomial R) :=
    Submonoid.map Polynomial.C.toMonoidHom p.primeCompl
  let Rp := Localization.AtPrime p
  let A := Polynomial Rp
  have hlocA : IsLocalization pc A := by
    exact Polynomial.isLocalization p.primeCompl Rp
  have hdisj : Disjoint (pc : Set (Polynomial R)) (q.asIdeal : Set (Polynomial R)) := by
    simpa [pc, p] using!
      Set.disjoint_image_left.mpr
        (Set.disjoint_compl_left_iff_subset.mpr (fun _ a => a))
  let Q : Ideal A := q.asIdeal.map (algebraMap (Polynomial R) A)
  have hQ : Q.IsPrime := by
    let := hlocA
    exact IsLocalization.isPrime_of_isPrime_disjoint pc A q.asIdeal q.2 hdisj
  have hcomap : Q.under (Polynomial R) = q.asIdeal := by
    let := hlocA
    exact IsLocalization.under_map_of_isPrime_disjoint pc A q.2 hdisj
  have hnormalA : IsNormalDomain A :=
    polynomial_isNormalDomain (R := Rp) (hR ⟨p, hp⟩)
  have hnormalB : IsNormalDomain (Localization Q.primeCompl) := by
    let : IsDomain A := hnormalA.1
    let : IsIntegrallyClosed A := hnormalA.2
    exact localization_isNormalDomain hnormalA Q.primeCompl
      Q.primeCompl_le_nonZeroDivisors
  let B := Localization Q.primeCompl
  have hlocB : IsLocalization q.asIdeal.primeCompl B := by
    let : Q.IsPrime := hQ
    let := hlocA
    have hlocB' :
        IsLocalization (Q.under (Polynomial R)).primeCompl B := by
      simpa only [Ideal.under_def] using
        (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
          (M := pc) (S := A) (T := B) Q)
    simpa only [hcomap] using hlocB'
  let T := Localization q.asIdeal.primeCompl
  have e : T ≃ₐ[Polynomial R] B := by
    let := hlocB
    exact IsLocalization.algEquiv q.asIdeal.primeCompl T B
  have hdomainT : IsDomain T :=
    (e.toRingEquiv.isDomain_iff).mpr hnormalB.1
  have hclosedT : IsIntegrallyClosed T :=
    hnormalB.2.of_equiv e.symm.toRingEquiv
  exact ⟨hdomainT, hclosedT⟩

/-- A finite product of normal rings is a normal ring. -/
theorem finite_product_isNormalRing
    {ι : Type u} [Fintype ι] {R : ι → Type v}
    [∀ i, CommRing (R i)] (hR : ∀ i, IsNormalRing (R i)) :
    IsNormalRing (∀ i, R i) := by
  classical
  intro p
  let I : ∀ i, Ideal (R i) := fun i =>
    p.asIdeal.map (Pi.evalRingHom R i)
  have hp : p.asIdeal = Ideal.pi I := by
    exact (Ideal.piOrderIso.symm_apply_apply p.asIdeal).symm
  have hex : ∃ i, I i ≠ ⊤ := by
    by_contra h
    have htop : ∀ i, I i = ⊤ := fun i => by
      exact Classical.not_not.mp (fun hi => h ⟨i, hi⟩)
    apply p.2.ne_top
    rw [hp]
    ext x
    simp [Ideal.mem_pi, htop]
  obtain ⟨i, hi⟩ := hex
  have hi1 : (1 : R i) ∉ I i := (Ideal.ne_top_iff_one _).mp hi
  have hother : ∀ j, i ≠ j → I j = ⊤ := by
    intro j hij
    apply (Ideal.eq_top_iff_one _).2
    by_contra hj
    have hxi : Pi.single i (1 : R i) ∉ p.asIdeal := by
      intro hmem
      apply hi1
      simpa using (Ideal.mem_pi I (Pi.single i (1 : R i))).mp (hp ▸ hmem) i
    have hxj : Pi.single j (1 : R j) ∉ p.asIdeal := by
      intro hmem
      apply hj
      simpa using (Ideal.mem_pi I (Pi.single j (1 : R j))).mp (hp ▸ hmem) j
    have hprod :
        Pi.single i (1 : R i) * Pi.single j (1 : R j) = 0 := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [hij]
      · by_cases hkj : k = j
        · subst k
          simp [hij]
        · simp [hki, hkj]
    have hmem :
        Pi.single i (1 : R i) * Pi.single j (1 : R j) ∈ p.asIdeal := by
      rw [hprod]
      exact p.asIdeal.zero_mem
    rcases p.2.mem_or_mem hmem with hmem | hmem
    · exact (hxi hmem).elim
    · exact (hxj hmem).elim
  have hker : RingHom.ker (Pi.evalRingHom R i) ≤ p.asIdeal := by
    intro x hx
    rw [hp, Ideal.mem_pi]
    intro j
    by_cases hji : j = i
    · subst j
      change x i = 0 at hx
      rw [hx]
      exact (I i).zero_mem
    · rw [hother j (Ne.symm hji)]
      trivial
  have hIprime : (I i).IsPrime := by
    change (p.asIdeal.map (Pi.evalRingHom R i)).IsPrime
    exact Ideal.map_isPrime_of_surjective (Function.surjective_eval _)
      hker
  have hpcomap : p.asIdeal = (I i).comap (Pi.evalRingHom R i) := by
    apply le_antisymm
    · exact Ideal.le_comap_map
    · intro x hx
      rw [hp, Ideal.mem_pi]
      intro j
      by_cases hji : j = i
      · subst j
        exact hx
      · rw [hother j (Ne.symm hji)]
        trivial
  let q : PrimeSpectrum (R i) := ⟨I i, hIprime⟩
  let e0 :
      Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom R i)) ≃+*
        Localization.AtPrime q.asIdeal := by
    exact RingEquiv.ofBijective
      (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
      (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
  let e : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal := by
    have hpc : p.asIdeal.primeCompl =
        (q.asIdeal.comap (Pi.evalRingHom R i)).primeCompl := by
      ext x
      change x ∉ p.asIdeal ↔ x ∉ (q.asIdeal.comap (Pi.evalRingHom R i))
      rw [hpcomap]
    change Localization p.asIdeal.primeCompl ≃+*
      Localization q.asIdeal.primeCompl
    rw [hpc]
    exact e0
  exact ⟨(e.isDomain_iff).mpr (hR i q).1,
    (hR i q).2.of_equiv e.symm⟩

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
  classical
  have hid : ∀ {x : Formalization.Books.Algebra.Unit09.totalQuotientRing R},
      IsIdempotentElem x → IsIntegral R x := by
    intro x hx
    refine ⟨Polynomial.X * (Polynomial.X - 1), ?_, ?_⟩
    · exact Polynomial.monic_X.mul (Polynomial.monic_X_sub_C _)
    · simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub,
        Polynomial.eval₂_X, Polynomial.eval₂_one]
      calc
        x * (x - 1) = x * x - x := by ring
        _ = 0 := by rw [hx.eq, sub_self]
  tfae_have 1 → 2 := fun h =>
    normalRing_isIntegrallyClosedIn_totalQuotientRing h
  tfae_have 2 → 3 := by
    intro h
    let P := Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R
    let : Fintype {p : Ideal R // p ∈ minimalPrimes R} := hfinite.fintype
    let _ : Finite P := Finite.of_injective
      (fun p : P => (⟨p.1.asIdeal, p.2⟩ : {p : Ideal R // p ∈ minimalPrimes R}))
      (by
        intro p q hpq
        apply Subtype.ext
        apply PrimeSpectrum.ext
        exact congrArg Subtype.val hpq)
    let : Fintype P := Fintype.ofFinite P
    let n := Fintype.card P
    let e : Fin n ≃ P := (Fintype.equivFin P).symm
    let q : Fin n → PrimeSpectrum R := fun i => (e i).1
    have hq : Set.range (fun i : Fin n => (q i).asIdeal) =
        minimalPrimes R := by
      ext I
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).2
      · intro hI
        let p : P := ⟨⟨I, hI.isPrime⟩, hI⟩
        refine ⟨e.symm p, ?_⟩
        simp [q, p]
    have hqi : Function.Injective q := by
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact hij
    have hz : (⋃ i : Fin n, ((q i).asIdeal : Set R)) =
        Formalization.Books.Algebra.Unit25.zeroDivisors := by
      apply Set.ext
      intro x
      constructor
      · intro hx
        rw [← Formalization.Books.Algebra.Unit25.iUnion_minimalPrimeSpectrum_eq_zeroDivisors]
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        apply Set.mem_iUnion.mpr
        refine ⟨e i, ?_⟩
        simpa [q] using hi
      · intro hx
        rw [← Formalization.Books.Algebra.Unit25.iUnion_minimalPrimeSpectrum_eq_zeroDivisors]
          at hx
        rcases Set.mem_iUnion.mp hx with ⟨p, hp⟩
        obtain ⟨i, rfl⟩ := e.surjective p
        exact Set.mem_iUnion.mpr ⟨i, hp⟩
    obtain ⟨E⟩ :=
      Formalization.Books.Algebra.Unit25.totalQuotientRing_equiv_pi_minimalPrime_localizations
        n q hq hqi hz
    let g : ∀ i : Fin n, R →+* Localization.AtPrime (q i).asIdeal :=
      fun i => (Pi.evalRingHom (fun j : Fin n =>
        Localization.AtPrime (q j).asIdeal) i).comp
          (E.toRingHom.comp (algebraMap R
            (Formalization.Books.Algebra.Unit09.totalQuotientRing R)))
    have hfrac (i : Fin n) :
        IsFractionRing (g i).range (Localization.AtPrime (q i).asIdeal) := by
      let hmin : (q i).asIdeal ∈ minimalPrimes R := by
        rw [← hq]
        exact Set.mem_range_self i
      let hfield : IsField (Localization.AtPrime (q i).asIdeal) :=
        Formalization.Books.Algebra.Unit25.isField_localizationAt_minimalPrime_of_isReduced
          ⟨q i, hmin⟩
      let : IsField (Localization.AtPrime (q i).asIdeal) := hfield
      let : Field (Localization.AtPrime (q i).asIdeal) := hfield.toField
      let : Nontrivial (g i).range := by
        refine ⟨⟨1, 0, ?_⟩⟩
        intro hzero
        have hzero' : (1 : Localization.AtPrime (q i).asIdeal) = 0 :=
          congrArg (fun x : (g i).range =>
            (x : Localization.AtPrime (q i).asIdeal)) hzero
        exact one_ne_zero hzero'
      change IsLocalization (nonZeroDivisors (g i).range)
        (Localization.AtPrime (q i).asIdeal)
      rw [isLocalization_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro s
        have hsne : algebraMap (g i).range
            (Localization.AtPrime (q i).asIdeal) s ≠ 0 := by
          intro hs
          apply nonZeroDivisors.ne_zero s.2
          apply Subtype.ext
          exact hs
        exact IsUnit.mk0 _ hsne
      · intro z
        let z' : ∀ j : Fin n, Localization.AtPrime (q j).asIdeal :=
          Pi.single i z
        let y := E.symm z'
        obtain ⟨⟨r, s⟩, hys⟩ :=
          IsLocalization.surj (M := nonZeroDivisors R)
            (S := Formalization.Books.Algebra.Unit09.totalQuotientRing R) y
        let ar : (g i).range := ⟨g i r, ⟨r, rfl⟩⟩
        let as : (g i).range := ⟨g i s, ⟨s, rfl⟩⟩
        have hsunit : IsUnit (g i s) := by
          have hu : IsUnit ((E (algebraMap R
              (Formalization.Books.Algebra.Unit09.totalQuotientRing R) s) :
                ∀ j : Fin n, Localization.AtPrime (q j).asIdeal) i) :=
            IsUnit.map (Pi.evalRingHom (fun j : Fin n =>
              Localization.AtPrime (q j).asIdeal) i)
              (IsUnit.map E.toRingHom
                (IsLocalization.map_units
                  (Formalization.Books.Algebra.Unit09.totalQuotientRing R) s))
          simpa [g] using hu
        let ds : nonZeroDivisors (g i).range :=
          ⟨as, mem_nonZeroDivisors_of_ne_zero (by
            intro has
            apply hsunit.ne_zero
            exact congrArg Subtype.val has)⟩
        refine ⟨(ar, ds), ?_⟩
        have hys' := congrArg E hys
        have hi := congrArg
          (fun w : ∀ j : Fin n, Localization.AtPrime (q j).asIdeal => w i) hys'
        have hy : E y i = z := by
          simp [y, z', E.apply_symm_apply]
        have hds : algebraMap (g i).range
            (Localization.AtPrime (q i).asIdeal) (ds : (g i).range) = g i (s : R) := by
          rfl
        have har : algebraMap (g i).range
            (Localization.AtPrime (q i).asIdeal) (ar : (g i).range) = g i r := by
          rfl
        rw [hds, har]
        simpa [g, map_mul, hy] using hi
      · intro x y hxy
        refine ⟨1, ?_⟩
        apply congrArg (fun z : (g i).range => (1 : (g i).range) * z)
        apply Subtype.ext
        exact hxy
    let eQ : Fin n → Formalization.Books.Algebra.Unit09.totalQuotientRing R :=
      fun i => E.symm (Pi.single i 1)
    have heQ : CompleteOrthogonalIdempotents eQ := by
      have he' := (CompleteOrthogonalIdempotents.single
        (fun i : Fin n => Localization.AtPrime (q i).asIdeal)).map E.symm.toRingHom
      simpa [eQ, Function.comp_def] using he'
    have herange : ∀ i, eQ i ∈ (algebraMap R
        (Formalization.Books.Algebra.Unit09.totalQuotientRing R)).range := by
      intro i
      rcases h.isIntegral_iff.mp (hid (heQ.idem i)) with ⟨r, hr⟩
      exact ⟨r, hr⟩
    have hker : ∀ x, x ∈ RingHom.ker
        (algebraMap R (Formalization.Books.Algebra.Unit09.totalQuotientRing R)) →
        IsNilpotent x := by
      intro x hx
      have hx0 : algebraMap R
          (Formalization.Books.Algebra.Unit09.totalQuotientRing R) x = 0 :=
        RingHom.mem_ker.mp hx
      have hinj : Function.Injective (algebraMap R
          (Formalization.Books.Algebra.Unit09.totalQuotientRing R)) :=
        IsLocalization.injective _ le_rfl
      have : x = 0 := hinj (by simpa using hx0)
      subst x
      exact IsNilpotent.zero
    obtain ⟨eR, heR, hemap⟩ :=
      CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
        (f := algebraMap R (Formalization.Books.Algebra.Unit09.totalQuotientRing R))
        hker heQ herange
    have heval (i : Fin n) : g i (eR i) = 1 := by
      change (E (algebraMap R
        (Formalization.Books.Algebra.Unit09.totalQuotientRing R) (eR i))) i = 1
      have hmap := congr_fun hemap i
      change algebraMap R
          (Formalization.Books.Algebra.Unit09.totalQuotientRing R) (eR i) =
        eQ i at hmap
      rw [hmap]
      simp [eQ]
    have hcross (i j : Fin n) (hij : i ≠ j) : g j (eR i) = 0 := by
      have hm := congrArg (g j) (heR.1.ortho hij)
      rw [map_mul, heval j, mul_one] at hm
      simpa using hm
    let G : R →+* (∀ i : Fin n, (g i).range) :=
      RingHom.pi fun i => (g i).rangeRestrict
    have hGsurj : Function.Surjective G := by
      intro a
      choose r hr using fun i => (a i).property
      refine ⟨∑ i, eR i * r i, ?_⟩
      funext j
      dsimp [G]
      apply Subtype.ext
      change g j (∑ i, eR i * r i) = (a j : Localization.AtPrime (q j).asIdeal)
      simp only [map_sum, map_mul]
      rw [Finset.sum_eq_single j]
      · rw [heval j, one_mul, hr j]
      · intro i hi hij
        simp [hcross i j hij]
      · simp
    have hGinj : Function.Injective G := by
      intro x y hxy
      have hinj : Function.Injective (algebraMap R
          (Formalization.Books.Algebra.Unit09.totalQuotientRing R)) :=
        IsLocalization.injective _ le_rfl
      apply hinj
      apply E.injective
      funext i
      change g i x = g i y
      exact congrArg Subtype.val (congr_fun hxy i)
    let EG : R ≃+* (∀ i : Fin n, (g i).range) := RingEquiv.ofBijective G
      ⟨hGinj, hGsurj⟩
    let : ∀ i : Fin n, SMul R (Localization.AtPrime (q i).asIdeal) :=
      fun i => (g i).toAlgebra.toSMul
    let : ∀ i : Fin n, Algebra R (Localization.AtPrime (q i).asIdeal) :=
      fun i => (g i).toAlgebra
    let : SMul R (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) :=
      Pi.instSMul
    let : Algebra R (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) :=
      Pi.algebra (ι := Fin n)
        (A := fun i : Fin n => Localization.AtPrime (q i).asIdeal)
    let : Algebra R (∀ i : Fin n, (g i).range) := G.toAlgebra
    let : ∀ i : Fin n, SMul (g i).range
        (Localization.AtPrime (q i).asIdeal) :=
      fun i => (g i).range.subtype.toAlgebra.toSMul
    let : ∀ i : Fin n, Algebra (g i).range
        (Localization.AtPrime (q i).asIdeal) :=
      fun i => (g i).range.subtype.toAlgebra
    let : SMul (∀ i : Fin n, (g i).range)
        (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) := Pi.smul'
    let : Algebra (∀ i : Fin n, (g i).range)
        (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) :=
      Pi.instAlgebraForall
        (fun i : Fin n => Localization.AtPrime (q i).asIdeal)
        (fun i : Fin n => (g i).range)
    have hEalg : ∀ r, E (algebraMap R
        (Formalization.Books.Algebra.Unit09.totalQuotientRing R) r) =
        algebraMap R (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) r := by
      intro r
      funext i
      dsimp [g]
      change (E (algebraMap R
        (Formalization.Books.Algebra.Unit09.totalQuotientRing R) r)) i =
        (E (algebraMap R
          (Formalization.Books.Algebra.Unit09.totalQuotientRing R) r)) i
      rfl
    let Ealg : Formalization.Books.Algebra.Unit09.totalQuotientRing R ≃ₐ[R]
        (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) :=
      { E with commutes' := hEalg }
    let : IsScalarTower R (∀ i : Fin n, (g i).range)
        (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) :=
      ⟨by
        intro r s x
        change (G r * s) • x = r • (s • x)
        funext i
        simp only [Pi.smul_apply', Pi.smul_apply, Algebra.smul_def, Pi.mul_apply]
        rw [map_mul]
        have hGr : algebraMap (g i).range
            (Localization.AtPrime (q i).asIdeal) (G r i) = g i r := by
          rfl
        have hsA :
            (algebraMap (∀ i : Fin n, (g i).range)
              (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) s) i =
              algebraMap (g i).range
                (Localization.AtPrime (q i).asIdeal) (s i) := by
          rfl
        rw [hGr, hsA]
        have hgr : algebraMap R (Localization.AtPrime (q i).asIdeal) r = g i r := by
          rfl
        rw [hgr]
        exact mul_assoc _ _ _
      ⟩
    let : Algebra.IsIntegral R (∀ i : Fin n, (g i).range) :=
      Algebra.isIntegral_of_surjective (by
        change Function.Surjective G
        exact hGsurj)
    have hclosed : IsIntegrallyClosedIn (∀ i : Fin n, (g i).range)
        (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        funext i
        exact Subtype.ext (congrFun hxy i)
      · intro x
        constructor
        · intro hx
          have hxR : IsIntegral R x := isIntegral_trans x hx
          have hxQ : IsIntegral R (Ealg.symm x) :=
            (isIntegral_algEquiv Ealg.symm).mpr hxR
          rcases h.isIntegral_iff.mp hxQ with ⟨r, hr⟩
          refine ⟨G r, ?_⟩
          have hGA : algebraMap (∀ i : Fin n, (g i).range)
              (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) (G r) =
              algebraMap R (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) r := by
            change algebraMap (∀ i : Fin n, (g i).range)
              (∀ i : Fin n, Localization.AtPrime (q i).asIdeal)
                (algebraMap R (∀ i : Fin n, (g i).range) r) = _
            exact IsScalarTower.algebraMap_apply R (∀ i : Fin n, (g i).range)
              (∀ i : Fin n, Localization.AtPrime (q i).asIdeal) r
          rw [hGA]
          apply Ealg.symm.injective
          change Ealg.symm (Ealg
            (algebraMap R (Formalization.Books.Algebra.Unit09.totalQuotientRing R) r)) =
            Ealg.symm x
          rw [Ealg.symm_apply_apply]
          exact hr
        · rintro ⟨y, rfl⟩
          exact isIntegral_algebraMap
    have hS : ∀ i, IsNormalDomain (g i).range := by
      intro i
      let hfield : IsField (Localization.AtPrime (q i).asIdeal) :=
        Formalization.Books.Algebra.Unit25.isField_localizationAt_minimalPrime_of_isReduced
          ⟨q i, by rw [← hq]; exact Set.mem_range_self i⟩
      let : IsField (Localization.AtPrime (q i).asIdeal) := hfield
      let : Field (Localization.AtPrime (q i).asIdeal) := hfield.toField
      let : IsFractionRing (g i).range (Localization.AtPrime (q i).asIdeal) := hfrac i
      have hclosed_i :=
        (Formalization.Books.Algebra.Unit36.product_isIntegrallyClosedIn_iff.mp hclosed) i
      exact ⟨inferInstance,
        (isIntegrallyClosed_iff
          (R := (g i).range)
          (K := Localization.AtPrime (q i).asIdeal)).2 (by
            intro x hx
            exact hclosed_i.isIntegral_iff.mp hx)⟩
    let u : Fin n ≃ ULift.{u} (Fin n) := Equiv.ulift.symm
    let EU : (∀ i : Fin n, (g i).range) ≃+*
        (∀ i : ULift.{u} (Fin n), (g i.down).range) :=
      RingEquiv.piCongrLeft (fun i : ULift.{u} (Fin n) => (g i.down).range) u
    exact ⟨ULift.{u} (Fin n), inferInstance,
      fun i => CommRingCat.of (g i.down).range,
      (fun i => hS i.down), ⟨EG.trans EU⟩⟩
  tfae_have 3 → 1 := by
    intro h
    rcases h with ⟨ι, hι, S, hS, hE⟩
    let : Fintype ι := hι
    obtain ⟨E⟩ := hE
    have hfactor : ∀ i, IsNormalRing (S i : Type u) := by
      intro i p
      let : IsDomain (S i : Type u) := (hS i).1
      exact localization_isNormalDomain (hS i) p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors
    have hprod : IsNormalRing (∀ i, (S i : Type u)) :=
      finite_product_isNormalRing hfactor
    have htransport : ∀ {A B : Type u} [CommRing A] [CommRing B],
        (A ≃+* B) → IsNormalRing B → IsNormalRing A := by
      intro A B _ _ e hB p
      let q : PrimeSpectrum B := PrimeSpectrum.comapEquiv e p
      have hqcomap : q.comap e = p := by
        change (PrimeSpectrum.comapEquiv e).symm
            ((PrimeSpectrum.comapEquiv e) p) = p
        exact (PrimeSpectrum.comapEquiv e).symm_apply_apply p
      have hsub : p.asIdeal.primeCompl.map e = q.asIdeal.primeCompl := by
        have hmap := RingEquiv.map_primeCompl_comap_eq e q.asIdeal
        have hqideal : q.asIdeal.comap e = p.asIdeal := by
          change (q.comap e).asIdeal = p.asIdeal
          rw [hqcomap]
        simpa only [hqideal] using hmap
      let eloc : Localization.AtPrime p.asIdeal ≃+*
          Localization.AtPrime q.asIdeal :=
        IsLocalization.ringEquivOfRingEquiv
          (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal) e hsub
      exact ⟨(eloc.isDomain_iff).mpr (hB q).1,
        (hB q).2.of_equiv eloc.symm⟩
    exact htransport E hprod
  tfae_finish

/-! ## Directed colimits -/

/-- A directed colimit of normal rings is a normal ring. -/
theorem directLimit_isNormalRing
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {R : ι → Type v} [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (f · · ·)]
    (hR : ∀ i, IsNormalRing (R i)) :
    IsNormalRing (DirectLimit R f) := by
  intro q
  let oi : ∀ i, R i →+* DirectLimit R f := DirectLimit.Ring.of R (f · · ·)
  let p : ∀ i, Ideal (R i) := fun i => q.asIdeal.comap (oi i)
  have hp : ∀ i, (p i).IsPrime := by
    intro i
    simpa [p, oi] using (Ideal.comap_isPrime (oi i) q.asIdeal)
  let S : ι → Type v := fun i => Localization.AtPrime (p i)
  have hmap : ∀ i j (hij : i ≤ j),
      (p i).primeCompl ≤ (p j).primeCompl.comap (f i j hij) := by
    intro i j hij x hx
    change x ∉ p i at hx
    change f i j hij x ∉ p j
    intro hmem
    change oi j (f i j hij x) ∈ q.asIdeal at hmem
    apply hx
    change oi i x ∈ q.asIdeal
    change (DirectLimit.Ring.of R (fun i j h => f i j h) j)
        (f i j hij x) ∈ q.asIdeal at hmem
    rw [DirectLimit.Ring.of_f (G := R)
      (f := fun i j h => f i j h) hij x] at hmem
    simpa [oi] using hmem
  let g : ∀ i j, i ≤ j → S i →+* S j := fun i j hij =>
    IsLocalization.map (S := S i) (M := (p i).primeCompl)
      (Q := S j) (T := (p j).primeCompl) (f i j hij) (hmap i j hij)
  let : DirectedSystem S (g · · ·) := by
    constructor
    · intro i
      have hself : g i i le_rfl = RingHom.id (S i) := by
        apply IsLocalization.ringHom_ext (R := R i) (M := (p i).primeCompl)
        ext x
        dsimp [g]
        rw [IsLocalization.map_eq]
        rw [DirectedSystem.map_self' f x]
      simp [hself]
    · intro i j k hij hjk
      have hcomp : (g j i hjk).comp (g k j hij) = g k i (hij.trans hjk) := by
        apply IsLocalization.ringHom_ext (R := R k) (M := (p k).primeCompl)
        ext x
        dsimp [g]
        rw [IsLocalization.map_eq, IsLocalization.map_eq, IsLocalization.map_eq]
        rw [← DirectedSystem.map_map' f hij hjk x]
      intro x
      exact DFunLike.congr_fun hcomp x
  have hS : ∀ i, IsNormalDomain (S i) := by
    intro i
    exact hR i ⟨p i, hp i⟩
  let U := Ring.DirectLimit S (g · · ·)
  have hUdomain : IsDomain U := by
    let : ∀ i, IsDomain (S i) := fun i => (hS i).1
    let : Nontrivial U := by
      let i : ι := Classical.arbitrary ι
      refine ⟨⟨Ring.DirectLimit.of S (g · · ·) i 0,
        Ring.DirectLimit.of S (g · · ·) i 1, ?_⟩⟩
      intro h
      have hzero : Ring.DirectLimit.of S (g · · ·) i (0 - 1) = 0 := by
        rw [(Ring.DirectLimit.of S (g · · ·) i).map_sub, h]
        simp
      obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hzero
      have : IsDomain (S j) := (hS j).1
      simp at hj
    let : NoZeroDivisors U := by
      constructor
      intro x y hxy
      obtain ⟨i, a, ha⟩ := Ring.DirectLimit.exists_of (G := S)
        (f := fun i j h => g i j h) x
      obtain ⟨j, b, hb⟩ := Ring.DirectLimit.exists_of (G := S)
        (f := fun i j h => g i j h) y
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let a' := g i k hik a
      let b' := g j k hjk b
      have hax : Ring.DirectLimit.of S (g · · ·) k a' = x := by
        rw [show a' = g i k hik a by rfl, Ring.DirectLimit.of_f]
        exact ha
      have hby : Ring.DirectLimit.of S (g · · ·) k b' = y := by
        rw [show b' = g j k hjk b by rfl, Ring.DirectLimit.of_f]
        exact hb
      have hprod : Ring.DirectLimit.of S (g · · ·) k (a' * b') = 0 := by
        calc
          Ring.DirectLimit.of S (g · · ·) k (a' * b') =
              Ring.DirectLimit.of S (g · · ·) k a' *
                Ring.DirectLimit.of S (g · · ·) k b' := by
            rw [(Ring.DirectLimit.of S (g · · ·) k).map_mul]
          _ = x * y := by rw [hax, hby]
          _ = 0 := hxy
      obtain ⟨l, hkl, hab⟩ := Ring.DirectLimit.of.zero_exact hprod
      let : IsDomain (S l) := (hS l).1
      have hab' : g k l hkl a' * g k l hkl b' = 0 := by
        simpa only [map_mul] using hab
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hab' with ha' | hb'
      · left
        calc
          x = Ring.DirectLimit.of S (g · · ·) k a' := hax.symm
          _ = Ring.DirectLimit.of S (g · · ·) l (g k l hkl a') :=
            (Ring.DirectLimit.of_f (G := S) (f := fun i j h => g i j h)
              hkl a').symm
          _ = 0 := by rw [ha', map_zero]
      · right
        calc
          y = Ring.DirectLimit.of S (g · · ·) k b' := hby.symm
          _ = Ring.DirectLimit.of S (g · · ·) l (g k l hkl b') :=
            (Ring.DirectLimit.of_f (G := S) (f := fun i j h => g i j h)
              hkl b').symm
          _ = 0 := by rw [hb', map_zero]
    exact NoZeroDivisors.to_isDomain U
  have hstage : ∀ {P : Polynomial U}, P.Monic →
      ∃ i, ∃ Q : Polynomial (S i), Q.Monic ∧
        Polynomial.map (Ring.DirectLimit.of S (g · · ·) i) Q = P := by
    intro P hP
    obtain ⟨i, P_i, hP_i⟩ := Ring.DirectLimit.Polynomial.exists_of (G := S)
      (f' := fun i j h => g i j h) P
    let : DecidableEq (S i) := Classical.decEq _
    let d := P.natDegree
    let N := d + 1
    let v : Fin N → S i := fun k => P_i.coeff (k : ℕ)
    let Q : Polynomial (S i) :=
      Polynomial.ofFn N v +
        Polynomial.C (1 - P_i.coeff d) * Polynomial.X ^ d
    have hdeg : Q.degree ≤ d := by
      apply Polynomial.degree_add_le_of_degree_le
      · have hN : 1 ≤ N := by simp [N]
        have hv : (Polynomial.ofFn N v).natDegree < N :=
          Polynomial.ofFn_natDegree_lt hN v
        exact Polynomial.degree_le_of_natDegree_le
          (Nat.le_of_lt_succ (by simpa [N] using hv))
      · simpa [Q] using
          (Polynomial.degree_C_mul_X_pow_le d (1 - P_i.coeff d))
    have hcoeff : Q.coeff d = 1 := by
      dsimp [Q]
      rw [Polynomial.coeff_add]
      rw [Polynomial.ofFn_coeff_eq_val_of_lt v (by simp [N])]
      rw [Polynomial.coeff_C_mul_X_pow]
      simp
      ring
    refine ⟨i, Q, Polynomial.monic_of_degree_le d hdeg hcoeff, ?_⟩
    have hcoeff_map : ∀ n, (Ring.DirectLimit.of S (g · · ·) i) (P_i.coeff n) =
        P.coeff n := by
      intro n
      simpa only [Polynomial.coeff_map] using
        congrArg (fun z => z.coeff n) hP_i
    let : DecidableEq U := Classical.decEq _
    have hmap_ofFn :
        Polynomial.map (Ring.DirectLimit.of S (g · · ·) i)
            (Polynomial.ofFn N v) =
          Polynomial.ofFn N (fun k => (Ring.DirectLimit.of S (g · · ·) i)
            (v k)) := by
      ext n
      by_cases hn : n < N
      · rw [Polynomial.coeff_map,
          Polynomial.ofFn_coeff_eq_val_of_lt v hn,
          Polynomial.ofFn_coeff_eq_val_of_lt _ hn]
      · have hn' : N ≤ n := Nat.le_of_not_gt hn
        rw [Polynomial.coeff_map,
          Polynomial.ofFn_coeff_eq_zero_of_ge v hn',
          Polynomial.ofFn_coeff_eq_zero_of_ge _ hn']
        exact RingHom.map_zero (Ring.DirectLimit.of S (g · · ·) i)
    have hmap_corr :
        Polynomial.map (Ring.DirectLimit.of S (g · · ·) i)
            (Polynomial.C (1 - P_i.coeff d) * Polynomial.X ^ d) =
          Polynomial.C (1 - P.coeff d) * Polynomial.X ^ d := by
      simp [hcoeff_map d]
    dsimp [Q]
    rw [Polynomial.map_add, hmap_ofFn, hmap_corr]
    ext n
    by_cases hn : n < N
    · have hn' : n ≤ d := by simpa [N] using hn
      by_cases hnd : n = d
      · rw [Polynomial.coeff_add,
          Polynomial.ofFn_coeff_eq_val_of_lt _ hn,
          Polynomial.coeff_C_mul_X_pow]
        simp [hnd, v, hcoeff_map]
        exact hP.coeff_natDegree.symm
      · rw [Polynomial.coeff_add,
          Polynomial.ofFn_coeff_eq_val_of_lt _ hn,
          Polynomial.coeff_C_mul_X_pow]
        simp [hnd, v, hcoeff_map]
    · have hn' : d < n := by simpa [N] using hn
      have hn'' : N ≤ n := by simpa [N] using hn
      rw [Polynomial.coeff_add,
          Polynomial.ofFn_coeff_eq_zero_of_ge _ hn'',
          Polynomial.coeff_C_mul_X_pow]
      rw [if_neg (Nat.ne_of_gt hn')]
      simp only [zero_add]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt hn').symm
  have hUclosed : IsIntegrallyClosed U := by
    refine (isIntegrallyClosed_iff (R := U) (K := FractionRing U)).2 ?_
    intro x hx
    obtain ⟨a, b, hb, xab⟩ := IsFractionRing.div_surjective U x
    rcases hx with ⟨P, hP, hroot⟩
    have hroot' : Polynomial.eval₂ (algebraMap U (FractionRing U))
        (algebraMap U (FractionRing U) a / algebraMap U (FractionRing U) b) P = 0 := by
      rw [xab]
      exact hroot
    have hscaled : Polynomial.eval₂ (algebraMap U (FractionRing U))
        (algebraMap U (FractionRing U) a) (P.scaleRoots b) = 0 :=
      Polynomial.scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero
        (IsFractionRing.injective U (FractionRing U)) hroot' hb
    obtain ⟨i, P_i, hP_i, hPmap⟩ := hstage hP
    obtain ⟨j, a_j, ha_j⟩ := Ring.DirectLimit.exists_of (G := S)
      (f := fun i j h => g i j h) a
    obtain ⟨k, b_k, hb_k⟩ := Ring.DirectLimit.exists_of (G := S)
      (f := fun i j h => g i j h) b
    obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
    obtain ⟨n, hmn, hkn⟩ := exists_ge_ge m k
    let P_m := Polynomial.map (g i n (him.trans hmn)) P_i
    let a_m := g j n (hjm.trans hmn) a_j
    let b_m := g k n hkn b_k
    have hP_m : P_m.Monic := by
      exact hP_i.map _
    have hPmap_m : Polynomial.map (Ring.DirectLimit.of S (g · · ·) n) P_m = P := by
      calc
          Polynomial.map (Ring.DirectLimit.of S (g · · ·) n) P_m =
              Polynomial.map ((Ring.DirectLimit.of S (g · · ·) n).comp
                (g i n (him.trans hmn))) P_i := by
            change Polynomial.map (Ring.DirectLimit.of S (g · · ·) n)
                (Polynomial.map (g i n (him.trans hmn)) P_i) = _
            rw [Polynomial.map_map]
          _ = Polynomial.map (Ring.DirectLimit.of S (g · · ·) i) P_i := by
            congr 1
            ext z
            exact Ring.DirectLimit.of_f (G := S) (f := fun i j h => g i j h)
              (him.trans hmn) z
          _ = P := hPmap
    have ha_m : Ring.DirectLimit.of S (g · · ·) n a_m = a := by
      rw [show a_m = g j n (hjm.trans hmn) a_j by rfl, Ring.DirectLimit.of_f]
      exact ha_j
    have hb_m : Ring.DirectLimit.of S (g · · ·) n b_m = b := by
      rw [show b_m = g k n hkn b_k by rfl, Ring.DirectLimit.of_f]
      exact hb_k
    let Q_m := P_m.scaleRoots b_m
    have hQmap_m : Polynomial.map (Ring.DirectLimit.of S (g · · ·) n) Q_m =
        P.scaleRoots b := by
      change Polynomial.map (Ring.DirectLimit.of S (g · · ·) n)
          (P_m.scaleRoots b_m) = P.scaleRoots b
      rw [Polynomial.map_scaleRoots P_m b_m
        (Ring.DirectLimit.of S (g · · ·) n) (by simp [hP_m.leadingCoeff])]
      rw [hPmap_m, hb_m]
    have hroot_m : Ring.DirectLimit.of S (g · · ·) n
        (Polynomial.eval₂ (RingHom.id (S n)) a_m Q_m) = 0 := by
      apply (IsFractionRing.injective U (FractionRing U))
      rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂]
      have hs : (Polynomial.map (Ring.DirectLimit.of S (g · · ·) n) Q_m).eval₂
          (algebraMap U (FractionRing U)) (algebraMap U (FractionRing U) a) = 0 := by
        rw [hQmap_m]
        exact hscaled
      rw [Polynomial.eval₂_map] at hs
      simpa [ha_m] using hs
    obtain ⟨l, hml, hroot_l⟩ := Ring.DirectLimit.of.zero_exact hroot_m
    let P_l := Polynomial.map (g n l hml) P_m
    let a_l := g n l hml a_m
    let b_l := g n l hml b_m
    have hP_l : P_l.Monic := by
      exact hP_m.map _
    have hroot_l' : Polynomial.eval₂ (RingHom.id (S l)) a_l
        (P_l.scaleRoots b_l) = 0 := by
      change Polynomial.eval₂ (RingHom.id (S l)) (g n l hml a_m)
          ((Polynomial.map (g n l hml) P_m).scaleRoots (g n l hml b_m)) = 0
      have h : Polynomial.eval₂ ((g n l hml).comp (RingHom.id (S n)))
          (g n l hml a_m) Q_m = 0 := by
        rw [← Polynomial.hom_eval₂]
        exact hroot_l
      have hmapQ : Polynomial.map (g n l hml) Q_m =
          (Polynomial.map (g n l hml) P_m).scaleRoots (g n l hml b_m) := by
        change Polynomial.map (g n l hml) (P_m.scaleRoots b_m) = _
        rw [Polynomial.map_scaleRoots P_m b_m (g n l hml)
          (by simp [hP_m.leadingCoeff])]
      rw [← hmapQ, Polynomial.eval₂_map]
      simpa using h
    have hb_l : b_l ≠ 0 := by
      have hb_ne : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
      intro h
      apply hb_ne
      rw [← hb_m]
      change g n l hml b_m = 0 at h
      rw [← Ring.DirectLimit.of_f (G := S)
        (f := fun i j h => g i j h) hml b_m, h, map_zero]
    let : IsDomain (S l) := (hS l).1
    have hb_lF : algebraMap (S l) (FractionRing (S l)) b_l ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hb_l)
    have hscaled_lF : Polynomial.eval₂ (algebraMap (S l) (FractionRing (S l)))
        (algebraMap (S l) (FractionRing (S l)) a_l)
          (P_l.scaleRoots b_l) = 0 := by
      simpa [Polynomial.hom_eval₂] using
        congrArg (algebraMap (S l) (FractionRing (S l))) hroot_l'
    have hroot_lF : Polynomial.eval₂ (algebraMap (S l) (FractionRing (S l)))
        (algebraMap (S l) (FractionRing (S l)) a_l /
          algebraMap (S l) (FractionRing (S l)) b_l) P_l = 0 := by
      have hzero : (algebraMap (S l) (FractionRing (S l)) b_l) ^ P_l.natDegree *
          Polynomial.eval₂ (algebraMap (S l) (FractionRing (S l)))
            (algebraMap (S l) (FractionRing (S l)) a_l /
              algebraMap (S l) (FractionRing (S l)) b_l) P_l = 0 := by
        calc
          _ = Polynomial.eval₂ (algebraMap (S l) (FractionRing (S l)))
              (algebraMap (S l) (FractionRing (S l)) b_l *
                (algebraMap (S l) (FractionRing (S l)) a_l /
                  algebraMap (S l) (FractionRing (S l)) b_l))
                (P_l.scaleRoots b_l) := by
            rw [Polynomial.scaleRoots_eval₂_mul]
          _ = Polynomial.eval₂ (algebraMap (S l) (FractionRing (S l)))
              (algebraMap (S l) (FractionRing (S l)) a_l) (P_l.scaleRoots b_l) := by
            rw [mul_div_cancel₀ _ hb_lF]
          _ = 0 := hscaled_lF
      exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hb_lF)
    obtain ⟨c, hc⟩ := (hS l).2.algebraMap_eq_of_integral
      ⟨P_l, hP_l, hroot_lF⟩
    have hc_stage : c * b_l = a_l := by
      apply IsFractionRing.injective (S l) (FractionRing (S l))
      rw [map_mul, hc, div_mul_cancel₀ _ hb_lF]
    have ha_l : Ring.DirectLimit.of S (g · · ·) l a_l = a := by
      rw [show a_l = g n l hml a_m by rfl, Ring.DirectLimit.of_f]
      exact ha_m
    have hb_l : Ring.DirectLimit.of S (g · · ·) l b_l = b := by
      rw [show b_l = g n l hml b_m by rfl, Ring.DirectLimit.of_f]
      exact hb_m
    have hcross : Ring.DirectLimit.of S (g · · ·) l c * b = a := by
      calc
        Ring.DirectLimit.of S (g · · ·) l c * b =
            Ring.DirectLimit.of S (g · · ·) l c *
              Ring.DirectLimit.of S (g · · ·) l b_l := by rw [hb_l]
        _ = Ring.DirectLimit.of S (g · · ·) l (c * b_l) := by rw [map_mul]
        _ = Ring.DirectLimit.of S (g · · ·) l a_l := by rw [hc_stage]
        _ = a := ha_l
    refine ⟨Ring.DirectLimit.of S (g · · ·) l c, ?_⟩
    rw [← xab]
    apply (eq_div_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)).2
    simpa only [map_mul] using congrArg (algebraMap U (FractionRing U)) hcross
  have hden : ∀ i, (p i).primeCompl ≤ q.asIdeal.primeCompl.comap (oi i) := by
    intro i x hx
    change oi i x ∉ q.asIdeal
    simpa [p] using hx
  let Q := Localization.AtPrime q.asIdeal
  let k : ∀ i, S i →+* Q := fun i =>
    IsLocalization.map (S := S i) (M := (p i).primeCompl)
      (Q := Q) (T := q.asIdeal.primeCompl) (oi i) (hden i)
  have hk : ∀ i j (hij : i ≤ j) (x : S i),
      k j (g i j hij x) = k i x := by
    intro i j hij x
    have hkj : (k j).comp (g i j hij) = k i := by
      apply IsLocalization.ringHom_ext (R := R i) (M := (p i).primeCompl)
      ext z
      dsimp [k, g]
      rw [IsLocalization.map_eq, IsLocalization.map_eq, IsLocalization.map_eq]
      rw [DirectLimit.Ring.of_f (G := R)
        (f := fun i j h => f i j h) hij z]
    exact DFunLike.congr_fun hkj x
  let u : U →+* Q :=
    Ring.DirectLimit.lift S (g · · ·) Q k hk
  have hu_stage : ∀ i (x : S i),
      u (Ring.DirectLimit.of S (g · · ·) i x) = k i x := by
    intro i x
    change Ring.DirectLimit.lift S (g · · ·) Q k hk
        (Ring.DirectLimit.of S (g · · ·) i x) = k i x
    exact
      (Ring.DirectLimit.lift_of Q k hk i x)
  let ri : ∀ i, R i →+* U := fun i =>
    (Ring.DirectLimit.of S (g · · ·) i).comp (algebraMap (R i) (S i))
  have hri : ∀ i j (hij : i ≤ j) (x : R i),
      ri j (f i j hij x) = ri i x := by
    intro i j hij x
    calc
      ri j (f i j hij x) =
          Ring.DirectLimit.of S (g · · ·) j
            (g i j hij (algebraMap (R i) (S i) x)) := by
        dsimp [ri]
        rw [IsLocalization.map_eq]
      _ = ri i x := by
        dsimp [ri]
        exact Ring.DirectLimit.of_f (G := S) (f := fun i j h => g i j h)
          hij (algebraMap (R i) (S i) x)
  let eR : DirectLimit R f ≃+* Ring.DirectLimit R (f · · ·) :=
    (Ring.DirectLimit.ringEquiv R f).symm
  let r' : Ring.DirectLimit R (f · · ·) →+* U :=
    Ring.DirectLimit.lift R (f · · ·) U ri hri
  let r : DirectLimit R f →+* U := r'.comp eR.toRingHom
  have hr_stage : ∀ i (x : R i),
      r (DirectLimit.Ring.of R (f · · ·) i x) = ri i x := by
    intro i x
    change r' (Ring.DirectLimit.of R (f · · ·) i x) = ri i x
    simp [r']
  have hunit : ∀ s : q.asIdeal.primeCompl,
      IsUnit (r (s : DirectLimit R f)) := by
    intro s
    obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk (f := f) (s : DirectLimit R f)
    have hxp : x ∉ p i := by
      intro hxp
      apply s.property
      rw [hx]
      change oi i x ∈ q.asIdeal
      exact hxp
    have hrs : r (s : DirectLimit R f) =
        Ring.DirectLimit.of S (g · · ·) i (algebraMap (R i) (S i) x) := by
      calc
        r (s : DirectLimit R f) =
            r (DirectLimit.Ring.of R (f · · ·) i x) := by rw [hx]; rfl
        _ = ri i x := hr_stage i x
        _ = Ring.DirectLimit.of S (g · · ·) i (algebraMap (R i) (S i) x) := by
          rfl
    rw [hrs]
    exact (IsLocalization.map_units (S := S i) (M := (p i).primeCompl)
      ⟨x, hxp⟩).map _
  let v : Q →+* U :=
    IsLocalization.lift (M := q.asIdeal.primeCompl) (S := Q) (g := r) hunit
  have hvr : v.comp (algebraMap (DirectLimit R f) Q) = r := by
    simp [v]
  have hur : u.comp r = algebraMap (DirectLimit R f) Q := by
    apply RingHom.ext
    intro z
    induction z using DirectLimit.induction with
    | _ i x =>
      calc
        u (r (DirectLimit.Ring.of R (f · · ·) i x)) =
            u (ri i x) := by rw [hr_stage]
      _ = k i (algebraMap (R i) (S i) x) := by
          change u (Ring.DirectLimit.of S (g · · ·) i
            (algebraMap (R i) (S i) x)) = _
          exact hu_stage i (algebraMap (R i) (S i) x)
        _ = algebraMap (DirectLimit R f) Q (oi i x) := by
          dsimp [k]
          rw [IsLocalization.map_eq]
        _ = algebraMap (DirectLimit R f) Q
            (DirectLimit.Ring.of R (f · · ·) i x) := by rfl
  have hvk : ∀ i, v.comp (k i) = Ring.DirectLimit.of S (g · · ·) i := by
    intro i
    apply IsLocalization.ringHom_ext (R := R i) (M := (p i).primeCompl)
    ext x
    calc
      v (k i (algebraMap (R i) (S i) x)) =
          v (algebraMap (DirectLimit R f) Q (oi i x)) := by
            dsimp [k]
            rw [IsLocalization.map_eq]
      _ = r (oi i x) := by
        rw [← hvr]
        rfl
      _ = ri i x := by
        rw [show oi i x = DirectLimit.Ring.of R (f · · ·) i x by rfl,
          hr_stage]
      _ = Ring.DirectLimit.of S (g · · ·) i (algebraMap (R i) (S i) x) := by
        rfl
  have huv : u.comp v = RingHom.id Q := by
    apply IsLocalization.ringHom_ext (R := DirectLimit R f)
      (M := q.asIdeal.primeCompl)
    rw [RingHom.comp_assoc, hvr, hur]
    simp
  have hvu : v.comp u = RingHom.id U := by
    apply Ring.DirectLimit.hom_ext
    intro i
    apply RingHom.ext
    intro x
    calc
      v (u (Ring.DirectLimit.of S (g · · ·) i x)) = v (k i x) := by
        rw [hu_stage]
      _ = Ring.DirectLimit.of S (g · · ·) i x :=
        DFunLike.congr_fun (hvk i) x
  let e : U ≃+* Q := RingEquiv.ofRingHom u v huv hvu
  exact ⟨(e.isDomain_iff).mp hUdomain,
    hUclosed.of_equiv e⟩
  

end

end Formalization.Books.Algebra.Unit37
