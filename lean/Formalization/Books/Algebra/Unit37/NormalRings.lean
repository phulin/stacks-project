import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit36.FiniteIntegralRingExtensions
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Polynomial.IsIntegral
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
  letI : Field (FractionRing R) := IsFractionRing.toField R
  let K := FractionRing R
  let P := PowerSeries R
  let L := LaurentSeries K
  let φ : P →+* L :=
    (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (algebraMap R K))
  letI : Algebra P L := φ.toAlgebra
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
        simpa [hz]
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
  letI : Field (FractionRing P) := IsFractionRing.toField P
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
