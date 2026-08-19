import Formalization.Books.Algebra.Unit59.NoetherianLocalRings
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Commutative Algebra, Chapter 60: Dimension

The source's Krull dimension and prime heights are represented by Mathlib's
canonical `ringKrullDim` and `Ideal.height`.  Likewise, a chain of prime
ideals is the canonical `LTSeries (PrimeSpectrum R)`.  The declarations below
add the source-facing interfaces that are not already part of those APIs.
-/

namespace Formalization.Books.Algebra.Unit60

open Formalization.Books.Algebra.Unit59
open Formalization.Books.Algebra.Unit58
open Set
open IsLocalRing

universe u v

noncomputable section

/-! ## Chains, dimension, and height -/

/- A chain of prime ideals is canonically an `LTSeries` in the prime spectrum.
   Its `length` is the source's number `n` of strict inclusions. -/
abbrev PrimeIdealChain (R : Type u) [CommRing R] := LTSeries (PrimeSpectrum R)

/- `ringKrullDim` is Mathlib's definition of the source's Krull dimension:
   the order-theoretic Krull dimension of `Spec R`. -/

/- `Ideal.height` is the canonical height of a prime ideal, and agrees with
   the order height of the corresponding point of the prime spectrum. -/

theorem ringKrullDim_eq_iSup_prime_height
    {R : Type u} [CommRing R] :
    ringKrullDim R =
      ⨆ p : PrimeSpectrum R, (p.asIdeal.height : WithBot ℕ∞) := by
  change Order.krullDim (PrimeSpectrum R) = _
  simpa only [PrimeSpectrum.height_eq_orderHeight] using
    (Order.krullDim_eq_iSup_height (α := PrimeSpectrum R))

theorem ringKrullDim_le_iff_prime_height_le
    {R : Type u} [CommRing R] (n : WithBot ℕ∞) :
    ringKrullDim R ≤ n ↔
      ∀ ⦃p : Ideal R⦄, p.IsPrime → p.height ≤ n :=
  ringKrullDim_le_iff_height_le n

theorem ringKrullDim_le_iff_maximal_height_le
    {R : Type u} [CommRing R] (n : WithBot ℕ∞) :
    ringKrullDim R ≤ n ↔
      ∀ ⦃m : Ideal R⦄, m.IsMaximal → m.height ≤ n :=
  ringKrullDim_le_iff_isMaximal_height_le n

theorem ringKrullDim_eq_iSup_maximal_height
    {R : Type u} [CommRing R] :
    ringKrullDim R =
      ⨆ m : MaximalSpectrum R, (m.asIdeal.height : WithBot ℕ∞) := by
  apply le_antisymm
  · rw [ringKrullDim_le_iff_maximal_height_le]
    intro m hm
    exact le_iSup (fun q : MaximalSpectrum R =>
      (q.asIdeal.height : WithBot ℕ∞)) ⟨m, hm⟩
  · refine iSup_le fun m => ?_
    exact (ringKrullDim_le_iff_prime_height_le (R := R) (ringKrullDim R)).mp
      le_rfl m.isMaximal.isPrime

/- The zero ring is handled separately by Mathlib: its empty spectrum has
   dimension `⊥`.  The source's dimension-zero equivalences therefore use the
   explicit nontriviality hypothesis below. -/
theorem noetherian_ringKrullDim_eq_zero_iff_artinian
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Nontrivial R] :
    ringKrullDim R = 0 ↔ IsArtinianRing R := by
  rw [← ringKrullDimZero_iff_ringKrullDim_eq_zero,
    isArtinianRing_iff_krullDimLE_zero]

theorem noetherian_ringKrullDimLE_zero_iff_artinian
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    Ring.KrullDimLE 0 R ↔ IsArtinianRing R :=
  (isArtinianRing_iff_krullDimLE_zero).symm

/-! ## The invariant `d` and zero-dimensional rings -/

private theorem numericalPolynomialDegree_eq_zero_of_eventually_eq
    (f : ℤ → ℤ) (c : ℤ)
    (hf : ∀ᶠ n : ℤ in Filter.atTop, f n = c)
    (hnum : IsNumericalPolynomial f) (hc : c ≠ 0) :
    numericalPolynomialDegree f = 0 := by
  unfold numericalPolynomialDegree
  let P := eventuallyRationalPolynomial f
  have hP : ∀ᶠ n : ℤ in Filter.atTop, P.eval (n : ℚ) = (c : ℚ) := by
    filter_upwards [eventuallyRationalPolynomial_spec f hnum, hf] with n hn hfn
    rw [hn, hfn]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hP
  have hinj : Function.Injective (fun k : ℕ => ((N + k : ℤ) : ℚ)) := by
    intro i j hij
    have hij' : (N + i : ℤ) = N + j := by
      change ((N + (i : ℤ) : ℤ) : ℚ) = ((N + (j : ℤ) : ℤ) : ℚ) at hij
      exact_mod_cast hij
    omega
  have hinf : Set.Infinite (Set.range (fun k : ℕ => ((N + k : ℤ) : ℚ))) :=
    Set.infinite_range_of_injective hinj
  have heq : P = Polynomial.C (c : ℚ) := by
    apply Polynomial.eq_of_infinite_eval_eq P (Polynomial.C (c : ℚ))
    refine hinf.mono ?_
    rintro x ⟨k, rfl⟩
    have hNk : N ≤ N + k := by omega
    simpa [P, Polynomial.eval_C] using hN (N + k) hNk
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  change P.degree = 0
  rw [heq]
  exact Polynomial.degree_C hcq

private theorem d_eq_zero_iff_isFiniteLength
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR₀ : Nontrivial R) :
    d R R = 0 ↔ IsFiniteLength R R := by
  classical
  by_cases hR : Nontrivial R
  · let : Nontrivial R := hR
    constructor
    · intro hd
      by_contra hfin
      have hnotArt : ¬ IsArtinianRing R := by
        intro hArt
        exact hfin
          ((Formalization.Books.Algebra.Unit53.artinian_iff_finite_length
            (R := R)).1 hArt)
      have hpows : ∀ n : ℕ,
          (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R R) ≠ ⊥ := by
        intro n hn
        apply hnotArt
        apply (isArtinianRing_iff_isNilpotent_maximalIdeal R).2
        refine ⟨n, ?_⟩
        rw [Ideal.zero_eq_bot]
        apply le_antisymm
        · intro y hy
          have hy' : y ∈ (IsLocalRing.maximalIdeal R) ^ n •
              (⊤ : Submodule R R) := by
            rw [smul_eq_mul, Ideal.mul_top]
            exact hy
          rw [hn] at hy'
          exact hy'
        · exact bot_le
      have hdegree := d_eq_hilbertPolynomial_degree_add_one R R hpows
      rw [hd] at hdegree
      have hne : (hilbertPolynomial R R).degree + 1 ≠ (0 : WithBot ℕ) := by
        intro hz
        cases hdeg : (hilbertPolynomial R R).degree with
        | bot => simp [hdeg] at hz
        | coe n =>
          rw [hdeg] at hz
          have hpos : (0 : WithBot ℕ) < (n : WithBot ℕ) + 1 := by
            change ((0 : ℕ) : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ)
            exact WithBot.coe_lt_coe.mpr (Nat.zero_lt_succ n)
          exact (ne_of_lt hpos) hz.symm
      exact hne hdegree.symm
    · intro hfin
      have hArt : IsArtinianRing R :=
        (Formalization.Books.Algebra.Unit53.artinian_iff_finite_length
          (R := R)).2 hfin
      obtain ⟨n, hn⟩ :=
        (isArtinianRing_iff_isNilpotent_maximalIdeal R).1 hArt
      have hcum (k : ℕ) (hk : n ≤ k) :
          cumulativeHilbertFunction R R k = moduleLengthNat (R := R) (M := R) := by
        have hpow : (IsLocalRing.maximalIdeal R) ^ (k + 1) = (⊥ : Ideal R) := by
          apply le_antisymm
          · rw [← Ideal.zero_eq_bot, ← hn]
            exact Ideal.pow_le_pow_right (Nat.le_succ_of_le hk)
          · exact bot_le
        have hsub :
            (IsLocalRing.maximalIdeal R) ^ (k + 1) •
                (⊤ : Submodule R R) = ⊥ := by
          rw [smul_eq_mul, Ideal.mul_top, hpow]
        change
          (Module.length R
              (R ⧸ ((IsLocalRing.maximalIdeal R) ^ (k + 1) •
                (⊤ : Submodule R R)))).toNat =
            (Module.length R R).toNat
        rw [hsub]
        exact congrArg ENat.toNat
          ((AlgEquiv.quotientBot R R).toLinearEquiv.length_eq)
      have hconst : ∀ᶠ z : ℤ in Filter.atTop,
          cumulativeHilbertFunctionInteger R R z =
            (moduleLengthNat (R := R) (M := R) : ℤ) := by
        filter_upwards [Filter.eventually_ge_atTop (n : ℤ)] with z hz
        have hz0 : 0 ≤ z := by omega
        have hzn : n ≤ z.toNat := by omega
        simp only [cumulativeHilbertFunctionInteger, natFunctionToInteger]
        rw [if_pos hz0]
        rw [hcum z.toNat hzn]
      have hcpos : 0 < moduleLengthNat (R := R) (M := R) := by
        unfold moduleLengthNat
        apply ENat.toNat_pos
        · exact ne_of_gt (Module.length_pos (R := R) (M := R))
        · exact Module.length_ne_top_iff.mpr hfin
      simpa [d, hR] using
        (numericalPolynomialDegree_eq_zero_of_eventually_eq
          (cumulativeHilbertFunctionInteger R R)
          (moduleLengthNat (R := R) (M := R) : ℤ) hconst
          (hilbert_functions_are_numerical R R).2 (by exact_mod_cast hcpos.ne'))
  · exact False.elim (hR hR₀)

theorem local_ringKrullDim_eq_zero_iff_d_eq_zero
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R = 0 ↔ d R R = 0 := by
  by_cases hR : Nontrivial R
  · let : Nontrivial R := hR
    rw [noetherian_ringKrullDim_eq_zero_iff_artinian]
    exact (Formalization.Books.Algebra.Unit53.artinian_iff_finite_length
      (R := R)).trans (d_eq_zero_iff_isFiniteLength R hR).symm
  · let : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    simp [ringKrullDim_eq_bot_of_subsingleton, d, hR]

/- The finite products in the source are represented through Mathlib's
   canonical finite product of localizations at maximal ideals.  The extra
   factorwise conjuncts record the stated properties of those local factors.
   This avoids introducing a second bundled notion of a finite ring product. -/
def IsFiniteProductOfArtinianLocalRings
    (R : Type u) [CommRing R] : Prop :=
  Finite (MaximalSpectrum R) ∧
    Nonempty (R ≃ₐ[R] MaximalSpectrum.PiLocalization R) ∧
      ∀ q : MaximalSpectrum R,
        IsArtinianRing (Localization.AtPrime q.asIdeal)

def IsFiniteProductOfNoetherianZeroDimensionalLocalRings
    (R : Type u) [CommRing R] : Prop :=
  ∃ hN : IsNoetherianRing R,
    letI : IsNoetherianRing R := hN
    Finite (MaximalSpectrum R) ∧
      Nonempty (R ≃ₐ[R] MaximalSpectrum.PiLocalization R) ∧
        ∀ q : MaximalSpectrum R,
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0

def IsFiniteProductOfDZeroLocalRings
    (R : Type u) [CommRing R] : Prop :=
  ∃ hN : IsNoetherianRing R,
    letI : IsNoetherianRing R := hN
    Finite (MaximalSpectrum R) ∧
      Nonempty (R ≃ₐ[R] MaximalSpectrum.PiLocalization R) ∧
        ∀ q : MaximalSpectrum R,
          d (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 0

def IsFiniteProductOfNilpotentMaximalLocalRings
    (R : Type u) [CommRing R] : Prop :=
  ∃ hN : IsNoetherianRing R,
    letI : IsNoetherianRing R := hN
    Finite (MaximalSpectrum R) ∧
      Nonempty (R ≃ₐ[R] MaximalSpectrum.PiLocalization R) ∧
        ∀ q : MaximalSpectrum R,
          IsNilpotent (maximalIdeal (Localization.AtPrime q.asIdeal))

def IsFiniteDiscretePrimeSpectrum
    (R : Type u) [CommRing R] : Prop :=
  Finite (PrimeSpectrum R) ∧
    DiscreteTopology (PrimeSpectrum R)

def HasFinitelyManyMaximalIdealsAndNilpotentJacobsonRadical
    (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    Set.Finite {m : Ideal R | m.IsMaximal} ∧
      IsNilpotent (Ring.jacobson R)

def HasNoStrictPrimeInclusions
    (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ ⦃p q : Ideal R⦄, p.IsPrime → q.IsPrime → ¬ p < q

theorem dimension_zero_ring_characterization
    (R : Type u) [CommRing R] [Nontrivial R] :
    List.TFAE
      [ IsArtinianRing R
      , IsNoetherianRing R ∧ ringKrullDim R = 0
      , IsFiniteLength R R
      , IsFiniteProductOfArtinianLocalRings R
      , IsNoetherianRing R ∧ IsFiniteDiscretePrimeSpectrum R
      , IsFiniteProductOfNoetherianZeroDimensionalLocalRings R
      , IsFiniteProductOfDZeroLocalRings R
      , IsFiniteProductOfNilpotentMaximalLocalRings R
      , HasFinitelyManyMaximalIdealsAndNilpotentJacobsonRadical R
      , HasNoStrictPrimeInclusions R ] := by
  have hArt_to_dim : IsArtinianRing R →
      IsNoetherianRing R ∧ ringKrullDim R = 0 := by
    intro hArt
    let : IsArtinianRing R := hArt
    exact ⟨inferInstance, (noetherian_ringKrullDim_eq_zero_iff_artinian
      (R := R)).2 hArt⟩
  have hDim_to_art : IsNoetherianRing R ∧ ringKrullDim R = 0 →
      IsArtinianRing R := by
    rintro ⟨hN, hdim⟩
    let : IsNoetherianRing R := hN
    exact (noetherian_ringKrullDim_eq_zero_iff_artinian (R := R)).1 hdim
  have hArt_to_length : IsArtinianRing R → IsFiniteLength R R := by
    exact fun hArt =>
      (Formalization.Books.Algebra.Unit53.artinian_iff_finite_length
        (R := R)).1 hArt
  have hLength_to_art : IsFiniteLength R R → IsArtinianRing R := by
    exact fun hLength =>
      (Formalization.Books.Algebra.Unit53.artinian_iff_finite_length
        (R := R)).2 hLength
  have hArt_to_productArt : IsArtinianRing R →
      IsFiniteProductOfArtinianLocalRings R := by
    intro hArt
    have hprops :=
      Formalization.Books.Algebra.Unit53.finite_length_ring_properties
        (hArt_to_length hArt)
    let : IsArtinianRing R := hArt
    refine ⟨hprops.2.2.2.1, hprops.2.2.2.2, ?_⟩
    intro q
    exact IsArtinianRing.localization_artinian q.asIdeal.primeCompl _
  have hProductArt_to_art : IsFiniteProductOfArtinianLocalRings R →
      IsArtinianRing R := by
    rintro ⟨hfinite, ⟨e⟩, hfactor⟩
    let : Finite (MaximalSpectrum R) := hfinite
    let : ∀ q : MaximalSpectrum R,
        IsArtinianRing (Localization.AtPrime q.asIdeal) := hfactor
    have : IsArtinianRing (MaximalSpectrum.PiLocalization R) := inferInstance
    exact e.symm.toRingEquiv.isArtinianRing
  have hArt_to_discrete : IsArtinianRing R →
      IsNoetherianRing R ∧ IsFiniteDiscretePrimeSpectrum R := by
    intro hArt
    let : IsArtinianRing R := hArt
    exact ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩
  have hDiscrete_to_art :
      IsNoetherianRing R ∧ IsFiniteDiscretePrimeSpectrum R →
        IsArtinianRing R := by
    rintro ⟨hN, ⟨hfinite, hdiscrete⟩⟩
    let : IsNoetherianRing R := hN
    have hdim : Ring.KrullDimLE 0 R :=
      (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp
        hdiscrete).2
    exact (isArtinianRing_iff_krullDimLE_zero).2 hdim
  have hArt_to_productDim : IsArtinianRing R →
      IsFiniteProductOfNoetherianZeroDimensionalLocalRings R := by
    intro hArt
    have hprops :=
      Formalization.Books.Algebra.Unit53.finite_length_ring_properties
        (hArt_to_length hArt)
    let : IsArtinianRing R := hArt
    refine ⟨inferInstance, hprops.2.2.2.1, hprops.2.2.2.2, ?_⟩
    intro q
    have hloc : IsArtinianRing (Localization.AtPrime q.asIdeal) :=
      IsArtinianRing.localization_artinian q.asIdeal.primeCompl _
    exact (noetherian_ringKrullDim_eq_zero_iff_artinian
      (R := Localization.AtPrime q.asIdeal)).2 hloc
  have hProductDim_to_art :
      IsFiniteProductOfNoetherianZeroDimensionalLocalRings R →
        IsArtinianRing R := by
    rintro ⟨hN, hfinite, ⟨e⟩, hdim⟩
    let : IsNoetherianRing R := hN
    let : Finite (MaximalSpectrum R) := hfinite
    let : ∀ q : MaximalSpectrum R,
        IsArtinianRing (Localization.AtPrime q.asIdeal) := by
      intro q
      exact (noetherian_ringKrullDim_eq_zero_iff_artinian
        (R := Localization.AtPrime q.asIdeal)).1 (hdim q)
    have : IsArtinianRing (MaximalSpectrum.PiLocalization R) := inferInstance
    exact e.symm.toRingEquiv.isArtinianRing
  have hArt_to_productD : IsArtinianRing R →
      IsFiniteProductOfDZeroLocalRings R := by
    intro hArt
    rcases hArt_to_productDim hArt with ⟨hN, hfinite, he, hdim⟩
    refine ⟨hN, hfinite, he, ?_⟩
    intro q
    exact (local_ringKrullDim_eq_zero_iff_d_eq_zero
      (Localization.AtPrime q.asIdeal)).mp (hdim q)
  have hProductD_to_art : IsFiniteProductOfDZeroLocalRings R →
      IsArtinianRing R := by
    rintro ⟨hN, hfinite, ⟨e⟩, hd⟩
    let : IsNoetherianRing R := hN
    let : Finite (MaximalSpectrum R) := hfinite
    let : ∀ q : MaximalSpectrum R,
        IsArtinianRing (Localization.AtPrime q.asIdeal) := by
      intro q
      have hdim := (local_ringKrullDim_eq_zero_iff_d_eq_zero
        (Localization.AtPrime q.asIdeal)).2 (hd q)
      exact (noetherian_ringKrullDim_eq_zero_iff_artinian
        (R := Localization.AtPrime q.asIdeal)).1 hdim
    have : IsArtinianRing (MaximalSpectrum.PiLocalization R) := inferInstance
    exact e.symm.toRingEquiv.isArtinianRing
  have hArt_to_productNil : IsArtinianRing R →
      IsFiniteProductOfNilpotentMaximalLocalRings R := by
    intro hArt
    rcases hArt_to_productDim hArt with ⟨hN, hfinite, he, hdim⟩
    refine ⟨hN, hfinite, he, ?_⟩
    intro q
    have hloc : IsArtinianRing (Localization.AtPrime q.asIdeal) :=
      (noetherian_ringKrullDim_eq_zero_iff_artinian
        (R := Localization.AtPrime q.asIdeal)).1 (hdim q)
    exact (isArtinianRing_iff_isNilpotent_maximalIdeal
      (Localization.AtPrime q.asIdeal)).1 hloc
  have hProductNil_to_art : IsFiniteProductOfNilpotentMaximalLocalRings R →
      IsArtinianRing R := by
    rintro ⟨hN, hfinite, ⟨e⟩, hnil⟩
    let : IsNoetherianRing R := hN
    let : Finite (MaximalSpectrum R) := hfinite
    let : ∀ q : MaximalSpectrum R,
        IsArtinianRing (Localization.AtPrime q.asIdeal) := by
      intro q
      exact (isArtinianRing_iff_isNilpotent_maximalIdeal
        (Localization.AtPrime q.asIdeal)).2 (hnil q)
    have : IsArtinianRing (MaximalSpectrum.PiLocalization R) := inferInstance
    exact e.symm.toRingEquiv.isArtinianRing
  have hArt_to_jacobson : IsArtinianRing R →
      HasFinitelyManyMaximalIdealsAndNilpotentJacobsonRadical R := by
    intro hArt
    let : IsArtinianRing R := hArt
    exact ⟨inferInstance,
      Formalization.Books.Algebra.Unit53.artinian_finite_maximal_ideals,
      Formalization.Books.Algebra.Unit53.artinian_jacobson_radical_is_nilpotent⟩
  have hJacobson_to_art :
      HasFinitelyManyMaximalIdealsAndNilpotentJacobsonRadical R →
        IsArtinianRing R := by
    rintro ⟨hN, hfinite, hjac⟩
    let : IsNoetherianRing R := hN
    have hjac' : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal
        (Ring.jacobson R) := by
      obtain ⟨n, hn⟩ := hjac
      intro x hx
      refine ⟨n, ?_⟩
      have hxpow : x ^ n ∈ (Ring.jacobson R) ^ n :=
        Ideal.pow_mem_pow hx n
      rw [hn] at hxpow
      exact hxpow
    have hprod :=
      Formalization.Books.Algebra.Unit53.product_localizations_of_finite_maximal_ideals
        hfinite hjac'
    exact (isArtinianRing_iff_krullDimLE_zero).2
      (Ring.KrullDimLE.mk₀ hprod.1)
  have hArt_to_noStrict : IsArtinianRing R → HasNoStrictPrimeInclusions R := by
    intro hArt
    let : IsArtinianRing R := hArt
    refine ⟨inferInstance, ?_⟩
    intro p q hp hq hpq
    let : p.IsPrime := hp
    have hpmax : p.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p
    exact hpq.ne (hpmax.eq_of_le hq.ne_top hpq.le)
  have hNoStrict_to_art : HasNoStrictPrimeInclusions R → IsArtinianRing R := by
    rintro ⟨hN, hnostrict⟩
    let : IsNoetherianRing R := hN
    have hall : ∀ (p : Ideal R), p.IsPrime → p.IsMaximal := by
      intro p hp
      obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hp.ne_top
      have hEq : p = m := by
        by_contra hne
        exact (hnostrict hp hm.isPrime) (lt_of_le_of_ne hpm hne)
      simpa [hEq] using hm
    exact (isArtinianRing_iff_krullDimLE_zero).2 (Ring.KrullDimLE.mk₀ hall)
  tfae_have 1 → 2 := hArt_to_dim
  tfae_have 2 → 1 := hDim_to_art
  tfae_have 1 → 3 := hArt_to_length
  tfae_have 3 → 1 := hLength_to_art
  tfae_have 1 → 4 := hArt_to_productArt
  tfae_have 4 → 1 := hProductArt_to_art
  tfae_have 1 → 5 := hArt_to_discrete
  tfae_have 5 → 1 := hDiscrete_to_art
  tfae_have 1 → 6 := hArt_to_productDim
  tfae_have 6 → 1 := hProductDim_to_art
  tfae_have 1 → 7 := hArt_to_productD
  tfae_have 7 → 1 := hProductD_to_art
  tfae_have 1 → 8 := hArt_to_productNil
  tfae_have 8 → 1 := hProductNil_to_art
  tfae_have 1 → 9 := hArt_to_jacobson
  tfae_have 9 → 1 := hJacobson_to_art
  tfae_have 1 → 10 := hArt_to_noStrict
  tfae_have 10 → 1 := hNoStrict_to_art
  tfae_finish

/-! ## Dimension one and general local dimension -/

theorem local_dimension_one_characterization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    List.TFAE
      [ ringKrullDim R = 1
      , d R R = 1
      , ∃ x : R, x ∈ maximalIdeal R ∧ ¬ IsNilpotent x ∧
          PrimeSpectrum.zeroLocus ({x} : Set R) = {closedPoint R}
      , ∃ x : R, x ∈ maximalIdeal R ∧ ¬ IsNilpotent x ∧
          maximalIdeal R = (Ideal.span ({x} : Set R)).radical
      , (∃ x : R, x ∈ maximalIdeal R ∧
          IsIdealOfDefinition R (Ideal.span ({x} : Set R))) ∧
          ¬ IsIdealOfDefinition R (⊥ : Ideal R) ] := by
  sorry

def HasIdealOfDefinitionGeneratedBy
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) : Prop :=
  ∃ x : Fin n → R,
    (∀ i, x i ∈ maximalIdeal R) ∧
      IsIdealOfDefinition R (Ideal.span (Set.range x))

theorem local_dimension_characterization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : Nontrivial R)
    (d₀ : ℕ) :
    List.TFAE
      [ ringKrullDim R = d₀
      , d R R = d₀
      , HasIdealOfDefinitionGeneratedBy R d₀ ∧
          ∀ n : ℕ, n < d₀ → ¬ HasIdealOfDefinitionGeneratedBy R n ] := by
  sorry

theorem ringKrullDim_le_maximalIdeal_spanFinrank
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ (maximalIdeal R).spanFinrank :=
  ringKrullDim_le_spanFinrank_maximalIdeal R

theorem ringKrullDim_le_cotangentSpace_finrank
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R]
  exact ringKrullDim_le_maximalIdeal_spanFinrank R

/-! ## Systems of parameters and regular local rings -/

def IsSystemOfParameters
    (R : Type u) [CommRing R] [IsLocalRing R]
    (d₀ : ℕ) (x : Fin d₀ → R) : Prop :=
  (∀ i, x i ∈ maximalIdeal R) ∧
    IsIdealOfDefinition R (Ideal.span (Set.range x))

def IsRegularSystemOfParameters
    (R : Type u) [CommRing R] [IsLocalRing R]
    (d₀ : ℕ) (x : Fin d₀ → R) : Prop :=
  (∀ i, x i ∈ maximalIdeal R) ∧
    Ideal.span (Set.range x) = maximalIdeal R

/- Mathlib's `IsRegularLocalRing` is the source's regular-local-ring
   property.  Its defining equality is the equality of maximal-ideal
   span-rank and ring Krull dimension. -/
theorem isRegularLocalRing_iff_exists_regularSystemOfParameters
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d₀ : ℕ) (hd : ringKrullDim R = d₀) :
    IsRegularLocalRing R ↔
      ∃ x : Fin d₀ → R,
        IsSystemOfParameters R d₀ x ∧ IsRegularSystemOfParameters R d₀ x := by
  constructor
  · intro hreg
    let : IsRegularLocalRing R := hreg
    have hspan : (maximalIdeal R).spanFinrank = d₀ := by
      exact_mod_cast ((isRegularLocalRing_iff R).mp hreg |>.trans hd)
    obtain ⟨s, hs_card, hs_span⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank
        (p := (maximalIdeal R : Submodule R R))
        (maximalIdeal R).fg_of_isNoetherianRing
    have hs_card' : s.card = d₀ := hs_card.trans hspan
    let e : s ≃ Fin d₀ := Finset.equivFinOfCardEq hs_card'
    let x : Fin d₀ → R := fun i => e.symm i
    have hxmem : ∀ i, x i ∈ maximalIdeal R := by
      intro i
      change (e.symm i : R) ∈ (maximalIdeal R : Submodule R R)
      rw [← hs_span]
      exact Submodule.subset_span (e.symm i).property
    have hrange : Set.range x = (s : Set R) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).property
      · intro hy
        let y' : s := ⟨y, hy⟩
        refine ⟨e y', ?_⟩
        exact congrArg Subtype.val (e.symm_apply_apply y')
    refine ⟨x, ⟨hxmem, ?_⟩, ⟨hxmem, ?_⟩⟩
    · rw [hrange]
      have hspanIdeal : Ideal.span (s : Set R) = maximalIdeal R := by
        simpa using hs_span
      rw [hspanIdeal]
      exact maximalIdeal_isIdealOfDefinition R
    · rw [hrange]
      simpa using hs_span
  · rintro ⟨x, hsys, hreg⟩
    change (∀ i, x i ∈ maximalIdeal R) ∧
      IsIdealOfDefinition R (Ideal.span (Set.range x)) at hsys
    change (∀ i, x i ∈ maximalIdeal R) ∧
      Ideal.span (Set.range x) = maximalIdeal R at hreg
    have hgen : Ideal.span (Set.range x) = maximalIdeal R := hreg.2
    have hspan_le : (maximalIdeal R).spanFinrank ≤ d₀ := by
      rw [← hgen]
      calc
        (Ideal.span (Set.range x)).spanFinrank ≤ (Set.range x).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)
        _ ≤ d₀ := by
          simpa [Set.image_univ] using
            (Set.ncard_image_le (f := x) (s := (Set.univ : Set (Fin d₀))))
    apply (isRegularLocalRing_iff R).2
    apply le_antisymm
    · rw [hd]
      exact_mod_cast hspan_le
    · exact ringKrullDim_le_maximalIdeal_spanFinrank R

theorem isRegularLocalRing_iff_cotangentSpace_finrank_eq_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔
      Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R :=
  IsRegularLocalRing.iff_finrank_cotangentSpace R

/-! ## Minimal primes over generated ideals -/

theorem height_le_one_of_minimal_over_singleton
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (x : R) {p : Ideal R}
    (hp : p ∈ (Ideal.span ({x} : Set R)).minimalPrimes) :
    p.height ≤ 1 := by
  sorry

theorem height_zero_or_one_of_minimal_over_singleton
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (x : R) {p : Ideal R}
    (hp : p ∈ (Ideal.span ({x} : Set R)).minimalPrimes) :
    p.height = 0 ∨ p.height = 1 := by
  sorry

theorem no_prime_strictly_between_minimal_over_singleton
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (x : R) {p q : Ideal R} (hp : p.IsPrime) (hq : q.IsPrime)
    (hqmin : q ∈ (p ⊔ Ideal.span ({x} : Set R)).minimalPrimes) :
    ¬ ∃ r : Ideal R, r.IsPrime ∧ p < r ∧ r < q := by
  sorry

theorem height_le_number_of_generators_of_minimal_over
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {r : ℕ} (f : Fin r → R) {p : Ideal R}
    (hp : p ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    p.height ≤ r := by
  sorry

theorem prime_chain_length_le_number_of_generators_of_minimal_over
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {r : ℕ} (f : Fin r → R) {p q : Ideal R}
    (hp : p.IsPrime) (hq : q.IsPrime)
    (hqmin : q ∈ (p ⊔ Ideal.span (Set.range f)).minimalPrimes) :
    ∀ C : PrimeIdealChain R,
      C.head = ⟨p, hp⟩ → C.last = ⟨q, hq⟩ → C.length ≤ r := by
  sorry

/-! ## One equation and successive parameter quotients -/

theorem one_equation_dimension_le
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 := by
  sorry

theorem one_equation_dimension_eq_of_not_mem_minimalPrimes
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : Nontrivial R)
    (x : R) (hx : x ∈ maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ∉ p) :
    ringKrullDim R =
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 := by
  sorry

theorem one_equation_dimension_eq_of_nonzerodivisor
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : Nontrivial R)
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : x ∈ nonZeroDivisors R) :
    ringKrullDim R =
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 := by
  sorry

theorem dimensions_of_successive_parameter_quotients
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d₀ : ℕ) (x : Fin d₀ → R)
    (hx : ∀ i, x i ∈ maximalIdeal R)
    (hdef : IsIdealOfDefinition R (Ideal.span (Set.range x)))
    (hdim : ringKrullDim R = d₀) :
    ∀ (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d₀),
      ringKrullDim
          (R ⧸ Ideal.span
            (Set.range (fun j : Fin i =>
              x ⟨j.1, lt_of_lt_of_le j.2 hid⟩))) = d₀ - i := by
  sorry

end

end Formalization.Books.Algebra.Unit60
