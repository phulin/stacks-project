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

private theorem numericalPolynomialDegree_le_zero_of_eventually_bounded
    (f : ℤ → ℤ) (hf : IsNumericalPolynomial f) (C : ℕ)
    (hbound : ∀ᶠ n : ℤ in Filter.atTop, 0 ≤ f n ∧ f n ≤ C) :
    numericalPolynomialDegree f ≤ 0 := by
  classical
  let P := eventuallyRationalPolynomial f
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((eventuallyRationalPolynomial_spec f hf).and hbound)
  let g : ℕ → Fin (C + 1) := fun k =>
    ⟨(f (N + k)).toNat, by
      have hk := (hN (N + k) (by omega)).2
      have hcast : ((f (N + k)).toNat : ℤ) = f (N + k) :=
        Int.toNat_of_nonneg hk.1
      have hle : ((f (N + k)).toNat : ℤ) ≤ C := by
        rw [hcast]
        exact hk.2
      exact Nat.lt_succ_of_le (by exact_mod_cast hle)⟩
  obtain ⟨a, ha⟩ := Finite.exists_infinite_fiber g
  let ι : (g ⁻¹' ({a} : Set (Fin (C + 1)))) → ℚ := fun k =>
    ((N + k.1 : ℤ) : ℚ)
  have hι : Function.Injective ι := by
    intro i j hij
    apply Subtype.ext
    have hij' : (i.1 : ℤ) = (j.1 : ℤ) := by
      dsimp [ι] at hij
      have hij'' : N + (i.1 : ℤ) = N + (j.1 : ℤ) := by
        exact_mod_cast hij
      omega
    exact_mod_cast hij'
  have hιinf : Set.Infinite (Set.range ι) :=
    Set.infinite_range_of_injective hι
  have heq : P = Polynomial.C (a.1 : ℚ) := by
    apply Polynomial.eq_of_infinite_eval_eq P (Polynomial.C (a.1 : ℚ))
    refine hιinf.mono ?_
    rintro z ⟨k, rfl⟩
    have hka : g k.1 = a := by
      have hk := k.2
      change g k.1 ∈ ({a} : Set (Fin (C + 1))) at hk
      simpa only [Set.mem_singleton_iff] using hk
    have hN' := hN (N + k.1) (by omega)
    have hto : (f (N + k.1)).toNat = a.1 :=
      congrArg Fin.val hka
    have hcast : ((f (N + k.1)).toNat : ℤ) = f (N + k.1) :=
      Int.toNat_of_nonneg hN'.2.1
    have hfc : (f (N + k.1) : ℚ) = (a.1 : ℚ) := by
      rw [← hcast]
      exact_mod_cast hto
    change (eventuallyRationalPolynomial f).eval
      ((N + k.1 : ℤ) : ℚ) =
      (Polynomial.C (a.1 : ℚ)).eval ((N + k.1 : ℤ) : ℚ)
    rw [hN'.1, hfc]
    simp
  change P.degree ≤ 0
  rw [heq]
  by_cases ha0 : (a.1 : ℚ) = 0
  · simp [ha0]
  · rw [Polynomial.degree_C ha0]

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

def HasIdealOfDefinitionGeneratedBy
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) : Prop :=
  ∃ x : Fin n → R,
    (∀ i, x i ∈ maximalIdeal R) ∧
      IsIdealOfDefinition R (Ideal.span (Set.range x))

/-- A Noetherian local ring of finite dimension `n` has an ideal of definition
generated by exactly `n` elements.  This is the finite-set form used before
choosing an indexing by `Fin n`. -/
theorem exists_isIdealOfDefinition_finset_card_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) :
    ∃ s : Finset R, s.card = n ∧
      IsIdealOfDefinition R (Ideal.span (s : Set R)) := by
  classical
  obtain ⟨s, hsmin, hscard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing
      (IsLocalRing.maximalIdeal R)
  have hscard' : s.card = n := by
    have hscard'' : (s.card : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      calc
        (s.card : WithBot ℕ∞) = (IsLocalRing.maximalIdeal R).height := by
          exact_mod_cast hscard
        _ = ringKrullDim R := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
        _ = (n : WithBot ℕ∞) := hdim
    exact_mod_cast hscard''
  refine ⟨s, hscard', ?_⟩
  unfold IsIdealOfDefinition
  apply le_antisymm
  · rw [← (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical]
    exact Ideal.radical_mono hsmin.le
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf fun p hp => ?_
    rcases hp with ⟨hpI, hp⟩
    have hpmax : p ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hp.ne_top
    have hmaxp : IsLocalRing.maximalIdeal R ≤ p := by
      exact hsmin.2 ⟨hp, hpI⟩ hpmax
    exact hmaxp

/-- Krull's height theorem bounds the dimension of a local ring by the number
of generators of any ideal of definition. -/
theorem ringKrullDim_le_of_isIdealOfDefinition_span
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {s : Finset R} (hdef : IsIdealOfDefinition R (Ideal.span (s : Set R))) :
    ringKrullDim R ≤ s.card := by
  have hmin : IsLocalRing.maximalIdeal R ∈
      (Ideal.span (s : Set R)).minimalPrimes := by
    refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal R).isPrime, ?_⟩, ?_⟩
    · exact Ideal.le_radical.trans_eq hdef
    · intro p hp hpI
      have hpm : p ≤ IsLocalRing.maximalIdeal R :=
        IsLocalRing.le_maximalIdeal hp.1.ne_top
      have hrad : IsLocalRing.maximalIdeal R ≤ p := by
        rw [← hdef]
        exact hp.1.radical_le_iff.mpr hp.2
      exact hrad
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span
    (Set.toFinite (s : Set R)) hmin
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast hh

/-- A Noetherian local ring of dimension `n` admits a system of `n`
parameters. -/
theorem exists_parameter_of_ringKrullDim_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) :
    ∃ x : Fin n → R,
      (∀ i, x i ∈ maximalIdeal R) ∧
        IsIdealOfDefinition R (Ideal.span (Set.range x)) := by
  classical
  obtain ⟨s, hs_card, hdef⟩ :=
    exists_isIdealOfDefinition_finset_card_eq R n hdim
  let e : s ≃ Fin n := Finset.equivFinOfCardEq hs_card
  let x : Fin n → R := fun i => e.symm i
  have hxmem : ∀ i, x i ∈ maximalIdeal R := by
    intro i
    rw [← hdef]
    exact Ideal.le_radical (Ideal.subset_span (e.symm i).property)
  have hrange : Set.range x = (s : Set R) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp [x]⟩
  refine ⟨x, hxmem, ?_⟩
  rw [hrange]
  exact hdef

/-- The dimension is the least cardinality of a system of parameters. -/
theorem ringKrullDim_eq_iff_parameter_minimal
    (R : Type u) [CommRing R] [IsLocalRing R]
    [hR : IsNoetherianRing R]
    (n : ℕ) :
    ringKrullDim R = n ↔
      HasIdealOfDefinitionGeneratedBy R n ∧
        ∀ m : ℕ, m < n → ¬ HasIdealOfDefinitionGeneratedBy R m := by
  classical
  constructor
  · intro hdim
    obtain ⟨x, hx, hdef⟩ :=
      @exists_parameter_of_ringKrullDim_eq R _ _ hR n hdim
    refine ⟨⟨x, hx, hdef⟩, ?_⟩
    intro m hm hparam
    rcases hparam with ⟨y, hy, hdefy⟩
    let s : Finset R := Finset.univ.image y
    have hspan : Ideal.span (s : Set R) = Ideal.span (Set.range y) := by
      have hsset : (s : Set R) = Set.range y := by
        ext z
        simp [s]
      rw [hsset]
    have hdefs : IsIdealOfDefinition R (Ideal.span (s : Set R)) := by
      simpa [hspan] using hdefy
    have hle : ringKrullDim R ≤ s.card :=
      @ringKrullDim_le_of_isIdealOfDefinition_span R _ _ hR s hdefs
    have hle' : n ≤ m := by
      have hs_card : s.card ≤ m := by
        dsimp [s]
        simpa using (Finset.card_image_le (f := y) (s := (Finset.univ : Finset (Fin m))))
      have hle'' : (n : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := by
        rw [← hdim]
        exact hle.trans (by exact_mod_cast hs_card)
      exact_mod_cast hle''
    omega
  · rintro ⟨hparam, hminimal⟩
    rcases hparam with ⟨x, hx, hdef⟩
    let s : Finset R := Finset.univ.image x
    have hspan : Ideal.span (s : Set R) = Ideal.span (Set.range x) := by
      have hsset : (s : Set R) = Set.range x := by
        ext z
        simp [s]
      rw [hsset]
    have hdefs : IsIdealOfDefinition R (Ideal.span (s : Set R)) := by
      simpa [hspan] using hdef
    have hle : ringKrullDim R ≤ s.card :=
      @ringKrullDim_le_of_isIdealOfDefinition_span R _ _ hR s hdefs
    have hle' : ringKrullDim R ≤ n := by
      have hs_card : s.card ≤ n := by
        dsimp [s]
        simpa using (Finset.card_image_le (f := x) (s := (Finset.univ : Finset (Fin n))))
      exact hle.trans (by exact_mod_cast hs_card)
    have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
    cases hq : ringKrullDim R with
    | bot => exact (hbot hq).elim
    | coe q =>
        cases q with
        | top => exact (htop hq).elim
        | coe k =>
            rw [hq] at hle'
            have hk : k ≤ n := by
              exact_mod_cast hle'
            have hkn : ¬ k < n := by
              intro hkn
              apply hminimal k hkn
              obtain ⟨z, hz, hdefz⟩ :=
                @exists_parameter_of_ringKrullDim_eq R _ _ hR k (by rw [hq]; rfl)
              exact ⟨z, hz, hdefz⟩
            have : k = n := by omega
            subst k
            rfl

theorem isIdealOfDefinition_bot_of_isNilpotent_of_principal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hdef : IsIdealOfDefinition R (Ideal.span ({x} : Set R)))
    (hnil : IsNilpotent x) :
    IsIdealOfDefinition R (⊥ : Ideal R) := by
  have hrad : (Ideal.span ({x} : Set R)).radical ≤ nilradical R := by
    intro y hy
    rcases (Ideal.mem_radical_iff.mp hy) with ⟨n, hyn⟩
    rcases (Ideal.mem_span_singleton.mp hyn) with ⟨r, hr⟩
    rcases hnil with ⟨k, hk⟩
    apply mem_nilradical.mpr
    refine ⟨n * k, ?_⟩
    rw [pow_mul, hr, mul_pow, hk, zero_mul]
  have hmax : IsLocalRing.maximalIdeal R ≤ nilradical R := by
    rw [← hdef]
    exact hrad
  have hmax' : nilradical R ≤ IsLocalRing.maximalIdeal R :=
    nilradical_le_prime (IsLocalRing.maximalIdeal R)
  have heq : IsLocalRing.maximalIdeal R = nilradical R :=
    le_antisymm hmax hmax'
  unfold IsIdealOfDefinition
  simpa [nilradical] using heq.symm

theorem hasIdealOfDefinitionGeneratedBy_zero_iff
    (R : Type u) [CommRing R] [IsLocalRing R] :
    HasIdealOfDefinitionGeneratedBy R 0 ↔
      IsIdealOfDefinition R (⊥ : Ideal R) := by
  constructor
  · rintro ⟨x, -, hx⟩
    simpa using hx
  · intro h
    refine ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_⟩
    simpa using h

theorem hasIdealOfDefinitionGeneratedBy_one_iff
    (R : Type u) [CommRing R] [IsLocalRing R] :
    HasIdealOfDefinitionGeneratedBy R 1 ↔
      ∃ x : R, x ∈ maximalIdeal R ∧
        IsIdealOfDefinition R (Ideal.span ({x} : Set R)) := by
  constructor
  · rintro ⟨x, hx, hdef⟩
    refine ⟨x 0, hx 0, ?_⟩
    simpa [Set.range_unique] using hdef
  · rintro ⟨x, hx, hdef⟩
    refine ⟨fun _ => x, fun _ => hx, ?_⟩
    simpa [Set.range_unique] using hdef

theorem principal_zeroLocus_eq_closedPoint_iff_isIdealOfDefinition
    (R : Type u) [CommRing R] [IsLocalRing R] (x : R) :
    PrimeSpectrum.zeroLocus ({x} : Set R) = {closedPoint R} ↔
      IsIdealOfDefinition R (Ideal.span ({x} : Set R)) := by
  rw [isIdealOfDefinition_iff_zeroLocus_eq_singleton]
  simp only [PrimeSpectrum.zeroLocus_span]

/-- The finite-dimensional form of the Hilbert–Samuel theorem identifying the
degree invariant from Chapter 59 with Krull dimension.

The proof should be assembled from the upper bound supplied by a system of
parameters and the lower bound obtained from the Hilbert polynomial of a
parameter ideal. -/
theorem local_ringKrullDim_eq_iff_d_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∀ n : ℕ, ringKrullDim R = n ↔ d R R = n := by
  sorry

theorem ringKrullDim_eq_one_iff_principal_idealOfDefinition
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R = 1 ↔
      (∃ x : R, x ∈ maximalIdeal R ∧
        IsIdealOfDefinition R (Ideal.span ({x} : Set R))) ∧
        ¬ IsIdealOfDefinition R (⊥ : Ideal R) := by
  have hzero :
      (∀ m : ℕ, m < 1 → ¬ HasIdealOfDefinitionGeneratedBy R m) ↔
        ¬ IsIdealOfDefinition R (⊥ : Ideal R) := by
    constructor
    · intro h hbot
      exact h 0 (by omega)
        ((hasIdealOfDefinitionGeneratedBy_zero_iff R).mpr hbot)
    · intro hbot m hm hgen
      have hm0 : m = 0 := by omega
      subst m
      exact hbot ((hasIdealOfDefinitionGeneratedBy_zero_iff R).mp hgen)
  refine (ringKrullDim_eq_iff_parameter_minimal R 1).trans ?_
  rw [hasIdealOfDefinitionGeneratedBy_one_iff, hzero]


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
  tfae_have 1 ↔ 2 := local_ringKrullDim_eq_iff_d_eq R 1
  tfae_have 1 ↔ 5 := ringKrullDim_eq_one_iff_principal_idealOfDefinition R
  tfae_have 3 ↔ 4 := by
    constructor
    · rintro ⟨x, hx, hnil, hz⟩
      have hdef :=
        (principal_zeroLocus_eq_closedPoint_iff_isIdealOfDefinition R x).mp hz
      exact ⟨x, hx, hnil, hdef.symm⟩
    · rintro ⟨x, hx, hnil, hdef⟩
      exact ⟨x, hx, hnil,
        (principal_zeroLocus_eq_closedPoint_iff_isIdealOfDefinition R x).mpr hdef.symm⟩
  tfae_have 4 ↔ 5 := by
    constructor
    · rintro ⟨x, hx, hnil, hdef⟩
      refine ⟨⟨x, hx, hdef.symm⟩, ?_⟩
      intro hbot
      exact hnil
        (isNilpotent_of_mem_maximalIdeal_of_bot_isIdealOfDefinition hx hbot)
    · rintro ⟨⟨x, hx, hdef⟩, hbot⟩
      refine ⟨x, hx, ?_, hdef.symm⟩
      intro hnil
      exact hbot (isIdealOfDefinition_bot_of_isNilpotent_of_principal R hdef hnil)
  tfae_finish

theorem local_dimension_characterization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (_hR : Nontrivial R)
    (d₀ : ℕ) :
    List.TFAE
      [ ringKrullDim R = d₀
      , d R R = d₀
      , HasIdealOfDefinitionGeneratedBy R d₀ ∧
          ∀ n : ℕ, n < d₀ → ¬ HasIdealOfDefinitionGeneratedBy R n ] := by
  tfae_have 1 ↔ 2 := local_ringKrullDim_eq_iff_d_eq R d₀
  tfae_have 1 ↔ 3 := ringKrullDim_eq_iff_parameter_minimal R d₀
  tfae_finish

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
  exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    (Ideal.span ({x} : Set R)) p hp

theorem height_zero_or_one_of_minimal_over_singleton
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (x : R) {p : Ideal R}
    (hp : p ∈ (Ideal.span ({x} : Set R)).minimalPrimes) :
    p.height = 0 ∨ p.height = 1 := by
  exact Order.le_one_iff.mp
    (height_le_one_of_minimal_over_singleton R x hp)

theorem no_prime_strictly_between_minimal_over_singleton
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (x : R) {p q : Ideal R} (hp : p.IsPrime) (hq : q.IsPrime)
    (hqmin : q ∈ (p ⊔ Ideal.span ({x} : Set R)).minimalPrimes) :
    ¬ ∃ r : Ideal R, r.IsPrime ∧ p < r ∧ r < q := by
  rintro ⟨r, hr, hpr, hrq⟩
  let f : R →+* R ⧸ p := Ideal.Quotient.mk p
  let _ : r.IsPrime := hr
  let _ : q.IsPrime := hq
  have hpr' : p.map f < r.map f := by
    apply lt_of_le_of_ne
    · exact Ideal.map_mono hpr.le
    · intro heq
      apply hpr.ne
      calc
        p = (p.map f).comap f := by
          rw [Ideal.comap_map_quotientMk, sup_eq_left.mpr le_rfl]
        _ = (r.map f).comap f := by rw [heq]
        _ = r := by
          rw [Ideal.comap_map_quotientMk, sup_eq_right.mpr hpr.le]
  have hrq' : r.map f < q.map f := by
    apply lt_of_le_of_ne
    · exact Ideal.map_mono hrq.le
    · intro heq
      apply hrq.ne
      calc
        r = (r.map f).comap f := by
          rw [Ideal.comap_map_quotientMk, sup_eq_right.mpr hpr.le]
        _ = (q.map f).comap f := by rw [heq]
        _ = q := by
          rw [Ideal.comap_map_quotientMk,
            sup_eq_right.mpr (le_sup_left.trans hqmin.le)]
  have hqupper : (q.map f).height ≤ 1 := by
    simpa [f] using (Ideal.map_height_le_one_of_mem_minimalPrimes
      (I := p) (x := x) hqmin)
  have hmr' : (r.map f).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpr.le
  have hmq' : (q.map f).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime (le_sup_left.trans hqmin.le)
  let _ : (p.map f).IsPrime := by
    simpa [f] using (Ideal.isPrime_map_quotientMk_of_isPrime
      (I := p) (p := p) le_rfl)
  let _ : (r.map f).IsPrime := hmr'
  let _ : (q.map f).IsPrime := hmq'
  have hzero : p.map f = (⊥ : Ideal (R ⧸ p)) := by
    simp [f]
  have hpheight : (p.map f).height = 0 := by
    rw [hzero]
    exact Ideal.height_eq_zero_iff_eq_bot.mpr rfl
  have hfirst : (1 : ℕ∞) ≤ (r.map f).height := by
    calc
      (1 : ℕ∞) = 0 + 1 := by simp
      _ ≤ (p.map f).height + 1 := by rw [hpheight]
      _ ≤ (r.map f).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hpr'
  have hsecond : (2 : ℕ∞) ≤ (q.map f).height := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (r.map f).height + 1 := add_le_add_left hfirst 1
      _ ≤ (q.map f).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hrq'
  exact (not_le_of_gt (by norm_num : (1 : ℕ∞) < 2))
    (hsecond.trans hqupper)

theorem height_le_number_of_generators_of_minimal_over
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {r : ℕ} (f : Fin r → R) {p : Ideal R}
    (hp : p ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    p.height ≤ r := by
  have hcard : (Set.range f).ncard ≤ r := by
    simpa [Set.image_univ] using
      (Set.ncard_image_le (f := f) (s := (Set.univ : Set (Fin r))))
  calc
    p.height ≤ (Set.range f).ncard :=
      Ideal.height_le_card_of_mem_minimalPrimes_span
        (Set.toFinite (Set.range f)) hp
    _ ≤ r := by exact_mod_cast hcard

theorem prime_chain_length_le_number_of_generators_of_minimal_over
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {r : ℕ} (f : Fin r → R) {p q : Ideal R}
    (hp : p.IsPrime) (hq : q.IsPrime)
    (hqmin : q ∈ (p ⊔ Ideal.span (Set.range f)).minimalPrimes) :
    ∀ C : PrimeIdealChain R,
      C.head = ⟨p, hp⟩ → C.last = ⟨q, hq⟩ → C.length ≤ r := by
  intro C hhead hlast
  let g : R →+* R ⧸ p := Ideal.Quotient.mk p
  have hpi (i : Fin (C.length + 1)) : p ≤ (C i).asIdeal := by
    have hi := C.head_le i
    rw [hhead] at hi
    exact hi
  have hmap_prime (i : Fin (C.length + 1)) :
      ((C i).asIdeal.map g).IsPrime := by
    let _ : (C i).asIdeal.IsPrime := (C i).isPrime
    exact Ideal.isPrime_map_quotientMk_of_isPrime (hpi i)
  let D : PrimeIdealChain (R ⧸ p) :=
    LTSeries.mk C.length
      (fun i => ⟨(C i).asIdeal.map g, hmap_prime i⟩)
      (by
        intro i j hij
        have hab : (C i).asIdeal < (C j).asIdeal := C.strictMono hij
        apply lt_of_le_of_ne
        · exact Ideal.map_mono hab.le
        · intro heq
          have heq' : (C i).asIdeal.map g = (C j).asIdeal.map g := by
            simpa using congrArg PrimeSpectrum.asIdeal heq
          apply hab.ne
          calc
            (C i).asIdeal = ((C i).asIdeal.map g).comap g := by
              rw [Ideal.comap_map_quotientMk, sup_eq_right.mpr (hpi i)]
            _ = ((C j).asIdeal.map g).comap g := by rw [heq']
            _ = (C j).asIdeal := by
              rw [Ideal.comap_map_quotientMk,
                sup_eq_right.mpr ((hpi i).trans hab.le)])
  have hDlast : D.last.asIdeal = q.map g := by
    change (C.last).asIdeal.map g = q.map g
    rw [hlast]
  have h := (Order.length_le_height_last (p := D))
  have h' : (D.length : ℕ∞) ≤ D.last.asIdeal.height := by
    simpa only [PrimeSpectrum.height_eq_orderHeight] using h
  rw [hDlast] at h'
  have hmapmin :
      q.map g ∈ ((p ⊔ Ideal.span (Set.range f)).map g).minimalPrimes := by
    rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective]
    refine ⟨q, ?_, rfl⟩
    simpa [Ideal.mk_ker, sup_eq_left.mpr le_sup_left] using hqmin
  have hgker : p.map g = (⊥ : Ideal (R ⧸ p)) := by
    simp [g]
  have himage :
      g '' Set.range f = Set.range (fun i => g (f i)) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  have hmapmin' :
      q.map g ∈ (Ideal.span (Set.range (fun i => g (f i)))).minimalPrimes := by
    simpa [Ideal.map_sup, Ideal.map_span, hgker, himage] using hmapmin
  have hqheight : (q.map g).height ≤ (r : ℕ∞) := by
    calc
      (q.map g).height ≤ (Set.range (fun i => g (f i))).ncard :=
        Ideal.height_le_card_of_mem_minimalPrimes_span
          (Set.toFinite _) hmapmin'
      _ ≤ r := by
        have hcard : (Set.range (fun i : Fin r => g (f i))).ncard ≤ r := by
          simpa [Set.image_univ] using
            (Set.ncard_image_le (f := fun i : Fin r => g (f i))
              (s := (Set.univ : Set (Fin r))))
        exact_mod_cast hcard
  have hlen : (C.length : ℕ∞) ≤ (r : ℕ∞) := h'.trans hqheight
  exact_mod_cast hlen

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
