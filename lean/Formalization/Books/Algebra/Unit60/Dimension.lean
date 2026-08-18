import Formalization.Books.Algebra.Unit59.NoetherianLocalRings
import Formalization.Books.Algebra.Unit53.ArtinianRings
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 60: Dimension

The source's Krull dimension and prime heights are represented by Mathlib's
canonical `ringKrullDim` and `Ideal.height`.  Likewise, a chain of prime
ideals is the canonical `LTSeries (PrimeSpectrum R)`.  The declarations below
add the source-facing interfaces that are not already part of those APIs.
-/

namespace Formalization.Books.Algebra.Unit60

open Formalization.Books.Algebra.Unit59
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

theorem local_ringKrullDim_eq_zero_iff_d_eq_zero
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R = 0 ↔ d R R = 0 := by
  sorry

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
    ∀ U : Set (PrimeSpectrum R), IsOpen U

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
  sorry

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
  sorry

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
  sorry

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
    (x : R) (hx : x ∈ maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ∉ p) :
    ringKrullDim R =
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 := by
  sorry

theorem one_equation_dimension_eq_of_nonzerodivisor
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
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
