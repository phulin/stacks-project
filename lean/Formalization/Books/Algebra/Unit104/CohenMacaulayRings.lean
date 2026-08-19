import Formalization.Books.Algebra.Unit71.ExtGroups
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Commutative Algebra, Chapter 104: Cohen-Macaulay rings

This file records the definitions and theorem interfaces in the section
“Cohen-Macaulay rings”.  The Cohen-Macaulay module predicate and the
dimension, chain, regular-sequence, and resolution interfaces are reused
from earlier chapters.
-/

namespace Formalization.Books.Algebra.Unit104

open Formalization.Books.Algebra.Unit72

universe u

noncomputable section

/-! ## Local Cohen-Macaulay rings -/

/- The source definition: a local ring is Cohen-Macaulay when its regular
   module is Cohen-Macaulay. -/
def IsCohenMacaulayLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  Formalization.Books.Algebra.Unit103.IsCohenMacaulay R R

/- The equivalent criterion stated immediately after the definition. -/
theorem isCohenMacaulayLocalRing_iff_exists_regularSequence
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsCohenMacaulayLocalRing R ↔
      ∃ xs : List R,
        (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
          RingTheory.Sequence.IsRegular R xs ∧
            ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) = 0 := by
  sorry

/- The first part of lemma-reformulate-CM.  Addition in `WithBot ℕ∞` is the
   canonical dimension normalization used by the preceding chapter. -/
theorem regularSequence_iff_expected_quotient_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) :
    RingTheory.Sequence.IsRegular R xs ↔
      ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) +
          (((xs.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := by
  sorry

/- The second part of lemma-reformulate-CM, namely that the sequence can be
   extended to maximal length and all its successive quotients are
   Cohen-Macaulay of the expected dimension. -/
def IsCohenMacaulayQuotientRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) : Prop :=
  ∃ hlocal : IsLocalRing (R ⧸ I),
    letI : IsLocalRing (R ⧸ I) := hlocal
    Formalization.Books.Algebra.Unit103.IsCohenMacaulay
      (R ⧸ I) (R ⧸ I)

theorem regularSequence_extend_and_quotients_are_CohenMacaulay
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular R xs) :
    ∃ ys : List R,
      RingTheory.Sequence.IsRegular R (xs ++ ys) ∧
        (((xs ++ ys).length : ℕ∞) : WithBot ℕ∞) = ringKrullDim R ∧
          ∀ i : Fin xs.length,
            IsCohenMacaulayQuotientRing R
                (Ideal.ofList (xs.take (i.1 + 1))) ∧
              ringKrullDim
                  (R ⧸ (Ideal.ofList (xs.take (i.1 + 1)) : Ideal R)) +
                ((((i.1 + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) =
                ringKrullDim R := by
  sorry

/-! ## Prime chains and localization -/

theorem maximalPrimeChain_length_eq_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R)
    (C : Formalization.Books.Algebra.Unit60.PrimeIdealChain R)
    (hC : Formalization.Books.Algebra.Unit103.IsMaximalPrimeChain C) :
    (((C.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := by
  sorry

theorem dimension_eq_localization_add_quotient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (p : PrimeSpectrum R) :
    ringKrullDim R =
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        ringKrullDim (R ⧸ p.asIdeal) := by
  sorry

theorem isCohenMacaulayLocalRing_localization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (p : PrimeSpectrum R) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal) := by
  sorry

/- The global definition is the source's condition on all local rings. -/
def IsCohenMacaulayRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal)

theorem isCohenMacaulayRing_mPolynomial
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayRing R) (n : ℕ) :
    IsCohenMacaulayRing (MvPolynomial (Fin n) R) := by
  sorry

/-! ## Dimension shift and maximal Cohen-Macaulay resolutions -/

theorem dimension_shift_in_exact_sequence
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K M : Type u) [AddCommGroup K] [Module R K] [Module.Finite R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : IsCohenMacaulayLocalRing R) (d n : ℕ)
    (hdim : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)))
    (f : K →ₗ[R] (Fin n → R))
    (g : (Fin n → R) →ₗ[R] M)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Subsingleton M ∨
      (((localDepth R K : ℕ∞) : WithBot ℕ∞) >
          ((localDepth R M : ℕ∞) : WithBot ℕ∞)) ∨
        ((((localDepth R K : ℕ∞) : WithBot ℕ∞) =
            ((localDepth R M : ℕ∞) : WithBot ℕ∞)) ∧
          ((localDepth R M : ℕ∞) : WithBot ℕ∞) =
            (((d : ℕ∞) : WithBot ℕ∞))) := by
  sorry

/- A source-facing predicate for a finite initial segment of a finite-free
   resolution whose last displayed kernel is maximal Cohen-Macaulay. -/
def HasMCMFiniteFreeResolutionPrefix
    (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ) : Prop :=
  ∃ F : Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M),
    (∀ i : Fin n,
        Module.Free R (F.complex.X i) ∧
          Module.Finite R (F.complex.X i)) ∧
      ∃ hK : Module.Finite R (F.complex.X n),
        letI : Module.Finite R (F.complex.X n) := hK
        Formalization.Books.Algebra.Unit103.IsMaximalCohenMacaulay
            R (F.complex.X n) ∧
          (n = 0 → Function.Bijective F.augmentation.hom) ∧
            (0 < n → Function.Injective (F.complex.d n (n - 1)).hom)

theorem exists_mcm_finite_free_resolution_prefix
    (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : IsCohenMacaulayLocalRing R) (d e : ℕ)
    (hdim : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)))
    (hdepth : localDepth R M = (e : ℕ∞)) :
    ∃ n : ℕ, n + e = d ∧ HasMCMFiniteFreeResolutionPrefix R M n := by
  sorry

/-! ## Regular sequences from a local map -/

theorem exists_regularSequence_of_localRingHom
    (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (hB : IsCohenMacaulayLocalRing B)
    (hmax : IsLocalRing.maximalIdeal B =
      Ideal.radical (Ideal.map φ (IsLocalRing.maximalIdeal A))) :
    ∃ xs : List A,
      (((xs.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim B ∧
        RingTheory.Sequence.IsRegular B (xs.map φ) := by
  sorry

end

end Formalization.Books.Algebra.Unit104
