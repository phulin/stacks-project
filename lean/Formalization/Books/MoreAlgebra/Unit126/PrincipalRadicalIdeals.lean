/-
# More on Algebra, Chapter 126: Principal radical ideals
-/

import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit52.Length
import Formalization.Books.Algebra.Unit59.NoetherianLocalRings
import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit105.CatenaryRings
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
This file records the definitions and theorem interfaces in the source chapter.
Length is represented by the existing natural-valued wrapper around
`Module.length`, while systems of parameters, normality, catenarity, radical
ideals, and reduced quotients use the established project and Mathlib APIs.
-/

namespace Formalization.Books.MoreAlgebra.Unit126

noncomputable section

open Set
open Formalization.Books.Algebra.Unit60

/-! ## Quotient lengths -/

/-- The natural-valued length of a quotient by an ideal. -/
def idealQuotientLength {R : Type*} [CommRing R] (I : Ideal R) : ℕ :=
  Formalization.Books.Algebra.Unit59.moduleLengthNat (R := R) (M := R ⧸ I)

/-- The function `n ↦ length (R / x^n R)` used in the first lemma. -/
def principalPowerQuotientLength
    {R : Type*} [CommRing R] (x : R) (n : ℕ) : ℕ :=
  idealQuotientLength (Ideal.span ({x ^ n} : Set R))

/-! ## One-dimensional length estimates -/

/-- Lengths of powers of a parameter grow at most linearly, with equality for
nonzerodivisors. -/
theorem lemma_polypoly
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ∉ p) :
    (∀ n : ℕ,
      principalPowerQuotientLength x n ≤
        n * principalPowerQuotientLength x 1) ∧
      (x ∈ nonZeroDivisors R →
        ∀ n : ℕ,
          principalPowerQuotientLength x n =
            n * principalPowerQuotientLength x 1) := by
  sorry

/-! ## Minimal primes in dimension one -/

/-- The number of minimal primes is bounded by the length of a principal
parameter quotient. -/
theorem lemma_minprimespoly
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ∉ p) :
    Nat.card {p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes} ≤
      principalPowerQuotientLength x 1 := by
  sorry

/-! ## Extending a parameter sequence -/

/-- A non-minimal-prime element can be completed to parameters, with the
other parameters chosen in any prescribed power of the maximal ideal. -/
theorem lemma_sopexists
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hd : 1 < d)
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, f ∉ p)
    (k : ℕ) :
    ∃ (g : Fin d → R) (i : Fin d),
      g i = f ∧
        (∀ j : Fin d, j ≠ i → g j ∈ (IsLocalRing.maximalIdeal R) ^ k) ∧
          IsSystemOfParameters R d g := by
  sorry

/-! ## Stability of parameter quotients -/

/-- In dimension two, a parameter pair and its sufficiently high-order
perturbations have the same quotient length. -/
theorem lemma_syspar
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 2)
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, f ∉ p) :
    ∃ (g : R) (N : ℕ),
      IsSystemOfParameters R 2 ![f, g] ∧
        ∀ h ∈ (IsLocalRing.maximalIdeal R) ^ N,
          IsSystemOfParameters R 2 ![f + h, g] ∧
            idealQuotientLength (Ideal.span (Set.range ![f, g])) =
              idealQuotientLength (Ideal.span (Set.range ![f + h, g])) := by
  sorry

/-! ## Reduced principal quotients in dimension two -/

/-- Finitely many distinct height-one primes in a two-dimensional normal local
domain contain a nonzero element generating a radical ideal. -/
theorem lemma_radical_element
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : Formalization.Books.Algebra.Unit37.IsNormalDomain R)
    (hdim : ringKrullDim R = 2)
    (r : ℕ) (p : Fin r → Ideal R)
    (hp : ∀ i, (p i).IsPrime ∧ (p i).height = 1)
    (hdistinct : ∀ ⦃i j : Fin r⦄, i ≠ j → p i ≠ p j) :
    ∃ f : R,
      f ≠ 0 ∧ (∀ i, f ∈ p i) ∧
        IsReduced (R ⧸ Ideal.span ({f} : Set R)) := by
  sorry

/-- A nonzero element in the maximal ideal divides a power of a reduced
principal element. -/
theorem lemma_divides_radical
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Formalization.Books.Algebra.Unit37.IsNormalDomain A)
    (hdim : ringKrullDim A = 2)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (ha0 : a ≠ 0) :
    ∃ c : A,
      IsReduced (A ⧸ Ideal.span ({c} : Set A)) ∧
        ∃ n : ℕ, a ∣ c ^ n := by
  sorry

/-! ## Multiplicity -/

/-- The multiplicity of a parameter ideal is bounded by its colength. -/
theorem lemma_multiplicity
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = d)
    (g : Fin d → R) (hg : IsSystemOfParameters R d g) :
    ∀ (e : ℕ) (P : Polynomial ℚ),
      Formalization.Books.Algebra.Unit59.IsEventuallyRationalPolynomial
          (Formalization.Books.Algebra.Unit59.idealCumulativeHilbertFunctionInteger
            (Ideal.span (Set.range g)) R) P →
        P.degree = d →
          P.leadingCoeff = (e : ℚ) / (Nat.factorial d : ℚ) →
            e ≤ idealQuotientLength (Ideal.span (Set.range g)) := by
  sorry

/-! ## Minimal primes in higher dimension -/

/-- The number of top-dimensional minimal primes is bounded by the length of
a parameter-ideal quotient. -/
theorem lemma_minprimespolyhigher
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = d)
    (g : Fin d → R) (hg : IsSystemOfParameters R d g) :
    Nat.card
        {p : Ideal R //
          p ∈ (⊥ : Ideal R).minimalPrimes ∧
            ringKrullDim (R ⧸ p) = d} ≤
      idealQuotientLength (Ideal.span (Set.range g)) := by
  sorry

/-! ## Stable parameter systems in higher dimension -/

/-- In any dimension, a parameter system beginning with a non-minimal-prime
element is stable under sufficiently high-order perturbations of that entry. -/
theorem lemma_sysparhigher
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = d)
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, f ∉ p) :
    ∃ (g : Fin d → R) (i : Fin d) (N : ℕ),
      g i = f ∧
        IsSystemOfParameters R d g ∧
          ∀ h ∈ (IsLocalRing.maximalIdeal R) ^ N,
            IsSystemOfParameters R d (Function.update g i (f + h)) ∧
              idealQuotientLength (Ideal.span (Set.range g)) =
                idealQuotientLength
                  (Ideal.span (Set.range (Function.update g i (f + h)))) := by
  sorry

/-! ## The principal radical ideal theorem -/

/-- A nonzero radical ideal in a catenary Noetherian normal local domain
contains a nonzero element generating a radical ideal. -/
theorem proposition_propdimd
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : Formalization.Books.Algebra.Unit37.IsNormalDomain R)
    (hcat : Formalization.Books.Algebra.Unit105.IsCatenaryRing R)
    (J : Ideal R) (hJ : J.IsRadical) (hJ0 : J ≠ ⊥) :
    ∃ f : R,
      f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ Ideal.span ({f} : Set R)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit126
