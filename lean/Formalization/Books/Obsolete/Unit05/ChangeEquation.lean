import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic

/-!
# Obsolete, Chapter 5: lemmas related to Zariski's Main Theorem

This file records the three elementary integral-equation lemmas at the start
of the source section.  Polynomial maps are represented by `Polynomial` and
the integral-element assertions use Mathlib's canonical `RingHom.IsIntegralElem`.
-/

namespace Formalization.Books.Obsolete.Unit05

open Polynomial
open Set

universe u v

noncomputable section

/-! ## Changing the polynomial coordinate -/

/- The coefficient map is the restriction of `φ` along `Polynomial.C`, while
   the new variable is sent to `φ (a * X)`. -/
def changeEquationMap
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R[X] →+* S) (a : R) : R[X] →+* S :=
  Polynomial.eval₂RingHom
    (φ.comp (Polynomial.C : R →+* R[X]))
    (φ (Polynomial.C a * Polynomial.X))

/- The source's `φ(a)` is the image of the constant polynomial `C a`. -/
theorem change_equation_multiply
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R[X] →+* S) (t : S) (ht : φ.IsIntegralElem t) :
    ∃ ℓ : ℕ, ∀ a : R,
      (changeEquationMap φ a).IsIntegralElem
        (φ (Polynomial.C a) ^ ℓ * t) := by
  sorry

/-! ## Making an integral equation less trivial -/

/- For `1 ≤ i ≤ n`, this is the closed form of the recursively defined
   coefficient `u_i = u_{i+1} t + φ(a_i)`.  It also makes sense for all
   natural `i`, with an empty sum when `i > n`. -/
def integralRelationU
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (a : ℕ → R) (n i : ℕ) : S :=
  ∑ j ∈ Finset.Icc i n, φ (a j) * t ^ (j - i)

/- The finite coefficient set `(φ(a_0), ..., φ(a_n))`. -/
def integralRelationCoefficientSet
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : ℕ → R) (n : ℕ) : Set S :=
  {x | ∃ i, i ≤ n ∧ x = φ (a i)}

/- The set of the recursively defined elements `u_n, ..., u_1`. -/
def integralRelationUSet
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (a : ℕ → R) (n : ℕ) : Set S :=
  {x | ∃ i, 1 ≤ i ∧ i ≤ n ∧ x = integralRelationU φ t a n i}

theorem make_integral_less_trivial
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (a : ℕ → R) (n : ℕ)
    (hrel : ∑ i ∈ Finset.range (n + 1), φ (a i) * t ^ i = 0) :
    (∀ i, 1 ≤ i → i ≤ n →
      φ.IsIntegralElem (integralRelationU φ t a n i) ∧
        φ.IsIntegralElem (integralRelationU φ t a n i * t)) ∧
      Ideal.span (integralRelationCoefficientSet φ a n) =
        Ideal.span (integralRelationUSet φ t a n) := by
  sorry

theorem make_integral_not_in_ideal
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (a : ℕ → R) (n : ℕ)
    (hrel : ∑ i ∈ Finset.range (n + 1), φ (a i) * t ^ i = 0)
    (J : Ideal S) (hnot : ∃ i, i ≤ n ∧ φ (a i) ∉ J) :
    ∃ u : S, u ∉ J ∧ φ.IsIntegralElem u ∧ φ.IsIntegralElem (u * t) := by
  sorry

end

end Formalization.Books.Obsolete.Unit05
