import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Set.Function
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Commutative Algebra, Chapter 32: Locally nilpotent ideals

The chapter reuses `Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal`
for the elementwise definition and Mathlib's `IsNilpotent` for nilpotent
ideals.  The declarations below record the chapter-specific examples and
consequences in source order.
-/

namespace Formalization.Books.Algebra.Unit32

open Set

universe u

noncomputable section

/-! ## Definition and example -/

/- The source's two definitions are already represented by the earlier
chapter's `locallyNilpotentIdeal` and Mathlib's `IsNilpotent` predicate. -/

/- The source uses the indexing convention `n ≥ 1` implicitly.  With Lean's
`ℕ` starting at zero, the exponent is written `n + 1`; this is the smallest
correction that makes the displayed example nontrivial. -/
def locallyNilpotentExampleBaseIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial ℕ k) :=
  Ideal.span (Set.range fun n : ℕ =>
    (MvPolynomial.X n : MvPolynomial ℕ k) ^ (n + 1))

def locallyNilpotentExampleIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial ℕ k ⧸ locallyNilpotentExampleBaseIdeal k) :=
  Ideal.map (Ideal.Quotient.mk (locallyNilpotentExampleBaseIdeal k))
    (Ideal.span (Set.range fun n : ℕ =>
      (MvPolynomial.X n : MvPolynomial ℕ k)))

theorem locallyNilpotentExample_not_mem_baseIdeal
    (k : Type u) [Field k] (n : ℕ) :
    (MvPolynomial.X (n + 1) : MvPolynomial ℕ k) ^ n ∉
      locallyNilpotentExampleBaseIdeal k := by
  sorry

theorem locallyNilpotentExample_pow_ne_bot
    (k : Type u) [Field k] (n : ℕ) :
    (locallyNilpotentExampleIdeal k) ^ n ≠
      (⊥ : Ideal (MvPolynomial ℕ k ⧸ locallyNilpotentExampleBaseIdeal k)) := by
  sorry

theorem locallyNilpotent_not_nilpotent_example (k : Type u) [Field k] :
    Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal
        (locallyNilpotentExampleIdeal k) ∧
      ¬ IsNilpotent (locallyNilpotentExampleIdeal k) := by
  sorry

/-! ## Basic consequences -/

theorem locallyNilpotentIdeal_map
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I) :
    Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal (I.map φ) := by
  sorry

theorem isUnit_iff_isUnit_quotient_of_locallyNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I) (x : R) :
    IsUnit x ↔ IsUnit (Ideal.Quotient.mk I x) := by
  sorry

/- The source's Noetherian power assertion and its stated consequence. -/
theorem exists_pow_le_of_le_radical_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hJ : J ≤ I.radical) :
    ∃ n : ℕ, J ^ n ≤ I := by
  sorry

theorem locallyNilpotentIdeal_iff_isNilpotent_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I ↔
      IsNilpotent I := by
  sorry

/-! ## Lifting idempotents -/

def quotientIdempotentMap
    {R : Type u} [CommRing R] (I : Ideal R) :
    {e : R // IsIdempotentElem e} →
      {e : R ⧸ I // IsIdempotentElem e} :=
  fun e => ⟨Ideal.Quotient.mk I e.1, e.2.map (Ideal.Quotient.mk I)⟩

theorem quotient_idempotentMap_bijective
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I) :
    Function.Bijective (quotientIdempotentMap I) := by
  sorry

/- The displayed Newton step in the source's second proof is recorded as a
usable identity. -/
theorem idempotent_lift_step_formula
    {R : Type u} [CommRing R] (e : R) :
    (e - (2 * e - 1) * (e ^ 2 - e) = 3 * e ^ 2 - 2 * e ^ 3) ∧
      ((3 * e ^ 2 - 2 * e ^ 3) ^ 2 - (3 * e ^ 2 - 2 * e ^ 3) =
        (4 * e ^ 2 - 4 * e - 3) * (e ^ 2 - e) ^ 2) := by
  sorry

theorem idempotent_sub_cube_eq
    {R : Type u} [CommRing R] {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) :
    (e₁ - e₂) ^ 3 = e₁ - e₂ := by
  sorry

theorem idempotent_sub_odd_pow_eq
    {R : Type u} [CommRing R] {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    {k : ℕ} (hk : Odd k) :
    (e₁ - e₂) ^ k = e₁ - e₂ := by
  sorry

theorem exists_idempotent_lift_polynomial
    {A : Type u} [Ring A] (e : A) (h : IsNilpotent (e ^ 2 - e)) :
    ∃ e' : A, IsIdempotentElem e' ∧
      ∃ (s : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℤ),
        e' = e + (e ^ 2 - e) *
          (∑ ij ∈ s, (a ij : A) * e ^ ij.1 * (e ^ 2 - e) ^ ij.2) := by
  sorry

/-! ## Nth roots -/

/- The notation `1 + I` is represented by the equivalent set of elements
whose difference from `1` lies in `I`. -/
def oneAddIdealSet {R : Type u} [CommRing R] (I : Ideal R) : Set R :=
  {x | x - 1 ∈ I}

theorem nth_power_bijective_on_oneAddIdealSet
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (n : ℕ) (hn : 1 ≤ n) (hnI : IsUnit ((n : R ⧸ I))) :
    Set.BijOn (fun x : R => x ^ n) (oneAddIdealSet I) (oneAddIdealSet I) := by
  sorry

theorem isNthPower_iff_isNthPower_quotient_of_locallyNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (n : ℕ) (hn : 1 ≤ n) (hnI : IsUnit ((n : R ⧸ I))) {x : R}
    (hx : IsUnit x) :
    (∃ y : R, x = y ^ n) ↔
      ∃ y : R, Ideal.Quotient.mk I x = (Ideal.Quotient.mk I y) ^ n := by
  sorry

end

end Formalization.Books.Algebra.Unit32
