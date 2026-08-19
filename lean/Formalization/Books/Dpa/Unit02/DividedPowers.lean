import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Divided Power Algebra, Chapter 2: Divided powers

Mathlib's `DividedPowers` is the canonical formalization of a divided power
structure.  It stores `dpow : ℕ → A → A`, extends the positive operations by
zero outside the ideal, and records exactly the five divided-power identities
used in the source.  The declarations below use that API directly; in
particular, no parallel divided-power structure is introduced here.
-/

namespace Formalization.Books.Dpa.Unit02

open Finset Nat Ideal

universe u v

noncomputable section

/-! ## Definition and the integral coefficients -/

/- The source convention `0! = 1` is Mathlib's `Nat.factorial_zero`. -/
theorem zero_factorial : Nat.factorial 0 = 1 := by
  exact Nat.factorial_zero

/- The two rational-looking coefficients in the source are natural numbers.
The first divisibility is Mathlib's factorial divisibility theorem; the second
is recorded in the form needed by the divided-power composition coefficient. -/
theorem divided_power_coefficients_are_integral (n m : ℕ) :
    Nat.factorial n * Nat.factorial m ∣ Nat.factorial (n + m) ∧
      Nat.factorial n * (Nat.factorial m) ^ n ∣ Nat.factorial (n * m) := by
  constructor
  · exact Nat.factorial_mul_factorial_dvd_factorial_add n m
  · sorry

/-!
The source's definition is represented by `DividedPowers I`.  Its fields are
`dpow_null`, `dpow_zero`, `dpow_one`, `dpow_mem`, `dpow_add`, `dpow_mul`,
`mul_dpow`, and `dpow_comp`; the last three fields contain the binomial and
composition coefficients as `Nat.choose` and `Nat.uniformBell`.
-/

/-! ## The basic factorial identity and the torsion-free characterizations -/

theorem factorial_mul_dpow_eq_pow {A : Type u} [CommSemiring A]
    {I : Ideal A} (hI : DividedPowers I) {n : ℕ} {x : A} (hx : x ∈ I) :
    (Nat.factorial n : A) * hI.dpow n x = x ^ n := by
  exact hI.factorial_mul_dpow_eq_pow hx

theorem dividedPowers_subsingleton_of_torsionFree
    {A : Type u} [CommRing A] {I : Ideal A}
    [Module.IsTorsionFree ℤ A] :
    Subsingleton (DividedPowers I) := by
  sorry

/-!
For the source's factorial criterion, `γ` is represented by its zero-extended
function on `A`.  The membership clause says that its positive values on `I`
land back in `I`; the factorial equation is the source's displayed condition.
-/
theorem exists_dividedPowers_iff_factorial_data
    {A : Type u} [CommRing A] {I : Ideal A}
    [Module.IsTorsionFree ℤ A] :
    Nonempty (DividedPowers I) ↔
      ∃ γ : ℕ → A → A,
        (∀ {n x}, x ∉ I → γ n x = 0) ∧
        (∀ {n x}, n ≠ 0 → x ∈ I → γ n x ∈ I) ∧
        (∀ {n x}, x ∈ I → (Nat.factorial n : A) * γ n x = x ^ n) := by
  sorry

theorem exists_dividedPowers_iff_factorial_generators
    {A : Type u} [CommRing A] {I : Ideal A}
    [Module.IsTorsionFree ℤ A] :
    Nonempty (DividedPowers I) ↔
      ∃ S : Set A, I = Ideal.span S ∧
        ∀ x ∈ S, ∀ n : ℕ, 0 < n →
          x ^ n ∈ Ideal.span ({(Nat.factorial n : A)} : Set A) * I := by
  sorry

/-! ## The prime-localized example -/

/-- A ring in which all integers prime to `p` are units. -/
def IsZLocalizedAtPrime (p : ℕ) (A : Type u) [CommRing A] : Prop :=
  ∀ n : ℤ, ¬(p : ℤ) ∣ n → IsUnit (n : A)

/-- The ideal denoted by `pA` in the source. -/
def primeMultipleIdeal {A : Type u} [CommRing A] (p : ℕ) : Ideal A :=
  Ideal.span ({(p : A)} : Set A)

/-- The canonical divided powers on `pA` in a `ℤ_(p)`-algebra.

The source writes the operation on `x = p * a` as `p^n / n! * a^n`.
The factorial identity is the division-free Lean interface for that formula. -/
theorem exists_dividedPowers_primeMultipleIdeal
    {A : Type u} [CommRing A] {p : ℕ} (hp : Nat.Prime p)
    (hA : IsZLocalizedAtPrime p A) :
    ∃ hI : DividedPowers (primeMultipleIdeal p),
      ∀ {n x}, x ∈ primeMultipleIdeal p →
        (Nat.factorial n : A) * hI.dpow n x = x ^ n := by
  sorry

/-! The source's observation at zero is an existing Mathlib theorem. -/
theorem dpow_pos_zero {A : Type u} [CommSemiring A] {I : Ideal A}
    (hI : DividedPowers I) {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := by
  exact hI.dpow_eval_zero hn

/-! ## Checking the divided-power identities on generators -/

/-!
This is the source's generator-checking lemma in the canonical `dpow` API.
The operations satisfy the zero, one, scalar, and addition identities on all
of `I`; the product and composition identities are required only on a set of
ideal generators.  The conclusion supplies the corresponding
`DividedPowers` structure and identifies its operations with `γ`.
-/
theorem exists_dividedPowers_of_generator_data
    {A : Type u} [CommSemiring A] {I : Ideal A} (S : Set A)
    (hspan : I = Ideal.span S) (γ : ℕ → A → A)
    (hnull : ∀ {n x}, x ∉ I → γ n x = 0)
    (hzero : ∀ {x}, x ∈ I → γ 0 x = 1)
    (hone : ∀ {x}, x ∈ I → γ 1 x = x)
    (hmem : ∀ {n x}, n ≠ 0 → x ∈ I → γ n x ∈ I)
    (hmul : ∀ {n a x}, x ∈ I → γ n (a * x) = a ^ n * γ n x)
    (hadd : ∀ {n x y}, x ∈ I → y ∈ I →
      γ n (x + y) = (antidiagonal n).sum fun k ↦ γ k.1 x * γ k.2 y)
    (hprod : ∀ {m n x}, x ∈ S →
      γ m x * γ n x = (Nat.choose (m + n) m : A) * γ (m + n) x)
    (hcomp : ∀ {m n x}, n ≠ 0 → x ∈ S →
      γ m (γ n x) = (Nat.uniformBell m n : A) * γ (m * n) x) :
    ∃ hI : DividedPowers I, ∀ {n x}, hI.dpow n x = γ n x := by
  sorry

/-!
Mathlib already proves the canonical uniqueness statement from generators;
this is the reusable interface for the source's generator argument.
-/
theorem dividedPowers_eq_of_generators
    {A : Type u} [CommSemiring A] {I : Ideal A} {S : Set A}
    (hspan : I = Ideal.span S) (hI hI' : DividedPowers I)
    (heq : ∀ {n : ℕ}, ∀ x ∈ S, hI.dpow n x = hI'.dpow n x) :
    hI' = hI := by
  exact hI.dpow_eq_from_gens hI' hspan heq

/-! ## Two ideals -/

theorem dividedPowers_agree_on_product
    {A : Type u} [CommSemiring A] {I J : Ideal A}
    (hI : DividedPowers I) (hJ : DividedPowers J)
    {n : ℕ} {x : A} (hx : x ∈ I • J) :
    hI.dpow n x = hJ.dpow n x := by
  exact hI.coincide_on_smul hJ hx

/-!
The source's second assertion glues compatible structures on `I` and `J`.
The displayed formula is included in the witness property, while the
restriction conditions are stated pointwise on `I` and `J` because Mathlib's
structure stores operations on the ambient ring.
-/
theorem exists_unique_dividedPowers_sup
    {A : Type u} [CommSemiring A] {I J : Ideal A}
    (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIJ : ∀ {n : ℕ} {x : A}, x ∈ I ⊓ J → hI.dpow n x = hJ.dpow n x) :
    ∃! h : DividedPowers (I ⊔ J),
      (∀ {n x}, x ∈ I → h.dpow n x = hI.dpow n x) ∧
      (∀ {n x}, x ∈ J → h.dpow n x = hJ.dpow n x) ∧
      (∀ {n x y}, x ∈ I → y ∈ J →
        h.dpow n (x + y) =
          (antidiagonal n).sum fun k ↦ hI.dpow k.1 x * hJ.dpow k.2 y) := by
  sorry

/-! ## The nilpotence criterion -/

theorem locallyNilpotentIdeal_iff_prime_isNilpotent
    {A : Type u} [CommRing A] {p : ℕ} (hp : Nat.Prime p)
    (I : Ideal A) (hI : DividedPowers I)
    (hquot : IsNilpotent (p : A ⧸ I)) :
    Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I ↔
      IsNilpotent (p : A) := by
  sorry

end
end Formalization.Books.Dpa.Unit02
