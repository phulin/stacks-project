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
  refine ⟨fun hI hI' ↦ ?_⟩
  apply DividedPowers.ext hI hI'
  intro n x hx
  apply smul_right_injective A (R := ℤ) (r := (Nat.factorial n : ℤ))
  · exact_mod_cast Nat.factorial_ne_zero n
  · simpa [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using
      (hI.factorial_mul_dpow_eq_pow (n := n) hx).trans
        (hI'.factorial_mul_dpow_eq_pow (n := n) hx).symm

private theorem natCast_mul_left_cancel_of_torsionFree
    {A : Type u} [CommRing A] [Module.IsTorsionFree ℤ A]
    {n : ℕ} (hn : n ≠ 0) {x y : A} (h : (n : A) * x = (n : A) * y) : x = y := by
  apply smul_right_injective A (R := ℤ) (r := (n : ℤ))
  · exact_mod_cast hn
  · simpa [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using h

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
  constructor
  · rintro ⟨hI⟩
    refine ⟨hI.dpow, hI.dpow_null, hI.dpow_mem, ?_⟩
    intro n x hx
    exact hI.factorial_mul_dpow_eq_pow hx
  · rintro ⟨γ, hnull, hmem, hfac⟩
    have hzero : ∀ {x}, x ∈ I → γ 0 x = 1 := by
      intro x hx
      simpa using hfac (n := 0) hx
    have hone : ∀ {x}, x ∈ I → γ 1 x = x := by
      intro x hx
      simpa using hfac (n := 1) hx
    refine ⟨{
      dpow := γ
      dpow_null := hnull
      dpow_zero := hzero
      dpow_one := hone
      dpow_mem := hmem
      dpow_add := ?_
      dpow_mul := ?_
      mul_dpow := ?_
      dpow_comp := ?_ }⟩
    · intro n x y hx hy
      apply natCast_mul_left_cancel_of_torsionFree (Nat.factorial_ne_zero n)
      rw [hfac (Ideal.add_mem _ hx hy), Finset.mul_sum, add_pow,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro k hk
      have hle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hsum : k + (n - k) = n := Nat.add_sub_of_le hle
      have hcoef : (Nat.factorial n : A) =
          (Nat.choose n k : A) * (Nat.factorial k : A) *
            (Nat.factorial (n - k) : A) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul]
        exact congrArg (fun z : ℕ => (z : A))
          (Nat.choose_mul_factorial_mul_factorial hle).symm
      rw [hcoef]
      change x ^ k * y ^ (n - k) * (Nat.choose n k : A) =
        (Nat.choose n k : A) * (Nat.factorial k : A) *
          (Nat.factorial (n - k) : A) * (γ k x * γ (n - k) y)
      rw [← hfac hx, ← hfac hy]
      ring
    · intro n a x hx
      apply natCast_mul_left_cancel_of_torsionFree (Nat.factorial_ne_zero n)
      calc
        (Nat.factorial n : A) * γ n (a * x) = (a * x) ^ n := hfac (Ideal.mul_mem_left _ _ hx)
        _ = a ^ n * x ^ n := by rw [mul_pow]
        _ = a ^ n * ((Nat.factorial n : A) * γ n x) := by rw [hfac hx]
        _ = (Nat.factorial n : A) * (a ^ n * γ n x) := by ring
    · intro m n x hx
      apply natCast_mul_left_cancel_of_torsionFree (Nat.factorial_ne_zero (m + n))
      have hchoose : Nat.choose (m + n) m = Nat.choose (m + n) n :=
        Nat.choose_symm_of_eq_add rfl
      have hcoef : (Nat.factorial (m + n) : A) =
          (Nat.choose (m + n) m : A) * (Nat.factorial m : A) *
            (Nat.factorial n : A) := by
        rw [hchoose]
        rw [← Nat.cast_mul, ← Nat.cast_mul]
        exact congrArg (fun z : ℕ => (z : A))
          (Nat.add_choose_mul_factorial_mul_factorial m n).symm
      calc
        (Nat.factorial (m + n) : A) * (γ m x * γ n x) =
            (Nat.choose (m + n) m : A) *
              ((Nat.factorial m : A) * γ m x) *
                ((Nat.factorial n : A) * γ n x) := by
                  rw [hcoef]
                  ring
        _ = (Nat.choose (m + n) m : A) * (x ^ m * x ^ n) := by
          rw [hfac hx, hfac hx]
          ring
        _ = (Nat.choose (m + n) m : A) * x ^ (m + n) := by
          rw [← pow_add]
        _ = (Nat.choose (m + n) m : A) *
              ((Nat.factorial (m + n) : A) * γ (m + n) x) := by
          rw [hfac hx]
        _ = (Nat.factorial (m + n) : A) *
              ((Nat.choose (m + n) m : A) * γ (m + n) x) := by ring
    · intro m n x hn hx
      apply natCast_mul_left_cancel_of_torsionFree (Nat.factorial_ne_zero (m * n))
      have hcoef : (Nat.factorial (m * n) : A) =
          (Nat.uniformBell m n : A) * (Nat.factorial n : A) ^ m *
            (Nat.factorial m : A) := by
        rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul]
        exact congrArg (fun z : ℕ => (z : A)) (Nat.uniformBell_mul_eq m hn).symm
      calc
        (Nat.factorial (m * n) : A) * γ m (γ n x) =
            (Nat.uniformBell m n : A) * (Nat.factorial n : A) ^ m *
              ((Nat.factorial m : A) * γ m (γ n x)) := by
                rw [hcoef]
                ring
        _ = (Nat.uniformBell m n : A) *
              ((Nat.factorial n : A) * γ n x) ^ m := by
                rw [hfac (hmem hn hx)]
                ring
        _ = (Nat.uniformBell m n : A) * x ^ (m * n) := by
                rw [hfac hx, ← pow_mul, mul_comm m n]
        _ = (Nat.uniformBell m n : A) *
              ((Nat.factorial (m * n) : A) * γ (m * n) x) := by
                rw [hfac (n := m * n) hx]
        _ = (Nat.factorial (m * n) : A) *
              ((Nat.uniformBell m n : A) * γ (m * n) x) := by ring

private theorem exists_factorial_multiple_of_span
    {A : Type u} [CommRing A] {I : Ideal A} {S : Set A}
    (hspan : I = Ideal.span S)
    (hgen : ∀ x ∈ S, ∀ n : ℕ, 0 < n →
      x ^ n ∈ Ideal.span ({(Nat.factorial n : A)} : Set A) * I) :
    ∀ {x : A}, x ∈ I → ∀ {n : ℕ}, 0 < n →
      ∃ y ∈ I, (Nat.factorial n : A) * y = x ^ n := by
  intro x hx
  rw [hspan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      intro n hn
      exact Ideal.mem_span_singleton_mul.mp (hgen x hx n hn)
  | zero =>
      intro n hn
      exact ⟨0, I.zero_mem, by simp [zero_pow (ne_of_gt hn)]⟩
  | add x y hx hy hx' hy' =>
      intro n hn
      let J : Ideal A := Ideal.span ({(Nat.factorial n : A)} : Set A) * I
      have hterm : ∀ k ∈ Finset.range (n + 1),
          x ^ k * y ^ (n - k) * (Nat.choose n k : A) ∈ J := by
        intro k hk
        have hle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        by_cases hk0 : k = 0
        · subst hk0
          rcases hy' hn with ⟨z, hz, hz_eq⟩
          refine Ideal.mem_span_singleton_mul.mpr ⟨z, hz, ?_⟩
          simpa using hz_eq
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          by_cases hkn : n - k = 0
          · rcases hx' hn with ⟨z, hz, hz_eq⟩
            refine Ideal.mem_span_singleton_mul.mpr ⟨z, hz, ?_⟩
            have hk_eq : k = n := Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hkn)
            subst k
            simp only [Nat.sub_self, pow_zero, mul_one,
              Nat.choose_self, Nat.cast_one]
            simpa using hz_eq
          · rcases hx' hkpos with ⟨u, hu, hu_eq⟩
            rcases hy' (Nat.pos_of_ne_zero hkn) with ⟨v, hv, hv_eq⟩
            refine Ideal.mem_span_singleton_mul.mpr
              ⟨u * v, I.mul_mem_left u hv, ?_⟩
            have hcoef := Nat.choose_mul_factorial_mul_factorial hle
            have hcoefA := congrArg (fun q : ℕ => (q : A)) hcoef
            calc
              (Nat.factorial n : A) * (u * v) =
                  ((Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) : ℕ) : A) *
                    (u * v) := by rw [hcoefA]
              _ = (Nat.choose n k : A) * (Nat.factorial k : A) *
                    (Nat.factorial (n - k) : A) * (u * v) := by
                      push_cast
                      rfl
              _ =
                  (Nat.choose n k : A) *
                    ((Nat.factorial k : A) * u) *
                      ((Nat.factorial (n - k) : A) * v) := by ring
              _ = (Nat.choose n k : A) * x ^ k * y ^ (n - k) := by
                    rw [hu_eq, hv_eq]
              _ = x ^ k * y ^ (n - k) * (Nat.choose n k : A) := by ring
      rw [add_pow]
      exact Ideal.mem_span_singleton_mul.mp (show
        (∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * (Nat.choose n m : A)) ∈ J from
          J.sum_mem hterm)
  | smul a x hx hx' =>
      intro n hn
      rcases hx' hn with ⟨z, hz, hz_eq⟩
      refine ⟨a ^ n * z, I.mul_mem_left _ hz, ?_⟩
      rw [smul_eq_mul, mul_pow, ← hz_eq]
      ring

theorem exists_dividedPowers_iff_factorial_generators
    {A : Type u} [CommRing A] {I : Ideal A}
    [Module.IsTorsionFree ℤ A] :
    Nonempty (DividedPowers I) ↔
      ∃ S : Set A, I = Ideal.span S ∧
        ∀ x ∈ S, ∀ n : ℕ, 0 < n →
          x ^ n ∈ Ideal.span ({(Nat.factorial n : A)} : Set A) * I := by
  constructor
  · rintro ⟨hI⟩
    refine ⟨(I : Set A), (Ideal.span_eq I).symm, ?_⟩
    intro x hx n hn
    refine Ideal.mem_span_singleton_mul.mpr
      ⟨hI.dpow n x, hI.dpow_mem (Nat.ne_of_gt hn) hx, ?_⟩
    exact hI.factorial_mul_dpow_eq_pow hx
  · rintro ⟨S, hspan, hgen⟩
    classical
    have hpow : ∀ {x : A}, x ∈ I → ∀ {n : ℕ}, 0 < n →
        ∃ y ∈ I, (Nat.factorial n : A) * y = x ^ n :=
      exists_factorial_multiple_of_span hspan hgen
    let γ : ℕ → A → A := fun n x ↦
      if hx : x ∈ I then
        if hn : n = 0 then 1 else
          Classical.choose (hpow hx (Nat.pos_of_ne_zero hn))
      else 0
    have hnull : ∀ {n x}, x ∉ I → γ n x = 0 := by
      intro n x hx
      simp [γ, hx]
    have hmem : ∀ {n x}, n ≠ 0 → x ∈ I → γ n x ∈ I := by
      intro n x hn hx
      simp only [γ, dif_pos hx, dif_neg hn]
      exact (Classical.choose_spec (hpow hx (Nat.pos_of_ne_zero hn))).1
    have hfac : ∀ {n x}, x ∈ I →
        (Nat.factorial n : A) * γ n x = x ^ n := by
      intro n x hx
      by_cases hn : n = 0
      · simp [γ, hx, hn]
      · simp only [γ, dif_pos hx, dif_neg hn]
        exact (Classical.choose_spec (hpow hx (Nat.pos_of_ne_zero hn))).2
    exact exists_dividedPowers_iff_factorial_data.mpr ⟨γ, hnull, hmem, hfac⟩

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
