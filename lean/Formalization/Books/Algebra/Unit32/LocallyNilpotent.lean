import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Ring.Parity
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

universe u v

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

private theorem locallyNilpotentIdeal_span_range
    {R : Type u} [CommRing R] {ι : Type v} (f : ι → R)
    (hf : ∀ i, IsNilpotent (f i)) :
    Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal
      (Ideal.span (Set.range f)) := by
  intro x hx
  obtain ⟨c, hc⟩ :=
    (Finsupp.mem_ideal_span_range_iff_exists_finsupp).mp hx
  rw [← hc]
  apply isNilpotent_sum
  intro i hi
  simpa [smul_eq_mul] using (hf i).smul (c i)

theorem locallyNilpotentExample_not_mem_baseIdeal
    (k : Type u) [Field k] (n : ℕ) :
    (MvPolynomial.X (n + 1) : MvPolynomial ℕ k) ^ n ∉
      locallyNilpotentExampleBaseIdeal k := by
  intro h
  let φ : MvPolynomial ℕ k →+* MvPolynomial ℕ k :=
    MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial ℕ k)
      (fun i : ℕ => if i = n + 1 then MvPolynomial.X 0 else 0)
  let J : Ideal (MvPolynomial ℕ k) :=
    Ideal.span ({(MvPolynomial.X 0 : MvPolynomial ℕ k) ^ (n + 2)} : Set _)
  have hle : locallyNilpotentExampleBaseIdeal k ≤ J.comap φ := by
    rw [locallyNilpotentExampleBaseIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change φ ((MvPolynomial.X i : MvPolynomial ℕ k) ^ (i + 1)) ∈ J
    by_cases hi : i = n + 1
    · subst i
      simp [φ, J, Nat.add_assoc]
    · simp [φ, J, hi]
  have hmem : (MvPolynomial.X 0 : MvPolynomial ℕ k) ^ n ∈ J := by
    simpa [J, φ, Ideal.mem_comap] using hle h
  have hdvd :
      (MvPolynomial.X 0 : MvPolynomial ℕ k) ^ (n + 2) ∣
        (MvPolynomial.X 0 : MvPolynomial ℕ k) ^ n :=
    (Ideal.mem_span_singleton.mp hmem)
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial]
    at hdvd
  rcases (MvPolynomial.monomial_dvd_monomial.mp hdvd) with ⟨hord, _⟩
  rcases hord with hzero | hord
  · exact one_ne_zero hzero
  · simp at hord

theorem locallyNilpotentExample_pow_ne_bot
    (k : Type u) [Field k] (n : ℕ) :
    (locallyNilpotentExampleIdeal k) ^ n ≠
      (⊥ : Ideal (MvPolynomial ℕ k ⧸ locallyNilpotentExampleBaseIdeal k)) := by
  intro hzero
  have hmemX :
      Ideal.Quotient.mk (locallyNilpotentExampleBaseIdeal k)
          (MvPolynomial.X (n + 1) : MvPolynomial ℕ k) ∈
        locallyNilpotentExampleIdeal k := by
    rw [locallyNilpotentExampleIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨n + 1, rfl⟩)
  have hmemPow :
      (Ideal.Quotient.mk (locallyNilpotentExampleBaseIdeal k)
          (MvPolynomial.X (n + 1) : MvPolynomial ℕ k)) ^ n ∈
        (locallyNilpotentExampleIdeal k) ^ n :=
    Ideal.pow_mem_pow hmemX n
  have hz :
      (Ideal.Quotient.mk (locallyNilpotentExampleBaseIdeal k)
          (MvPolynomial.X (n + 1) : MvPolynomial ℕ k)) ^ n = 0 := by
    apply Ideal.mem_bot.mp
    rw [← hzero]
    exact hmemPow
  apply locallyNilpotentExample_not_mem_baseIdeal k n
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_pow] using hz

theorem locallyNilpotent_not_nilpotent_example (k : Type u) [Field k] :
    Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal
        (locallyNilpotentExampleIdeal k) ∧
      ¬ IsNilpotent (locallyNilpotentExampleIdeal k) := by
  constructor
  · have hset :
        Ideal.Quotient.mk (locallyNilpotentExampleBaseIdeal k) ''
            Set.range (fun i : ℕ => (MvPolynomial.X i : MvPolynomial ℕ k)) =
          Set.range (fun i : ℕ =>
            Ideal.Quotient.mk (locallyNilpotentExampleBaseIdeal k)
              (MvPolynomial.X i : MvPolynomial ℕ k)) := by
      ext z
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, rfl⟩
    rw [locallyNilpotentExampleIdeal, Ideal.map_span, hset]
    apply locallyNilpotentIdeal_span_range
    intro i
    refine ⟨i + 1, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  · intro hnil
    rcases hnil with ⟨m, hm⟩
    exact locallyNilpotentExample_pow_ne_bot k m hm

/-! ## Basic consequences -/

theorem locallyNilpotentIdeal_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I) :
    Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal (I.map φ) := by
  have hset :
      φ '' (I : Set R) = Set.range (fun y : I => φ y) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
  have hspan :
      I.map φ = Ideal.span (Set.range (fun y : I => φ y)) := by
    change Ideal.span (φ '' (I : Set R)) = _
    rw [hset]
  rw [hspan]
  apply locallyNilpotentIdeal_span_range
  intro y
  exact (hI y.1 y.2).map φ

theorem isUnit_iff_isUnit_quotient_of_locallyNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I) (x : R) :
    IsUnit x ↔ IsUnit (Ideal.Quotient.mk I x) := by
  constructor
  · intro h
    exact h.map (Ideal.Quotient.mk I)
  · intro h
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hxy : Ideal.Quotient.mk I (x * y) = 1 := by
      simpa only [map_mul] using hy
    have hz : 1 - x * y ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_one, hxy, sub_self]
    have hunit : IsUnit (x * y) := by
      simpa only [sub_sub_cancel] using (hI (1 - x * y) hz).isUnit_one_sub
    exact isUnit_of_mul_isUnit_left hunit

/- The source's Noetherian power assertion and its stated consequence. -/
theorem exists_pow_le_of_le_radical_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hJ : J ≤ I.radical) :
    ∃ n : ℕ, J ^ n ≤ I := by
  obtain ⟨n, hn⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hJ (Ideal.FG.of_isNoetherianRing J)
  exact ⟨n, hn⟩

theorem locallyNilpotentIdeal_iff_isNilpotent_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I ↔
      IsNilpotent I := by
  constructor
  · intro hI
    obtain ⟨n, hn⟩ :=
      exists_pow_le_of_le_radical_of_noetherian (⊥ : Ideal R) I (by
        intro x hx
        exact hI x hx)
    exact ⟨n, le_bot_iff.mp hn⟩
  · rintro ⟨n, hn⟩ x hx
    refine ⟨n, ?_⟩
    apply Ideal.mem_bot.mp
    rw [← Ideal.zero_eq_bot, ← hn]
    exact Ideal.pow_mem_pow hx n

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
  have hker :
      ∀ x ∈ RingHom.ker (Ideal.Quotient.mk I), IsNilpotent x := by
    intro x hx
    apply hI x
    rw [RingHom.mem_ker] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  constructor
  · rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    have h' : Ideal.Quotient.mk I e₁ = Ideal.Quotient.mk I e₂ := by
      simpa [quotientIdempotentMap] using congrArg Subtype.val h
    apply Subtype.ext
    apply eq_of_isNilpotent_sub_of_isIdempotentElem he₁ he₂
    apply hI (e₁ - e₂)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, h', sub_self]
  · rintro ⟨e, he⟩
    obtain ⟨e₀, rfl⟩ := Ideal.Quotient.mk_surjective e
    obtain ⟨e', he', hmap⟩ :=
      exists_isIdempotentElem_eq_of_ker_isNilpotent
        (Ideal.Quotient.mk I) hker (Ideal.Quotient.mk I e₀)
        ⟨e₀, rfl⟩ he
    refine ⟨⟨e', he'⟩, ?_⟩
    apply Subtype.ext
    simpa [quotientIdempotentMap] using hmap

/- The displayed Newton step in the source's second proof is recorded as a
usable identity. -/
theorem idempotent_lift_step_formula
    {R : Type u} [CommRing R] (e : R) :
    (e - (2 * e - 1) * (e ^ 2 - e) = 3 * e ^ 2 - 2 * e ^ 3) ∧
      ((3 * e ^ 2 - 2 * e ^ 3) ^ 2 - (3 * e ^ 2 - 2 * e ^ 3) =
        (4 * e ^ 2 - 4 * e - 3) * (e ^ 2 - e) ^ 2) := by
  constructor <;> ring

theorem idempotent_sub_cube_eq
    {R : Type u} [CommRing R] {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) :
    (e₁ - e₂) ^ 3 = e₁ - e₂ := by
  have hcomm : Commute e₁ e₂ := .all _ _
  simp only [pow_succ, pow_zero, mul_sub, one_mul, sub_mul, he₁.eq, he₂.eq,
    hcomm.eq, mul_assoc]
  simp only [← mul_assoc, he₂.eq]
  abel

theorem idempotent_sub_odd_pow_eq
    {R : Type u} [CommRing R] {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    {k : ℕ} (hk : Odd k) :
    (e₁ - e₂) ^ k = e₁ - e₂ := by
  obtain ⟨n, rfl⟩ := hk
  have hcube : (e₁ - e₂) ^ 3 = e₁ - e₂ :=
    idempotent_sub_cube_eq he₁ he₂
  have hpow : (e₁ - e₂) ^ (2 * n + 1) = e₁ - e₂ := by
    induction n <;>
      simp [mul_add, add_assoc, pow_add _ (2 * _) 3, ← pow_succ, hcube, *]
  exact hpow

theorem exists_idempotent_lift_polynomial
    {A : Type u} [Ring A] (e : A) (h : IsNilpotent (e ^ 2 - e)) :
    ∃ e' : A, IsIdempotentElem e' ∧
      ∃ (s : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℤ),
        e' = e + (e ^ 2 - e) *
          (∑ ij ∈ s, (a ij : A) * e ^ ij.1 * (e ^ 2 - e) ^ ij.2) := by
  obtain ⟨n, hn⟩ := h
  let q : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.X
  let p : ℕ → Polynomial ℤ :=
    Nat.rec Polynomial.X (fun _ p => 3 * p ^ 2 - 2 * p ^ 3)
  have qpow_step {m : ℕ} (hm : 1 ≤ m) (r : Polynomial ℤ)
      (hr : q ^ m ∣ r ^ 2 - r) :
      q ^ (m + 1) ∣ (3 * r ^ 2 - 2 * r ^ 3) ^ 2 -
        (3 * r ^ 2 - 2 * r ^ 3) := by
    rcases hr with ⟨s, hs⟩
    let t : Polynomial ℤ := 3 * r ^ 2 - 2 * r ^ 3
    have hpow : q ^ (2 * m) = q ^ (m + 1) * q ^ (m - 1) := by
      rw [← pow_add]
      congr 1
      omega
    refine ⟨q ^ (m - 1) * (4 * r ^ 2 - 4 * r - 3) * s ^ 2, ?_⟩
    calc
      t ^ 2 - t = (4 * r ^ 2 - 4 * r - 3) * (r ^ 2 - r) ^ 2 := by
        dsimp [t]
        ring
      _ = (4 * r ^ 2 - 4 * r - 3) * (q ^ m * s) ^ 2 := by rw [hs]
      _ = q ^ (m + 1) *
          (q ^ (m - 1) * (4 * r ^ 2 - 4 * r - 3) * s ^ 2) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm, hpow]
        ring
  have hp (n : ℕ) : q ^ (n + 1) ∣ p n ^ 2 - p n := by
    induction n with
    | zero =>
        refine ⟨1, ?_⟩
        simp [p, q]
    | succ n ih =>
        simpa [p, Nat.add_assoc] using
          qpow_step (m := n + 1) (by omega) (p n) ih
  have q_sub_update (r : Polynomial ℤ) (hr : q ∣ r - Polynomial.X) :
      q ∣ (3 * r ^ 2 - 2 * r ^ 3) - Polynomial.X := by
    rcases hr with ⟨s, hs⟩
    refine ⟨-(2 * r - 1) * (s * (r + Polynomial.X - 1) + 1) + s, ?_⟩
    calc
      (3 * r ^ 2 - 2 * r ^ 3) - Polynomial.X =
          -(2 * r - 1) * (r ^ 2 - r) + (r - Polynomial.X) := by ring
      _ = q * (-(2 * r - 1) * (s * (r + Polynomial.X - 1) + 1) + s) := by
        rw [show r ^ 2 - r =
            (r - Polynomial.X) * (r + Polynomial.X - 1) + q by ring, hs]
        ring
  have hp_sub (n : ℕ) : q ∣ p n - Polynomial.X := by
    induction n with
    | zero =>
        refine ⟨0, ?_⟩
        simp [p]
    | succ n ih =>
        simpa [p] using q_sub_update (p n) ih
  let ev : Polynomial ℤ → A := fun r => r.eval₂ (Int.castRingHom A) e
  have ev_mul (r s : Polynomial ℤ) : ev (r * s) = ev r * ev s := by
    apply Polynomial.eval₂_mul_noncomm
    intro k
    simp [ev]
  have ev_sub (r s : Polynomial ℤ) : ev (r - s) = ev r - ev s := by
    dsimp [ev]
    rw [Polynomial.eval₂_sub]
  have ev_pow (r : Polynomial ℤ) (k : ℕ) : ev (r ^ k) = ev r ^ k := by
    induction k with
    | zero => simp [ev]
    | succ k ih =>
        rw [pow_succ, ev_mul, ih, pow_succ]
  have ev_X : ev Polynomial.X = e := by simp [ev]
  have ev_q : ev q = e ^ 2 - e := by
    simp [ev, q]
  have heval_zero : ev (p n ^ 2 - p n) = 0 := by
    obtain ⟨r, hr⟩ := hp n
    rw [hr, ev_mul, ev_pow, ev_q, pow_succ, hn]
    simp
  let e' : A := ev (p n)
  have he' : IsIdempotentElem e' := by
    rw [IsIdempotentElem]
    dsimp [e']
    have hz := heval_zero
    rw [ev_sub, ev_pow] at hz
    simpa [pow_two] using sub_eq_zero.mp hz
  obtain ⟨r, hr⟩ := hp_sub n
  let s : Finset (ℕ × ℕ) := r.support.image (fun i => (i, 0))
  let a : ℕ × ℕ → ℤ := fun ij => r.coeff ij.1
  have hsum :
      (∑ ij ∈ s, (a ij : A) * e ^ ij.1 * (e ^ 2 - e) ^ ij.2) = ev r := by
    classical
    rw [show ev r = r.eval₂ (Int.castRingHom A) e by rfl,
      Polynomial.eval₂_eq_sum]
    rw [show s = r.support.image (fun i => (i, 0)) by rfl, Finset.sum_image]
    · simp [a, Polynomial.sum_def]
    · intro i hi j hj hij
      simpa using congrArg Prod.fst hij
  refine ⟨e', he', s, a, ?_⟩
  have hrel : e' = e + (e ^ 2 - e) * ev r := by
    dsimp [e']
    have hrel' := congrArg ev hr
    rw [ev_sub, ev_mul, ev_X, ev_q] at hrel'
    simpa [ev, add_comm] using (sub_eq_iff_eq_add.mp hrel')
  rw [hrel, hsum]

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
