import Formalization.Books.Dpa.Unit03
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Crystalline Cohomology, Chapter 3: Some explicit divided power thickenings

This file formalizes the two explicit thickenings used later for the
connection on a crystal.  The divided-power operations are kept as explicit
functions, while the divided-power axioms are packaged by Mathlib's
`DividedPowers` structure.
-/

namespace Formalization.Books.Crystalline.Unit03

open Formalization.Books.Dpa.Unit03
open Formalization.Books.Dpa.Unit03.DividedPowerRing

universe u

noncomputable section

/-! ## The first-order thickening -/

/-- The carrier `A ⊕ M` of the first-order thickening. -/
structure FirstOrderThickening (A M : Type u) where
  base : A
  infinitesimal : M

@[ext]
theorem FirstOrderThickening.ext {A M : Type u}
    (x y : FirstOrderThickening A M) (hbase : x.base = y.base)
    (hinfinitesimal : x.infinitesimal = y.infinitesimal) : x = y := by
  cases x
  cases y
  cases hbase
  cases hinfinitesimal
  rfl

namespace FirstOrderThickening

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]

instance instAdd : Add (FirstOrderThickening A M) :=
  ⟨fun x y => ⟨x.base + y.base, x.infinitesimal + y.infinitesimal⟩⟩

instance instZero : Zero (FirstOrderThickening A M) := ⟨⟨0, 0⟩⟩

instance instNeg : Neg (FirstOrderThickening A M) :=
  ⟨fun x => ⟨-x.base, -x.infinitesimal⟩⟩

instance instMul : Mul (FirstOrderThickening A M) :=
  ⟨fun x y =>
    ⟨x.base * y.base,
      x.base • y.infinitesimal + y.base • x.infinitesimal⟩⟩

instance instOne : One (FirstOrderThickening A M) := ⟨⟨1, 0⟩⟩

instance : CommRing (FirstOrderThickening A M) :=
  CommRing.ofMinimalAxioms
    (by
      intro x y z
      apply FirstOrderThickening.ext
      · change (x.base + y.base) + z.base = x.base + (y.base + z.base)
        exact add_assoc _ _ _
      · change (x.infinitesimal + y.infinitesimal) + z.infinitesimal =
          x.infinitesimal + (y.infinitesimal + z.infinitesimal)
        exact add_assoc _ _ _)
    (by
      intro x
      apply FirstOrderThickening.ext
      · change 0 + x.base = x.base
        exact zero_add _
      · change 0 + x.infinitesimal = x.infinitesimal
        exact zero_add _)
    (by
      intro x
      apply FirstOrderThickening.ext
      · change -x.base + x.base = 0
        exact neg_add_cancel _
      · change -x.infinitesimal + x.infinitesimal = 0
        exact neg_add_cancel _)
    (by
      intro x y z
      apply FirstOrderThickening.ext
      · change (x.base * y.base) * z.base = x.base * (y.base * z.base)
        exact mul_assoc _ _ _
      · change
          ((x.base * y.base) • z.infinitesimal +
            z.base • (x.base • y.infinitesimal + y.base • x.infinitesimal)) =
            x.base • (y.base • z.infinitesimal + z.base • y.infinitesimal) +
              (y.base * z.base) • x.infinitesimal
        simp only [smul_add, mul_smul]
        have h₁ : z.base • (x.base • y.infinitesimal) =
            x.base • (z.base • y.infinitesimal) := by
          rw [← mul_smul, ← mul_smul, mul_comm z.base x.base]
        have h₂ : z.base • (y.base • x.infinitesimal) =
            y.base • (z.base • x.infinitesimal) := by
          rw [← mul_smul, ← mul_smul, mul_comm z.base y.base]
        rw [h₁, h₂]
        abel)
    (by
      intro x y
      apply FirstOrderThickening.ext
      · change x.base * y.base = y.base * x.base
        exact mul_comm _ _
      · change x.base • y.infinitesimal + y.base • x.infinitesimal =
          y.base • x.infinitesimal + x.base • y.infinitesimal
        exact add_comm _ _)
    (by
      intro x
      apply FirstOrderThickening.ext
      · change 1 * x.base = x.base
        exact one_mul _
      · change 1 • x.infinitesimal + x.base • (0 : M) = x.infinitesimal
        simp)
    (by
      intro x y z
      apply FirstOrderThickening.ext
      · change x.base * (y.base + z.base) = x.base * y.base + x.base * z.base
        exact mul_add _ _ _
      · change x.base • (y.infinitesimal + z.infinitesimal) +
          (y.base + z.base) • x.infinitesimal =
          (x.base • y.infinitesimal + y.base • x.infinitesimal) +
            (x.base • z.infinitesimal + z.base • x.infinitesimal)
        simp only [smul_add, add_smul]
        abel)

/-- The canonical inclusion of `A` into its first-order thickening. -/
def baseHom : A →+* FirstOrderThickening A M where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' x y := by
    change (⟨x * y, (0 : M)⟩ : FirstOrderThickening A M) =
      ⟨x * y, x • (0 : M) + y • (0 : M)⟩
    simp
  map_zero' := rfl
  map_add' x y := by
    change (⟨x + y, (0 : M)⟩ : FirstOrderThickening A M) =
      ⟨x + y, (0 : M) + 0⟩
    simp

/-- The canonical `A`-algebra structure on the first-order thickening. -/
instance algebra : Algebra A (FirstOrderThickening A M) := baseHom.toAlgebra

end FirstOrderThickening

open FirstOrderThickening

/-- The ideal `I ⊕ M` in the first-order thickening. -/
def firstOrderIdeal {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) : Ideal (FirstOrderThickening A M) where
  carrier := {x | x.base ∈ I}
  zero_mem' := by
    change (0 : A) ∈ I
    exact I.zero_mem
  add_mem' := by
    intro x y hx hy
    exact I.add_mem hx hy
  smul_mem' := by
    intro r x hx
    exact I.mul_mem_left r.base hx

/-- The copy of the square-zero ideal `M` inside `A ⊕ M`. -/
def firstOrderInfinitesimal {A M : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] (m : M) : FirstOrderThickening A M :=
  ⟨0, m⟩

@[simp]
theorem firstOrderInfinitesimal_mem_ideal
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (m : M) :
    firstOrderInfinitesimal m ∈ firstOrderIdeal I := by
  exact I.zero_mem

/-- The infinitesimal summand in the first-order thickening has square zero. -/
theorem firstOrderInfinitesimal_mul
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (m m' : M) :
    firstOrderInfinitesimal m * firstOrderInfinitesimal m' =
      (0 : FirstOrderThickening A M) := by
  apply FirstOrderThickening.ext
  · dsimp [firstOrderInfinitesimal]
    change (0 : A) * 0 = 0
    simp
  · dsimp [firstOrderInfinitesimal]
    change (0 : A) • m' + 0 • m = (0 : M)
    simp

/-- The source's formula for the divided powers on the first-order thickening.
The zero case makes the convention `γ_{-1} = 0` explicit. -/
def firstOrderDpow {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (γ : ℕ → A → A) (n : ℕ) (x : FirstOrderThickening A M) :
    FirstOrderThickening A M :=
  match n with
  | 0 => ⟨1, 0⟩
  | n + 1 => ⟨γ (n + 1) x.base, γ n x.base • x.infinitesimal⟩

private theorem firstOrder_pow
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (a : FirstOrderThickening A M) (k : ℕ) :
    (a ^ k).base = a.base ^ k ∧
      (a ^ k).infinitesimal =
        (k : A) • (a.base ^ (k - 1) • a.infinitesimal) := by
  induction k with
  | zero =>
      simp only [pow_zero]
      constructor
      · rfl
      · change (⟨1, 0⟩ : FirstOrderThickening A M).infinitesimal = _
        simp
  | succ k ih =>
      rw [pow_succ]
      apply And.intro
      · change (a ^ k).base * a.base = a.base ^ (k + 1)
        rw [ih.1, pow_succ]
      · change (a ^ k).base • a.infinitesimal +
            a.base • (a ^ k).infinitesimal =
          ((k + 1 : ℕ) : A) •
            (a.base ^ ((k + 1 : ℕ) - 1) • a.infinitesimal)
        rw [ih.1, ih.2]
        by_cases hk : k = 0
        · subst k
          simp [pow_zero]
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
          simp only [Nat.succ_sub_one]
          rw [pow_succ]
          simp only [smul_smul]
          rw [← add_smul]
          simp only [Nat.cast_succ]
          congr 1
          ring

private theorem firstOrder_natCast
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M] (n : ℕ) :
    (n : FirstOrderThickening A M) = ⟨n, 0⟩ := by
  change (n : FirstOrderThickening A M) =
    FirstOrderThickening.baseHom (n : A)
  exact (map_natCast (FirstOrderThickening.baseHom (A := A) (M := M)) n).symm

private theorem firstOrder_sum_base
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (s : Finset ℕ) (f : ℕ → FirstOrderThickening A M) :
    (s.sum f).base = s.sum (fun k => (f k).base) := by
  induction s using Finset.induction_on with
  | empty =>
      change (0 : A) = 0
      rfl
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      dsimp [HAdd.hAdd, Add.add, FirstOrderThickening.instAdd]
      rw [ih]

private theorem firstOrder_sum_infinitesimal
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (s : Finset ℕ) (f : ℕ → FirstOrderThickening A M) :
    (s.sum f).infinitesimal = s.sum (fun k => (f k).infinitesimal) := by
  induction s using Finset.induction_on with
  | empty =>
      change (0 : M) = 0
      rfl
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      dsimp [HAdd.hAdd, Add.add, FirstOrderThickening.instAdd]
      rw [ih]

/-- The first-order thickening as a divided-power ring, once its displayed
divided-power operations have been shown to satisfy the axioms. -/
def firstOrderDividedPowerRing {A M : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A)
    (δ : DividedPowers (firstOrderIdeal (A := A) (M := M) I)) :
    DividedPowerRing.{u} :=
  { toCommRing := CommRingCat.of (FirstOrderThickening A M)
    ideal := firstOrderIdeal (A := A) (M := M) I
    dividedPowers := δ }

/-- Existence of the divided powers in the first-order thickening, together
with the fact that the canonical inclusion is a divided-power-ring map. -/
theorem exists_firstOrderDividedPowers
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] :
    ∃ δ : DividedPowers (firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal),
      (∀ {n : ℕ} {x : FirstOrderThickening (A : Type u) M},
        x ∈ firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal →
          δ.dpow n x =
            firstOrderDpow A.dividedPowers.dpow n x) ∧
      ∃ h : DividedPowerRing.Hom A
          (firstOrderDividedPowerRing (A := (A : Type u)) (M := M) A.ideal δ),
        h.hom = FirstOrderThickening.baseHom := by
  classical
  let J := firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal
  let S : Set (FirstOrderThickening (A : Type u) M) := {x | x ∈ J}
  let γ : ℕ → FirstOrderThickening (A : Type u) M →
      FirstOrderThickening (A : Type u) M :=
    fun n x => if x ∈ J then firstOrderDpow A.dividedPowers.dpow n x else 0
  have hspan : J = Ideal.span S := by
    apply le_antisymm
    · intro x hx
      exact Ideal.subset_span hx
    · exact Ideal.span_le.2 (fun x hx => hx)
  obtain ⟨δ, hδ⟩ :=
    Formalization.Books.Dpa.Unit02.exists_dividedPowers_of_generator_data
      S hspan γ
      (by
        intro n x hx
        dsimp [γ]
        rw [if_neg hx])
      (by
        intro x hx
        dsimp [γ]
        rw [if_pos hx]
        simp only [firstOrderDpow]
        rfl)
      (by
        intro x hx
        dsimp [γ]
        rw [if_pos hx]
        simp only [firstOrderDpow, Nat.zero_add]
        apply FirstOrderThickening.ext
        · exact A.dividedPowers.dpow_one hx
        · rw [A.dividedPowers.dpow_zero hx]
          simp)
      (by
        intro n x hn hx
        dsimp [γ]
        rw [if_pos hx]
        cases n with
        | zero => exact False.elim (hn rfl)
        | succ n =>
            simp only [firstOrderDpow]
            exact A.dividedPowers.dpow_mem (Nat.succ_ne_zero n) hx)
      (by
        intro n a x hx
        have hax : a * x ∈ J := by
          change (a.base * x.base) ∈ A.ideal
          exact A.ideal.mul_mem_left a.base hx
        simp only [γ, if_pos hax, if_pos hx]
        cases n with
        | zero =>
            simp only [firstOrderDpow, pow_zero, one_mul]
        | succ n =>
            simp only [firstOrderDpow]
            apply FirstOrderThickening.ext
            · change A.dividedPowers.dpow (n + 1) (a.base * x.base) =
                (a ^ (n + 1)).base * A.dividedPowers.dpow (n + 1) x.base
              rw [A.dividedPowers.dpow_mul hx, firstOrder_pow a (n + 1) |>.1]
            · change A.dividedPowers.dpow n (a.base * x.base) •
                  (a.base • x.infinitesimal + x.base • a.infinitesimal) =
                (a ^ (n + 1)).base •
                    (A.dividedPowers.dpow n x.base • x.infinitesimal) +
                  A.dividedPowers.dpow (n + 1) x.base • (a ^ (n + 1)).infinitesimal
              rw [A.dividedPowers.dpow_mul hx, firstOrder_pow a (n + 1) |>.1,
                firstOrder_pow a (n + 1) |>.2]
              have hone : A.dividedPowers.dpow 1 x.base = x.base :=
                A.dividedPowers.dpow_one hx
              have hrel : A.dividedPowers.dpow n x.base * x.base =
                  ((n + 1 : ℕ) : (A : Type u)) *
                    A.dividedPowers.dpow (n + 1) x.base := by
                calc
                  A.dividedPowers.dpow n x.base * x.base =
                      A.dividedPowers.dpow n x.base *
                        A.dividedPowers.dpow 1 x.base := by rw [hone]
                  _ = (Nat.choose (n + 1) n : (A : Type u)) *
                      A.dividedPowers.dpow (n + 1) x.base :=
                    A.dividedPowers.mul_dpow hx
                  _ = _ := by simp
              simp only [smul_add, smul_smul]
              have hfirst :
                  (a.base ^ n * A.dividedPowers.dpow n x.base) * a.base =
                    a.base ^ (n + 1) * A.dividedPowers.dpow n x.base := by
                rw [pow_succ]
                ring
              have hsecond :
                  (a.base ^ n * A.dividedPowers.dpow n x.base) * x.base =
                    A.dividedPowers.dpow (n + 1) x.base *
                      ((n + 1 : ℕ) : (A : Type u)) * a.base ^ n := by
                rw [show a.base ^ n * A.dividedPowers.dpow n x.base * x.base =
                  a.base ^ n * (A.dividedPowers.dpow n x.base * x.base) by ring, hrel]
                ring
              rw [hfirst, hsecond]
              have hlast :
                  (A.dividedPowers.dpow (n + 1) x.base *
                      ((n + 1 : ℕ) : (A : Type u)) * a.base ^ n) • a.infinitesimal =
                    (A.dividedPowers.dpow (n + 1) x.base *
                      (((n + 1 : ℕ) : (A : Type u)) * a.base ^ n)) •
                        a.infinitesimal := by
                rw [mul_assoc]
              rw [show n + 1 - 1 = n by omega]
              rw [hlast])
      (by
        intro n x y hx hy
        have hxJ : x ∈ J := by simpa [S] using hx
        have hyJ : y ∈ J := by simpa [S] using hy
        have hxyJ : x + y ∈ J := J.add_mem hxJ hyJ
        have hadd_base : (x + y).base = x.base + y.base := by
          dsimp [HAdd.hAdd, Add.add, FirstOrderThickening.instAdd]
        have hadd_inf : (x + y).infinitesimal =
            x.infinitesimal + y.infinitesimal := by
          dsimp [HAdd.hAdd, Add.add, FirstOrderThickening.instAdd]
        have hbaseD (z : FirstOrderThickening (A : Type u) M)
            (hz : z ∈ J) (k : ℕ) :
            (firstOrderDpow A.dividedPowers.dpow k z).base =
              A.dividedPowers.dpow k z.base := by
          cases k with
          | zero =>
              simp only [firstOrderDpow]
              rw [A.dividedPowers.dpow_zero hz]
          | succ k => rfl
        have hinfD (z : FirstOrderThickening (A : Type u) M)
            (k : ℕ) :
            (firstOrderDpow A.dividedPowers.dpow k z).infinitesimal =
              match k with
              | 0 => 0
              | k + 1 => A.dividedPowers.dpow k z.base • z.infinitesimal := by
          cases k <;> rfl
        dsimp [γ]
        simp only [if_pos hxJ, if_pos hyJ, if_pos hxyJ]
        cases n with
        | zero =>
            simp only [firstOrderDpow, Finset.Nat.antidiagonal_zero,
              Finset.sum_singleton]
            apply FirstOrderThickening.ext
            · dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul,
                HAdd.hAdd, Add.add, FirstOrderThickening.instAdd]
              change (1 : (A : Type u)) = 1 * 1
              simp
            · dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul,
                HAdd.hAdd, Add.add, FirstOrderThickening.instAdd]
              change (0 : M) = (1 : (A : Type u)) • 0 + (1 : (A : Type u)) • 0
              simp
        | succ n =>
            have hreverse :
                ∀ (f : ℕ → M), (Finset.range (n + 1 + 1)).sum f =
                  (Finset.range (n + 1 + 1)).sum (fun k => f (n + 1 - k)) := by
              intro f
              refine Finset.sum_bij (fun k hk => n + 1 - k) ?_ ?_ ?_ ?_
              · intro a ha
                have ha' := Finset.mem_range.mp ha
                exact Finset.mem_range.mpr (by omega)
              · intro a₁ ha₁ a₂ ha₂ h
                have ha₁' := Finset.mem_range.mp ha₁
                have ha₂' := Finset.mem_range.mp ha₂
                omega
              · intro b hb
                have hb' := Finset.mem_range.mp hb
                refine ⟨n + 1 - b, Finset.mem_range.mpr (by omega), ?_⟩
                omega
              · intro a ha
                have ha' := Finset.mem_range.mp ha
                congr 1
                omega
            have hconv :
                ∀ (z w : FirstOrderThickening (A : Type u) M),
                  z ∈ J → w ∈ J →
                  (Finset.range (n + 1 + 1)).sum (fun k =>
                    (firstOrderDpow A.dividedPowers.dpow k z).base •
                      (firstOrderDpow A.dividedPowers.dpow (n + 1 - k) w).infinitesimal) =
                    A.dividedPowers.dpow n (z + w).base • w.infinitesimal := by
              intro z w hz hw
              rw [Finset.sum_range_succ]
              have hlast :
                  (firstOrderDpow A.dividedPowers.dpow (n + 1) z).base •
                      (firstOrderDpow A.dividedPowers.dpow (n + 1 - (n + 1)) w).infinitesimal =
                    0 := by
                rw [hinfD]
                simp
              rw [hlast, add_zero]
              have hterms :
                  ∀ k ∈ Finset.range (n + 1),
                    (firstOrderDpow A.dividedPowers.dpow k z).base •
                        (firstOrderDpow A.dividedPowers.dpow (n + 1 - k) w).infinitesimal =
                      (A.dividedPowers.dpow k z.base *
                          A.dividedPowers.dpow (n - k) w.base) • w.infinitesimal := by
                intro k hk
                have hklt : k < n + 1 := Finset.mem_range.mp hk
                have hpos : n + 1 - k ≠ 0 := by omega
                obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos
                have hj' : j = n - k := by omega
                rw [hinfD, hj, hj', hbaseD z hz k]
                rw [← mul_smul]
              rw [Finset.sum_congr rfl hterms]
              rw [← Finset.sum_smul]
              have hzw : (z + w).base = z.base + w.base := by
                dsimp [HAdd.hAdd, Add.add, FirstOrderThickening.instAdd]
              rw [hzw]
              rw [A.dividedPowers.dpow_add' (n := n)
                (a := z.base) (b := w.base) hz hw]
            have hconv_y := hconv x y hxJ hyJ
            have hconv_x :
                (Finset.range (n + 1 + 1)).sum (fun k =>
                  (firstOrderDpow A.dividedPowers.dpow (n + 1 - k) y).base •
                    (firstOrderDpow A.dividedPowers.dpow k x).infinitesimal) =
                  A.dividedPowers.dpow n (x + y).base • x.infinitesimal := by
              have hrev := hreverse (fun k =>
                (firstOrderDpow A.dividedPowers.dpow k y).base •
                  (firstOrderDpow A.dividedPowers.dpow (n + 1 - k) x).infinitesimal)
              have hrev_eq :
                  (Finset.range (n + 1 + 1)).sum (fun k =>
                    (firstOrderDpow A.dividedPowers.dpow k y).base •
                      (firstOrderDpow A.dividedPowers.dpow (n + 1 - k) x).infinitesimal) =
                  (Finset.range (n + 1 + 1)).sum (fun k =>
                    (firstOrderDpow A.dividedPowers.dpow (n + 1 - k) y).base •
                      (firstOrderDpow A.dividedPowers.dpow k x).infinitesimal) := by
                rw [hrev]
                apply Finset.sum_congr rfl
                intro k hk
                have hk' := Finset.mem_range.mp hk
                have hk_le : k ≤ n + 1 := by omega
                have hEq : n + 1 - (n + 1 - k) = k := by omega
                rw [hEq]
              rw [← hrev_eq]
              have hyx := hconv y x hyJ hxJ
              rw [show y + x = x + y by exact add_comm _ _] at hyx
              exact hyx
            rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
            apply FirstOrderThickening.ext
            · rw [firstOrder_sum_base]
              have hterms :
                  ∀ k ∈ Finset.range (n + 1 + 1),
                    (firstOrderDpow A.dividedPowers.dpow k x *
                      firstOrderDpow A.dividedPowers.dpow (n + 1 - k) y).base =
                    A.dividedPowers.dpow k x.base *
                      A.dividedPowers.dpow (n + 1 - k) y.base := by
                intro k hk
                dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
                rw [hbaseD x hxJ k, hbaseD y hyJ (n + 1 - k)]
              rw [Finset.sum_congr rfl hterms]
              rw [hbaseD (x + y) hxyJ (n + 1), hadd_base]
              exact A.dividedPowers.dpow_add' (n := n + 1)
                (a := x.base) (b := y.base) hxJ hyJ
            · rw [firstOrder_sum_infinitesimal]
              dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
              rw [Finset.sum_add_distrib, hconv_y, hconv_x]
              dsimp [firstOrderDpow]
              rw [hadd_inf]
              rw [smul_add]
              exact add_comm _ _)
      (by
        intro m n x hx
        have hxJ : x ∈ J := by simpa [S] using hx
        simp only [γ, if_pos hxJ]
        cases m with
        | zero =>
            cases n with
            | zero =>
                simp only [firstOrderDpow, firstOrder_natCast,
                  Nat.choose_zero_right]
                dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]; simp
            | succ n =>
                simp only [firstOrderDpow, firstOrder_natCast,
                  Nat.zero_add, Nat.choose_zero_right]
                dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]; simp
        | succ m =>
            cases n with
            | zero =>
                simp only [firstOrderDpow, firstOrder_natCast, Nat.add_zero,
                  Nat.choose_self]
                apply FirstOrderThickening.ext
                · dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
                  rw [Nat.cast_one]
                  exact mul_comm (A.dividedPowers.dpow (m + 1) x.base) 1
                · dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]; simp
            | succ n =>
                simp only [firstOrderDpow]
                rw [firstOrder_natCast]
                apply FirstOrderThickening.ext
                · dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
                  change
                    A.dividedPowers.dpow (m + 1) x.base *
                        A.dividedPowers.dpow (n + 1) x.base =
                      (Nat.choose ((m + 1) + (n + 1)) (m + 1) : (A : Type u)) *
                        A.dividedPowers.dpow (m + 1 + n + 1) x.base
                  have hmul :=
                    A.dividedPowers.mul_dpow (m := m + 1) (n := n + 1) hxJ
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
                · dsimp [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
                  simp only [smul_zero, add_zero]
                  change
                    A.dividedPowers.dpow (m + 1) x.base •
                        (A.dividedPowers.dpow n x.base • x.infinitesimal) +
                      A.dividedPowers.dpow (n + 1) x.base •
                        (A.dividedPowers.dpow m x.base • x.infinitesimal) =
                      (Nat.choose ((m + 1) + (n + 1)) (m + 1) : (A : Type u)) •
                        (A.dividedPowers.dpow (m + 1 + n) x.base •
                          x.infinitesimal)
                  simp only [smul_smul]
                  have h₁ :=
                    A.dividedPowers.mul_dpow (m := m + 1) (n := n) hxJ
                  have h₂ :=
                    A.dividedPowers.mul_dpow (m := n + 1) (n := m) hxJ
                  have h₁' :
                      A.dividedPowers.dpow (m + 1) x.base *
                          A.dividedPowers.dpow n x.base =
                        (Nat.choose (m + n + 1) (m + 1) : (A : Type u)) *
                          A.dividedPowers.dpow (m + n + 1) x.base := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₁
                  have h₂' :
                      A.dividedPowers.dpow (n + 1) x.base *
                          A.dividedPowers.dpow m x.base =
                        (Nat.choose (m + n + 1) m : (A : Type u)) *
                          A.dividedPowers.dpow (m + n + 1) x.base := by
                    calc
                      _ = (Nat.choose ((n + 1) + m) (n + 1) : (A : Type u)) *
                            A.dividedPowers.dpow ((n + 1) + m) x.base := h₂
                      _ = (Nat.choose ((n + 1) + m) m : (A : Type u)) *
                            A.dividedPowers.dpow ((n + 1) + m) x.base := by
                              rw [Nat.choose_symm_add]
                      _ = _ := by
                        simp [Nat.add_assoc, Nat.add_comm]
                  have hCnat :
                      Nat.choose ((m + 1) + (n + 1)) (m + 1) =
                        Nat.choose (m + n + 1) (m + 1) +
                          Nat.choose (m + n + 1) m := by
                    rw [show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega,
                      Nat.choose_succ_succ']
                    exact add_comm _ _
                  have hC := congrArg (fun k : ℕ => (k : (A : Type u))) hCnat
                  rw [h₁', h₂', show m + 1 + n = m + n + 1 by omega, hC]
                  simp only [Nat.cast_add, add_smul, add_mul])
      (by
        intro m n x hn hx
        have hxJ : x ∈ J := by simpa [S] using hx
        cases n with
        | zero => exact False.elim (hn rfl)
        | succ k =>
            have hyJ :
                firstOrderDpow A.dividedPowers.dpow (k + 1) x ∈ J := by
              change A.dividedPowers.dpow (k + 1) x.base ∈ A.ideal
              exact A.dividedPowers.dpow_mem (Nat.succ_ne_zero k) hxJ
            simp only [γ, if_pos hxJ, if_pos hyJ]
            cases m with
            | zero =>
                simp only [zero_mul, firstOrderDpow, Nat.uniformBell_zero_left]
                rw [firstOrder_natCast]
                apply FirstOrderThickening.ext
                · dsimp only [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
                  rw [Nat.cast_one]
                  exact (one_mul (1 : (A : Type u))).symm
                · dsimp only [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
                  simp only [Nat.cast_one, smul_zero, add_zero]
            | succ r =>
                have hprod : (r + 1) * (k + 1) = r * (k + 1) + k + 1 := by
                  rw [Nat.succ_mul]
                  omega
                rw [hprod]
                simp only [firstOrderDpow]
                rw [firstOrder_natCast]
                apply FirstOrderThickening.ext
                · dsimp only [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
                  change
                    A.dividedPowers.dpow (r + 1)
                        (A.dividedPowers.dpow (k + 1) x.base) =
                      (Nat.uniformBell (r + 1) (k + 1) : (A : Type u)) *
                        A.dividedPowers.dpow (r * (k + 1) + k + 1) x.base
                  rw [← hprod]
                  exact A.dividedPowers.dpow_comp (Nat.succ_ne_zero k) hxJ
                · dsimp only [HMul.hMul, Mul.mul, FirstOrderThickening.instMul]
                  simp only [smul_zero, add_zero]
                  change
                    A.dividedPowers.dpow r
                        (A.dividedPowers.dpow (k + 1) x.base) •
                        (A.dividedPowers.dpow k x.base • x.infinitesimal) =
                        (Nat.uniformBell (r + 1) (k + 1) : (A : Type u)) •
                        (A.dividedPowers.dpow (r * (k + 1) + k) x.base •
                          x.infinitesimal)
                  have hcomp :=
                    A.dividedPowers.dpow_comp (m := r) (n := k + 1)
                      (Nat.succ_ne_zero k) hxJ
                  have hmul :=
                    A.dividedPowers.mul_dpow (m := r * (k + 1)) (n := k) hxJ
                  have hbell :
                      Nat.uniformBell (r + 1) (k + 1) =
                        Nat.choose (r * (k + 1) + k) k *
                          Nat.uniformBell r (k + 1) := by
                    simpa [Nat.add_assoc] using
                      (Nat.uniformBell_succ_left r (k + 1))
                  have hchoose :
                      Nat.choose (r * (k + 1) + k) (r * (k + 1)) =
                        Nat.choose (r * (k + 1) + k) k :=
                    Nat.choose_symm_add
                  have hcoeff :
                      (Nat.uniformBell r (k + 1) : (A : Type u)) *
                          (Nat.choose (r * (k + 1) + k) (r * (k + 1)) : (A : Type u)) =
                        (Nat.uniformBell (r + 1) (k + 1) : (A : Type u)) := by
                    rw [hchoose, hbell]
                    push_cast
                    ring
                  have hleft :
                      ((Nat.uniformBell r (k + 1) : (A : Type u)) *
                          A.dividedPowers.dpow (r * (k + 1)) x.base) *
                          A.dividedPowers.dpow k x.base =
                        ((Nat.uniformBell r (k + 1) : (A : Type u)) *
                          (Nat.choose (r * (k + 1) + k) (r * (k + 1)) : (A : Type u))) *
                          A.dividedPowers.dpow (r * (k + 1) + k) x.base := by
                    calc
                      _ = (Nat.uniformBell r (k + 1) : (A : Type u)) *
                          (A.dividedPowers.dpow (r * (k + 1)) x.base *
                            A.dividedPowers.dpow k x.base) := by ring
                      _ = _ := by rw [hmul]
                      _ = _ := by ring
                  rw [hcomp]
                  simp only [smul_smul]
                  rw [hleft, hcoeff])
  refine ⟨δ, ?_, ?_⟩
  · intro n x hx
    have hxJ : x ∈ J := hx
    exact hδ (n := n) (x := x) |>.trans (by simp [γ, hxJ])
  · let h : DividedPowerRing.Hom A
        (firstOrderDividedPowerRing (A := (A : Type u)) (M := M) A.ideal δ) :=
      { hom := FirstOrderThickening.baseHom
        ideal_map := by
          intro x hx
          exact hx
        dpow_comm := by
          intro n x hx
          change δ.dpow n (FirstOrderThickening.baseHom x) =
            FirstOrderThickening.baseHom (A.dividedPowers.dpow n x)
          have hxJ : FirstOrderThickening.baseHom x ∈ J := hx
          have hδ' := hδ (n := n) (x := FirstOrderThickening.baseHom x)
          rw [show γ n (FirstOrderThickening.baseHom x) =
            firstOrderDpow A.dividedPowers.dpow n (FirstOrderThickening.baseHom x) by
              simp [γ, hxJ]] at hδ'
          rw [hδ']
          cases n with
          | zero =>
              rw [A.dividedPowers.dpow_zero hx]
              rfl
          | succ n =>
              dsimp [firstOrderDpow, FirstOrderThickening.baseHom]
              simp only [smul_zero] }
    exact ⟨h, rfl⟩

/-- A chosen divided-power structure on the first-order thickening. -/
noncomputable def firstOrderDividedPowers
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] :
    DividedPowers (firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal) :=
  Classical.choose (exists_firstOrderDividedPowers A M)

theorem firstOrderDividedPowers_dpow
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] {n : ℕ}
    {x : FirstOrderThickening (A : Type u) M}
    (hx : x ∈ firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal) :
    (firstOrderDividedPowers A M).dpow n x = firstOrderDpow A.dividedPowers.dpow n x :=
  (Classical.choose_spec (exists_firstOrderDividedPowers A M)).1 hx

/-- The canonical divided-power-ring map from `A` to the chosen first-order
thickening. -/
noncomputable def firstOrderDividedPowerHom
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] :
    DividedPowerRing.Hom A
      (firstOrderDividedPowerRing (A := (A : Type u)) (M := M) A.ideal
        (firstOrderDividedPowers A M)) :=
  Classical.choose ((Classical.choose_spec (exists_firstOrderDividedPowers A M)).2)

theorem firstOrderDividedPowerHom_eq_baseHom
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] :
    (firstOrderDividedPowerHom A M).hom = FirstOrderThickening.baseHom :=
  Classical.choose_spec ((Classical.choose_spec (exists_firstOrderDividedPowers A M)).2)

/-! ## The second-order thickening -/

/-- The carrier `A ⊕ M ⊕ N` of the second-order thickening. -/
structure SecondOrderThickening (A M N : Type u) [CommRing A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) where
  base : A
  first : M
  second : N

@[ext]
theorem SecondOrderThickening.ext {A M N : Type u}
    [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    (x y : SecondOrderThickening A M N q) (hbase : x.base = y.base)
    (hfirst : x.first = y.first) (hsecond : x.second = y.second) : x = y := by
  cases x
  cases y
  cases hbase
  cases hfirst
  cases hsecond
  rfl

namespace SecondOrderThickening

variable {A M N : Type u} [CommRing A] [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module A N] (q : M →ₗ[A] M →ₗ[A] N)

instance instAdd : Add (SecondOrderThickening A M N q) :=
  ⟨fun x y => ⟨x.base + y.base, x.first + y.first, x.second + y.second⟩⟩

instance instZero : Zero (SecondOrderThickening A M N q) := ⟨⟨0, 0, 0⟩⟩

instance instNeg : Neg (SecondOrderThickening A M N q) :=
  ⟨fun x => ⟨-x.base, -x.first, -x.second⟩⟩

instance instMul : Mul (SecondOrderThickening A M N q) :=
  ⟨fun x y =>
    ⟨x.base * y.base,
      x.base • y.first + y.base • x.first,
      x.base • y.second + y.base • x.second + q x.first y.first +
        q y.first x.first⟩⟩

instance instOne : One (SecondOrderThickening A M N q) := ⟨⟨1, 0, 0⟩⟩

/-- Associativity of the displayed second-order multiplication. -/
theorem secondOrder_mul_assoc
    (x y z : SecondOrderThickening A M N q) : x * y * z = x * (y * z) := by
  apply SecondOrderThickening.ext q
  · change (x.base * y.base) * z.base = x.base * (y.base * z.base)
    exact mul_assoc _ _ _
  · change (x.base * y.base) • z.first + z.base •
        (x.base • y.first + y.base • x.first) =
      x.base • (y.base • z.first + z.base • y.first) +
        (y.base * z.base) • x.first
    simp only [smul_add, mul_smul]
    have h₁ : z.base • (x.base • y.first) =
        x.base • (z.base • y.first) := by
      rw [← mul_smul, ← mul_smul, mul_comm z.base x.base]
    have h₂ : z.base • (y.base • x.first) =
        y.base • (z.base • x.first) := by
      rw [← mul_smul, ← mul_smul, mul_comm z.base y.base]
    rw [h₁, h₂]
    abel
  · change (x.base * y.base) • z.second + z.base •
        (x.base • y.second + y.base • x.second + q x.first y.first +
          q y.first x.first) +
        q (x.base • y.first + y.base • x.first) z.first +
        q z.first (x.base • y.first + y.base • x.first) =
      x.base • (y.base • z.second + z.base • y.second +
          q y.first z.first + q z.first y.first) +
        (y.base * z.base) • x.second +
        q x.first (y.base • z.first + z.base • y.first) +
        q (y.base • z.first + z.base • y.first) x.first
    simp only [smul_add, mul_smul]
    have h₁ : z.base • (x.base • y.second) =
        x.base • (z.base • y.second) := by
      rw [← mul_smul, ← mul_smul, mul_comm z.base x.base]
    have h₂ : z.base • (y.base • x.second) =
        y.base • (z.base • x.second) := by
      rw [← mul_smul, ← mul_smul, mul_comm z.base y.base]
    rw [h₁, h₂]
    have hq₁ : q (x.base • y.first + y.base • x.first) z.first =
        q (x.base • y.first) z.first + q (y.base • x.first) z.first := by
      rw [q.map_add]
      rfl
    have hq₂ : q z.first (x.base • y.first + y.base • x.first) =
        q z.first (x.base • y.first) + q z.first (y.base • x.first) := by
      rw [(q z.first).map_add]
    have hq₃ : q x.first (y.base • z.first + z.base • y.first) =
        q x.first (y.base • z.first) + q x.first (z.base • y.first) := by
      rw [(q x.first).map_add]
    have hq₄ : q (y.base • z.first + z.base • y.first) x.first =
        q (y.base • z.first) x.first + q (z.base • y.first) x.first := by
      rw [q.map_add]
      rfl
    rw [hq₁, hq₂, hq₃, hq₄]
    have h₁' : q (x.base • y.first) z.first =
        x.base • q y.first z.first := by
      convert congrArg (fun f : M →ₗ[A] N => f z.first)
        (q.map_smul x.base y.first) using 1; simp
    have h₂' : q (y.base • x.first) z.first =
        y.base • q x.first z.first := by
      convert congrArg (fun f : M →ₗ[A] N => f z.first)
        (q.map_smul y.base x.first) using 1; simp
    have h₃' : q z.first (x.base • y.first) =
        x.base • q z.first y.first := by
      rw [(q z.first).map_smul]
    have h₄' : q z.first (y.base • x.first) =
        y.base • q z.first x.first := by
      rw [(q z.first).map_smul]
    rw [h₁', h₂', h₃', h₄']
    have h₅ : q x.first (y.base • z.first) =
        y.base • q x.first z.first := by
      rw [(q x.first).map_smul]
    have h₆ : q x.first (z.base • y.first) =
        z.base • q x.first y.first := by
      rw [(q x.first).map_smul]
    have h₇ : q (y.base • z.first) x.first =
        y.base • q z.first x.first := by
      convert congrArg (fun f : M →ₗ[A] N => f x.first)
        (q.map_smul y.base z.first) using 1; simp
    have h₈ : q (z.base • y.first) x.first =
        z.base • q y.first x.first := by
      convert congrArg (fun f : M →ₗ[A] N => f x.first)
        (q.map_smul z.base y.first) using 1; simp
    rw [h₅, h₆, h₇, h₈]
    abel

/-- Left distributivity of the displayed second-order multiplication. -/
theorem secondOrder_left_distrib
    (x y z : SecondOrderThickening A M N q) : x * (y + z) = x * y + x * z := by
  apply SecondOrderThickening.ext q
  · change x.base * (y.base + z.base) = x.base * y.base + x.base * z.base
    exact mul_add _ _ _
  · change x.base • (y.first + z.first) + (y.base + z.base) • x.first =
      (x.base • y.first + y.base • x.first) +
        (x.base • z.first + z.base • x.first)
    simp only [add_smul, smul_add]
    abel
  · change x.base • (y.second + z.second) + (y.base + z.base) • x.second +
        q x.first (y.first + z.first) + q (y.first + z.first) x.first =
      (x.base • y.second + y.base • x.second + q x.first y.first +
          q y.first x.first) +
        (x.base • z.second + z.base • x.second + q x.first z.first +
          q z.first x.first)
    simp only [add_smul, smul_add]
    have h₁ : q x.first (y.first + z.first) =
        q x.first y.first + q x.first z.first := by
      rw [(q x.first).map_add]
    have h₂ : q (y.first + z.first) x.first =
        q y.first x.first + q z.first x.first := by
      rw [q.map_add]
      rfl
    rw [h₁, h₂]
    abel

instance : CommRing (SecondOrderThickening A M N q) :=
  CommRing.ofMinimalAxioms
    (by
      intro x y z
      apply SecondOrderThickening.ext q
      · change (x.base + y.base) + z.base = x.base + (y.base + z.base)
        exact add_assoc _ _ _
      · change (x.first + y.first) + z.first = x.first + (y.first + z.first)
        exact add_assoc _ _ _
      · change (x.second + y.second) + z.second =
          x.second + (y.second + z.second)
        exact add_assoc _ _ _)
    (by
      intro x
      apply SecondOrderThickening.ext q
      · change 0 + x.base = x.base
        exact zero_add _
      · change 0 + x.first = x.first
        exact zero_add _
      · change 0 + x.second = x.second
        exact zero_add _)
    (by
      intro x
      apply SecondOrderThickening.ext q
      · change -x.base + x.base = 0
        exact neg_add_cancel _
      · change -x.first + x.first = 0
        exact neg_add_cancel _
      · change -x.second + x.second = 0
        exact neg_add_cancel _)
    (by
      exact secondOrder_mul_assoc q)
    (by
      intro x y
      apply SecondOrderThickening.ext q
      · change x.base * y.base = y.base * x.base
        exact mul_comm _ _
      · change x.base • y.first + y.base • x.first =
          y.base • x.first + x.base • y.first
        exact add_comm _ _
      · change x.base • y.second + y.base • x.second + q x.first y.first +
          q y.first x.first =
          y.base • x.second + x.base • y.second + q y.first x.first +
            q x.first y.first
        simp [add_comm, add_left_comm, add_assoc])
    (by
      intro x
      apply SecondOrderThickening.ext q
      · change 1 * x.base = x.base
        exact one_mul _
      · change 1 • x.first + x.base • (0 : M) = x.first
        simp
      · change 1 • x.second + x.base • (0 : N) + q 0 x.first + q x.first 0 =
          x.second
        simp)
    (by
      exact secondOrder_left_distrib q)

/-- The canonical inclusion of `A` into its second-order thickening. -/
def baseHom : A →+* SecondOrderThickening A M N q where
  toFun a := ⟨a, 0, 0⟩
  map_one' := rfl
  map_mul' x y := by
    change (⟨x * y, (0 : M), (0 : N)⟩ : SecondOrderThickening A M N q) =
      ⟨x * y, x • (0 : M) + y • (0 : M),
        x • (0 : N) + y • (0 : N) + q 0 0 + q 0 0⟩
    simp
  map_zero' := rfl
  map_add' x y := by
    change (⟨x + y, (0 : M), (0 : N)⟩ : SecondOrderThickening A M N q) =
      ⟨x + y, (0 : M) + 0, (0 : N) + 0⟩
    simp

instance algebra : Algebra A (SecondOrderThickening A M N q) := baseHom q |>.toAlgebra

end SecondOrderThickening

open SecondOrderThickening

/-- The ideal `I ⊕ M ⊕ N` in the second-order thickening. -/
def secondOrderIdeal {A M N : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N]
    (I : Ideal A) (q : M →ₗ[A] M →ₗ[A] N) :
    Ideal (SecondOrderThickening A M N q) where
  carrier := {x | x.base ∈ I}
  zero_mem' := by
    change (0 : A) ∈ I
    exact I.zero_mem
  add_mem' := by
    intro x y hx hy
    exact I.add_mem hx hy
  smul_mem' := by
    intro r x hx
    exact I.mul_mem_left r.base hx

/-- The source's formula for the divided powers on the second-order
thickening, with the low-degree conventions made explicit. -/
def secondOrderDpow {A M N : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N]
    (γ : ℕ → A → A) (q : M →ₗ[A] M →ₗ[A] N) (n : ℕ)
    (x : SecondOrderThickening A M N q) : SecondOrderThickening A M N q :=
  match n with
  | 0 => ⟨1, 0, 0⟩
  | 1 => ⟨γ 1 x.base, γ 0 x.base • x.first, γ 0 x.base • x.second⟩
  | n + 2 =>
      ⟨γ (n + 2) x.base, γ (n + 1) x.base • x.first,
        γ (n + 1) x.base • x.second + γ n x.base • q x.first x.first⟩

/-- The second-order thickening as a divided-power ring, once its displayed
divided-power operations have been shown to satisfy the axioms. -/
def secondOrderDividedPowerRing {A M N : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N]
    (I : Ideal A) (q : M →ₗ[A] M →ₗ[A] N)
    (δ : DividedPowers (secondOrderIdeal I q)) : DividedPowerRing.{u} :=
  { toCommRing := CommRingCat.of (SecondOrderThickening A M N q)
    ideal := secondOrderIdeal I q
    dividedPowers := δ }

/-- Existence of the divided powers in the second-order thickening, together
with the fact that the canonical inclusion is a divided-power-ring map. -/
theorem exists_secondOrderDividedPowers
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) :
    ∃ δ : DividedPowers (secondOrderIdeal A.ideal q),
      (∀ {n : ℕ} {x : SecondOrderThickening (A : Type u) M N q},
        x ∈ secondOrderIdeal A.ideal q →
          δ.dpow n x = secondOrderDpow A.dividedPowers.dpow q n x) ∧
      ∃ h : DividedPowerRing.Hom A
          (secondOrderDividedPowerRing A.ideal q δ),
        h.hom = SecondOrderThickening.baseHom q := by
  sorry

/-- A chosen divided-power structure on the second-order thickening. -/
noncomputable def secondOrderDividedPowers
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) :
    DividedPowers (secondOrderIdeal A.ideal q) :=
  Classical.choose (exists_secondOrderDividedPowers A M N q)

theorem secondOrderDividedPowers_dpow
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) {n : ℕ}
    {x : SecondOrderThickening (A : Type u) M N q}
    (hx : x ∈ secondOrderIdeal A.ideal q) :
    (secondOrderDividedPowers A M N q).dpow n x =
      secondOrderDpow A.dividedPowers.dpow q n x :=
  (Classical.choose_spec (exists_secondOrderDividedPowers A M N q)).1 hx

/-- The canonical divided-power-ring map from `A` to the chosen second-order
thickening. -/
noncomputable def secondOrderDividedPowerHom
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) :
    DividedPowerRing.Hom A
      (secondOrderDividedPowerRing A.ideal q
        (secondOrderDividedPowers A M N q)) :=
  Classical.choose ((Classical.choose_spec (exists_secondOrderDividedPowers A M N q)).2)

theorem secondOrderDividedPowerHom_eq_baseHom
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) :
    (secondOrderDividedPowerHom A M N q).hom = SecondOrderThickening.baseHom q :=
  Classical.choose_spec
    ((Classical.choose_spec (exists_secondOrderDividedPowers A M N q)).2)

end
end Formalization.Books.Crystalline.Unit03
