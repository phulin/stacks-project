import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Examples, Chapter 31: A nonfinite module with finite free rank 1 stalks

This file records the constructions and theorem interfaces in the source
section.  The proposition proofs belong to the proving stage.
-/

noncomputable section

namespace Formalization.Books.Examples.Unit31

/-! ## The fractional module over `ℚ[x]` -/

/-- The polynomial ring `R = ℚ[x]` used in the example. -/
abbrev exampleBaseRing := Polynomial ℚ

/-- The fraction ring containing the displayed fractional generators. -/
abbrev exampleFractionRing := FractionRing exampleBaseRing

/-- The denominator `x - n` in `ℚ[x]`. -/
def exampleDenominator (n : ℕ) : exampleBaseRing :=
  Polynomial.X - Polynomial.C (n : ℚ)

/-- The element `1 / (x - n)` in the fraction ring of `ℚ[x]`. -/
def exampleFractionalGenerator (n : ℕ) : exampleFractionRing :=
  (algebraMap exampleBaseRing exampleFractionRing (exampleDenominator n))⁻¹

/-- The `ℚ[x]`-submodule `M = ∑ₙ (1 / (x - n)) R` in the fraction ring. -/
def exampleModule : Submodule exampleBaseRing exampleFractionRing :=
  Submodule.span exampleBaseRing (Set.range exampleFractionalGenerator)

abbrev ExampleModule := (exampleModule : Type)

/-- The localization `Rₚ` of `R` at a prime ideal `p`. -/
abbrev exampleBaseRingAtPrime (p : Ideal exampleBaseRing) [p.IsPrime] :=
  Localization p.primeCompl

/-- The localization `Mₚ` of `M` at the same prime ideal. -/
abbrev exampleModuleAtPrime (p : Ideal exampleBaseRing) [p.IsPrime] :=
  LocalizedModule p.primeCompl ExampleModule

/-- The module `M` is not finitely generated over `ℚ[x]`. -/
theorem exampleModule_not_finite :
    ¬ Module.Finite exampleBaseRing ExampleModule := by
  have hden (k : ℕ) :
      algebraMap exampleBaseRing exampleFractionRing (exampleDenominator k) ≠ 0 := by
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.X_sub_C_ne_zero _)
  have hcommon : ∀ (x : exampleFractionRing) (hx : x ∈ (exampleModule : Set _)),
      ∃ (q r : exampleBaseRing), q ≠ 0 ∧
        algebraMap exampleBaseRing exampleFractionRing q * x =
          algebraMap exampleBaseRing exampleFractionRing r := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨k, rfl⟩
        refine ⟨exampleDenominator k, 1, ?_, ?_⟩
        · exact Polynomial.X_sub_C_ne_zero _
        · simp [exampleFractionalGenerator, hden]
    | zero =>
        exact ⟨1, 0, one_ne_zero, by simp⟩
    | add x y hx hy hx' hy' =>
        rcases hx' with ⟨q₁, r₁, hq₁, h₁⟩
        rcases hy' with ⟨q₂, r₂, hq₂, h₂⟩
        refine ⟨q₁ * q₂, r₁ * q₂ + r₂ * q₁, mul_ne_zero hq₁ hq₂, ?_⟩
        calc
          algebraMap exampleBaseRing exampleFractionRing (q₁ * q₂) * (x + y) =
              algebraMap exampleBaseRing exampleFractionRing q₂ *
                  (algebraMap exampleBaseRing exampleFractionRing q₁ * x) +
              algebraMap exampleBaseRing exampleFractionRing q₁ *
                  (algebraMap exampleBaseRing exampleFractionRing q₂ * y) := by
                    simp [map_mul, mul_add, mul_assoc, mul_comm, mul_left_comm]
                    ring
          _ = algebraMap exampleBaseRing exampleFractionRing q₂ *
                  algebraMap exampleBaseRing exampleFractionRing r₁ +
                algebraMap exampleBaseRing exampleFractionRing q₁ *
                  algebraMap exampleBaseRing exampleFractionRing r₂ := by
                    rw [h₁, h₂]
          _ = algebraMap exampleBaseRing exampleFractionRing (r₁ * q₂ + r₂ * q₁) := by
                    simp [map_add, map_mul, mul_comm]
    | smul a x hx hx' =>
        rcases hx' with ⟨q, r, hq, h⟩
        refine ⟨q, a * r, hq, ?_⟩
        rw [Algebra.smul_def]
        calc
          algebraMap exampleBaseRing exampleFractionRing q *
                (algebraMap exampleBaseRing exampleFractionRing a * x) =
              algebraMap exampleBaseRing exampleFractionRing a *
                (algebraMap exampleBaseRing exampleFractionRing q * x) := by ring
          _ = algebraMap exampleBaseRing exampleFractionRing a *
                algebraMap exampleBaseRing exampleFractionRing r := by rw [h]
          _ = algebraMap exampleBaseRing exampleFractionRing (a * r) := by
                rw [map_mul]
  intro hfinite
  letI : Module.Finite exampleBaseRing ExampleModule := hfinite
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin
    (R := exampleBaseRing) (M := ExampleModule)
  choose q r hq hr using fun i : Fin N => hcommon (s i).1 (s i).2
  let Q : exampleBaseRing := ∏ i : Fin N, q i
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)
  have hspan : ∀ (x : ExampleModule),
      x ∈ Submodule.span exampleBaseRing (Set.range s) →
        ∃ r : exampleBaseRing,
          algebraMap exampleBaseRing exampleFractionRing Q * x.1 =
            algebraMap exampleBaseRing exampleFractionRing r := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨i, rfl⟩
        let qrest : exampleBaseRing := ∏ j ∈ Finset.univ.erase i, q j
        have hprod : q i * qrest = Q := by
          dsimp [Q, qrest]
          exact Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
        refine ⟨r i * qrest, ?_⟩
        calc
          algebraMap exampleBaseRing exampleFractionRing Q * (s i).1 =
              algebraMap exampleBaseRing exampleFractionRing (q i * qrest) *
                (s i).1 := by rw [hprod]
          _ = algebraMap exampleBaseRing exampleFractionRing qrest *
                (algebraMap exampleBaseRing exampleFractionRing (q i) *
                  (s i).1) := by
              simp only [map_mul]
              ring
          _ = algebraMap exampleBaseRing exampleFractionRing qrest *
                algebraMap exampleBaseRing exampleFractionRing (r i) := by
              rw [hr i]
          _ = algebraMap exampleBaseRing exampleFractionRing (r i * qrest) := by
              simp [map_mul, mul_comm]
    | zero =>
        exact ⟨0, by simp⟩
    | add x y hx hy hx' hy' =>
        rcases hx' with ⟨rx, hrx⟩
        rcases hy' with ⟨ry, hry⟩
        refine ⟨rx + ry, ?_⟩
        calc
          algebraMap exampleBaseRing exampleFractionRing Q * (x + y).1 =
              algebraMap exampleBaseRing exampleFractionRing Q * x.1 +
                algebraMap exampleBaseRing exampleFractionRing Q * y.1 := by
                  rw [map_mul, mul_add]
          _ = algebraMap exampleBaseRing exampleFractionRing rx +
                algebraMap exampleBaseRing exampleFractionRing ry := by
                  rw [hrx, hry]
          _ = algebraMap exampleBaseRing exampleFractionRing (rx + ry) := by
                  rw [map_add]
    | smul a x hx hx' =>
        rcases hx' with ⟨rx, hrx⟩
        refine ⟨a * rx, ?_⟩
        calc
          algebraMap exampleBaseRing exampleFractionRing Q * (a • x).1 =
              algebraMap exampleBaseRing exampleFractionRing Q *
                (algebraMap exampleBaseRing exampleFractionRing a * x.1) := by
                  rw [Algebra.smul_def]
          _ = algebraMap exampleBaseRing exampleFractionRing a *
                (algebraMap exampleBaseRing exampleFractionRing Q * x.1) := by
                  ring
          _ = algebraMap exampleBaseRing exampleFractionRing a *
                algebraMap exampleBaseRing exampleFractionRing rx := by
                  rw [hrx]
          _ = algebraMap exampleBaseRing exampleFractionRing (a * rx) := by
                  rw [map_mul]
  obtain ⟨x₀, hx₀⟩ := Polynomial.exists_max_root Q hQ
  obtain ⟨n, hn⟩ := exists_nat_gt x₀
  have hQeval : Q.eval (n : ℚ) ≠ 0 := by
    intro hzero
    have hle := hx₀ (n : ℚ) hzero
    exact (not_lt_of_ge hle) hn
  let target : ExampleModule :=
    ⟨exampleFractionalGenerator n, Submodule.subset_span ⟨n, rfl⟩⟩
  obtain ⟨r₀, hr₀⟩ := hspan target (by
    rw [hs]
    exact Submodule.mem_top)
  have hr₀' :
      algebraMap exampleBaseRing exampleFractionRing Q *
          (algebraMap exampleBaseRing exampleFractionRing
            (exampleDenominator n))⁻¹ =
        algebraMap exampleBaseRing exampleFractionRing r₀ := by
    simpa [target, exampleFractionalGenerator] using hr₀
  have hfactor : Q = r₀ * exampleDenominator n := by
    apply IsFractionRing.injective exampleBaseRing exampleFractionRing
    calc
      algebraMap exampleBaseRing exampleFractionRing Q =
          (algebraMap exampleBaseRing exampleFractionRing Q *
            (algebraMap exampleBaseRing exampleFractionRing
              (exampleDenominator n))⁻¹) *
              algebraMap exampleBaseRing exampleFractionRing
                (exampleDenominator n) := by
                  rw [mul_assoc, inv_mul_cancel₀ (hden n), mul_one]
      _ = algebraMap exampleBaseRing exampleFractionRing r₀ *
            algebraMap exampleBaseRing exampleFractionRing
              (exampleDenominator n) := by rw [hr₀']
      _ = algebraMap exampleBaseRing exampleFractionRing
            (r₀ * exampleDenominator n) := by rw [map_mul]
  apply hQeval
  calc
    Q.eval (n : ℚ) = (r₀ * exampleDenominator n).eval (n : ℚ) := by
      rw [hfactor]
    _ = 0 := by simp [exampleDenominator]

/-- Every prime localization of `M` is a free rank-one module over `Rₚ`. -/
theorem exampleModule_localized_equiv
    (p : Ideal exampleBaseRing) [p.IsPrime] :
    Nonempty (exampleModuleAtPrime p ≃ₗ[exampleBaseRingAtPrime p]
      exampleBaseRingAtPrime p) := by
  have hden_not_mem {n k : ℕ} (hneq : k ≠ n)
      (hn : exampleDenominator n ∈ p) : exampleDenominator k ∉ p := by
    intro hk
    have hc : Polynomial.C ((n : ℚ) - (k : ℚ)) ∈ p := by
      have hsub := sub_mem hk hn
      simpa [exampleDenominator] using hsub
    have hunit : IsUnit (Polynomial.C ((n : ℚ) - (k : ℚ))) := by
      rw [Polynomial.isUnit_C]
      exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hneq.symm))
    exact (show p.IsPrime from inferInstance).ne_top
      (Ideal.eq_top_of_isUnit_mem p hc hunit)
  have hbranch (n : ℕ)
      (hnot : ∀ k, k ≠ n → exampleDenominator k ∉ p) :
      Nonempty (exampleModuleAtPrime p ≃ₗ[exampleBaseRingAtPrime p]
        exampleBaseRingAtPrime p) := by
    let gen : ℕ → ExampleModule := fun k =>
      ⟨exampleFractionalGenerator k, Submodule.subset_span ⟨k, rfl⟩⟩
    let g : ExampleModule := gen n
    let h : exampleBaseRing →ₗ[exampleBaseRing] ExampleModule :=
      { toFun := fun r => r • g
        map_add' := by
          intro r s
          simp only [add_smul]
        map_smul' := by
          intro r s
          change (r * s) • g = r • (s • g)
          rw [mul_smul] }
    have hd (k : ℕ) :
        algebraMap exampleBaseRing exampleFractionRing (exampleDenominator k) ≠ 0 := by
      apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (by
        exact Polynomial.X_sub_C_ne_zero _)
    have hh : Function.Injective h := by
      intro r s hrs
      have hrs' := congrArg Subtype.val hrs
      dsimp [h, g, gen] at hrs'
      apply IsFractionRing.injective exampleBaseRing exampleFractionRing
      apply (mul_right_cancel₀ (inv_ne_zero (hd n)))
      simpa [exampleFractionalGenerator, Algebra.smul_def, hd n] using hrs'
    have hlocal' : ∀ (x : exampleFractionRing) (hx : x ∈ (exampleModule : Set _)),
        ∃ (r : exampleBaseRing) (t : p.primeCompl),
          (t : exampleBaseRing) • x = (h r).1 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          rcases hx with ⟨k, rfl⟩
          by_cases hk : k = n
          · subst k
            exact ⟨1, 1, by simp [h, g, gen]⟩
          · let t : p.primeCompl := ⟨exampleDenominator k, hnot k hk⟩
            refine ⟨exampleDenominator n, t, ?_⟩
            simp [h, g, gen, t, exampleFractionalGenerator, Algebra.smul_def, hd]
      | zero =>
          exact ⟨0, 1, by simp [h]⟩
      | add x y hx hy hx' hy' =>
          rcases hx' with ⟨r₁, t₁, ht₁⟩
          rcases hy' with ⟨r₂, t₂, ht₂⟩
          refine ⟨(t₂ : exampleBaseRing) * r₁ + (t₁ : exampleBaseRing) * r₂,
            t₁ * t₂, ?_⟩
          calc
            ((t₁ * t₂ : p.primeCompl) : exampleBaseRing) • (x + y) =
                (t₂ : exampleBaseRing) • ((t₁ : exampleBaseRing) • x) +
                  (t₁ : exampleBaseRing) • ((t₂ : exampleBaseRing) • y) := by
                    change ((t₁ : exampleBaseRing) * (t₂ : exampleBaseRing)) • (x + y) = _
                    rw [smul_add, mul_smul, mul_smul]
                    congr 1 <;> rw [smul_comm]
            _ = (t₂ : exampleBaseRing) • (h r₁).1 +
                  (t₁ : exampleBaseRing) • (h r₂).1 := by
              rw [ht₁, ht₂]
            _ = (h ((t₂ : exampleBaseRing) * r₁ + (t₁ : exampleBaseRing) * r₂)).1 := by
              calc
                (t₂ : exampleBaseRing) • (h r₁).1 +
                    (t₁ : exampleBaseRing) • (h r₂).1 =
                    (h ((t₂ : exampleBaseRing) * r₁)).1 +
                      (h ((t₁ : exampleBaseRing) * r₂)).1 := by
                        congr 1
                        · simpa [smul_eq_mul] using
                            (congrArg Subtype.val (h.map_smul (t₂ : exampleBaseRing) r₁)).symm
                        · simpa [smul_eq_mul] using
                            (congrArg Subtype.val (h.map_smul (t₁ : exampleBaseRing) r₂)).symm
                _ = (h ((t₂ : exampleBaseRing) * r₁ +
                    (t₁ : exampleBaseRing) * r₂)).1 := by
                      exact congrArg Subtype.val
                        (h.map_add ((t₂ : exampleBaseRing) * r₁)
                          ((t₁ : exampleBaseRing) * r₂)).symm
      | smul a x hx hx' =>
          rcases hx' with ⟨r, t, ht⟩
          refine ⟨a * r, t, ?_⟩
          calc
            (t : exampleBaseRing) • (a • x) =
                a • ((t : exampleBaseRing) • x) := by rw [smul_comm]
            _ = a • (h r).1 := by rw [ht]
            _ = (h (a * r)).1 := by
              simpa [smul_eq_mul] using congrArg Subtype.val (h.map_smul a r).symm
    let e := LocalizedModule.map p.primeCompl h
    have he_inj : Function.Injective e :=
      LocalizedModule.map_injective p.primeCompl h hh
    have he_surj : Function.Surjective e := by
      intro y
      induction y using LocalizedModule.induction_on with
      | h m s =>
          obtain ⟨r, t, ht⟩ := hlocal' m.1 m.2
          have ht' : (t : exampleBaseRing) • m = h r := by
            exact Subtype.ext ht
          refine ⟨LocalizedModule.mk r (s * t), ?_⟩
          simp only [e, LocalizedModule.map_mk]
          rw [← ht', mul_comm]
          exact LocalizedModule.mk_cancel_common_left t s m
    exact ⟨(LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩).symm⟩
  classical
  by_cases hp : ∃ n, exampleDenominator n ∈ p
  · obtain ⟨n, hn⟩ := hp
    exact hbranch n (fun k hk => hden_not_mem hk hn)
  · exact hbranch 0 (fun k hk hk' => hp ⟨k, hk'⟩)

/-! ## The analogous prime-reciprocal module over `ℤ` -/

/-- The base ring `R = ℤ` in the analogous example. -/
abbrev integerExampleBaseRing := ℤ

/-- The ambient fraction field `ℚ` in the analogous example. -/
abbrev integerExampleFractionRing := ℚ

/-- The element `1 / p` of `ℚ` for a prime natural number `p`. -/
def integerExampleFractionalGenerator (p : Nat.Primes) :
    integerExampleFractionRing :=
  (algebraMap integerExampleBaseRing integerExampleFractionRing (p.1 : ℤ))⁻¹

/-- The `ℤ`-submodule `M = ∑ₚ (1 / p) ℤ` in `ℚ`. -/
def integerExampleModule :
    Submodule integerExampleBaseRing integerExampleFractionRing :=
  Submodule.span integerExampleBaseRing (Set.range integerExampleFractionalGenerator)

/-- The set of rational fractions with a nonzero squarefree natural denominator. -/
def integerExampleSquarefreeFractions : Set integerExampleFractionRing :=
  {q | ∃ a : ℤ, ∃ b : ℕ, b ≠ 0 ∧ Squarefree b ∧
    q = (a : ℚ) / (b : ℚ)}

/-- The prime-reciprocal module consists exactly of the squarefree-denominator fractions. -/
theorem integerExampleModule_eq_squarefreeFractions :
    (integerExampleModule : Set integerExampleFractionRing) =
      integerExampleSquarefreeFractions := by
  sorry

end Formalization.Books.Examples.Unit31
