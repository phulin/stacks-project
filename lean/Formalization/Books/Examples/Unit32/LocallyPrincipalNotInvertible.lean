import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Regular.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Examples, Chapter 32: A noninvertible ideal invertible in stalks

This file records the constructions and theorem interfaces in the source
section.  The mathematical proofs belong to the proof stage.
-/

noncomputable section

namespace Formalization.Books.Examples.Unit32

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
                    simp [map_mul, mul_comm, mul_left_comm]
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
  obtain ⟨N, s, hs⟩ := @Module.Finite.exists_fin exampleBaseRing ExampleModule
    _ _ _ hfinite
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
                  change algebraMap exampleBaseRing exampleFractionRing Q *
                      (x.1 + y.1) = _
                  rw [mul_add]
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
                  change algebraMap exampleBaseRing exampleFractionRing Q *
                      (a • x.1) = _
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

/-- Every prime localization of `M` is a free rank-one module. -/
theorem exampleModule_localized_equiv
    (p : Ideal exampleBaseRing) [p.IsPrime] :
    Nonempty
      (LocalizedModule p.primeCompl ExampleModule ≃ₗ[Localization p.primeCompl]
        Localization p.primeCompl) := by
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
      Nonempty (LocalizedModule p.primeCompl ExampleModule ≃ₗ[Localization p.primeCompl]
        Localization p.primeCompl) := by
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
                    congr 1; rw [smul_comm]
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

/-! ## The symmetric algebra and its module-generated ideal -/

/-- The ring `A = SymmetricAlgebra_R(M)`. -/
abbrev exampleAlgebra := SymmetricAlgebra exampleBaseRing ExampleModule

/-- The ideal generated by the image of `M` in its symmetric algebra.

The source writes this ideal as `M A` and as the direct sum of the positive
graded pieces.  `Ideal.span` of the canonical map is the ideal-level form of
that same construction available in Mathlib's ungraded symmetric-algebra API.
-/
def exampleIdeal : Ideal exampleAlgebra :=
  Ideal.span (Set.range (SymmetricAlgebra.ι exampleBaseRing ExampleModule))

/-- The ideal `I` is nonzero. -/
theorem exampleIdeal_ne_bot : exampleIdeal ≠ ⊥ := by
  let f : exampleAlgebra →ₐ[exampleBaseRing]
      TrivSqZeroExt exampleBaseRing ExampleModule :=
    SymmetricAlgebra.lift (R := exampleBaseRing) (M := ExampleModule)
      (A := TrivSqZeroExt exampleBaseRing ExampleModule)
      (TrivSqZeroExt.inrHom exampleBaseRing ExampleModule)
  let proj : exampleAlgebra →ₗ[exampleBaseRing] ExampleModule :=
    (TrivSqZeroExt.sndHom exampleBaseRing ExampleModule).comp f.toLinearMap
  have hproj (m : ExampleModule) :
      proj (SymmetricAlgebra.ι exampleBaseRing ExampleModule m) = m := by
    simp [proj, f]
  have hden (k : ℕ) :
      algebraMap exampleBaseRing exampleFractionRing (exampleDenominator k) ≠ 0 := by
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.X_sub_C_ne_zero _)
  let m : ExampleModule :=
    ⟨exampleFractionalGenerator 0, Submodule.subset_span ⟨0, rfl⟩⟩
  have hm : m ≠ 0 := by
    intro hm
    have hm' : exampleFractionalGenerator 0 = 0 := congrArg Subtype.val hm
    exact inv_ne_zero (hden 0) hm'
  intro hbot
  have hi : SymmetricAlgebra.ι exampleBaseRing ExampleModule m = 0 := by
    have hi' : SymmetricAlgebra.ι exampleBaseRing ExampleModule m ∈
        (⊥ : Ideal exampleAlgebra) := by
      rw [← hbot]
      exact Ideal.subset_span ⟨m, rfl⟩
    simpa using hi'
  apply hm
  rw [← hproj m, hi]
  simp [proj]

private instance exampleModuleOppositeModule :
    Module (exampleBaseRingᵐᵒᵖ) ExampleModule :=
  Submodule.module' exampleModule

/-- The ideal `I` is not finitely generated as an ideal of `A`. -/
theorem exampleIdeal_not_finitely_generated : ¬ exampleIdeal.FG := by
  intro hfg
  rcases hfg with ⟨S, hS⟩
  let f : exampleAlgebra →ₐ[exampleBaseRing]
      TrivSqZeroExt exampleBaseRing ExampleModule :=
    SymmetricAlgebra.lift (R := exampleBaseRing) (M := ExampleModule)
      (A := TrivSqZeroExt exampleBaseRing ExampleModule)
      (TrivSqZeroExt.inrHom exampleBaseRing ExampleModule)
  let proj : exampleAlgebra →ₗ[exampleBaseRing] ExampleModule :=
    (TrivSqZeroExt.sndHom exampleBaseRing ExampleModule).comp f.toLinearMap
  have hproj (m : ExampleModule) :
      proj (SymmetricAlgebra.ι exampleBaseRing ExampleModule m) = m := by
    simp [proj, f]
  have hzero : ∀ a : exampleAlgebra, a ∈ exampleIdeal → (f a).fst = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨m, rfl⟩
        simp [f]
    | zero => simp
    | add x y hx hy hx' hy' =>
        simp [hx', hy']
    | smul r x hx hx' =>
        simp [f, hx']
  have hspan (a : exampleAlgebra)
      (ha : a ∈ Ideal.span (S : Set exampleAlgebra)) :
      proj a ∈ Submodule.span exampleBaseRing (proj '' (S : Set exampleAlgebra)) := by
    induction ha using Submodule.span_induction with
    | mem x hx =>
        exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y hx hy hx' hy' =>
        rw [map_add]
        exact Submodule.add_mem _ hx' hy'
    | smul r x hx hx' =>
        have hxI : x ∈ exampleIdeal := by
          rw [← hS]
          exact hx
        have hxzero := hzero x hxI
        change (f (r * x)).snd ∈ _
        rw [map_mul]
        simp only [TrivSqZeroExt.snd_mul, hxzero, MulOpposite.op_zero, zero_smul, add_zero]
        exact Submodule.smul_mem _ (f r).fst hx'
  have htop :
      Submodule.span exampleBaseRing (proj '' (S : Set exampleAlgebra)) =
        (⊤ : Submodule exampleBaseRing ExampleModule) := by
    apply le_antisymm le_top
    intro m hm
    have hi : SymmetricAlgebra.ι exampleBaseRing ExampleModule m ∈
        Ideal.span (S : Set exampleAlgebra) := by
      rw [hS]
      exact Ideal.subset_span ⟨m, rfl⟩
    have hi' := hspan _ hi
    simpa [hproj] using hi'
  have hfg_top : (⊤ : Submodule exampleBaseRing ExampleModule).FG := by
    rw [← htop]
    exact Submodule.fg_span (S.finite_toSet.image proj)
  exact exampleModule_not_finite (Module.Finite.of_fg_top hfg_top)

/-- The ideal `I` is not invertible as an `A`-module. -/
theorem exampleIdeal_not_invertible :
    ¬ Module.Invertible exampleAlgebra exampleIdeal := by
  sorry

/-! ## The local computations -/

/-- The localization of `R` at a prime `p`. -/
abbrev exampleBaseRingAtPrime (p : Ideal exampleBaseRing) [p.IsPrime] :=
  Localization p.primeCompl

/-- The localization of `M` at the same prime. -/
abbrev exampleModuleAtPrime (p : Ideal exampleBaseRing) [p.IsPrime] :=
  LocalizedModule p.primeCompl ExampleModule

/-- The localization `Aₚ` obtained by inverting the image of `R \ p` in `A`. -/
abbrev exampleAlgebraAtBasePrime (p : Ideal exampleBaseRing) [p.IsPrime] :=
  Localization (Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl)

/-- The localization `Iₚ` of `I` in `Aₚ`. -/
def exampleIdealAtBasePrime
    (p : Ideal exampleBaseRing) [p.IsPrime] :
    Ideal (exampleAlgebraAtBasePrime p) :=
  exampleIdeal.map (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p))

/-- The symmetric-algebra identification after localizing at `p`. -/
theorem exampleAlgebraAtBasePrime_equiv_symmetricAlgebra
    (p : Ideal exampleBaseRing) [p.IsPrime] :
    Nonempty
      (exampleAlgebraAtBasePrime p ≃ₐ[exampleBaseRingAtPrime p]
        SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) := by
  sorry

/-- The one-variable symmetric algebra is a polynomial ring. -/
noncomputable def symmetricAlgebraSelfPolynomialEquiv
    (S : Type*) [CommSemiring S] :
    SymmetricAlgebra S S ≃ₐ[S] Polynomial S :=
  (SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton Unit S)).trans
    (MvPolynomial.uniqueAlgEquiv S Unit)

/-- The local symmetric algebra is therefore identified with `Rₚ[T]`. -/
theorem exampleAlgebraAtBasePrime_equiv_polynomial
    (p : Ideal exampleBaseRing) [p.IsPrime] :
    Nonempty
      (exampleAlgebraAtBasePrime p ≃ₐ[exampleBaseRingAtPrime p]
        Polynomial (exampleBaseRingAtPrime p)) := by
  sorry

/-- At a base prime, `Iₚ` is generated by a regular element `T`. -/
theorem exampleIdealAtBasePrime_isPrincipal_regular
    (p : Ideal exampleBaseRing) [p.IsPrime] :
    ∃ T : exampleAlgebraAtBasePrime p,
      exampleIdealAtBasePrime p = Ideal.span {T} ∧ IsRegular T := by
  sorry

/-- The localization of `I` at a prime ideal `q` of `A`. -/
def exampleIdealAtPrime (q : Ideal exampleAlgebra) [q.IsPrime] :
    Ideal (Localization q.primeCompl) :=
  exampleIdeal.map (algebraMap exampleAlgebra (Localization q.primeCompl))

/-- Every prime stalk of `I` is a principal ideal. -/
theorem exampleIdealAtPrime_isPrincipal
    (q : Ideal exampleAlgebra) [q.IsPrime] :
    (exampleIdealAtPrime q).IsPrincipal := by
  sorry

/-! ## The ring-theoretic properties of the example -/

/-- The ring `A` is a domain. -/
theorem exampleAlgebra_isDomain : IsDomain exampleAlgebra := by
  sorry

/-- Every prime stalk of `I` is generated by a nonzero element. -/
theorem exampleIdealAtPrime_isPrincipal_nonzero
    (q : Ideal exampleAlgebra) [q.IsPrime] :
    ∃ f : Localization q.primeCompl,
      exampleIdealAtPrime q = Ideal.span {f} ∧ f ≠ 0 := by
  sorry

/-- The ring `A` is not Noetherian. -/
theorem exampleAlgebra_not_noetherian : ¬ IsNoetherianRing exampleAlgebra := by
  sorry

/-- Every prime localization of `A` is Noetherian. -/
theorem exampleAlgebra_prime_localizations_noetherian :
    ∀ (q : Ideal exampleAlgebra) (hq : q.IsPrime),
      letI : q.IsPrime := hq
      IsNoetherianRing (Localization q.primeCompl) := by
  sorry

/-! ## A source-facing predicate and the final example -/

/-- An ideal is principal after localization at every prime.

This name records the prime-local condition without using the source's
potentially misleading shorthand “locally principal”.
-/
def PrincipalAtEveryPrime {A : Type*} [CommRing A] (I : Ideal A) : Prop :=
  ∀ (q : Ideal A) (hq : q.IsPrime),
    letI : q.IsPrime := hq
    (I.map (algebraMap A (Localization q.primeCompl))).IsPrincipal

/-- The constructed ideal satisfies the source's all-primes principal condition. -/
theorem exampleIdeal_principalAtEveryPrime :
    PrincipalAtEveryPrime exampleIdeal := by
  intro q hq
  exact @exampleIdealAtPrime_isPrincipal q hq

/-- There is a domain with a nonzero ideal principal in every prime localization
but not invertible as a module. -/
theorem exists_domain_nonzeroIdeal_principalAtEveryPrime_not_invertible :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (I : Ideal A),
      I ≠ ⊥ ∧ PrincipalAtEveryPrime I ∧ ¬ Module.Invertible A I := by
  sorry

end Formalization.Books.Examples.Unit32
