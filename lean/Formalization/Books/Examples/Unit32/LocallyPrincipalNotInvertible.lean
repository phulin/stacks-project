import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Regular.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.Basic
import Formalization.Books.Examples.Unit31.NonfiniteModule

/-!
# Examples, Chapter 32: A noninvertible ideal invertible in stalks

This file records the constructions and theorem interfaces in the source
section.  The mathematical proofs belong to the proof stage.
-/

noncomputable section

namespace Formalization.Books.Examples.Unit32

open Formalization.Books.Examples.Unit31

/-! ## The fractional module over `ℚ[x]`

The ring, fractional module, and its prime-local equivalence are defined in
the immediately preceding chapter and reused here, as in the source's
reference to the construction of Section `section-nonfree`.
-/

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
  intro h
  let _ : Module.Invertible exampleAlgebra exampleIdeal := h
  exact exampleIdeal_not_finitely_generated (Module.Finite.iff_fg.mp inferInstance)

/-! ## The local computations -/

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
  refine ⟨?_⟩
  let fA : exampleAlgebra →ₐ[exampleBaseRing]
      SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) :=
    SymmetricAlgebra.lift
      (((SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)).restrictScalars
          exampleBaseRing).comp (LocalizedModule.mkLinearMap p.primeCompl ExampleModule))
  let hunit : ∀ y : Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl,
      IsUnit (fA y.1) := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    rw [fA.commutes]
    have hmap : algebraMap exampleBaseRing
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) =
        (algebraMap (exampleBaseRingAtPrime p)
          (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))).comp
            (algebraMap exampleBaseRing (exampleBaseRingAtPrime p)) :=
      IsScalarTower.algebraMap_eq _ _ _
    rw [hmap]
    simpa only [RingHom.comp_apply] using
      IsUnit.map (algebraMap (exampleBaseRingAtPrime p)
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)))
        (IsLocalization.map_units (S := exampleBaseRingAtPrime p) ⟨s, hs⟩)
  let f0 : exampleAlgebraAtBasePrime p →ₐ[exampleBaseRing]
      SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) :=
    IsLocalization.liftAlgHom hunit
  let f : exampleAlgebraAtBasePrime p →ₐ[exampleBaseRingAtPrime p]
      SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) :=
    f0.extendScalarsOfIsLocalization (exampleBaseRingAtPrime p) p.primeCompl
  let gA : ExampleModule →ₗ[exampleBaseRing] exampleAlgebraAtBasePrime p :=
    ((Algebra.linearMap exampleAlgebra (exampleAlgebraAtBasePrime p)).restrictScalars
        exampleBaseRing).comp (SymmetricAlgebra.ι exampleBaseRing ExampleModule)
  let hEnd : ∀ s : p.primeCompl,
      IsUnit (algebraMap exampleBaseRing
        (Module.End exampleBaseRing (exampleAlgebraAtBasePrime p)) s) := by
    intro s
    have hsA : IsUnit (algebraMap exampleBaseRing
        (exampleAlgebraAtBasePrime p) s) := by
      have hmap : algebraMap exampleBaseRing (exampleAlgebraAtBasePrime p) =
          (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)).comp
            (algebraMap exampleBaseRing exampleAlgebra) :=
        IsScalarTower.algebraMap_eq _ _ _
      rw [hmap]
      simpa only [RingHom.comp_apply] using
        (IsLocalization.map_units (S := exampleAlgebraAtBasePrime p)
          (⟨algebraMap exampleBaseRing exampleAlgebra s,
            (show algebraMap exampleBaseRing exampleAlgebra s ∈
              Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl from
              ⟨s, s.2, rfl⟩)⟩ :
            Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl))
    rw [Module.End.isUnit_iff]
    constructor
    · rintro a b (e : s • a = s • b)
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      exact hsA.mul_left_cancel e
    · intro a
      refine ⟨((hsA.unit⁻¹ : (exampleAlgebraAtBasePrime p)ˣ) :
          exampleAlgebraAtBasePrime p) * a, ?_⟩
      rw [Module.algebraMap_end_apply, Algebra.smul_def, ← mul_assoc,
        IsUnit.mul_val_inv, one_mul]
  let hR : exampleModuleAtPrime p →ₗ[exampleBaseRing] exampleAlgebraAtBasePrime p :=
    IsLocalizedModule.lift p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl ExampleModule) gA hEnd
  let hRp : exampleModuleAtPrime p →ₗ[exampleBaseRingAtPrime p]
      exampleAlgebraAtBasePrime p :=
    hR.extendScalarsOfIsLocalization p.primeCompl (exampleBaseRingAtPrime p)
  let g : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) →ₐ[
      exampleBaseRingAtPrime p] exampleAlgebraAtBasePrime p :=
    SymmetricAlgebra.lift hRp
  let aMap : exampleAlgebra →ₐ[exampleBaseRing] exampleAlgebraAtBasePrime p :=
    IsScalarTower.toAlgHom exampleBaseRing exampleAlgebra (exampleAlgebraAtBasePrime p)
  have hfA : f.toRingHom.comp (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)) =
      fA.toRingHom := by
    change f0.toRingHom.comp (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)) =
      fA.toRingHom
    exact IsLocalization.lift_comp hunit
  have hcomp : (g.restrictScalars exampleBaseRing).comp fA = aMap := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [g, hRp, fA]
    change hR (LocalizedModule.mkLinearMap p.primeCompl ExampleModule m) =
      aMap (SymmetricAlgebra.ι exampleBaseRing ExampleModule m)
    rw [IsLocalizedModule.lift_apply]
    rfl
  have hlin :
      (f.toLinearMap.comp hRp).restrictScalars exampleBaseRing =
        (SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)).restrictScalars
          exampleBaseRing := by
    have hEndSym : ∀ s : p.primeCompl,
        IsUnit (algebraMap exampleBaseRing
          (Module.End exampleBaseRing
            (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))) s) := by
      intro s
      have hs : IsUnit (algebraMap exampleBaseRing
          (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) s) := by
        have hmap : algebraMap exampleBaseRing
            (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) =
            (algebraMap (exampleBaseRingAtPrime p)
              (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))).comp
                (algebraMap exampleBaseRing (exampleBaseRingAtPrime p)) :=
          IsScalarTower.algebraMap_eq _ _ _
        rw [hmap]
        simpa only [RingHom.comp_apply] using
          IsUnit.map (algebraMap (exampleBaseRingAtPrime p)
            (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)))
            (IsLocalization.map_units (S := exampleBaseRingAtPrime p) s)
      rw [Module.End.isUnit_iff]
      constructor
      · rintro a b (e : s • a = s • b)
        simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
        exact hs.mul_left_cancel e
      · intro a
        refine ⟨((hs.unit⁻¹ :
            (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))ˣ) :
            SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) * a, ?_⟩
        rw [Module.algebraMap_end_apply, Algebra.smul_def, ← mul_assoc,
          IsUnit.mul_val_inv, one_mul]
    apply IsLocalizedModule.ext p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl ExampleModule) hEndSym
    ext m
    simp [f, hRp, hR, gA]
    change f0 (hR (LocalizedModule.mkLinearMap p.primeCompl ExampleModule m)) =
      (SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))
        (LocalizedModule.mkLinearMap p.primeCompl ExampleModule m)
    rw [IsLocalizedModule.lift_apply]
    have hfAm := congrArg
      (fun k => k (SymmetricAlgebra.ι exampleBaseRing ExampleModule m)) hfA
    simpa [gA, f, fA] using hfAm
  have hgf : (g.comp f).toRingHom =
      (AlgHom.id (exampleBaseRingAtPrime p) (exampleAlgebraAtBasePrime p)).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl)
    apply RingHom.ext
    intro a
    change g (f (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p) a)) =
      aMap a
    have hfa : f (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p) a) = fA a :=
      congrArg (fun k => k a) hfA
    calc
      g (f (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p) a)) = g (fA a) :=
        congrArg g hfa
      _ = aMap a := congrArg (fun k => k a) hcomp
  have hfg : f.comp g =
      AlgHom.id (exampleBaseRingAtPrime p)
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    change f (g (SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) m)) = _
    rw [SymmetricAlgebra.lift_ι_apply]
    exact congrArg (fun k => k m) hlin
  refine AlgEquiv.ofBijective f ?_
  constructor
  · intro x y hxy
    calc
      x = g (f x) := (congrArg (fun k => k x) hgf).symm
      _ = g (f y) := congrArg g hxy
      _ = y := congrArg (fun k => k y) hgf
  · intro y
    refine ⟨g y, ?_⟩
    simpa using congrArg (fun k => k y) hfg

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
  obtain ⟨eA⟩ := exampleAlgebraAtBasePrime_equiv_symmetricAlgebra p
  obtain ⟨eM⟩ := exampleModule_localized_equiv p
  let seHom : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) →ₐ[
      exampleBaseRingAtPrime p] SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p) :=
    SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p)).comp
        eM.toLinearMap)
  let seInv : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p) →ₐ[
      exampleBaseRingAtPrime p] SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) :=
    SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)).comp
        eM.symm.toLinearMap)
  have hse1 : seInv.comp seHom =
      AlgHom.id (exampleBaseRingAtPrime p)
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    simp [seHom, seInv]
  have hse2 : seHom.comp seInv =
      AlgHom.id (exampleBaseRingAtPrime p)
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p)) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    simp [seHom, seInv]
  let se : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) ≃ₐ[
      exampleBaseRingAtPrime p] SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p) :=
    AlgEquiv.ofBijective seHom (by
      constructor
      · intro x y hxy
        calc
          x = seInv (seHom x) := (congrArg (fun k => k x) hse1).symm
          _ = seInv (seHom y) := congrArg seInv hxy
          _ = y := congrArg (fun k => k y) hse1
      · intro y
        refine ⟨seInv y, ?_⟩
        exact congrArg (fun k => k y) hse2)
  exact ⟨eA.trans (se.trans (symmetricAlgebraSelfPolynomialEquiv
    (exampleBaseRingAtPrime p)))⟩

/-- At a base prime, `Iₚ` is generated by a regular element `T`. -/
theorem exampleIdealAtBasePrime_isPrincipal_regular
    (p : Ideal exampleBaseRing) [p.IsPrime] :
    ∃ T : exampleAlgebraAtBasePrime p,
      exampleIdealAtBasePrime p = Ideal.span {T} ∧ IsRegular T := by
  obtain ⟨eM⟩ := exampleModule_localized_equiv p
  let gA : ExampleModule →ₗ[exampleBaseRing] exampleAlgebraAtBasePrime p :=
    ((Algebra.linearMap exampleAlgebra (exampleAlgebraAtBasePrime p)).restrictScalars
        exampleBaseRing).comp (SymmetricAlgebra.ι exampleBaseRing ExampleModule)
  let hEnd : ∀ s : p.primeCompl,
      IsUnit (algebraMap exampleBaseRing
        (Module.End exampleBaseRing (exampleAlgebraAtBasePrime p)) s) := by
    intro s
    have hsA : IsUnit (algebraMap exampleBaseRing
        (exampleAlgebraAtBasePrime p) s) := by
      have hmap : algebraMap exampleBaseRing (exampleAlgebraAtBasePrime p) =
          (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)).comp
            (algebraMap exampleBaseRing exampleAlgebra) :=
        IsScalarTower.algebraMap_eq _ _ _
      rw [hmap]
      simpa only [RingHom.comp_apply] using
        (IsLocalization.map_units (S := exampleAlgebraAtBasePrime p)
          (⟨algebraMap exampleBaseRing exampleAlgebra s,
            (show algebraMap exampleBaseRing exampleAlgebra s ∈
              Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl from
              ⟨s, s.2, rfl⟩)⟩ :
            Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl))
    rw [Module.End.isUnit_iff]
    constructor
    · rintro a b (e : s • a = s • b)
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      exact hsA.mul_left_cancel e
    · intro a
      refine ⟨((hsA.unit⁻¹ : (exampleAlgebraAtBasePrime p)ˣ) :
          exampleAlgebraAtBasePrime p) * a, ?_⟩
      rw [Module.algebraMap_end_apply, Algebra.smul_def, ← mul_assoc,
        IsUnit.mul_val_inv, one_mul]
  let hR : exampleModuleAtPrime p →ₗ[exampleBaseRing] exampleAlgebraAtBasePrime p :=
    IsLocalizedModule.lift p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl ExampleModule) gA hEnd
  let hRp : exampleModuleAtPrime p →ₗ[exampleBaseRingAtPrime p]
      exampleAlgebraAtBasePrime p :=
    hR.extendScalarsOfIsLocalization p.primeCompl (exampleBaseRingAtPrime p)
  let T : exampleAlgebraAtBasePrime p := hRp (eM.symm 1)
  have hmk (m : ExampleModule) :
      hRp (LocalizedModule.mkLinearMap p.primeCompl ExampleModule m) = gA m := by
    change hR (LocalizedModule.mkLinearMap p.primeCompl ExampleModule m) = gA m
    rw [IsLocalizedModule.lift_apply]
  have hgen (m : ExampleModule) : gA m ∈ Ideal.span ({T} : Set _ ) := by
    let x : exampleModuleAtPrime p := LocalizedModule.mkLinearMap p.primeCompl ExampleModule m
    have hx : x = eM x • eM.symm 1 := by
      apply eM.injective
      simp
    have hgx : gA m = (algebraMap (exampleBaseRingAtPrime p)
        (exampleAlgebraAtBasePrime p) (eM x)) * T := by
      calc
        gA m = hRp x := (hmk m).symm
        _ = hRp (eM x • eM.symm 1) := congrArg hRp hx
        _ = (algebraMap (exampleBaseRingAtPrime p)
            (exampleAlgebraAtBasePrime p) (eM x)) * T := by
          rw [map_smul]
          simp [T, Algebra.smul_def]
    rw [hgx]
    exact (Ideal.span ({T} : Set _)).mul_mem_left _ (Ideal.subset_span (by simp))
  have hIdeal : exampleIdealAtBasePrime p = Ideal.span (Set.range gA) := by
    rw [exampleIdealAtBasePrime, exampleIdeal, Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨SymmetricAlgebra.ι exampleBaseRing ExampleModule m,
        ⟨m, rfl⟩, rfl⟩
  have hspan : Ideal.span (Set.range gA) = Ideal.span ({T} : Set _) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro x hx
      rcases hx with ⟨m, rfl⟩
      exact hgen m
    · rw [Ideal.span_le]
      intro x hx
      rcases hx with rfl
      change hRp (eM.symm (1 : exampleBaseRingAtPrime p)) ∈
        Ideal.span (Set.range gA)
      induction eM.symm (1 : exampleBaseRingAtPrime p) using
          LocalizedModule.induction_on with
      | h m s =>
          have hIso :
              (IsLocalizedModule.iso p.primeCompl
                (LocalizedModule.mkLinearMap p.primeCompl ExampleModule)).symm
                  (LocalizedModule.mk m s) = LocalizedModule.mk m s := by
            apply IsLocalizedModule.iso_symm_apply'
            change (s : exampleBaseRing) • LocalizedModule.mk m s =
              LocalizedModule.mk m 1
            rw [LocalizedModule.smul'_mk]
            apply LocalizedModule.mk_eq.mpr
            refine ⟨1, ?_⟩
            simp [Submonoid.smul_def]
          change hR (LocalizedModule.mk m s) ∈ Ideal.span (Set.range gA)
          simp only [hR, IsLocalizedModule.lift]
          simp only [LinearMap.coe_comp, Function.comp_apply]
          change (LocalizedModule.lift p.primeCompl gA hEnd)
              ((IsLocalizedModule.iso p.primeCompl
                (LocalizedModule.mkLinearMap p.primeCompl ExampleModule)).symm
                  (LocalizedModule.mk m s)) ∈ Ideal.span (Set.range gA)
          rw [hIso]
          rw [LocalizedModule.lift_mk]
          have hsA : IsUnit (algebraMap exampleBaseRing
              (exampleAlgebraAtBasePrime p) s) := by
            have hmap : algebraMap exampleBaseRing (exampleAlgebraAtBasePrime p) =
                (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)).comp
                  (algebraMap exampleBaseRing exampleAlgebra) :=
              IsScalarTower.algebraMap_eq _ _ _
            rw [hmap]
            simpa only [RingHom.comp_apply] using
              (IsLocalization.map_units (S := exampleAlgebraAtBasePrime p)
                (⟨algebraMap exampleBaseRing exampleAlgebra s,
                  (show algebraMap exampleBaseRing exampleAlgebra s ∈
                    Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl from
                    ⟨s, s.2, rfl⟩)⟩ :
                  Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl))
          have hscalar : (hEnd s).unit⁻¹.val (gA m) =
              ((hsA.unit⁻¹ : (exampleAlgebraAtBasePrime p)ˣ) :
                exampleAlgebraAtBasePrime p) * gA m := by
            apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff
              exampleBaseRing (hEnd s)
              (gA m) (((hsA.unit⁻¹ : (exampleAlgebraAtBasePrime p)ˣ) :
                exampleAlgebraAtBasePrime p) * gA m)).2
            rw [Algebra.smul_def, ← mul_assoc,
              hsA.mul_val_inv, one_mul]
          rw [hscalar]
          exact (Ideal.span (Set.range gA)).mul_mem_left _
            (Ideal.subset_span ⟨m, rfl⟩)
  let fA : exampleAlgebra →ₐ[exampleBaseRing]
      SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) :=
    SymmetricAlgebra.lift
      (((SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)).restrictScalars
          exampleBaseRing).comp (LocalizedModule.mkLinearMap p.primeCompl ExampleModule))
  let hunit : ∀ y : Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl,
      IsUnit (fA y.1) := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    rw [fA.commutes]
    have hmap : algebraMap exampleBaseRing
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) =
        (algebraMap (exampleBaseRingAtPrime p)
          (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))).comp
            (algebraMap exampleBaseRing (exampleBaseRingAtPrime p)) :=
      IsScalarTower.algebraMap_eq _ _ _
    rw [hmap]
    simpa only [RingHom.comp_apply] using
      IsUnit.map (algebraMap (exampleBaseRingAtPrime p)
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)))
        (IsLocalization.map_units (S := exampleBaseRingAtPrime p) ⟨s, hs⟩)
  let f0 : exampleAlgebraAtBasePrime p →ₐ[exampleBaseRing]
      SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) :=
    IsLocalization.liftAlgHom hunit
  let f : exampleAlgebraAtBasePrime p →ₐ[exampleBaseRingAtPrime p]
      SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) :=
    f0.extendScalarsOfIsLocalization (exampleBaseRingAtPrime p) p.primeCompl
  let g : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) →ₐ[
      exampleBaseRingAtPrime p] exampleAlgebraAtBasePrime p :=
    SymmetricAlgebra.lift hRp
  let aMap : exampleAlgebra →ₐ[exampleBaseRing] exampleAlgebraAtBasePrime p :=
    IsScalarTower.toAlgHom exampleBaseRing exampleAlgebra (exampleAlgebraAtBasePrime p)
  have hfA : f.toRingHom.comp (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)) =
      fA.toRingHom := by
    change f0.toRingHom.comp (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)) =
      fA.toRingHom
    exact IsLocalization.lift_comp hunit
  have hcomp : (g.restrictScalars exampleBaseRing).comp fA = aMap := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [g, hRp, fA]
    change hR (LocalizedModule.mkLinearMap p.primeCompl ExampleModule m) =
      aMap (SymmetricAlgebra.ι exampleBaseRing ExampleModule m)
    rw [IsLocalizedModule.lift_apply]
    rfl
  have hgf : (g.comp f).toRingHom =
      (AlgHom.id (exampleBaseRingAtPrime p) (exampleAlgebraAtBasePrime p)).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl)
    apply RingHom.ext
    intro a
    change g (f (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p) a)) =
      aMap a
    have hfa : f (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p) a) = fA a :=
      congrArg (fun k => k a) hfA
    calc
      g (f (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p) a)) = g (fA a) :=
        congrArg g hfa
      _ = aMap a := congrArg (fun k => k a) hcomp
  have hf_inj : Function.Injective f := by
    intro x y hxy
    calc
      x = g (f x) := (congrArg (fun k => k x) hgf).symm
      _ = g (f y) := congrArg g hxy
      _ = y := congrArg (fun k => k y) hgf
  have hlin :
      (f.toLinearMap.comp hRp).restrictScalars exampleBaseRing =
        (SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)).restrictScalars
          exampleBaseRing := by
    have hEndSym : ∀ s : p.primeCompl,
        IsUnit (algebraMap exampleBaseRing
          (Module.End exampleBaseRing
            (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))) s) := by
      intro s
      have hs : IsUnit (algebraMap exampleBaseRing
          (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) s) := by
        have hmap : algebraMap exampleBaseRing
            (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) =
            (algebraMap (exampleBaseRingAtPrime p)
              (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))).comp
                (algebraMap exampleBaseRing (exampleBaseRingAtPrime p)) :=
          IsScalarTower.algebraMap_eq _ _ _
        rw [hmap]
        simpa only [RingHom.comp_apply] using
          IsUnit.map (algebraMap (exampleBaseRingAtPrime p)
            (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)))
            (IsLocalization.map_units (S := exampleBaseRingAtPrime p) s)
      rw [Module.End.isUnit_iff]
      constructor
      · rintro a b (e : s • a = s • b)
        simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
        exact hs.mul_left_cancel e
      · intro a
        refine ⟨((hs.unit⁻¹ :
            (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))ˣ) :
            SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) * a, ?_⟩
        rw [Module.algebraMap_end_apply, Algebra.smul_def, ← mul_assoc,
          IsUnit.mul_val_inv, one_mul]
    apply IsLocalizedModule.ext p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl ExampleModule) hEndSym
    ext m
    simp [f, hRp, hR, gA]
    change f0 (hR (LocalizedModule.mkLinearMap p.primeCompl ExampleModule m)) =
      (SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))
        (LocalizedModule.mkLinearMap p.primeCompl ExampleModule m)
    rw [IsLocalizedModule.lift_apply]
    have hfAm := congrArg
      (fun k => k (SymmetricAlgebra.ι exampleBaseRing ExampleModule m)) hfA
    convert hfAm using 1 <;> simp [gA, f, f0, fA]
  have hT : f T =
      (SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))
        (eM.symm 1) := by
    have hm := congrArg
      (fun k => k (eM.symm (1 : exampleBaseRingAtPrime p))) hlin
    simpa [T, f] using hm
  let seHom : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) →ₐ[
      exampleBaseRingAtPrime p] SymmetricAlgebra (exampleBaseRingAtPrime p)
        (exampleBaseRingAtPrime p) :=
    SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p)).comp
        eM.toLinearMap)
  let seInv : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p) →ₐ[
      exampleBaseRingAtPrime p] SymmetricAlgebra (exampleBaseRingAtPrime p)
        (exampleModuleAtPrime p) :=
    SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)).comp
        eM.symm.toLinearMap)
  have hse1 : seInv.comp seHom =
      AlgHom.id (exampleBaseRingAtPrime p)
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p)) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    simp [seHom, seInv]
  have hse2 : seHom.comp seInv =
      AlgHom.id (exampleBaseRingAtPrime p)
        (SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p)) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    simp [seHom, seInv]
  let se : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) ≃ₐ[
      exampleBaseRingAtPrime p] SymmetricAlgebra (exampleBaseRingAtPrime p)
        (exampleBaseRingAtPrime p) :=
    AlgEquiv.ofBijective seHom (by
      constructor
      · intro x y hxy
        calc
          x = seInv (seHom x) := (congrArg (fun k => k x) hse1).symm
          _ = seInv (seHom y) := congrArg seInv hxy
          _ = y := congrArg (fun k => k y) hse1
      · intro y
        refine ⟨seInv y, ?_⟩
        exact congrArg (fun k => k y) hse2)
  let E : SymmetricAlgebra (exampleBaseRingAtPrime p) (exampleModuleAtPrime p) ≃ₐ[
      exampleBaseRingAtPrime p] Polynomial (exampleBaseRingAtPrime p) :=
    se.trans (symmetricAlgebraSelfPolynomialEquiv (exampleBaseRingAtPrime p))
  have hsegen : se ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p)
      (exampleModuleAtPrime p)) (eM.symm 1)) =
        SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleBaseRingAtPrime p) 1 := by
    change seHom ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p)
      (exampleModuleAtPrime p)) (eM.symm 1)) = _
    simp [seHom]
  have hEgen : E ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p)
      (exampleModuleAtPrime p)) (eM.symm 1)) =
        Polynomial.X := by
    rw [show E ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p)
        (exampleModuleAtPrime p)) (eM.symm 1)) =
          symmetricAlgebraSelfPolynomialEquiv (exampleBaseRingAtPrime p)
            (se ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p)
              (exampleModuleAtPrime p)) (eM.symm 1)) :
              SymmetricAlgebra (exampleBaseRingAtPrime p)
                (exampleBaseRingAtPrime p) ) by rfl]
    rw [hsegen]
    have heq : SymmetricAlgebra.equivMvPolynomial
        (Module.Basis.singleton Unit (exampleBaseRingAtPrime p))
        (SymmetricAlgebra.ι (exampleBaseRingAtPrime p)
          (exampleBaseRingAtPrime p) 1) = MvPolynomial.X () := by
      simpa using SymmetricAlgebra.equivMvPolynomial_ι_apply
        (Module.Basis.singleton Unit (exampleBaseRingAtPrime p)) ()
    change MvPolynomial.uniqueAlgEquiv (exampleBaseRingAtPrime p) Unit
      (SymmetricAlgebra.equivMvPolynomial
        (Module.Basis.singleton Unit (exampleBaseRingAtPrime p))
        (SymmetricAlgebra.ι (exampleBaseRingAtPrime p)
          (exampleBaseRingAtPrime p) 1)) = Polynomial.X
    rw [heq]
    change MvPolynomial.eval₂ Polynomial.C (fun _ : Unit => Polynomial.X)
      (MvPolynomial.X ()) = Polynomial.X
    rw [MvPolynomial.eval₂_X]
  have hreg0 : IsRegular
      ((SymmetricAlgebra.ι (exampleBaseRingAtPrime p) (exampleModuleAtPrime p))
        (eM.symm 1)) := by
    have hX : IsRegular (Polynomial.X : Polynomial (exampleBaseRingAtPrime p)) :=
      Polynomial.isRegular_X
    constructor
    · intro a b hab
      apply E.injective
      apply hX.left
      simpa [map_mul, hEgen, mul_comm] using congrArg E hab
    · intro a b hab
      apply E.injective
      apply hX.right
      simpa [map_mul, hEgen, mul_comm] using congrArg E hab
  have hregT : IsRegular T := by
    constructor
    · intro a b hab
      apply hf_inj
      apply hreg0.left
      simpa only [map_mul, hT] using congrArg f hab
    · intro a b hab
      apply hf_inj
      apply hreg0.right
      simpa only [map_mul, hT] using congrArg f hab
  refine ⟨T, hIdeal.trans hspan, ?_⟩
  exact hregT

/-- The localization of `I` at a prime ideal `q` of `A`. -/
def exampleIdealAtPrime (q : Ideal exampleAlgebra) [q.IsPrime] :
    Ideal (Localization q.primeCompl) :=
  exampleIdeal.map (algebraMap exampleAlgebra (Localization q.primeCompl))

/-- Every prime stalk of `I` is a principal ideal. -/
theorem exampleIdealAtPrime_isPrincipal
    (q : Ideal exampleAlgebra) [q.IsPrime] :
    (exampleIdealAtPrime q).IsPrincipal := by
  let p : Ideal exampleBaseRing :=
    q.comap (algebraMap exampleBaseRing exampleAlgebra)
  let _ : p.IsPrime := by
    dsimp [p]
    exact Ideal.comap_isPrime (algebraMap exampleBaseRing exampleAlgebra) q
  let hunit : ∀ s : Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl,
      IsUnit (algebraMap exampleAlgebra (Localization q.primeCompl) s.1) := by
    rintro ⟨_, ⟨r, hr, rfl⟩⟩
    change IsUnit (algebraMap exampleAlgebra (Localization q.primeCompl)
      (algebraMap exampleBaseRing exampleAlgebra r))
    exact IsLocalization.map_units (S := Localization q.primeCompl)
      (⟨algebraMap exampleBaseRing exampleAlgebra r,
        by simpa [p] using hr⟩ : q.primeCompl)
  let φ : exampleAlgebraAtBasePrime p →+* Localization q.primeCompl :=
    IsLocalization.lift
      (M := Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl)
      (S := exampleAlgebraAtBasePrime p) hunit
  have hφ : φ.comp (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)) =
      algebraMap exampleAlgebra (Localization q.primeCompl) := by
    exact IsLocalization.lift_comp hunit
  have hmap : (exampleIdealAtBasePrime p).map φ = exampleIdealAtPrime q := by
    rw [exampleIdealAtBasePrime, exampleIdealAtPrime, Ideal.map_map, hφ]
  obtain ⟨T, hT, hreg⟩ := exampleIdealAtBasePrime_isPrincipal_regular p
  rw [← hmap]
  exact (⟨⟨T, hT⟩⟩ : (exampleIdealAtBasePrime p).IsPrincipal).map_ringHom φ

/-! ## The ring-theoretic properties of the example -/

/-- The ring `A` is a domain. -/
theorem exampleAlgebra_isDomain : IsDomain exampleAlgebra := by
  have hcommon : ∀ (m n : ExampleModule), ∃ g : ExampleModule,
      ∃ a b : exampleBaseRing, a • g = m ∧ b • g = n := by
    intro m n
    let N : Submodule exampleBaseRing exampleFractionRing :=
      Submodule.span exampleBaseRing
        ({(m : exampleFractionRing), (n : exampleFractionRing)} : Set _)
    have hN_le : N ≤ exampleModule := by
      change Submodule.span exampleBaseRing
        ({(m : exampleFractionRing), (n : exampleFractionRing)} : Set _) ≤
        exampleModule
      refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with (rfl | rfl)
      · exact m.property
      · exact n.property
    have hfg : N.FG := Submodule.fg_span (Set.toFinite _)
    let _ : Module.Finite exampleBaseRing N := (Module.Finite.iff_fg).mpr hfg
    let _ : Module.IsTorsionFree exampleBaseRing N :=
      Module.IsTorsionFree.of_smul_eq_zero (fun r z hz => by
        by_cases hr : r = 0
        · exact Or.inl hr
        · right
          apply Subtype.ext
          have hz' := congrArg Subtype.val hz
          change (r : exampleBaseRing) • (z : exampleFractionRing) = 0 at hz'
          rw [Algebra.smul_def] at hz'
          have hr' : algebraMap exampleBaseRing exampleFractionRing r ≠ 0 := by
            apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
            exact mem_nonZeroDivisors_iff_ne_zero.mpr hr
          exact (mul_eq_zero.mp hz').resolve_left hr')
    have hfree : Module.Free exampleBaseRing N := by infer_instance
    have hrank : Module.rank exampleBaseRing N ≤ 1 := by
      calc
        Module.rank exampleBaseRing N ≤ Module.rank exampleBaseRing exampleFractionRing :=
          LinearMap.rank_le_of_injective N.subtype N.injective_subtype
        _ = Module.rank exampleFractionRing exampleFractionRing :=
          (IsFractionRing.rank_right_eq exampleBaseRing exampleFractionRing
            exampleFractionRing).symm
        _ = 1 := by simp
    have hprincipal : (⊤ : Submodule exampleBaseRing N).IsPrincipal :=
      (Module.rank_le_one_iff_top_isPrincipal).mp hrank
    rcases hprincipal with ⟨⟨g₀, hg₀⟩⟩
    let g : ExampleModule := ⟨g₀.1, hN_le g₀.2⟩
    have hm : (⟨(m : exampleFractionRing), by
        change (m : exampleFractionRing) ∈ Submodule.span exampleBaseRing
          ({(m : exampleFractionRing), (n : exampleFractionRing)} : Set _)
        apply Submodule.subset_span
        simp⟩ : N) ∈
        Submodule.span exampleBaseRing {g₀} := by
      rw [← hg₀]
      exact Submodule.mem_top
    have hn : (⟨(n : exampleFractionRing), by
        change (n : exampleFractionRing) ∈ Submodule.span exampleBaseRing
          ({(m : exampleFractionRing), (n : exampleFractionRing)} : Set _)
        apply Submodule.subset_span
        simp⟩ : N) ∈
        Submodule.span exampleBaseRing {g₀} := by
      rw [← hg₀]
      exact Submodule.mem_top
    rcases Submodule.mem_span_singleton.mp hm with ⟨a, ha⟩
    rcases Submodule.mem_span_singleton.mp hn with ⟨b, hb⟩
    refine ⟨g, a, b, ?_, ?_⟩
    · apply Subtype.ext
      simpa [g] using congrArg Subtype.val ha
    · apply Subtype.ext
      simpa [g] using congrArg Subtype.val hb
  have hmem : ∀ x : exampleAlgebra, ∃ g : ExampleModule,
      x ∈ Algebra.adjoin exampleBaseRing
        ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g} : Set exampleAlgebra) := by
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap r =>
        refine ⟨0, ?_⟩
        exact (Algebra.adjoin exampleBaseRing _).algebraMap_mem r
    | ι m =>
        exact ⟨m, Algebra.subset_adjoin (by simp)⟩
    | mul x y hx hy =>
        obtain ⟨g₁, hx⟩ := hx
        obtain ⟨g₂, hy⟩ := hy
        obtain ⟨g, a, b, ha, hb⟩ := hcommon g₁ g₂
        let S := Algebra.adjoin exampleBaseRing
          ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g} : Set exampleAlgebra)
        have h1 : SymmetricAlgebra.ι exampleBaseRing ExampleModule g₁ ∈ S := by
          rw [← ha, map_smul, Algebra.smul_def]
          exact S.mul_mem (S.algebraMap_mem a) (Algebra.subset_adjoin (by simp))
        have h2 : SymmetricAlgebra.ι exampleBaseRing ExampleModule g₂ ∈ S := by
          rw [← hb, map_smul, Algebra.smul_def]
          exact S.mul_mem (S.algebraMap_mem b) (Algebra.subset_adjoin (by simp))
        have hle1 : Algebra.adjoin exampleBaseRing
            ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g₁} : Set exampleAlgebra) ≤ S :=
          Algebra.adjoin_le (by simpa using h1)
        have hle2 : Algebra.adjoin exampleBaseRing
            ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g₂} : Set exampleAlgebra) ≤ S :=
          Algebra.adjoin_le (by simpa using h2)
        refine ⟨g, ?_⟩
        change x * y ∈ S
        exact S.mul_mem (hle1 hx) (hle2 hy)
    | add x y hx hy =>
        obtain ⟨g₁, hx⟩ := hx
        obtain ⟨g₂, hy⟩ := hy
        obtain ⟨g, a, b, ha, hb⟩ := hcommon g₁ g₂
        let S := Algebra.adjoin exampleBaseRing
          ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g} : Set exampleAlgebra)
        have h1 : SymmetricAlgebra.ι exampleBaseRing ExampleModule g₁ ∈ S := by
          rw [← ha, map_smul, Algebra.smul_def]
          exact S.mul_mem (S.algebraMap_mem a) (Algebra.subset_adjoin (by simp))
        have h2 : SymmetricAlgebra.ι exampleBaseRing ExampleModule g₂ ∈ S := by
          rw [← hb, map_smul, Algebra.smul_def]
          exact S.mul_mem (S.algebraMap_mem b) (Algebra.subset_adjoin (by simp))
        have hle1 : Algebra.adjoin exampleBaseRing
            ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g₁} : Set exampleAlgebra) ≤ S :=
          Algebra.adjoin_le (by simpa using h1)
        have hle2 : Algebra.adjoin exampleBaseRing
            ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g₂} : Set exampleAlgebra) ≤ S :=
          Algebra.adjoin_le (by simpa using h2)
        refine ⟨g, ?_⟩
        change x + y ∈ S
        exact S.add_mem (hle1 hx) (hle2 hy)
  have hsmul : ∀ (r : exampleBaseRing) (m : ExampleModule),
      Polynomial.C ((r • m : ExampleModule) : exampleFractionRing) * Polynomial.X =
        r • (Polynomial.C (m : exampleFractionRing) * Polynomial.X) := by
    intro r m
    have hcoe :
        ((r • m : ExampleModule) : exampleFractionRing) =
          r • (m : exampleFractionRing) := rfl
    rw [hcoe]
    conv_rhs =>
      rw [← algebraMap_smul exampleFractionRing r, Algebra.smul_def]
    conv_lhs => rw [Algebra.smul_def]
    change Polynomial.C (algebraMap exampleBaseRing exampleFractionRing r *
      (m : exampleFractionRing)) * Polynomial.X =
      algebraMap exampleFractionRing (Polynomial exampleFractionRing)
        (algebraMap exampleBaseRing exampleFractionRing r) *
        (Polynomial.C (m : exampleFractionRing) * Polynomial.X)
    rw [Polynomial.C_mul, ← Polynomial.C_eq_algebraMap]
    ring
  let f : ExampleModule →ₗ[exampleBaseRing] Polynomial exampleFractionRing :=
    { toFun := fun m => Polynomial.C (m : exampleFractionRing) * Polynomial.X
      map_add' := by
        intro m n
        change Polynomial.C ((m : exampleFractionRing) + (n : exampleFractionRing)) *
            Polynomial.X =
          Polynomial.C (m : exampleFractionRing) * Polynomial.X +
            Polynomial.C (n : exampleFractionRing) * Polynomial.X
        rw [Polynomial.C_add, add_mul]
      map_smul' := by
        intro r m
        exact hsmul r m }
  let F : exampleAlgebra →ₐ[exampleBaseRing] Polynomial exampleFractionRing :=
    SymmetricAlgebra.lift f
  have hFι (g : ExampleModule) :
      F (SymmetricAlgebra.ι exampleBaseRing ExampleModule g) =
        Polynomial.C (g : exampleFractionRing) * Polynomial.X := by
    change (SymmetricAlgebra.lift f)
      (SymmetricAlgebra.ι exampleBaseRing ExampleModule g) = _
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  have hFaeval (g : ExampleModule) (P : Polynomial exampleBaseRing) :
      F (Polynomial.aeval
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g) P) =
        Polynomial.aeval (F (SymmetricAlgebra.ι exampleBaseRing ExampleModule g)) P := by
    rw [Polynomial.aeval_algHom]
    rfl
  have hscale : ∀ (g : ExampleModule) (hg : g ≠ 0)
      (P : Polynomial exampleBaseRing),
      Polynomial.aeval
          (Polynomial.C (g : exampleFractionRing) * Polynomial.X) P = 0 →
        P = 0 := by
    intro g hg P hP
    have hgK : (g : exampleFractionRing) ≠ 0 := by
      intro h
      apply hg
      apply Subtype.ext
      exact h
    let _ : Invertible (g : exampleFractionRing) := invertibleOfNonzero hgK
    have hcomp :
        (algebraMap exampleFractionRing (Polynomial exampleFractionRing)).comp
            (algebraMap exampleBaseRing exampleFractionRing) =
          algebraMap exampleBaseRing (Polynomial exampleFractionRing) := by
      apply RingHom.ext
      intro r
      exact IsScalarTower.algebraMap_apply exampleBaseRing exampleFractionRing
        (Polynomial exampleFractionRing) r
    have hP' :
        Polynomial.eval₂ (algebraMap exampleBaseRing (Polynomial exampleFractionRing))
          (Polynomial.C (g : exampleFractionRing) * Polynomial.X) P = 0 := by
      simpa [Polynomial.aeval_def] using hP
    have hevalK :
        Polynomial.aeval
            (Polynomial.C (g : exampleFractionRing) * Polynomial.X)
            (P.map (algebraMap exampleBaseRing exampleFractionRing)) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
      exact hP'
    have heq :
        Polynomial.aeval
            (Polynomial.C (g : exampleFractionRing) * Polynomial.X) =
          (Polynomial.algEquivCMulXAddC (g : exampleFractionRing) 0).toAlgHom := by
      apply Polynomial.algHom_ext
      simp [Polynomial.algEquivCMulXAddC]
    have hzero :
        (Polynomial.algEquivCMulXAddC (g : exampleFractionRing) 0).toAlgHom
            (P.map (algebraMap exampleBaseRing exampleFractionRing)) = 0 := by
      rw [← heq]
      exact hevalK
    have hmapzero : P.map (algebraMap exampleBaseRing exampleFractionRing) = 0 := by
      apply (Polynomial.algEquivCMulXAddC (g : exampleFractionRing) 0).injective
      simpa using hzero
    exact (Polynomial.map_eq_zero_iff
      (FaithfulSMul.algebraMap_injective exampleBaseRing exampleFractionRing)).mp hmapzero
  have hF_inj : ∀ (g : ExampleModule) (P : Polynomial exampleBaseRing),
      F (Polynomial.aeval
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g) P) = 0 →
      Polynomial.aeval
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g) P = 0 := by
    intro g P hP
    have hEval :
        Polynomial.aeval
            (F (SymmetricAlgebra.ι exampleBaseRing ExampleModule g)) P = 0 := by
      rw [← hFaeval g P]
      exact hP
    by_cases hg : g = 0
    · subst g
      rw [hFι 0] at hEval
      have hcoeffmap :
          algebraMap exampleBaseRing (Polynomial exampleFractionRing) (P.coeff 0) = 0 := by
        calc
          algebraMap exampleBaseRing (Polynomial exampleFractionRing) (P.coeff 0) =
              Polynomial.aeval (0 : Polynomial exampleFractionRing) P :=
            Polynomial.coeff_zero_eq_aeval_zero' P
          _ = 0 := by simpa using hEval
      have hcoeff : P.coeff 0 = 0 :=
        (FaithfulSMul.algebraMap_injective exampleBaseRing
          (Polynomial exampleFractionRing)) (by simpa using hcoeffmap)
      have hzero :
          Polynomial.aeval (0 : exampleAlgebra) P = 0 := by
        rw [← Polynomial.coeff_zero_eq_aeval_zero' (A := exampleAlgebra) P]
        simp [hcoeff]
      simpa using hzero
    · rw [hFι] at hEval
      have hPzero := hscale g hg P hEval
      simp [hPzero]
  refine (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨?_, inferInstance⟩
  refine ⟨?_⟩
  intro x y hxy
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  by_cases hy0 : y = 0
  · exact Or.inr hy0
  obtain ⟨g₁, hx₁⟩ := hmem x
  obtain ⟨g₂, hy₁⟩ := hmem y
  obtain ⟨g, a, b, ha, hb⟩ := hcommon g₁ g₂
  let S := Algebra.adjoin exampleBaseRing
    ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g} : Set exampleAlgebra)
  have h1 : SymmetricAlgebra.ι exampleBaseRing ExampleModule g₁ ∈ S := by
    rw [← ha, map_smul, Algebra.smul_def]
    exact S.mul_mem (S.algebraMap_mem a) (Algebra.subset_adjoin (by simp))
  have h2 : SymmetricAlgebra.ι exampleBaseRing ExampleModule g₂ ∈ S := by
    rw [← hb, map_smul, Algebra.smul_def]
    exact S.mul_mem (S.algebraMap_mem b) (Algebra.subset_adjoin (by simp))
  have hle1 : Algebra.adjoin exampleBaseRing
      ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g₁} : Set exampleAlgebra) ≤ S :=
    Algebra.adjoin_le (by simpa using h1)
  have hle2 : Algebra.adjoin exampleBaseRing
      ({SymmetricAlgebra.ι exampleBaseRing ExampleModule g₂} : Set exampleAlgebra) ≤ S :=
    Algebra.adjoin_le (by simpa using h2)
  have hxS := hle1 hx₁
  have hyS := hle2 hy₁
  have hxrange : x ∈
      (Polynomial.aeval (R := exampleBaseRing) (A := exampleAlgebra)
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g)).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval (A := exampleAlgebra)
      exampleBaseRing (SymmetricAlgebra.ι exampleBaseRing ExampleModule g)]
    exact hxS
  have hyrange : y ∈
      (Polynomial.aeval (R := exampleBaseRing) (A := exampleAlgebra)
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g)).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval (A := exampleAlgebra)
      exampleBaseRing (SymmetricAlgebra.ι exampleBaseRing ExampleModule g)]
    exact hyS
  rcases hxrange with ⟨P, hPx⟩
  rcases hyrange with ⟨Q, hQy⟩
  have hFx : F x ≠ 0 := by
    intro hFx
    apply hx0
    have hEval : F (Polynomial.aeval
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g) P) = 0 := by
      change F ((Polynomial.aeval
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g)).toRingHom P) = 0
      rw [hPx]
      exact hFx
    exact hPx.symm.trans (hF_inj g P hEval)
  have hFy : F y ≠ 0 := by
    intro hFy
    apply hy0
    have hEval : F (Polynomial.aeval
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g) Q) = 0 := by
      change F ((Polynomial.aeval
        (SymmetricAlgebra.ι exampleBaseRing ExampleModule g)).toRingHom Q) = 0
      rw [hQy]
      exact hFy
    exact hQy.symm.trans (hF_inj g Q hEval)
  apply False.elim
  have hFxy : F x * F y = 0 := by
    calc
      F x * F y = F (x * y) := (map_mul F x y).symm
      _ = F 0 := by rw [hxy]
      _ = 0 := map_zero F
  exact (mul_eq_zero.mp hFxy).elim hFx hFy

/-- Every prime stalk of `I` is generated by a nonzero element. -/
theorem exampleIdealAtPrime_isPrincipal_nonzero
    (q : Ideal exampleAlgebra) [q.IsPrime] :
    ∃ f : Localization q.primeCompl,
      exampleIdealAtPrime q = Ideal.span {f} ∧ f ≠ 0 := by
  obtain ⟨f, hf⟩ := exampleIdealAtPrime_isPrincipal q
  refine ⟨f, hf, ?_⟩
  intro hf0
  have hI : ∃ a : exampleAlgebra, a ∈ exampleIdeal ∧ a ≠ 0 := by
    by_contra h
    apply exampleIdeal_ne_bot
    apply le_antisymm
    · intro a ha
      have ha0 : a = 0 := by
        by_contra ha0
        exact h ⟨a, ha, ha0⟩
      simpa [ha0]
    · exact bot_le
  obtain ⟨a, ha, ha0⟩ := hI
  have hmem : algebraMap exampleAlgebra (Localization q.primeCompl) a ∈
      exampleIdealAtPrime q :=
    Ideal.mem_map_of_mem (algebraMap exampleAlgebra (Localization q.primeCompl)) ha
  have hmap0 : algebraMap exampleAlgebra (Localization q.primeCompl) a = 0 := by
    have hbot : exampleIdealAtPrime q = ⊥ := by
      simpa [hf0] using hf
    rw [hbot, Ideal.mem_bot] at hmem
    exact hmem
  let _ : IsDomain exampleAlgebra := exampleAlgebra_isDomain
  have hinj : Function.Injective (algebraMap exampleAlgebra
      (Localization q.primeCompl)) :=
    IsLocalization.injective (Localization q.primeCompl)
      q.primeCompl_le_nonZeroDivisors
  exact ha0 (hinj (by simpa using hmap0))

/-- The ring `A` is not Noetherian. -/
theorem exampleAlgebra_not_noetherian : ¬ IsNoetherianRing exampleAlgebra := by
  intro h
  let _ : IsNoetherianRing exampleAlgebra := h
  exact exampleIdeal_not_finitely_generated
    (Ideal.fg_of_isNoetherianRing exampleIdeal)

/-- Every prime localization of `A` is Noetherian. -/
theorem exampleAlgebra_prime_localizations_noetherian :
    ∀ (q : Ideal exampleAlgebra) (hq : q.IsPrime),
      letI : q.IsPrime := hq
      IsNoetherianRing (Localization q.primeCompl) := by
  intro q hq
  let _ : q.IsPrime := hq
  let p : Ideal exampleBaseRing :=
    q.comap (algebraMap exampleBaseRing exampleAlgebra)
  let _ : p.IsPrime := by
    dsimp [p]
    exact Ideal.comap_isPrime (algebraMap exampleBaseRing exampleAlgebra) q
  let M : Submonoid exampleAlgebra :=
    Algebra.algebraMapSubmonoid exampleAlgebra p.primeCompl
  have hMN : M ≤ q.primeCompl := by
    intro s hs
    rcases hs with ⟨r, hr, rfl⟩
    change algebraMap exampleBaseRing exampleAlgebra r ∉ q
    intro hq'
    exact hr (by simpa [p] using hq')
  let _ : IsNoetherianRing (exampleBaseRingAtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl
      (Localization p.primeCompl) inferInstance
  obtain ⟨e⟩ := exampleAlgebraAtBasePrime_equiv_polynomial p
  let _ : IsNoetherianRing (exampleAlgebraAtBasePrime p) :=
    isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  let _ : Algebra (exampleAlgebraAtBasePrime p) (Localization q.primeCompl) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (exampleAlgebraAtBasePrime p) (Localization q.primeCompl) M q.primeCompl hMN
  let _ : IsScalarTower exampleAlgebra (exampleAlgebraAtBasePrime p)
      (Localization q.primeCompl) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (exampleAlgebraAtBasePrime p) (Localization q.primeCompl) M q.primeCompl hMN
  let _ : IsLocalization (q.primeCompl.map
      (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)))
      (Localization q.primeCompl) :=
    IsLocalization.isLocalization_of_submonoid_le
      (exampleAlgebraAtBasePrime p) (Localization q.primeCompl) M q.primeCompl hMN
  exact IsLocalization.isNoetherianRing
    (q.primeCompl.map (algebraMap exampleAlgebra (exampleAlgebraAtBasePrime p)))
    (Localization q.primeCompl)
    (inferInstance : IsNoetherianRing (exampleAlgebraAtBasePrime p))

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
  refine ⟨exampleAlgebra, inferInstance, exampleAlgebra_isDomain, exampleIdeal,
    exampleIdeal_ne_bot, exampleIdeal_principalAtEveryPrime, exampleIdeal_not_invertible⟩

end Formalization.Books.Examples.Unit32
