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
