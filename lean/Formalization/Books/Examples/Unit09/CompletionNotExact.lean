import Formalization.Books.Examples.Unit08.NoncompleteQuotient
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Examples, Chapter 9: Completion is not exact

The source section is expressed using Mathlib's canonical `AdicCompletion`
and its functorial map.  The first example uses a positive indexing shift, so
the component indexed by `n` is the source summand `R/(t^(n + 1))`.
-/

open scoped DirectSum
open scoped BigOperators
open DirectSum
open Formalization.Books.Examples.Unit08

namespace Formalization.Books.Examples.Unit09

universe u

noncomputable section

section FirstCounterexample

variable (k : Type u) [Field k]

/-- The polynomial ring in the first completion counterexample. -/
abbrev polynomialRing := Polynomial k

/-- The `(t)`-adic ideal, with `Polynomial.X` playing the role of `t`. -/
def polynomialAdicIdeal : Ideal (polynomialRing k) :=
  Ideal.span {Polynomial.X}

/-- The direct sum `K = ⨁ R` in the first example. -/
abbrev firstKernel := ⨁ _n : ℕ, polynomialRing k

/-- The direct sum `P = ⨁ R` in the first example. -/
abbrev firstMiddle := ⨁ _n : ℕ, polynomialRing k

/-- The direct sum `M = ⨁ R/(t^(n + 1))` in the first example. -/
abbrev firstCokernel :=
  ⨁ n : ℕ, polynomialRing k ⧸ (polynomialAdicIdeal k) ^ (n + 1)

/-- Multiplication by the power assigned to the `n`th summand. -/
def firstKernelComponentMap (n : ℕ) :
    polynomialRing k →ₗ[polynomialRing k] polynomialRing k :=
  LinearMap.mulLeft (polynomialRing k) (Polynomial.X ^ (n + 1))

/-- The quotient map on the `n`th summand. -/
def firstQuotientComponentMap (n : ℕ) :
    polynomialRing k →ₗ[polynomialRing k]
      polynomialRing k ⧸ (polynomialAdicIdeal k) ^ (n + 1) :=
  ((polynomialAdicIdeal k) ^ (n + 1)).mkQ

/-- The componentwise multiplication map `K → P`. -/
def firstKernelMap : firstKernel k →ₗ[polynomialRing k] firstMiddle k :=
  DirectSum.toModule (polynomialRing k) ℕ (firstMiddle k) (fun n ↦
    (DirectSum.lof (polynomialRing k) ℕ (fun _ : ℕ ↦ polynomialRing k) n) ∘ₗ
      firstKernelComponentMap k n)

/-- The componentwise quotient map `P → M`. -/
def firstQuotientMap : firstMiddle k →ₗ[polynomialRing k] firstCokernel k :=
  DirectSum.toModule (polynomialRing k) ℕ (firstCokernel k) (fun n ↦
    (DirectSum.lof (polynomialRing k) ℕ
      (fun n : ℕ ↦ polynomialRing k ⧸ (polynomialAdicIdeal k) ^ (n + 1)) n) ∘ₗ
      firstQuotientComponentMap k n)

/-- The finite truncation of the element `(t^2, t^3, t^4, ...)`. -/
def firstXiTruncation (m : ℕ) : firstMiddle k :=
  ∑ n ∈ Finset.range m,
    DirectSum.lof (polynomialRing k) ℕ (fun _ : ℕ ↦ polynomialRing k) n
      (Polynomial.X ^ (n + 2))

/-- The completion-level meaning of the displayed element `ξ`. -/
def IsFirstXi
    (ξ : AdicCompletion (polynomialAdicIdeal k) (firstMiddle k)) : Prop :=
  ∀ m : ℕ,
    AdicCompletion.eval (polynomialAdicIdeal k) (firstMiddle k) m ξ =
      ((polynomialAdicIdeal k) ^ m •
        (⊤ : Submodule (polynomialRing k) (firstMiddle k))).mkQ
        (firstXiTruncation k m)

/-- The completion of the componentwise multiplication map. -/
def firstCompletedKernelMap :
    AdicCompletion (polynomialAdicIdeal k) (firstKernel k) →ₗ[
      AdicCompletion (polynomialAdicIdeal k) (polynomialRing k)]
      AdicCompletion (polynomialAdicIdeal k) (firstMiddle k) :=
  AdicCompletion.map (polynomialAdicIdeal k) (firstKernelMap k)

/-- The completion of the componentwise quotient map. -/
def firstCompletedQuotientMap :
    AdicCompletion (polynomialAdicIdeal k) (firstMiddle k) →ₗ[
      AdicCompletion (polynomialAdicIdeal k) (polynomialRing k)]
      AdicCompletion (polynomialAdicIdeal k) (firstCokernel k) :=
  AdicCompletion.map (polynomialAdicIdeal k) (firstQuotientMap k)

/-- The finite truncations of the putative constant vector `(t, t, t, ...)`. -/
def firstConstantTruncation (m : ℕ) : firstKernel k :=
  ∑ n ∈ Finset.range m,
    DirectSum.lof (polynomialRing k) ℕ (fun _ : ℕ ↦ polynomialRing k) n Polynomial.X

/-- A completion element with all components equal to `t`, if one existed. -/
def IsFirstConstantVector
    (x : AdicCompletion (polynomialAdicIdeal k) (firstKernel k)) : Prop :=
  ∀ m : ℕ,
    AdicCompletion.eval (polynomialAdicIdeal k) (firstKernel k) m x =
      ((polynomialAdicIdeal k) ^ m •
        (⊤ : Submodule (polynomialRing k) (firstKernel k))).mkQ
        (firstConstantTruncation k m)

/-- The displayed constant vector is not an element of the completed direct sum. -/
theorem first_constant_vector_not_in_completion :
    ¬ ∃ x : AdicCompletion (polynomialAdicIdeal k) (firstKernel k),
      IsFirstConstantVector k x := by
  intro h
  cases h with
  | intro x hx =>
    have htrans := AdicCompletion.transitionMap_comp_eval_apply
      (I := polynomialAdicIdeal k) (M := firstKernel k) (show 2 ≤ 3 by decide) x
    have hq :
        ((polynomialAdicIdeal k) ^ 2 •
            (⊤ : Submodule (polynomialRing k) (firstKernel k))).mkQ
            (firstConstantTruncation k 3) =
          ((polynomialAdicIdeal k) ^ 2 •
            (⊤ : Submodule (polynomialRing k) (firstKernel k))).mkQ
            (firstConstantTruncation k 2) := by
      change AdicCompletion.transitionMap (polynomialAdicIdeal k) (firstKernel k)
          (show 2 ≤ 3 by decide)
            (AdicCompletion.eval (polynomialAdicIdeal k) (firstKernel k) 3 x) =
        AdicCompletion.eval (polynomialAdicIdeal k) (firstKernel k) 2 x at htrans
      rw [hx 3, hx 2] at htrans
      simpa only [AdicCompletion.transitionMap, Submodule.factorPow,
        Submodule.factor_mk] using htrans
    have hzero :
        ((polynomialAdicIdeal k) ^ 2 •
            (⊤ : Submodule (polynomialRing k) (firstKernel k))).mkQ
            (DirectSum.lof (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) 2 Polynomial.X) = 0 := by
      rw [show firstConstantTruncation k 3 =
          firstConstantTruncation k 2 +
            DirectSum.lof (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) 2 Polynomial.X by
        simp [firstConstantTruncation, Finset.sum_range_succ]] at hq
      rw [map_add] at hq
      exact add_eq_left.mp hq
    have hmem :
        DirectSum.lof (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) 2 Polynomial.X ∈
          (polynomialAdicIdeal k) ^ 2 •
            (⊤ : Submodule (polynomialRing k) (firstKernel k)) :=
      (Submodule.Quotient.mk_eq_zero _).mp hzero
    have hcomponent :
        ∀ y : firstKernel k,
          y ∈ (polynomialAdicIdeal k) ^ 2 •
            (⊤ : Submodule (polynomialRing k) (firstKernel k)) →
          DirectSum.component (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) 2 y ∈
            (polynomialAdicIdeal k) ^ 2 := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr z hz
        simpa [DirectSum.smul_apply, smul_eq_mul] using
          (polynomialAdicIdeal k ^ 2).mul_mem_right
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) 2 z) hr
      · intro y z hy hz
        exact (polynomialAdicIdeal k ^ 2).add_mem hy hz
    have hX : Polynomial.X ∈ (polynomialAdicIdeal k) ^ 2 := by
      simpa using hcomponent _ hmem
    have hnot : Polynomial.X ∉ (polynomialAdicIdeal k) ^ 2 := by
      rw [polynomialAdicIdeal, Ideal.span_singleton_pow]
      intro hX'
      exact (Polynomial.monic_X_pow 2).not_dvd_of_natDegree_lt
        (by simp) (by simp) (Ideal.mem_span_singleton.mp hX')
    exact hnot hX

/-- The first completed direct sum contains the displayed obstruction. -/
theorem firstXi_exists :
    ∃ ξ : AdicCompletion (polynomialAdicIdeal k) (firstMiddle k),
      IsFirstXi k ξ ∧
        firstCompletedQuotientMap k ξ = 0 ∧
          ξ ∉ LinearMap.range (firstCompletedKernelMap k) := by
  classical
  have hpow (n : ℕ) : Polynomial.X ^ (n + 2) ∈ (polynomialAdicIdeal k) ^ n := by
    have hX : Polynomial.X ∈ polynomialAdicIdeal k :=
      Ideal.subset_span (Set.mem_singleton Polynomial.X)
    have h := (polynomialAdicIdeal k ^ n).mul_mem_right
      (Polynomial.X ^ 2) (Ideal.pow_mem_pow hX n)
    simpa [← pow_add] using h
  have hCauchy (n : ℕ) :
      firstXiTruncation k n ≡ firstXiTruncation k (n + 1) [SMOD
        ((polynomialAdicIdeal k) ^ n •
          (⊤ : Submodule (polynomialRing k) (firstMiddle k)))] := by
    rw [SModEq.sub_mem]
    have hterm :
        DirectSum.lof (polynomialRing k) ℕ (fun _ : ℕ ↦ polynomialRing k) n
            (Polynomial.X ^ (n + 2)) ∈
          (polynomialAdicIdeal k) ^ n •
            (⊤ : Submodule (polynomialRing k) (firstMiddle k)) :=
      by
        have hs := Submodule.smul_mem_smul (hpow n)
          (Submodule.mem_top :
            DirectSum.of (fun _ : ℕ ↦ polynomialRing k) n 1 ∈
              (⊤ : Submodule (polynomialRing k) (firstMiddle k)))
        rw [← DirectSum.of_smul] at hs
        simpa [DirectSum.lof_eq_of] using hs
    rw [show firstXiTruncation k (n + 1) =
        firstXiTruncation k n +
          DirectSum.lof (polynomialRing k) ℕ (fun _ : ℕ ↦ polynomialRing k) n
            (Polynomial.X ^ (n + 2)) by
      simp [firstXiTruncation, Finset.sum_range_succ]]
    simpa [sub_eq_add_neg] using (Submodule.neg_mem _ hterm)
  let ξ : AdicCompletion (polynomialAdicIdeal k) (firstMiddle k) :=
    AdicCompletion.mk (polynomialAdicIdeal k) (firstMiddle k)
      (AdicCompletion.AdicCauchySequence.mk (polynomialAdicIdeal k) (firstMiddle k)
        (firstXiTruncation k) hCauchy)
  have hquot (n : ℕ) : firstQuotientMap k (firstXiTruncation k n) = 0 := by
    have hX : Polynomial.X ∈ polynomialAdicIdeal k :=
      Ideal.subset_span (Set.mem_singleton Polynomial.X)
    rw [firstXiTruncation, firstQuotientMap]
    simp only [map_sum, DirectSum.toModule_lof, LinearMap.comp_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [firstQuotientComponentMap]
    change (DFinsupp.single i
        ((polynomialAdicIdeal k ^ (i + 1)).mkQ (Polynomial.X ^ (i + 2))) :
          firstCokernel k) = 0
    rw [DFinsupp.single_eq_zero]
    apply (Submodule.Quotient.mk_eq_zero _).2
    have h := (polynomialAdicIdeal k ^ (i + 1)).mul_mem_right
      Polynomial.X (Ideal.pow_mem_pow hX (i + 1))
    change Polynomial.X ^ (i + 2) ∈ polynomialAdicIdeal k ^ (i + 1)
    convert h using 1
    rw [pow_succ]
  have hnot : Polynomial.X ∉ (polynomialAdicIdeal k) ^ 2 := by
    rw [polynomialAdicIdeal, Ideal.span_singleton_pow]
    intro hX'
    exact (Polynomial.monic_X_pow 2).not_dvd_of_natDegree_lt
      (by simp) (by simp) (Ideal.mem_span_singleton.mp hX')
  have hxi : IsFirstXi k ξ := by
    intro n
    simp [ξ, AdicCompletion.eval_apply, AdicCompletion.mk_apply_coe]
  have hmapzero : firstCompletedQuotientMap k ξ = 0 := by
    rw [firstCompletedQuotientMap, AdicCompletion.map_mk]
    apply AdicCompletion.ext
    intro n
    change ((polynomialAdicIdeal k) ^ n •
      (⊤ : Submodule (polynomialRing k) (firstCokernel k))).mkQ
      (firstQuotientMap k (firstXiTruncation k n)) = 0
    rw [hquot n, map_zero]
  have hnonrange : ξ ∉ LinearMap.range (firstCompletedKernelMap k) := by
    intro h
    cases h with
    | intro x hx =>
      revert hx
      apply AdicCompletion.induction_on (polynomialAdicIdeal k) (firstKernel k) x
      intro a ha
      have hbad (n : ℕ) (hn2 : 2 ≤ n)
          (hn : n ∉ (a 2).support) : False := by
        let l := n + 3
        have heval :
            ((polynomialAdicIdeal k) ^ l •
                (⊤ : Submodule (polynomialRing k) (firstMiddle k))).mkQ
                (firstKernelMap k (a l)) =
              ((polynomialAdicIdeal k) ^ l •
                (⊤ : Submodule (polynomialRing k) (firstMiddle k))).mkQ
                (firstXiTruncation k l) := by
          have hh := congrArg
            (fun z ↦ AdicCompletion.eval (polynomialAdicIdeal k)
              (firstMiddle k) l z) ha
          rw [hxi l] at hh
          simpa [firstCompletedKernelMap, AdicCompletion.map_mk,
            AdicCompletion.eval_apply, AdicCompletion.mk_apply_coe] using hh
        have hmem :
            firstKernelMap k (a l) - firstXiTruncation k l ∈
              (polynomialAdicIdeal k) ^ l •
                (⊤ : Submodule (polynomialRing k) (firstMiddle k)) :=
          (Submodule.Quotient.eq _).mp heval
        have hcomponent (m : ℕ) (y : firstMiddle k)
            (hy : y ∈ (polynomialAdicIdeal k) ^ m •
              (⊤ : Submodule (polynomialRing k) (firstMiddle k))) :
            DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) n y ∈
              (polynomialAdicIdeal k) ^ m := by
          refine Submodule.smul_induction_on hy ?_ ?_
          · intro r hr z hz
            simpa [DirectSum.smul_apply, smul_eq_mul] using
              (polynomialAdicIdeal k ^ m).mul_mem_right
                (DirectSum.component (polynomialRing k) ℕ
                  (fun _ : ℕ ↦ polynomialRing k) n z) hr
          · intro y z hy hz
            exact (polynomialAdicIdeal k ^ m).add_mem hy hz
        have hdiag :
            (DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) n).comp
                (firstKernelMap k) =
              (firstKernelComponentMap k n).comp
                (DirectSum.component (polynomialRing k) ℕ
                  (fun _ : ℕ ↦ polynomialRing k) n) := by
          apply DirectSum.linearMap_ext
          intro i
          by_cases hi : i = n
          · subst i
            ext z
            simp [firstKernelMap, firstKernelComponentMap,
              LinearMap.comp_apply]
          · simp [firstKernelMap, firstKernelComponentMap]
            ext z
            simp [DirectSum.component.of, LinearMap.comp_apply, hi]
        have htrunc :
            DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) n (firstXiTruncation k l) =
              Polynomial.X ^ (n + 2) := by
          simp [firstXiTruncation, DirectSum.component.of, l]
        have hcoord := hcomponent l
          (firstKernelMap k (a l) - firstXiTruncation k l) hmem
        have hdiag_apply := congrArg (fun f ↦ f (a l)) hdiag
        have hcoord' :
            Polynomial.X ^ (n + 1) *
                DirectSum.component (polynomialRing k) ℕ
                  (fun _ : ℕ ↦ polynomialRing k) n (a l) -
              Polynomial.X ^ (n + 2) ∈ (polynomialAdicIdeal k) ^ l := by
          have hcoord'' :
              DirectSum.component (polynomialRing k) ℕ
                  (fun _ : ℕ ↦ polynomialRing k) n (firstKernelMap k (a l)) -
                DirectSum.component (polynomialRing k) ℕ
                  (fun _ : ℕ ↦ polynomialRing k) n (firstXiTruncation k l) ∈
                (polynomialAdicIdeal k) ^ l := by
            simpa [map_sub] using hcoord
          have hdiag_apply' :
              DirectSum.component (polynomialRing k) ℕ
                  (fun _ : ℕ ↦ polynomialRing k) n (firstKernelMap k (a l)) =
                Polynomial.X ^ (n + 1) *
                  DirectSum.component (polynomialRing k) ℕ
                    (fun _ : ℕ ↦ polynomialRing k) n (a l) := by
            simpa [LinearMap.comp_apply, firstKernelComponentMap] using hdiag_apply
          rw [hdiag_apply', htrunc] at hcoord''
          simpa [firstKernelComponentMap, LinearMap.comp_apply] using hcoord''
        have hlowmem :
            a l - a 2 ∈ (polynomialAdicIdeal k) ^ 2 •
              (⊤ : Submodule (polynomialRing k) (firstKernel k)) := by
          exact SModEq.sub_mem.mp
            (SModEq.symm (a.property (show 2 ≤ l by simp [l])))
        have hlow := hcomponent 2 (a l - a 2) hlowmem
        have hlow' :
            DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) n (a l) ∈
              (polynomialAdicIdeal k) ^ 2 := by
          have hzero :
              DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) n (a 2) = 0 := by
            exact (DFinsupp.notMem_support_iff.mp hn)
          simpa [map_sub, hzero] using hlow
        have hdiv : Polynomial.X ^ l ∣
            Polynomial.X ^ (n + 1) *
                DirectSum.component (polynomialRing k) ℕ
                  (fun _ : ℕ ↦ polynomialRing k) n (a l) -
              Polynomial.X ^ (n + 2) := by
          change _ ∈ (Ideal.span {Polynomial.X}) ^ l at hcoord'
          rw [Ideal.span_singleton_pow] at hcoord'
          exact Ideal.mem_span_singleton.mp hcoord'
        have hfactor :
            Polynomial.X ^ (n + 1) *
                DirectSum.component (polynomialRing k) ℕ
                  (fun _ : ℕ ↦ polynomialRing k) n (a l) -
              Polynomial.X ^ (n + 2) =
            Polynomial.X ^ (n + 1) *
              (DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) n (a l) - Polynomial.X) := by
          rw [show Polynomial.X ^ (n + 2) =
              Polynomial.X ^ (n + 1) * Polynomial.X by rw [pow_succ],
            mul_sub]
        have hdiv' : Polynomial.X ^ l ∣
            Polynomial.X ^ (n + 1) *
              (DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) n (a l) - Polynomial.X) := by
          rw [← hfactor]
          exact hdiv
        have hpowfactor : (Polynomial.X : polynomialRing k) ^ l =
            Polynomial.X ^ (n + 1) * Polynomial.X ^ 2 := by
          dsimp [l]
          rw [show n + 3 = (n + 1) + 2 by simp [Nat.add_assoc]]
          exact pow_add Polynomial.X (n + 1) 2
        have hcancel : Polynomial.X ^ 2 ∣
            DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) n (a l) - Polynomial.X := by
          apply (mul_dvd_mul_iff_left
            (pow_ne_zero _ (Polynomial.X_ne_zero :
              (Polynomial.X : polynomialRing k) ≠ 0))).mp
          rw [← hpowfactor]
          exact hdiv'
        have hdifference :
            DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) n (a l) - Polynomial.X ∈
              (polynomialAdicIdeal k) ^ 2 := by
          change _ ∈ (Ideal.span {Polynomial.X}) ^ 2
          rw [Ideal.span_singleton_pow]
          exact Ideal.mem_span_singleton.mpr hcancel
        have hX : Polynomial.X ∈ (polynomialAdicIdeal k) ^ 2 := by
          have hsub := (polynomialAdicIdeal k ^ 2).sub_mem hlow' hdifference
          simpa using hsub
        exact hnot hX
      by_cases hs : (a 2).support = ∅
      · exact hbad 2 (by decide) (by simp [hs])
      · let b := (a 2).support.max'
          (Finset.nonempty_iff_ne_empty.mpr hs)
        let n := max 2 (b + 1)
        have hn2 : 2 ≤ n := by
          exact Nat.le_max_left _ _
        have hbn : b < n := by
          exact lt_of_lt_of_le (Nat.lt_succ_self b) (Nat.le_max_right _ _)
        have hn : n ∉ (a 2).support := by
          intro hnmem
          have hle : n ≤ b := Finset.le_max' _ _ hnmem
          exact (Nat.not_lt_of_ge hle) hbn
        exact hbad n hn2 hn
  exact ⟨ξ, hxi, hmapzero, hnonrange⟩

/-- A named choice of the obstruction `ξ`. -/
noncomputable def firstXi :
    AdicCompletion (polynomialAdicIdeal k) (firstMiddle k) :=
  Classical.choose (firstXi_exists k)

/-- The defining properties of the chosen obstruction. -/
theorem firstXi_spec :
    IsFirstXi k (firstXi k) ∧
      firstCompletedQuotientMap k (firstXi k) = 0 ∧
        firstXi k ∉ LinearMap.range (firstCompletedKernelMap k) :=
  Classical.choose_spec (firstXi_exists k)

/-- The uncompleted sequence `0 → K → P → M → 0` is short exact. -/
theorem first_sequence_short_exact :
    Function.Injective (firstKernelMap k) ∧
      Function.Exact (firstKernelMap k) (firstQuotientMap k) ∧
        Function.Surjective (firstQuotientMap k) := by
  classical
  have hX : Polynomial.X ∈ polynomialAdicIdeal k :=
    Ideal.subset_span (Set.mem_singleton Polynomial.X)
  have hkernel_diag (n : ℕ) :
      (DirectSum.component (polynomialRing k) ℕ
          (fun _ : ℕ ↦ polynomialRing k) n).comp (firstKernelMap k) =
        (firstKernelComponentMap k n).comp
          (DirectSum.component (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) n) := by
    apply DirectSum.linearMap_ext
    intro i
    by_cases hi : i = n
    · subst i
      ext z
      simp [firstKernelMap, firstKernelComponentMap,
        LinearMap.comp_apply]
    · simp [firstKernelMap, firstKernelComponentMap]
      ext z
      simp [DirectSum.component.of, LinearMap.comp_apply, hi]
  have hquot_diag (n : ℕ) :
      (DirectSum.component (polynomialRing k) ℕ
          (fun n : ℕ ↦ polynomialRing k ⧸
            (polynomialAdicIdeal k) ^ (n + 1)) n).comp
          (firstQuotientMap k) =
        (firstQuotientComponentMap k n).comp
          (DirectSum.component (polynomialRing k) ℕ
            (fun n : ℕ ↦ polynomialRing k) n) := by
    apply DirectSum.linearMap_ext
    intro i
    by_cases hi : i = n
    · subst i
      ext
      simp [firstQuotientMap, firstQuotientComponentMap,
        LinearMap.comp_apply]
    · simp [firstQuotientMap, firstQuotientComponentMap]
      ext
      simp [DirectSum.component.of, LinearMap.comp_apply, hi]
  have hcomponent_exact (n : ℕ) (r : polynomialRing k) :
      firstQuotientComponentMap k n r = 0 ↔
        ∃ s : polynomialRing k, firstKernelComponentMap k n s = r := by
    constructor
    · intro hr
      change ((polynomialAdicIdeal k) ^ (n + 1)).mkQ r = 0 at hr
      have hrmem : r ∈ (polynomialAdicIdeal k) ^ (n + 1) :=
        (Submodule.Quotient.mk_eq_zero _).mp hr
      change r ∈ (Ideal.span {Polynomial.X}) ^ (n + 1) at hrmem
      rw [Ideal.span_singleton_pow] at hrmem
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hrmem
      refine ⟨s, ?_⟩
      simpa [firstKernelComponentMap] using hs.symm
    · rintro ⟨s, hs⟩
      change ((polynomialAdicIdeal k) ^ (n + 1)).mkQ r = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      rw [← hs]
      exact (polynomialAdicIdeal k ^ (n + 1)).mul_mem_right s
        (Ideal.pow_mem_pow hX (n + 1))
  have hrange_of_ker :
      ∀ z : firstMiddle k, firstQuotientMap k z = 0 →
        z ∈ LinearMap.range (firstKernelMap k) := by
    intro z hz
    have hpre (i : ℕ) (hi : i ∈ z.support) :
        ∃ s : polynomialRing k, firstKernelComponentMap k i s = z i := by
      have hdiag := congrArg (fun f ↦ f z) (hquot_diag i)
      have hzi : firstQuotientComponentMap k i (z i) = 0 := by
        have hzi' : firstQuotientComponentMap k i
              (DirectSum.component (polynomialRing k) ℕ
                (fun _ : ℕ ↦ polynomialRing k) i z) = 0 := by
          rw [← LinearMap.comp_apply (firstQuotientComponentMap k i)
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) i) z]
          rw [← hdiag]
          simp [LinearMap.comp_apply, hz]
        change firstQuotientComponentMap k i
          (DirectSum.component (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) i z) = 0
        exact hzi'
      exact (hcomponent_exact i (z i)).mp hzi
    let y : firstKernel k :=
      DFinsupp.mk z.support (fun i ↦ Classical.choose (hpre i i.property))
    refine ⟨y, ?_⟩
    apply DirectSum.ext_component (polynomialRing k)
    intro i
    have hdiag := congrArg (fun f ↦ f y) (hkernel_diag i)
    by_cases hi : i ∈ z.support
    · have hy : firstKernelComponentMap k i (y i) = z i := by
        rw [DFinsupp.mk_of_mem hi]
        exact Classical.choose_spec (hpre i hi)
      calc
        DirectSum.component (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) i (firstKernelMap k y) =
          firstKernelComponentMap k i
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) i y) := by
            simpa [LinearMap.comp_apply] using hdiag
        _ = z i := by
          change firstKernelComponentMap k i (y i) = z i
          exact hy
    · have hy : y i = 0 := DFinsupp.mk_of_notMem hi
      have hz' : z i = 0 := DFinsupp.notMem_support_iff.mp hi
      calc
        DirectSum.component (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) i (firstKernelMap k y) =
          firstKernelComponentMap k i
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) i y) := by
            simpa [LinearMap.comp_apply] using hdiag
        _ = z i := by
          change firstKernelComponentMap k i (y i) = z i
          simp [hy, hz']
  have hinjective : Function.Injective (firstKernelMap k) := by
    intro x y hxy
    apply DirectSum.ext_component (polynomialRing k)
    intro n
    have hxy' := congrArg
      (DirectSum.component (polynomialRing k) ℕ
        (fun _ : ℕ ↦ polynomialRing k) n) hxy
    have hdx := congrArg (fun f ↦ f x) (hkernel_diag n)
    have hdy := congrArg (fun f ↦ f y) (hkernel_diag n)
    rw [show DirectSum.component (polynomialRing k) ℕ
          (fun _ : ℕ ↦ polynomialRing k) n (firstKernelMap k x) =
        firstKernelComponentMap k n
          (DirectSum.component (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) n x) by
          simpa [LinearMap.comp_apply] using hdx,
      show DirectSum.component (polynomialRing k) ℕ
          (fun _ : ℕ ↦ polynomialRing k) n (firstKernelMap k y) =
        firstKernelComponentMap k n
          (DirectSum.component (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) n y) by
          simpa [LinearMap.comp_apply] using hdy] at hxy'
    exact mul_left_cancel₀ (pow_ne_zero _ (Polynomial.X_ne_zero :
      (Polynomial.X : polynomialRing k) ≠ 0)) hxy'
  have hcompzero :
      (firstQuotientMap k) ∘ₗ (firstKernelMap k) = 0 := by
    apply LinearMap.ext
    intro x
    apply DirectSum.ext_component (polynomialRing k)
    intro n
    have hq := congrArg (fun f ↦ f (firstKernelMap k x)) (hquot_diag n)
    have hk := congrArg (fun f ↦ f x) (hkernel_diag n)
    have hz : firstQuotientComponentMap k n
          (firstKernelComponentMap k n
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) n x)) = 0 :=
      (hcomponent_exact n _).mpr ⟨_, rfl⟩
    change DirectSum.component (polynomialRing k) ℕ
        (fun i : ℕ ↦ polynomialRing k ⧸
          (polynomialAdicIdeal k) ^ (i + 1)) n
        (firstQuotientMap k (firstKernelMap k x)) = 0
    have hq' :
        DirectSum.component (polynomialRing k) ℕ
            (fun i : ℕ ↦ polynomialRing k ⧸
              (polynomialAdicIdeal k) ^ (i + 1)) n
            (firstQuotientMap k (firstKernelMap k x)) =
          firstQuotientComponentMap k n
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) n (firstKernelMap k x)) := by
      simpa [LinearMap.comp_apply] using hq
    have hk' :
        DirectSum.component (polynomialRing k) ℕ
            (fun _ : ℕ ↦ polynomialRing k) n (firstKernelMap k x) =
          firstKernelComponentMap k n
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) n x) := by
      simpa [LinearMap.comp_apply] using hk
    rw [hq', hk']
    exact hz
  have hsurjective : Function.Surjective (firstQuotientMap k) := by
    intro z
    have hpre (i : ℕ) : ∃ r : polynomialRing k,
        firstQuotientComponentMap k i r = z i := by
      exact Submodule.mkQ_surjective _ (z i)
    let y : firstMiddle k :=
      DFinsupp.mk z.support (fun i ↦ Classical.choose (hpre i))
    refine ⟨y, ?_⟩
    apply DirectSum.ext_component (polynomialRing k)
    intro i
    have hdiag := congrArg (fun f ↦ f y) (hquot_diag i)
    by_cases hi : i ∈ z.support
    · have hy : firstQuotientComponentMap k i (y i) = z i := by
        rw [DFinsupp.mk_of_mem hi]
        exact Classical.choose_spec (hpre i)
      calc
        DirectSum.component (polynomialRing k) ℕ
            (fun n : ℕ ↦ polynomialRing k ⧸
              (polynomialAdicIdeal k) ^ (n + 1)) i
              (firstQuotientMap k y) =
          firstQuotientComponentMap k i
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) i y) := by
            simpa [LinearMap.comp_apply] using hdiag
        _ = z i := by
          change firstQuotientComponentMap k i (y i) = z i
          exact hy
    · have hy : y i = 0 := DFinsupp.mk_of_notMem hi
      have hz' : z i = 0 := DFinsupp.notMem_support_iff.mp hi
      calc
        DirectSum.component (polynomialRing k) ℕ
            (fun n : ℕ ↦ polynomialRing k ⧸
              (polynomialAdicIdeal k) ^ (n + 1)) i
              (firstQuotientMap k y) =
          firstQuotientComponentMap k i
            (DirectSum.component (polynomialRing k) ℕ
              (fun _ : ℕ ↦ polynomialRing k) i y) := by
            simpa [LinearMap.comp_apply] using hdiag
        _ = z i := by
          change firstQuotientComponentMap k i (y i) = z i
          simp [hy, hz']
  exact ⟨hinjective, LinearMap.exact_of_comp_of_mem_range hcompzero hrange_of_ker,
    hsurjective⟩

/-- The completed sequence fails exactness in the middle. -/
theorem first_completed_sequence_not_exact :
    ¬ Function.Exact (firstCompletedKernelMap k) (firstCompletedQuotientMap k) := by
  intro h
  exact (firstXi_spec k).2.2 ((h (firstXi k)).mp (firstXi_spec k).2.1)

end FirstCounterexample

section PrincipalQuotientCounterexample

variable {R : Type u} [CommRing R]

/-- Multiplication by a generator, with codomain restricted to its ideal. -/
def principalMultiplicationMap (J : Ideal R) (f : R) (hf : f ∈ J) : R →ₗ[R] J :=
  (LinearMap.mulLeft R f).codRestrict J (fun x ↦ J.mul_mem_right x hf)

/-- The inclusion of an ideal into its ambient ring. -/
def idealInclusionMap (J : Ideal R) : J →ₗ[R] R :=
  J.subtype

/-- The quotient map by an ideal, viewed as an `R`-linear map. -/
def idealQuotientMap (J : Ideal R) : R →ₗ[R] R ⧸ J :=
  J.mkQ

/-- The completed map from the ambient ring to the completed ideal. -/
def completedPrincipalMultiplicationMap (I J : Ideal R) (f : R) (hf : f ∈ J) :
    AdicCompletion I R →ₗ[AdicCompletion I R] AdicCompletion I J :=
  AdicCompletion.map I (principalMultiplicationMap J f hf)

/-- The completed inclusion of the ideal. -/
def completedIdealInclusionMap (I J : Ideal R) :
    AdicCompletion I J →ₗ[AdicCompletion I R] AdicCompletion I R :=
  AdicCompletion.map I (idealInclusionMap J)

/-- The completed quotient map. -/
def completedIdealQuotientMap (I J : Ideal R) :
    AdicCompletion I R →ₗ[AdicCompletion I R] AdicCompletion I (R ⧸ J) :=
  AdicCompletion.map I (idealQuotientMap J)

/-- The quotient map from `R` into the completion of `R/J`. -/
def idealQuotientCompletionFromRing (I J : Ideal R) :
    R →ₗ[R] AdicCompletion I (R ⧸ J) :=
  (completedIdealQuotientMap I J).restrictScalars R ∘ₗ AdicCompletion.of I R

/-- Multiplication by `f` on `R`. -/
def principalEndomorphism (f : R) : R →ₗ[R] R :=
  LinearMap.mulLeft R f

/-- The quotient map `R → R/(f)`. -/
def principalQuotientMap (f : R) : R →ₗ[R] R ⧸ Ideal.span {f} :=
  (Ideal.span {f}).mkQ

/-- The completed multiplication-by-`f` map. -/
def completedPrincipalEndomorphism (I : Ideal R) (f : R) :
    AdicCompletion I R →ₗ[AdicCompletion I R] AdicCompletion I R :=
  AdicCompletion.map I (principalEndomorphism f)

/-- The completed quotient map `R^ → (R/(f))^`. -/
def completedPrincipalQuotientMap (I : Ideal R) (f : R) :
    AdicCompletion I R →ₗ[AdicCompletion I R]
      AdicCompletion I (R ⧸ Ideal.span {f}) :=
  AdicCompletion.map I (principalQuotientMap f)

/-- The ordinary ideal inclusion has image exactly `J`. -/
theorem ideal_inclusion_range (J : Ideal R) :
    LinearMap.range (idealInclusionMap J) = J := by
  ext x
  constructor
  · intro h
    cases h with
    | intro y hy =>
      rw [← hy]
      exact y.property
  · intro hx
    change ∃ y : J, (y : R) = x
    refine ⟨{ val := x, property := hx }, ?_⟩
    rfl

/-- The principal-ideal quotient example fails after completion. -/
theorem principal_quotient_completion_failure
    (a f : R) (I J : Ideal R)
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {f}) (hf : f ∈ J)
    (hR : IsAdicComplete I R)
    (hquot : ¬ IsAdicComplete I (R ⧸ J)) :
    Function.Surjective (completedPrincipalMultiplicationMap I J f hf) ∧
      Function.Surjective (completedIdealQuotientMap I J) ∧
        Set.range (completedIdealInclusionMap I J) =
          Set.range (AdicCompletion.of I R ∘ₗ idealInclusionMap J) ∧
      J < LinearMap.ker (idealQuotientCompletionFromRing I J) ∧
          ¬ Function.Exact (completedIdealInclusionMap I J)
              (completedIdealQuotientMap I J) := by
  classical
  let _hR := hR
  have _hI := hI
  have hmul : Function.Surjective (principalMultiplicationMap J f hf) := by
    intro y
    have hy : (y : R) ∈ Ideal.span {f} := by
      rw [← hJ]
      exact y.property
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change f * r = (y : R)
    exact hr.symm
  have hquotient : Function.Surjective (idealQuotientMap J) := by
    intro y
    exact Submodule.mkQ_surjective J y
  have hmul' :
      Function.Surjective (completedPrincipalMultiplicationMap I J f hf) := by
    exact AdicCompletion.map_surjective I hmul
  have hquotient' :
      Function.Surjective (completedIdealQuotientMap I J) := by
    exact AdicCompletion.map_surjective I hquotient
  have hcomp :
      completedIdealInclusionMap I J ∘ₗ
          completedPrincipalMultiplicationMap I J f hf =
      AdicCompletion.map I (principalEndomorphism f) := by
    change AdicCompletion.map I (idealInclusionMap J) ∘ₗ
        AdicCompletion.map I (principalMultiplicationMap J f hf) =
      AdicCompletion.map I (principalEndomorphism f)
    rw [AdicCompletion.map_comp]
    congr 1
  have himage (x : AdicCompletion I J) :
      ∃ y : J, completedIdealInclusionMap I J x =
        AdicCompletion.of I R (y : R) := by
    obtain ⟨z, hz⟩ := hmul' x
    obtain ⟨r, hr⟩ := AdicCompletion.of_surjective I R z
    refine ⟨⟨f * r, J.mul_mem_right r hf⟩, ?_⟩
    calc
      completedIdealInclusionMap I J x =
          completedIdealInclusionMap I J
            (completedPrincipalMultiplicationMap I J f hf z) := by
              rw [hz]
      _ = (AdicCompletion.map I (principalEndomorphism f)) z := by
            exact congrArg (fun q ↦ q z) hcomp
      _ = (AdicCompletion.map I (principalEndomorphism f))
            (AdicCompletion.of I R r) := by rw [hr]
      _ = AdicCompletion.of I R (f * r) := by
            rw [AdicCompletion.map_of]
            rfl
  have hrange :
      Set.range (completedIdealInclusionMap I J) =
        Set.range (AdicCompletion.of I R ∘ₗ idealInclusionMap J) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := himage x
      refine ⟨y, ?_⟩
      change AdicCompletion.of I R (y : R) = completedIdealInclusionMap I J x
      exact hy.symm
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := hmul' (AdicCompletion.of I J y)
      refine ⟨completedPrincipalMultiplicationMap I J f hf z, ?_⟩
      change completedIdealInclusionMap I J
          (completedPrincipalMultiplicationMap I J f hf z) =
        AdicCompletion.of I R (y : R)
      calc
        completedIdealInclusionMap I J
            (completedPrincipalMultiplicationMap I J f hf z) =
            completedIdealInclusionMap I J
              (AdicCompletion.of I J y) := by rw [← hz]
        _ = AdicCompletion.of I R (y : R) := by
          change (AdicCompletion.map I (idealInclusionMap J))
              (AdicCompletion.of I J y) = AdicCompletion.of I R (y : R)
          exact AdicCompletion.map_of I (idealInclusionMap J) y
  have hJker : J ≤ LinearMap.ker (idealQuotientCompletionFromRing I J) := by
    intro r hr
    change completedIdealQuotientMap I J (AdicCompletion.of I R r) = 0
    change (AdicCompletion.map I (idealQuotientMap J))
        (AdicCompletion.of I R r) = 0
    rw [AdicCompletion.map_of]
    have hr0 : idealQuotientMap J r = 0 := by
      change J.mkQ r = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 hr
    rw [hr0]
    rfl
  have hsurjFromRing :
      Function.Surjective (idealQuotientCompletionFromRing I J) := by
    intro z
    obtain ⟨x, hx⟩ := hquotient' z
    obtain ⟨r, hr⟩ := AdicCompletion.of_surjective I R x
    rw [← hr] at hx
    refine ⟨r, ?_⟩
    change (AdicCompletion.map I (idealQuotientMap J))
        (AdicCompletion.of I R r) = z
    rw [AdicCompletion.map_of]
    exact hx
  have hofquot_surj :
      Function.Surjective (AdicCompletion.of I (R ⧸ J)) := by
    intro z
    obtain ⟨r, hr⟩ := hsurjFromRing z
    refine ⟨idealQuotientMap J r, ?_⟩
    change (AdicCompletion.map I (idealQuotientMap J))
        (AdicCompletion.of I R r) = z
    rw [AdicCompletion.map_of]
    exact hr
  have hquot_of (r : R) :
      completedIdealQuotientMap I J (AdicCompletion.of I R r) =
        AdicCompletion.of I (R ⧸ J) (idealQuotientMap J r) := by
    change (AdicCompletion.map I (idealQuotientMap J))
        (AdicCompletion.of I R r) =
      AdicCompletion.of I (R ⧸ J) (idealQuotientMap J r)
    exact AdicCompletion.map_of I (idealQuotientMap J) r
  have hstrict : J < LinearMap.ker (idealQuotientCompletionFromRing I J) := by
    refine lt_of_le_of_ne hJker ?_
    intro heq
    apply hquot
    apply (AdicCompletion.of_bijective_iff (I := I) (M := R ⧸ J)).1
    constructor
    · intro x y hxy
      obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective J x
      obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective J y
      have hxy' : idealQuotientCompletionFromRing I J r =
          idealQuotientCompletionFromRing I J s := by
        change completedIdealQuotientMap I J (AdicCompletion.of I R r) =
          completedIdealQuotientMap I J (AdicCompletion.of I R s)
        calc
          completedIdealQuotientMap I J (AdicCompletion.of I R r) =
              AdicCompletion.of I (R ⧸ J) (idealQuotientMap J r) := hquot_of r
          _ = AdicCompletion.of I (R ⧸ J) (idealQuotientMap J s) := hxy
          _ = completedIdealQuotientMap I J (AdicCompletion.of I R s) :=
            (hquot_of s).symm
      have hrs : r - s ∈ LinearMap.ker (idealQuotientCompletionFromRing I J) := by
        change idealQuotientCompletionFromRing I J (r - s) = 0
        rw [map_sub, hxy', sub_self]
      have hrsJ : r - s ∈ J := by
        rw [heq]
        exact hrs
      change (Submodule.Quotient.mk (p := J) r) =
        Submodule.Quotient.mk (p := J) s
      exact (Submodule.Quotient.eq J).2 hrsJ
    · exact hofquot_surj
  have hnotexact :
      ¬ Function.Exact (completedIdealInclusionMap I J)
          (completedIdealQuotientMap I J) := by
    intro hex
    have hnotle : ¬ LinearMap.ker (idealQuotientCompletionFromRing I J) ≤ J := by
      intro hle
      exact (not_lt_of_ge hle) hstrict
    obtain ⟨r, hrker, hrnotJ⟩ := SetLike.not_le_iff_exists.mp hnotle
    change idealQuotientCompletionFromRing I J r = 0 at hrker
    have hzero :
        completedIdealQuotientMap I J (AdicCompletion.of I R r) = 0 := by
      simpa [idealQuotientCompletionFromRing, LinearMap.comp_apply] using hrker
    obtain ⟨x, hx⟩ := (hex (AdicCompletion.of I R r)).mp hzero
    obtain ⟨y, hy⟩ := himage x
    have hEq : AdicCompletion.of I R (y : R) =
        AdicCompletion.of I R r := hy.symm.trans hx
    have hEq' : (y : R) = r := (AdicCompletion.of_inj (I := I)).mp hEq
    apply hrnotJ
    rw [← hEq']
    exact y.property
  exact ⟨hmul', hquotient', hrange, hstrict, hnotexact⟩

/-- The same quotient phenomenon gives failure for the sequence
`R → R → R/(f) → 0`. -/
theorem principal_right_completion_failure
    (a f : R) (I : Ideal R) (hI : I = Ideal.span {a})
    (hR : IsAdicComplete I R)
    (hquot : ¬ IsAdicComplete I (R ⧸ Ideal.span {f})) :
    Function.Surjective (completedPrincipalQuotientMap I f) ∧
      ¬ Function.Exact (completedPrincipalEndomorphism I f)
        (completedPrincipalQuotientMap I f) := by
  classical
  have hmain := principal_quotient_completion_failure a f I (Ideal.span {f}) hI rfl
    (Ideal.subset_span (Set.mem_singleton f)) hR hquot
  have hpm := hmain.1
  have hcomp :
      completedIdealInclusionMap I (Ideal.span {f}) ∘ₗ
          completedPrincipalMultiplicationMap I (Ideal.span {f}) f
            (Ideal.subset_span (Set.mem_singleton f)) =
        completedPrincipalEndomorphism I f := by
    change AdicCompletion.map I (idealInclusionMap (Ideal.span {f})) ∘ₗ
        AdicCompletion.map I (principalMultiplicationMap (Ideal.span {f}) f
          (Ideal.subset_span (Set.mem_singleton f))) =
      AdicCompletion.map I (principalEndomorphism f)
    rw [AdicCompletion.map_comp]
    congr 1
  refine ⟨?_, ?_⟩
  · simpa [completedPrincipalQuotientMap, principalQuotientMap,
      completedIdealQuotientMap, idealQuotientMap] using hmain.2.1
  · intro hex
    apply hmain.2.2.2.2
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (hex y).mp hy
      refine ⟨completedPrincipalMultiplicationMap I (Ideal.span {f}) f
          (Ideal.subset_span (Set.mem_singleton f)) z, ?_⟩
      calc
        completedIdealInclusionMap I (Ideal.span {f})
            (completedPrincipalMultiplicationMap I (Ideal.span {f}) f
              (Ideal.subset_span (Set.mem_singleton f)) z) =
            completedPrincipalEndomorphism I f z := by
          change completedIdealInclusionMap I (Ideal.span {f})
              (completedPrincipalMultiplicationMap I (Ideal.span {f}) f
                (Ideal.subset_span (Set.mem_singleton f)) z) =
            (AdicCompletion.map I (principalEndomorphism f)) z
          exact congrArg (fun q ↦ q z) hcomp
        _ = y := hz
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz⟩ := hpm x
      apply (hex y).mpr
      refine ⟨z, ?_⟩
      calc
        completedPrincipalEndomorphism I f z =
            completedIdealInclusionMap I (Ideal.span {f})
              (completedPrincipalMultiplicationMap I (Ideal.span {f}) f
                (Ideal.subset_span (Set.mem_singleton f)) z) := by
          change (AdicCompletion.map I (principalEndomorphism f)) z =
            completedIdealInclusionMap I (Ideal.span {f})
              (completedPrincipalMultiplicationMap I (Ideal.span {f}) f
                (Ideal.subset_span (Set.mem_singleton f)) z)
          exact (congrArg (fun q ↦ q z) hcomp).symm
        _ = completedIdealInclusionMap I (Ideal.span {f}) x := by rw [hz]
        _ = y := hx

end PrincipalQuotientCounterexample

section ExactnessPredicates

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- Preservation of short exact sequences by the `I`-adic completion maps. -/
def CompletionPreservesExactness : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
      Function.Injective (AdicCompletion.map I f) ∧
        Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
          Function.Surjective (AdicCompletion.map I g)

/-- Preservation of left exact sequences by completion. -/
def CompletionPreservesLeftExactness : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Exact f g →
      Function.Injective (AdicCompletion.map I f) ∧
        Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g)

/-- Preservation of right exact sequences by completion. -/
def CompletionPreservesRightExactness : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Exact f g → Function.Surjective g →
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
        Function.Surjective (AdicCompletion.map I g)

/-- The left exactness predicate restricted to finitely presented modules. -/
def CompletionPreservesLeftExactnessOnFinitelyPresentedModules : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    [Module.FinitePresentation R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Exact f g →
      Function.Injective (AdicCompletion.map I f) ∧
        Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g)

/-- The right exactness predicate restricted to finitely presented modules. -/
def CompletionPreservesRightExactnessOnFinitelyPresentedModules : Prop :=
  ∀ {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    [Module.FinitePresentation R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Exact f g → Function.Surjective g →
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
        Function.Surjective (AdicCompletion.map I g)

/-- Completion is neither left nor right exact in general; right exactness
already fails on finitely presented modules for a finitely generated ideal. -/
theorem completion_not_exact :
    (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
      CompletionPreservesExactness R I) ∧
      (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
        CompletionPreservesLeftExactness R I) ∧
        (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
          CompletionPreservesRightExactness R I) ∧
          (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R), I.FG →
            CompletionPreservesRightExactnessOnFinitelyPresentedModules R I) := by
  classical
  let uliftRatField : Field (ULift.{u} ℚ) := Field.ofIsUnitOrEqZero (by
    intro q
    cases q with
    | up q =>
      rcases eq_or_ne q 0 with rfl | hq
      · exact Or.inr rfl
      · left
        rw [isUnit_iff_exists_inv']
        refine ⟨ULift.up q⁻¹, ?_⟩
        change ULift.up (q⁻¹ * q) = ULift.up 1
        rw [inv_mul_cancel₀ hq])
  have hnot_exact :
      ¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
        CompletionPreservesExactness R I := by
    intro h
    have hshort := first_sequence_short_exact (ULift.{u} ℚ)
    have hp : CompletionPreservesExactness (polynomialRing (ULift.{u} ℚ))
        (polynomialAdicIdeal (ULift.{u} ℚ)) :=
      h (polynomialRing (ULift.{u} ℚ))
        (polynomialAdicIdeal (ULift.{u} ℚ))
    dsimp [CompletionPreservesExactness] at hp
    have hpres := hp (M := firstKernel (ULift.{u} ℚ))
      (N := firstMiddle (ULift.{u} ℚ))
      (P := firstCokernel (ULift.{u} ℚ))
      (firstKernelMap (ULift.{u} ℚ))
      (firstQuotientMap (ULift.{u} ℚ))
      hshort.1 hshort.2.1 hshort.2.2
    exact (first_completed_sequence_not_exact (ULift.{u} ℚ)) hpres.2.1
  have hnot_left :
      ¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
        CompletionPreservesLeftExactness R I := by
    intro h
    have hshort := first_sequence_short_exact (ULift.{u} ℚ)
    have hp : CompletionPreservesLeftExactness (polynomialRing (ULift.{u} ℚ))
        (polynomialAdicIdeal (ULift.{u} ℚ)) :=
      h (polynomialRing (ULift.{u} ℚ))
        (polynomialAdicIdeal (ULift.{u} ℚ))
    dsimp [CompletionPreservesLeftExactness] at hp
    have hpres := hp (M := firstKernel (ULift.{u} ℚ))
      (N := firstMiddle (ULift.{u} ℚ))
      (P := firstCokernel (ULift.{u} ℚ))
      (firstKernelMap (ULift.{u} ℚ))
      (firstQuotientMap (ULift.{u} ℚ))
      hshort.1 hshort.2.1
    exact (first_completed_sequence_not_exact (ULift.{u} ℚ)) hpres.2
  have hnot_right :
      ¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
        CompletionPreservesRightExactness R I := by
    intro h
    have hshort := first_sequence_short_exact (ULift.{u} ℚ)
    have hp : CompletionPreservesRightExactness (polynomialRing (ULift.{u} ℚ))
        (polynomialAdicIdeal (ULift.{u} ℚ)) :=
      h (polynomialRing (ULift.{u} ℚ))
        (polynomialAdicIdeal (ULift.{u} ℚ))
    dsimp [CompletionPreservesRightExactness] at hp
    have hpres := hp (M := firstKernel (ULift.{u} ℚ))
      (N := firstMiddle (ULift.{u} ℚ))
      (P := firstCokernel (ULift.{u} ℚ))
      (firstKernelMap (ULift.{u} ℚ))
      (firstQuotientMap (ULift.{u} ℚ))
      hshort.2.1 hshort.2.2
    exact (first_completed_sequence_not_exact (ULift.{u} ℚ)) hpres.1
  have hnot_right_fp :
      ¬ ∀ (R : Type u) [CommRing R] (I : Ideal R), I.FG →
        CompletionPreservesRightExactnessOnFinitelyPresentedModules R I := by
    intro h
    let A := NoncompleteQuotientCompletion (ULift.{u} ℚ)
    let IA : Ideal A := noncompleteQuotientCompletionXIdeal (ULift.{u} ℚ)
    let JA : Ideal A := noncompleteQuotientCompletionTIdeal (ULift.{u} ℚ)
    let xA : A := algebraMap (NoncompleteQuotientRing (ULift.{u} ℚ)) A
      (xElement (ULift.{u} ℚ))
    let tA : A := algebraMap (NoncompleteQuotientRing (ULift.{u} ℚ)) A
      (tElement (ULift.{u} ℚ))
    have hIA : IA = Ideal.span {xA} := by
      dsimp [IA, xA]
      simp [noncompleteQuotientCompletionXIdeal, noncompleteQuotientXIdeal,
        Ideal.map_span]
      rfl
    have hJA : JA = Ideal.span {tA} := by
      dsimp [JA, tA]
      simp [noncompleteQuotientCompletionTIdeal, noncompleteQuotientTIdeal,
        Ideal.map_span]
      rfl
    have hIAFG : IA.FG := by
      dsimp [IA]
      exact (noncompleteQuotientCompletionXIdeal_isPrincipal (ULift.{u} ℚ)).fg
    have hspanFG : (Ideal.span {tA}).FG := by
      exact Submodule.fg_span_singleton tA
    let quotientFP : Module.FinitePresentation A (A ⧸ Ideal.span {tA}) := by
      apply Module.finitePresentation_of_surjective (Ideal.span {tA}).mkQ
        (Submodule.mkQ_surjective (Ideal.span {tA}))
      rw [Submodule.ker_mkQ]
      exact hspanFG
    have hA : IsAdicComplete IA A := by
      dsimp [IA]
      exact noncompleteQuotientCompletion_isAdicComplete (ULift.{u} ℚ)
    have hnotA : ¬ IsAdicComplete IA (A ⧸ JA) := by
      dsimp [IA, JA, A]
      exact noncompleteQuotientCompletion_quotient_not_isAdicComplete
        (ULift.{u} ℚ)
    have hnotSpan : ¬ IsAdicComplete IA (A ⧸ Ideal.span {tA}) := by
      rw [← hJA]
      exact hnotA
    have hcompzero :
        principalQuotientMap tA ∘ₗ principalEndomorphism tA = 0 := by
      apply LinearMap.ext
      intro r
      change (Ideal.span {tA}).mkQ (tA * r) = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact (Ideal.span {tA}).mul_mem_right r
        (Ideal.subset_span (Set.mem_singleton tA))
    have hkerange : ∀ r, principalQuotientMap tA r = 0 →
        r ∈ LinearMap.range (principalEndomorphism tA) := by
      intro r hr
      change (Ideal.span {tA}).mkQ r = 0 at hr
      have hrmem := (Submodule.Quotient.mk_eq_zero _).mp hr
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hrmem
      refine ⟨s, ?_⟩
      change tA * s = r
      exact hs.symm
    have hex : Function.Exact (principalEndomorphism tA)
        (principalQuotientMap tA) :=
      LinearMap.exact_of_comp_of_mem_range hcompzero hkerange
    have hsurj : Function.Surjective (principalQuotientMap tA) :=
      Submodule.mkQ_surjective (Ideal.span {tA})
    have hp : CompletionPreservesRightExactnessOnFinitelyPresentedModules A IA :=
      h A IA hIAFG
    dsimp [CompletionPreservesRightExactnessOnFinitelyPresentedModules] at hp
    have hpres := hp (M := A) (N := A) (P := A ⧸ Ideal.span {tA})
      (principalEndomorphism tA)
      (principalQuotientMap tA) hex hsurj
    exact (principal_right_completion_failure xA tA IA hIA hA hnotSpan).2 hpres.1
  exact ⟨hnot_exact, hnot_left, hnot_right, hnot_right_fp⟩

end ExactnessPredicates

end

end Formalization.Books.Examples.Unit09
