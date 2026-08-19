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
              DirectSum.component.of, LinearMap.comp_apply]
          · simp [firstKernelMap, firstKernelComponentMap,
              DirectSum.component.of, LinearMap.comp_apply, hi]
            ext z
            simp [firstKernelMap, firstKernelComponentMap,
              DirectSum.component.of, LinearMap.comp_apply, hi]
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
            (SModEq.symm (a.property (show 2 ≤ l by simp [l, hn2])))
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
      · exact hbad 2 (by decide) (by simpa [hs])
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
        DirectSum.component.of, LinearMap.comp_apply]
    · simp [firstKernelMap, firstKernelComponentMap,
        DirectSum.component.of, LinearMap.comp_apply, hi]
      ext z
      simp [firstKernelMap, firstKernelComponentMap,
        DirectSum.component.of, LinearMap.comp_apply, hi]
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
      ext z
      simp [firstQuotientMap, firstQuotientComponentMap,
        DirectSum.component.of, LinearMap.comp_apply]
    · simp [firstQuotientMap, firstQuotientComponentMap,
        DirectSum.component.of, LinearMap.comp_apply, hi]
      ext z
      simp [firstQuotientMap, firstQuotientComponentMap,
        DirectSum.component.of, LinearMap.comp_apply, hi]
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
  sorry

/-- The same quotient phenomenon gives failure for the sequence
`R → R → R/(f) → 0`. -/
theorem principal_right_completion_failure
    (a f : R) (I : Ideal R) (hI : I = Ideal.span {a})
    (hR : IsAdicComplete I R)
    (hquot : ¬ IsAdicComplete I (R ⧸ Ideal.span {f})) :
    Function.Surjective (completedPrincipalQuotientMap I f) ∧
      ¬ Function.Exact (completedPrincipalEndomorphism I f)
        (completedPrincipalQuotientMap I f) := by
  sorry

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

/-- Completion is neither left nor right exact in general, including on
finitely presented modules with a finitely generated ideal. -/
theorem completion_not_exact :
    (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
      CompletionPreservesExactness R I) ∧
      (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
        CompletionPreservesLeftExactness R I) ∧
        (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
          CompletionPreservesRightExactness R I) ∧
          (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R), I.FG →
            CompletionPreservesLeftExactnessOnFinitelyPresentedModules R I) ∧
            (¬ ∀ (R : Type u) [CommRing R] (I : Ideal R), I.FG →
              CompletionPreservesRightExactnessOnFinitelyPresentedModules R I) := by
  sorry

end ExactnessPredicates

end

end Formalization.Books.Examples.Unit09
