import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Noncomplete completion

This file formalizes the precise statements in Section 7 of `books/examples.tex`.
The completion used throughout is Mathlib's inverse-limit construction
`AdicCompletion`; proposition proofs are left for the proving stage.
-/

namespace Formalization.Books.Examples.Unit07

open scoped BigOperators

open Ideal Submodule

universe u v

section Completion

variable {R : Type u} [CommRing R] (m : Ideal R)

/-- The kernel of the zeroth residue map of the adic completion. -/
noncomputable def completionMaximalIdeal : Ideal (AdicCompletion m R) :=
  RingHom.ker (AdicCompletion.evalOneₐ m).toRingHom

/-- The kernel of the projection of the completion to the `n`th quotient. -/
noncomputable def completionKernel (n : ℕ) : Ideal (AdicCompletion m R) :=
  RingHom.ker (AdicCompletion.evalₐ m n).toRingHom

/-- The assertion that the completion's maximal ideal is extended from `m`. -/
def maximalIdealIsExtended : Prop :=
  m.map (algebraMap R (AdicCompletion m R)) = completionMaximalIdeal m

/-- Completeness of the completion as a module over its own local ring. -/
def completionIsCompleteAsCompletionModule : Prop :=
  IsAdicComplete (completionMaximalIdeal m) (AdicCompletion m R)

/-- Completeness of the completion as an `R`-module for the original ideal. -/
def completionIsCompleteAsOriginalModule : Prop :=
  IsAdicComplete m (AdicCompletion m R)

/-- Every element of the inverse-limit completion is represented by an adic Cauchy sequence. -/
theorem adicCompletion_is_complete_in_inverse_limit_topology :
    Function.Surjective (AdicCompletion.mk m R) := by
  exact AdicCompletion.mk_surjective m R

/-- An element outside the kernel-defined maximal ideal is a unit. -/
theorem completion_unit_of_not_mem_maximalIdeal
    (x : AdicCompletion m R) (hx : x ∉ completionMaximalIdeal m) :
    ∃ y : AdicCompletion m R, x * y = 1 := by
  sorry

/-- The completion is local when the defining ideal is maximal. -/
theorem adicCompletion_isLocalRing [m.IsMaximal] :
    IsLocalRing (AdicCompletion m R) := by
  have unit_of_not_mem :
      ∀ (x : AdicCompletion m R), x ∉ completionMaximalIdeal m → IsUnit x := by
    intro x hx
    have hx' : AdicCompletion.evalOneₐ m x ≠ 0 := by
      simpa [completionMaximalIdeal, RingHom.mem_ker] using hx
    have hx1 : x.val 1 ≠ 0 := by
      intro hzero
      apply hx'
      simp [AdicCompletion.evalOneₐ, AdicCompletion.evalₐ, AdicCompletion.eval, hzero]
    have hu : ∀ n, IsUnit (x.val n) := by
      intro n
      cases n with
      | zero =>
          rcases Ideal.Quotient.mk_surjective (x.val 0) with ⟨a, ha⟩
          rw [← ha]
          haveI : Subsingleton (R ⧸ (m ^ 0 • ⊤ : Ideal R)) :=
            subsingleton_of_zero_eq_one (by
              change Ideal.Quotient.mk (m ^ 0 • ⊤) 0 =
                Ideal.Quotient.mk (m ^ 0 • ⊤) 1
              rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
              simp)
          exact isUnit_of_subsingleton _
      | succ n =>
          rcases Ideal.Quotient.mk_surjective (x.val (Nat.succ n)) with ⟨a, ha⟩
          rw [← ha]
          let e := (Ideal.quotientEquivAlgOfEq R
            (show (m ^ Nat.succ n • ⊤ : Ideal R) = m ^ Nat.succ n by
              ext
              simp)).toRingEquiv
          have htarget :
              IsUnit (e (Ideal.Quotient.mk (m ^ Nat.succ n • ⊤) a)) := by
            have hnot : a ∉ m := by
              intro ham
              apply hx1
              have hle : 1 ≤ Nat.succ n :=
                Nat.succ_le_succ (Nat.zero_le n)
              calc
                x.val 1 =
                    AdicCompletion.transitionMap m R hle (x.val (Nat.succ n)) :=
                  (x.property hle).symm
                _ = AdicCompletion.transitionMap m R hle
                    (Ideal.Quotient.mk (m ^ Nat.succ n • ⊤ : Ideal R) a) := by
                  rw [ha]
                _ = 0 := by
                  rw [AdicCompletion.transitionMap_ideal_mk]
                  rw [Ideal.Quotient.eq_zero_iff_mem]
                  simpa [smul_eq_mul, Ideal.mul_top, pow_one] using ham
            simpa [e] using
              (Ideal.Quotient.isUnit_mk_pow_of_notMem
                (I := m) (n := Nat.succ n) hnot)
          simpa [e] using htarget.map e.symm.toRingHom
    let y : AdicCompletion m R :=
      { val := fun n =>
          (↑((hu n).unit⁻¹) : R ⧸ (m ^ n • ⊤ : Ideal R))
        property := by
          intro i j hij
          have hjinv :
              (↑((hu j).unit⁻¹) : R ⧸ (m ^ j • ⊤ : Ideal R)) * x.val j = 1 := by
            calc
              (↑((hu j).unit⁻¹) : R ⧸ (m ^ j • ⊤ : Ideal R)) * x.val j =
                  (↑((hu j).unit⁻¹) : R ⧸ (m ^ j • ⊤ : Ideal R)) * (hu j).unit := by
                    rw [IsUnit.unit_spec]
              _ = 1 := (hu j).unit.inv_val
          have hiinv :
              (↑((hu i).unit⁻¹) : R ⧸ (m ^ i • ⊤ : Ideal R)) * x.val i = 1 := by
            calc
              (↑((hu i).unit⁻¹) : R ⧸ (m ^ i • ⊤ : Ideal R)) * x.val i =
                  (↑((hu i).unit⁻¹) : R ⧸ (m ^ i • ⊤ : Ideal R)) * (hu i).unit := by
                    rw [IsUnit.unit_spec]
              _ = 1 := (hu i).unit.inv_val
          apply (hu i).mul_left_inj.mp
          calc
            AdicCompletion.transitionMap m R hij
                (↑((hu j).unit⁻¹) : R ⧸ (m ^ j • ⊤ : Ideal R)) * x.val i = 1 := by
              rw [← x.property hij]
              rw [← AdicCompletion.transitionMap_map_mul]
              rw [hjinv]
              exact AdicCompletion.transitionMap_map_one m hij
            _ = (↑((hu i).unit⁻¹) : R ⧸ (m ^ i • ⊤ : Ideal R)) * x.val i :=
              hiinv.symm }
    apply isUnit_iff_exists_inv.mpr
    refine ⟨y, ?_⟩
    ext n
    change x.val n *
        (↑((hu n).unit⁻¹) : R ⧸ (m ^ n • ⊤ : Ideal R)) = 1
    calc
      x.val n *
          (↑((hu n).unit⁻¹) : R ⧸ (m ^ n • ⊤ : Ideal R)) =
          (hu n).unit *
            (↑((hu n).unit⁻¹) : R ⧸ (m ^ n • ⊤ : Ideal R)) := by
        rw [IsUnit.unit_spec]
      _ = 1 := (hu n).unit.val_inv
  let _ := Ideal.Quotient.field m
  have hne : (0 : AdicCompletion m R) ≠ 1 := by
    intro h
    have h' := congrArg (AdicCompletion.evalOneₐ m) h
    simpa using h'
  refine { toNontrivial := ⟨⟨0, 1, hne⟩⟩, isUnit_or_isUnit_of_add_one := ?_ }
  intro a b hab
  by_cases ha : a ∈ completionMaximalIdeal m
  · right
    apply unit_of_not_mem b
    intro hb
    have hab0 : a + b ∈ completionMaximalIdeal m := add_mem ha hb
    have hzero : AdicCompletion.evalOneₐ m (a + b) = 0 := by
      simpa [completionMaximalIdeal, RingHom.mem_ker] using hab0
    rw [hab, map_one] at hzero
    exact one_ne_zero hzero
  · left
    exact unit_of_not_mem a ha

/-- The kernel-defined maximal ideal is maximal. -/
theorem completionMaximalIdeal_isMaximal [m.IsMaximal] :
    (completionMaximalIdeal m).IsMaximal := by
  let _ := Ideal.Quotient.field m
  unfold completionMaximalIdeal
  exact RingHom.ker_isMaximal_of_surjective (AdicCompletion.evalOneₐ m).toRingHom
    (AdicCompletion.evalOneₐ_surjective m)

/-- Completeness for the original ideal forces the maximal ideal to be extended. -/
theorem completion_original_complete_implies_extended :
    completionIsCompleteAsOriginalModule m → maximalIdealIsExtended m := by
  intro hcomplete
  unfold completionIsCompleteAsOriginalModule at hcomplete
  unfold maximalIdealIsExtended
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change ((AdicCompletion.evalOneₐ m).toRingHom.comp
      (algebraMap R (AdicCompletion m R))) r = 0
    rw [AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  · intro x hx
    let K : ℕ → Submodule R (AdicCompletion m R) :=
      fun n => (AdicCompletion.eval m R n).ker
    have hxval : x.val 1 = 0 := by
      have hx' : AdicCompletion.evalOneₐ m x = 0 := by
        simpa [completionMaximalIdeal, RingHom.mem_ker] using hx
      have heq : m ^ 1 = m := by simp
      have hfactor : Function.Injective
          (Ideal.Quotient.factor (le_of_eq heq)) := by
        simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
          using Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
      have hxevalₐ : AdicCompletion.evalₐ m 1 x = 0 := by
        apply hfactor
        rw [AdicCompletion.factorₐ_evalₐ_one]
        exact hx'
      have hxeval : AdicCompletion.eval m R 1 x = 0 := by
        let h : m ^ 1 ≤ m ^ 1 • (⊤ : Ideal R) := by simp
        calc
          AdicCompletion.eval m R 1 x =
              Ideal.Quotient.factor h (AdicCompletion.evalₐ m 1 x) :=
            (AdicCompletion.factor_evalₐ_eq_eval m x h).symm
          _ = Ideal.Quotient.factor h 0 := congrArg (Ideal.Quotient.factor h) hxevalₐ
          _ = 0 := map_zero _
      simpa only [AdicCompletion.eval_apply] using hxeval
    have hstep (n : ℕ) {z : AdicCompletion m R} (hz : z ∈ K n) :
        ∃ y : AdicCompletion m R, y ∈ K (n + 1) ∧
          z - y ∈ m ^ n • (⊤ : Submodule R (AdicCompletion m R)) := by
      have hzval : z.val n = 0 := by
        exact LinearMap.mem_ker.mp (by simpa [K] using hz)
      have hmem : z.val (n + 1) ∈
          m ^ n • (⊤ : Submodule R
            (R ⧸ (m ^ (n + 1) • (⊤ : Submodule R R)))) :=
        (AdicCompletion.val_apply_mem_smul_top_iff (I := m) (M := R)
          (Nat.le_succ n)).2 hzval
      have hmap :
          Submodule.map (Submodule.mkQ (m ^ (n + 1) • (⊤ : Submodule R R)))
              (m ^ n • (⊤ : Submodule R R)) =
            m ^ n • (⊤ : Submodule R
              (R ⧸ (m ^ (n + 1) • (⊤ : Submodule R R)))) := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      rw [← hmap] at hmem
      obtain ⟨a, ha, haz⟩ := (Submodule.mem_map
        (f := Submodule.mkQ (m ^ (n + 1) • (⊤ : Submodule R R)))
        (p := m ^ n • (⊤ : Submodule R R))
        (x := z.val (n + 1))).1 hmem
      refine ⟨z - AdicCompletion.of m R a, ?_, ?_⟩
      · rw [LinearMap.mem_ker, AdicCompletion.eval_apply,
          AdicCompletion.val_sub_apply, AdicCompletion.of_apply, haz]
        simp
      · have hofa : AdicCompletion.of m R a ∈
            m ^ n • (⊤ : Submodule R (AdicCompletion m R)) := by
          have hmapof : Submodule.map (AdicCompletion.of m R)
                (m ^ n • (⊤ : Submodule R R)) ≤
              m ^ n • (⊤ : Submodule R (AdicCompletion m R)) := by
            rw [Submodule.map_smul'', Submodule.map_top]
            exact smul_mono_right _ le_top
          exact hmapof (Submodule.mem_map_of_mem ha)
        convert hofa using 1
        abel
    let next (j : ℕ)
        (z : {z : AdicCompletion m R // z ∈ K (1 + j)}) :
        {z : AdicCompletion m R // z ∈ K (1 + j + 1)} := by
      let h := hstep (1 + j) z.property
      exact ⟨h.choose, h.choose_spec.1⟩
    have hnext (j : ℕ)
        (z : {z : AdicCompletion m R // z ∈ K (1 + j)}) :
        z.1 - (next j z).1 ∈ m ^ (1 + j) •
          (⊤ : Submodule R (AdicCompletion m R)) := by
      dsimp [next]
      exact (hstep (1 + j) z.property).choose_spec.2
    let cseq : (j : ℕ) →
        {z : AdicCompletion m R // z ∈ K (1 + j)} :=
      Nat.rec ⟨x, by simpa [K] using
        (show AdicCompletion.eval m R 1 x = 0 by
          simpa only [AdicCompletion.eval_apply] using hxval)⟩
        (fun j z => next j z)
    have hcstep (j : ℕ) :
        (cseq j).1 - (cseq (j + 1)).1 ∈
          m ^ (1 + j) • (⊤ : Submodule R (AdicCompletion m R)) := by
      simpa [cseq] using hnext j (cseq j)
    have hcchain : ∀ {j l : ℕ}, j ≤ l →
        (cseq j).1 - (cseq l).1 ∈
          m ^ (1 + j) • (⊤ : Submodule R (AdicCompletion m R)) := by
      intro j l hjl
      induction l, hjl using Nat.le_induction with
      | base => simp
      | succ l hle ih =>
          have hmon : m ^ (1 + l) • (⊤ : Submodule R (AdicCompletion m R)) ≤
              m ^ (1 + j) • (⊤ : Submodule R (AdicCompletion m R)) :=
            Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
          have hlast := hmon (hcstep l)
          convert Submodule.add_mem _ ih hlast using 1
          abel
    have hcx (j : ℕ) :
        x - (cseq j).1 ∈ m • (⊤ : Submodule R (AdicCompletion m R)) := by
      simpa [cseq] using hcchain (j := 0) (l := j) (Nat.zero_le j)
    let b (k : ℕ) : AdicCompletion m R :=
      if hkn : k ≤ 1 then x else (cseq (k - 1)).1
    have hbK (k : ℕ) : b k ∈ K k := by
      by_cases hkn : k ≤ 1
      · simp only [b, dif_pos hkn]
        change x.val k = 0
        have hprop := x.property hkn
        rw [hxval] at hprop
        simpa using hprop.symm
      · simp only [b, dif_neg hkn]
        have h1k : 1 ≤ k := Nat.le_of_not_ge hkn
        simpa [Nat.add_sub_of_le h1k] using (cseq (k - 1)).property
    have hb_cauchy : ∀ {i k : ℕ}, i ≤ k →
        b i ≡ b k [SMOD (m ^ i • (⊤ : Submodule R (AdicCompletion m R)))] := by
      intro i k hik
      rw [SModEq.sub_mem]
      by_cases hk : k ≤ 1
      · have hik' : i ≤ 1 := hik.trans hk
        simp only [b]
        rw [dif_pos hik', dif_pos hk]
        simp
      · have h1k : 1 ≤ k := Nat.le_of_not_ge hk
        by_cases hi : i ≤ 1
        · have hmon : m • (⊤ : Submodule R (AdicCompletion m R)) ≤
              m ^ i • (⊤ : Submodule R (AdicCompletion m R)) := by
            have hi' : i = 0 ∨ i = 1 := by omega
            rcases hi' with rfl | rfl
            · simpa using
                (Ideal.map_mono (f := algebraMap R (AdicCompletion m R))
                  (I := m) (J := (⊤ : Ideal R)) le_top)
            · simp
          have hmem := hmon (hcx (k - 1))
          simp only [b]
          rw [dif_pos hi, dif_neg hk]
          exact hmem
        · have hi' : 1 < i := Nat.lt_of_not_ge hi
          have hchain := hcchain (j := i - 1) (l := k - 1) (by omega)
          simp only [b]
          rw [dif_neg hi, dif_neg hk]
          simpa [Nat.add_sub_of_le (Nat.le_of_lt hi')] using hchain
    obtain ⟨L, hL⟩ := hcomplete.toIsPrecomplete.prec' b hb_cauchy
    have hLzero : L = 0 := by
      apply AdicCompletion.ext
      intro k
      have hdiff := SModEq.sub_mem.mp (hL k)
      have hdiffK : b k - L ∈ K k := by
        change b k - L ∈ (AdicCompletion.eval m R k).ker
        exact (AdicCompletion.pow_smul_top_le_ker_eval (I := m) (M := R) k) hdiff
      have hLK : L ∈ K k := by
        have hsub := (K k).sub_mem (hbK k) hdiffK
        convert hsub using 1
        abel
      have hLK' := LinearMap.mem_ker.mp (show L ∈ (AdicCompletion.eval m R k).ker by
        exact hLK)
      rw [AdicCompletion.eval_apply] at hLK'
      exact hLK'
    have h1mem : x ∈ m • (⊤ : Submodule R (AdicCompletion m R)) := by
      have hnconv := SModEq.sub_mem.mp (hL 1)
      rw [show b 1 = x by simp [b], hLzero] at hnconv
      simpa using hnconv
    have hsmul_le_map : m • (⊤ : Submodule R (AdicCompletion m R)) ≤
        (m.map (algebraMap R (AdicCompletion m R))).restrictScalars R := by
      refine Submodule.smul_le.mpr ?_
      intro r hr c hc
      simpa [Algebra.smul_def, mul_comm] using
        (m.map (algebraMap R (AdicCompletion m R))).mul_mem_left c
          (Ideal.mem_map_of_mem (algebraMap R (AdicCompletion m R)) hr)
    exact hsmul_le_map h1mem

theorem completionMaximalIdeal_pow_le_kernel (n : ℕ) :
    completionMaximalIdeal m ^ n ≤ completionKernel m n := by
  sorry

theorem completionKernel_succ_le (n : ℕ) :
    completionKernel m (n + 1) ≤ completionKernel m n := by
  sorry

/-- The projection sends `(m')ⁿ` onto `mⁿ/mⁿ⁺¹`. -/
theorem completion_projection_pow_image (n : ℕ) :
    (completionMaximalIdeal m ^ n).map
        (AdicCompletion.evalₐ m (n + 1)).toRingHom =
      (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
  sorry

/-- The additive quotient `Kₙ/(m')ⁿ` from the exact sequence in the source. -/
noncomputable abbrev completionKernelQuotient (n : ℕ) :=
  (completionKernel m n : Type _) ⧸
    (Submodule.comap
      (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
      (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R)))

/-- The additive quotient `R̂/(m')ⁿ` from the exact sequence in the source. -/
noncomputable abbrev completionQuotient (n : ℕ) :=
  AdicCompletion m R ⧸
    (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R))

/-- The projection `Kₙ₊₁ → Kₙ/(m')ⁿ`. -/
noncomputable def completionKernelTransition (n : ℕ) :
    completionKernel m (n + 1) →ₗ[AdicCompletion m R] completionKernelQuotient m n :=
  let i := (completionKernel m (n + 1) : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype.codRestrict
    (completionKernel m n)
    (fun x => completionKernel_succ_le m n x.property)
  (Submodule.comap
    (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
    (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R))).mkQ.comp i

/-- The transition maps on the kernels are surjective. -/
theorem completionKernelTransition_surjective (n : ℕ) :
    Function.Surjective (completionKernelTransition m n) := by
  sorry

/-- The map from `Kₙ/(m')ⁿ` into `R̂/(m')ⁿ`. -/
noncomputable def completionKernelQuotientMap (m : Ideal R) (n : ℕ) :
    completionKernelQuotient m n →ₗ[AdicCompletion m R] completionQuotient m n :=
  Submodule.mapQ
    (Submodule.comap
      (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
      (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R)))
    (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R))
    (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
    (by
      intro x hx
      exact hx)

/-- The map from `R̂/(m')ⁿ` to `R/mⁿ`. -/
noncomputable def completionQuotientToResidue (n : ℕ) :
    completionQuotient m n →+* R ⧸ m ^ n :=
  Ideal.Quotient.lift (completionMaximalIdeal m ^ n)
    (AdicCompletion.evalₐ m n).toRingHom
    (fun a ha => by
      exact completionMaximalIdeal_pow_le_kernel m n ha)

/-- The short exact sequence
`0 → Kₙ/(m')ⁿ → R̂/(m')ⁿ → R/mⁿ → 0`. -/
theorem completion_kernel_quotient_short_exact (n : ℕ) :
    Function.Injective (completionKernelQuotientMap m n) ∧
      Function.Exact (completionKernelQuotientMap m n).toAddMonoidHom
        (completionQuotientToResidue m n).toAddMonoidHom ∧
      Function.Surjective (completionQuotientToResidue m n) := by
  sorry

/-- The inverse-limit/Mittag--Leffler criterion for completeness in the maximal-ideal topology. -/
theorem completion_is_completeAsCompletionModule_iff_kernel_eq_pow :
    completionIsCompleteAsCompletionModule m ↔
      ∀ n : ℕ, 1 ≤ n → completionKernel m n = completionMaximalIdeal m ^ n := by
  sorry

end Completion

section InfinitePolynomialExample

variable (k : Type u) [Field k]

/-- The countably generated polynomial ring used in the example. -/
abbrev infinitePolynomialRing := MvPolynomial ℕ k

/-- Its ideal generated by all variables. -/
noncomputable abbrev infinitePolynomialMaximalIdeal : Ideal (infinitePolynomialRing k) :=
  MvPolynomial.idealOfVars ℕ k

/-- The ideal generated by all variables is maximal, with residue field `k`. -/
theorem infinitePolynomialMaximalIdeal_isMaximal :
    (infinitePolynomialMaximalIdeal k).IsMaximal := by
  sorry

/-- The finite partial sums of `x₁ + x₂² + x₃³ + ⋯`. -/
noncomputable def infiniteVariableSeriesPartial (n : ℕ) : infinitePolynomialRing k :=
  Finset.sum (Finset.range n) (fun i =>
    (MvPolynomial.X i : infinitePolynomialRing k) ^ (i + 1))

/-- The formal infinite sum `x₁ + x₂² + x₃³ + ⋯` in the adic completion. -/
noncomputable def infiniteVariableSeries :
    AdicCompletion (infinitePolynomialMaximalIdeal k) (infinitePolynomialRing k) :=
  AdicCompletion.mk _ _
    (AdicCompletion.AdicCauchySequence.mk _ _ (infiniteVariableSeriesPartial k) (by
      intro n
      apply (SModEq.sub_mem).2
      have hmem :
          (MvPolynomial.X n : infinitePolynomialRing k) ^ (n + 1) ∈
            infinitePolynomialMaximalIdeal k ^ n := by
        rw [MvPolynomial.X_pow_eq_monomial]
        apply (MvPolynomial.monomial_mem_pow_idealOfVars_iff n
          (Finsupp.single n (n + 1)) (by simp)).2
        simp
      have hneg :
          -(MvPolynomial.X n : infinitePolynomialRing k) ^ (n + 1) ∈
            infinitePolynomialMaximalIdeal k ^ n :=
        (infinitePolynomialMaximalIdeal k ^ n).neg_mem hmem
      simpa [infiniteVariableSeriesPartial, Finset.sum_range_succ, sub_eq_add_neg,
        add_assoc, smul_eq_mul, Ideal.mul_top] using hneg))

/-- Coordinates of the formal infinite sum are its finite partial sums. -/
theorem infiniteVariableSeries_coordinate (n : ℕ) :
    AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) n
        (infiniteVariableSeries k) =
      Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ n)
        (infiniteVariableSeriesPartial k n) := by
  sorry

/-- The series has zero constant term. -/
theorem infiniteVariableSeries_mem_completionMaximalIdeal :
    infiniteVariableSeries k ∈
      Formalization.Books.Examples.Unit07.completionMaximalIdeal
        (infinitePolynomialMaximalIdeal k) := by
  sorry

/-- The series is not a finite `R`-linear combination of elements of the completion. -/
theorem infiniteVariableSeries_not_mem_extendedMaximalIdeal :
    infiniteVariableSeries k ∉
      (infinitePolynomialMaximalIdeal k).map
        (algebraMap (infinitePolynomialRing k)
          (AdicCompletion (infinitePolynomialMaximalIdeal k) (infinitePolynomialRing k))) := by
  sorry

theorem infinitePolynomial_maximalIdeal_not_extended :
    ¬ Formalization.Books.Examples.Unit07.maximalIdealIsExtended
        (infinitePolynomialMaximalIdeal k) := by
  sorry

/-- The series lies in `K₂` but not in the square of the completion's maximal ideal. -/
theorem infiniteVariableSeries_mem_completionKernel_two :
    infiniteVariableSeries k ∈
      Formalization.Books.Examples.Unit07.completionKernel
        (infinitePolynomialMaximalIdeal k) 2 := by
  sorry

theorem infiniteVariableSeries_not_mem_completionMaximalIdeal_sq :
    infiniteVariableSeries k ∉
      Formalization.Books.Examples.Unit07.completionMaximalIdeal
        (infinitePolynomialMaximalIdeal k) ^ 2 := by
  sorry

theorem infinitePolynomial_completion_not_complete_as_completionModule :
    ¬ Formalization.Books.Examples.Unit07.completionIsCompleteAsCompletionModule
        (infinitePolynomialMaximalIdeal k) := by
  sorry

theorem infinitePolynomial_completion_not_complete_as_originalModule :
    ¬ Formalization.Books.Examples.Unit07.completionIsCompleteAsOriginalModule
        (infinitePolynomialMaximalIdeal k) := by
  sorry

end InfinitePolynomialExample

section DerivativeObstruction

variable (k : Type u) [Field k]

/-- A finite sum of products with both factors having zero constant term. -/
def IsFiniteProductSum {n : ℕ} (t : ℕ) (p : MvPolynomial (Fin n) k) : Prop :=
  ∃ f g : Fin t → MvPowerSeries (Fin n) k,
    (∀ i, MvPowerSeries.constantCoeff (f i) = 0 ∧
      MvPowerSeries.constantCoeff (g i) = 0) ∧
      (p : MvPowerSeries (Fin n) k) = ∑ i, f i * g i

/-- The homogeneous polynomial `x₁ᵈ + ⋯ + xₙᵈ`. -/
noncomputable def powerSumPolynomial (n d : ℕ) : MvPolynomial (Fin n) k :=
  ∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) k) ^ d

/-- The ideal generated by the formal partial derivatives of a polynomial. -/
noncomputable def polynomialDerivativeIdeal {n : ℕ} (p : MvPolynomial (Fin n) k) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span (Set.range (fun i : Fin n => MvPolynomial.pderiv i p))

/-- The ideal generated by the formal partial derivatives of a power series. -/
noncomputable def powerSeriesDerivativeIdeal {n t : ℕ}
    (f g : Fin t → MvPowerSeries (Fin n) k) :
    Ideal (MvPowerSeries (Fin n) k) :=
  Ideal.span (Set.range (fun i : Fin n =>
    MvPowerSeries.pderiv k i (∑ j, f j * g j)))

/-- The ideal generated by the factors in a finite product sum. -/
noncomputable def powerSeriesFactorIdeal {n t : ℕ}
    (f g : Fin t → MvPowerSeries (Fin n) k) :
    Ideal (MvPowerSeries (Fin n) k) :=
  Ideal.span (Set.range f ∪ Set.range g)

/-- The Krull dimension of the closed locus defined by an ideal. -/
noncomputable def zeroLocusKrullDimension {A : Type v} [CommRing A] (I : Ideal A) : WithBot ℕ∞ :=
  ringKrullDim (A ⧸ I)

theorem powerSumPolynomial_isHomogeneous (n d : ℕ) :
    MvPolynomial.IsHomogeneous (powerSumPolynomial k n d) d := by
  sorry

theorem powerSumPolynomial_derivative_ideal (n d : ℕ) (hd : (d : k) ≠ 0) :
    polynomialDerivativeIdeal k (powerSumPolynomial k n d) =
      Ideal.span (Set.range (fun i : Fin n =>
        (d : k) • (MvPolynomial.X i : MvPolynomial (Fin n) k) ^ (d - 1))) := by
  sorry

theorem powerSumPolynomial_derivative_zeroLocus_is_singleton
    (n d : ℕ) (hn : 0 < n) (hd : (d : k) ≠ 0) :
    ∃ x : PrimeSpectrum (MvPolynomial (Fin n) k),
      PrimeSpectrum.zeroLocus (polynomialDerivativeIdeal k (powerSumPolynomial k n d)) = {x} := by
  sorry

theorem finiteProductSum_derivative_mem_factorIdeal
    {n t : ℕ} (f g : Fin t → MvPowerSeries (Fin n) k) (i : Fin n) :
    MvPowerSeries.pderiv k i (∑ j, f j * g j) ∈ powerSeriesFactorIdeal k f g := by
  sorry

theorem finiteProductSum_factor_locus_dimension
    {n t : ℕ} (f g : Fin t → MvPowerSeries (Fin n) k) :
    ((n - 2 * t : ℕ) : WithBot ℕ∞) ≤
      zeroLocusKrullDimension (powerSeriesFactorIdeal k f g) := by
  sorry

theorem finiteProductSum_derivative_locus_contains_factor_locus
    {n t : ℕ} (f g : Fin t → MvPowerSeries (Fin n) k) :
      PrimeSpectrum.zeroLocus (powerSeriesFactorIdeal k f g : Set (MvPowerSeries (Fin n) k)) ⊆
      PrimeSpectrum.zeroLocus (powerSeriesDerivativeIdeal k f g : Set (MvPowerSeries (Fin n) k)) := by
  sorry

theorem powerSumPolynomial_not_finiteProductSum
    (n d t : ℕ) (hnt : 2 * t < n) (hd : 1 < d) (hchar : (d : k) ≠ 0) :
    ¬ IsFiniteProductSum k t (powerSumPolynomial k n d) := by
  sorry

theorem exists_powerSum_obstruction (t : ℕ) (ht : 0 < t) :
    ∃ (n d : ℕ), 2 * t < n ∧ 1 < d ∧ (d : k) ≠ 0 ∧
      ¬ IsFiniteProductSum k t (powerSumPolynomial k n d) := by
  sorry

/-- A block-by-block sequence of homogeneous polynomials with the required obstruction. -/
structure HomogeneousBlockSeries where
  degree : ℕ → ℕ
  blockStart : ℕ → ℕ
  block : ∀ i, MvPolynomial (Fin (blockStart (i + 1) - blockStart i)) k
  degree_strict : StrictMono degree
  block_start_strict : StrictMono blockStart
  positive_block_start : ∀ i, 0 < blockStart i
  degree_gt_one : ∀ i, 1 < degree i
  homogeneous : ∀ i, MvPolynomial.IsHomogeneous (block i) (degree i)
  obstruction : ∀ i t, t ≤ i → ¬ IsFiniteProductSum k t (block i)

theorem exists_homogeneousBlockSeries :
    Nonempty (HomogeneousBlockSeries k) := by
  sorry

theorem exists_completion_kernel_not_square :
    ∃ z : AdicCompletion (MvPolynomial.idealOfVars ℕ k) (MvPolynomial ℕ k),
      z ∈ Formalization.Books.Examples.Unit07.completionKernel
          (MvPolynomial.idealOfVars ℕ k) 2 ∧
        z ∉ Formalization.Books.Examples.Unit07.completionMaximalIdeal
          (MvPolynomial.idealOfVars ℕ k) ^ 2 := by
  sorry

end DerivativeObstruction

section FinalStatement

variable (k : Type u) [Field k]

/-- The local-ring counterexample supplied by the infinite polynomial construction. -/
theorem lemma_noncomplete_completion :
    ∃ (R : CommRingCat.{u}) (m : Ideal (R : Type u)),
      m.IsMaximal ∧
        IsLocalRing (R : Type u) ∧
        IsLocalRing (AdicCompletion m (R : Type u)) ∧
        completionMaximalIdeal m ≠
          m.map (algebraMap (R : Type u) (AdicCompletion m (R : Type u))) ∧
        ¬ completionIsCompleteAsCompletionModule m ∧
        ¬ completionIsCompleteAsOriginalModule m := by
  sorry

end FinalStatement

/- The chapter-level result packages the local, nonextended, and two distinct
completeness failures established by the preceding declarations. -/
end Formalization.Books.Examples.Unit07
