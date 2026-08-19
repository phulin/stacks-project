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
    [m.IsMaximal]
    (x : AdicCompletion m R) (hx : x ∉ completionMaximalIdeal m) :
    ∃ y : AdicCompletion m R, x * y = 1 := by
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
          have : Subsingleton (R ⧸ (m ^ 0 • ⊤ : Ideal R)) :=
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
  exact isUnit_iff_exists_inv.mp (unit_of_not_mem x hx)

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
          have : Subsingleton (R ⧸ (m ^ 0 • ⊤ : Ideal R)) :=
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
    simp at h'
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
  cases n with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      intro x hx
      change AdicCompletion.evalₐ m 0 x = 0
      have hsub : Subsingleton (R ⧸ (m ^ 0)) := by
        apply subsingleton_of_zero_eq_one
        change Ideal.Quotient.mk (m ^ 0) 0 = Ideal.Quotient.mk (m ^ 0) 1
        rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        simp
      exact @Subsingleton.elim _ hsub _ _
  | succ n =>
      let f := (AdicCompletion.evalₐ m (n + 1)).toRingHom
      let q := Ideal.Quotient.mk (m ^ (n + 1))
      have hcomp :
          (Ideal.Quotient.factor (Ideal.pow_le_self (by omega))).comp f =
            (AdicCompletion.evalOneₐ m).toRingHom := by
        ext x
        induction x using AdicCompletion.induction_on with
        | h a =>
            simp [f, AdicCompletion.evalOneₐ]
            have ha := a.property (show 1 ≤ n + 1 by omega)
            simpa [AdicCompletion.transitionMap_ideal_mk] using
              congrArg
                (fun z : R ⧸ (m ^ 1 • (⊤ : Ideal R)) =>
                  Ideal.Quotient.factor
                    (show m ^ 1 • (⊤ : Ideal R) ≤ m by simp) z) ha
                |>.symm
      have hm : m.map (algebraMap R (AdicCompletion m R)) ≤
          completionMaximalIdeal m := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        change ((AdicCompletion.evalOneₐ m).toRingHom.comp
          (algebraMap R (AdicCompletion m R))) r = 0
        rw [AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
      have hmap : Ideal.map f (completionMaximalIdeal m) ≤ Ideal.map q m := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        change f x ∈ Ideal.map q m
        rw [← Ideal.Quotient.factor_ker (Ideal.pow_le_self (by omega))]
        change ((Ideal.Quotient.factor (Ideal.pow_le_self (by omega))).comp f) x = 0
        rw [hcomp]
        simpa [completionMaximalIdeal, RingHom.mem_ker] using hx
      intro x hx
      change f x = 0
      have hzero : Ideal.map f (completionMaximalIdeal m ^ (n + 1)) = ⊥ := by
        apply le_antisymm
        · calc
            Ideal.map f (completionMaximalIdeal m ^ (n + 1)) =
                Ideal.map f (completionMaximalIdeal m) ^ (n + 1) :=
              Ideal.map_pow f (completionMaximalIdeal m) (n + 1)
            _ ≤ Ideal.map q m ^ (n + 1) := Ideal.pow_right_mono hmap (n + 1)
            _ = Ideal.map q (m ^ (n + 1)) := (Ideal.map_pow q m (n + 1)).symm
            _ = ⊥ := Ideal.map_quotient_self _
        · exact bot_le
      have hxzero : f x ∈ (⊥ : Ideal (R ⧸ m ^ (n + 1))) := by
        rw [← hzero]
        exact Ideal.mem_map_of_mem f hx
      simpa using hxzero

theorem completionKernel_succ_le (n : ℕ) :
    completionKernel m (n + 1) ≤ completionKernel m n := by
  intro x hx
  change AdicCompletion.evalₐ m n x = 0
  have h : AdicCompletion.evalₐ m (n + 1) x = 0 := hx
  have hfactor (k : ℕ) :
      Function.Injective
        (Ideal.Quotient.factor (show m ^ k • (⊤ : Ideal R) ≤ m ^ k by simp)) := by
    have heq : m ^ k • (⊤ : Ideal R) = m ^ k := by ext; simp
    simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      using Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
  have h' : AdicCompletion.eval m R (n + 1) x = 0 := by
    apply hfactor (n + 1)
    calc
      (Ideal.Quotient.factor (show m ^ (n + 1) • (⊤ : Ideal R) ≤ m ^ (n + 1) by simp))
          (AdicCompletion.eval m R (n + 1) x) =
          AdicCompletion.evalₐ m (n + 1) x := by
            exact AdicCompletion.factor_eval_eq_evalₐ m x (by simp)
      _ = 0 := h
  have hn : AdicCompletion.eval m R n x = 0 := by
    calc
      AdicCompletion.eval m R n x = x.val n := AdicCompletion.eval_apply m R n x
      _ = AdicCompletion.transitionMap m R (Nat.le_succ n) (x.val (n + 1)) :=
        (AdicCompletion.transitionMap_comp_eval_apply m R (Nat.le_succ n) x).symm
      _ = AdicCompletion.transitionMap m R (Nat.le_succ n)
          (AdicCompletion.eval m R (n + 1) x) := by
            rw [AdicCompletion.eval_apply]
      _ = 0 := by rw [h']; simp
  calc
    AdicCompletion.evalₐ m n x =
        (Ideal.Quotient.factor (show m ^ n • (⊤ : Ideal R) ≤ m ^ n by simp))
          (AdicCompletion.eval m R n x) :=
      (AdicCompletion.factor_eval_eq_evalₐ m x (by simp)).symm
    _ = 0 := by rw [hn]; simp

/-- The projection sends `(m')ⁿ` onto `mⁿ/mⁿ⁺¹`. -/
theorem completion_projection_pow_image (n : ℕ) :
    (completionMaximalIdeal m ^ n).map
        (AdicCompletion.evalₐ m (n + 1)).toRingHom =
      (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
  let f := (AdicCompletion.evalₐ m (n + 1)).toRingHom
  let q := Ideal.Quotient.mk (m ^ (n + 1))
  have hcomp :
      (Ideal.Quotient.factor (Ideal.pow_le_self (by omega))).comp f =
        (AdicCompletion.evalOneₐ m).toRingHom := by
    ext x
    induction x using AdicCompletion.induction_on with
    | h a =>
        simp [f, AdicCompletion.evalOneₐ]
        have ha := a.property (show 1 ≤ n + 1 by omega)
        simpa [AdicCompletion.transitionMap_ideal_mk] using
          congrArg
            (fun z : R ⧸ (m ^ 1 • (⊤ : Ideal R)) =>
              Ideal.Quotient.factor (show m ^ 1 • (⊤ : Ideal R) ≤ m by simp) z) ha
            |>.symm
  have hm : m.map (algebraMap R (AdicCompletion m R)) ≤ completionMaximalIdeal m := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change ((AdicCompletion.evalOneₐ m).toRingHom.comp
      (algebraMap R (AdicCompletion m R))) r = 0
    rw [AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  have hmap : Ideal.map f (completionMaximalIdeal m) ≤ Ideal.map q m := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change f x ∈ Ideal.map q m
    rw [← Ideal.Quotient.factor_ker (Ideal.pow_le_self (by omega))]
    change ((Ideal.Quotient.factor (Ideal.pow_le_self (by omega))).comp f) x = 0
    rw [hcomp]
    simpa [completionMaximalIdeal, RingHom.mem_ker] using hx
  have hqcomp : f.comp (algebraMap R (AdicCompletion m R)) = q := by
    ext r
    rfl
  apply le_antisymm
  · calc
      Ideal.map f (completionMaximalIdeal m ^ n) =
          Ideal.map f (completionMaximalIdeal m) ^ n :=
        Ideal.map_pow f (completionMaximalIdeal m) n
      _ ≤ Ideal.map q m ^ n := Ideal.pow_right_mono hmap n
      _ = Ideal.map q (m ^ n) := (Ideal.map_pow q m n).symm
  · calc
      Ideal.map q (m ^ n) = Ideal.map (f.comp (algebraMap R (AdicCompletion m R))) (m ^ n) := by
        rw [hqcomp]
      _ = Ideal.map f (Ideal.map (algebraMap R (AdicCompletion m R)) (m ^ n)) := by
        rw [Ideal.map_map]
      _ = Ideal.map f (m.map (algebraMap R (AdicCompletion m R)) ^ n) := by
        rw [Ideal.map_pow]
      _ ≤ Ideal.map f (completionMaximalIdeal m ^ n) := by
        exact Ideal.map_mono (Ideal.pow_right_mono hm n)

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
  rintro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      have hxK : (x : AdicCompletion m R) ∈ completionKernel m n := x.property
      have hxval : (x : AdicCompletion m R).val n = 0 := by
        have hfactor (k : ℕ) :
            Function.Injective
              (Ideal.Quotient.factor
                (show m ^ k • (⊤ : Ideal R) ≤ m ^ k by simp)) := by
          have heq : m ^ k • (⊤ : Ideal R) = m ^ k := by ext z; simp
          simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
            using Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
        have hzero : AdicCompletion.evalₐ m n (x : AdicCompletion m R) = 0 := hxK
        have hzero' : AdicCompletion.eval m R n (x : AdicCompletion m R) = 0 := by
          apply hfactor n
          calc
            Ideal.Quotient.factor
                (show m ^ n • (⊤ : Ideal R) ≤ m ^ n by simp)
                (AdicCompletion.eval m R n (x : AdicCompletion m R)) =
                AdicCompletion.evalₐ m n (x : AdicCompletion m R) :=
              AdicCompletion.factor_eval_eq_evalₐ m (x : AdicCompletion m R) (by simp)
            _ = 0 := hzero
        rw [AdicCompletion.eval_apply] at hzero'
        exact hzero'
      have htransition :
          AdicCompletion.transitionMap m R (Nat.le_succ n)
              ((x : AdicCompletion m R).val (n + 1)) = 0 := by
        rw [AdicCompletion.transitionMap_comp_eval_apply]
        exact hxval
      have hxmap :
          AdicCompletion.evalₐ m (n + 1) (x : AdicCompletion m R) ∈
            (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
        rcases Ideal.Quotient.mk_surjective ((x : AdicCompletion m R).val (n + 1)) with
          ⟨a, ha⟩
        have ha_mem : a ∈ m ^ n := by
          have hzero :
              Ideal.Quotient.mk (m ^ n • (⊤ : Ideal R)) a = 0 := by
            rw [← AdicCompletion.transitionMap_ideal_mk]
            rw [ha]
            exact htransition
          simpa [Ideal.Quotient.eq_zero_iff_mem] using hzero
        have heval :
            AdicCompletion.evalₐ m (n + 1) (x : AdicCompletion m R) =
              Ideal.Quotient.mk (m ^ (n + 1)) a := by
          calc
            AdicCompletion.evalₐ m (n + 1) (x : AdicCompletion m R) =
                Ideal.Quotient.factor
                  (show m ^ (n + 1) • (⊤ : Ideal R) ≤ m ^ (n + 1) by simp)
                  (AdicCompletion.eval m R (n + 1) (x : AdicCompletion m R)) :=
              (AdicCompletion.factor_eval_eq_evalₐ m (x : AdicCompletion m R) (by simp)).symm
            _ = Ideal.Quotient.factor
                  (show m ^ (n + 1) • (⊤ : Ideal R) ≤ m ^ (n + 1) by simp)
                  (Ideal.Quotient.mk (m ^ (n + 1) • (⊤ : Ideal R)) a) := by
              rw [AdicCompletion.eval_apply, ha]
            _ = Ideal.Quotient.mk (m ^ (n + 1)) a := by rfl
        rw [heval]
        exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (m ^ (n + 1))) ha_mem
      have hz : ∃ z : AdicCompletion m R,
          z ∈ completionMaximalIdeal m ^ n ∧
            AdicCompletion.evalₐ m (n + 1) z =
              AdicCompletion.evalₐ m (n + 1) (x : AdicCompletion m R) := by
        rw [← completion_projection_pow_image m n] at hxmap
        have hximage :
            AdicCompletion.evalₐ m (n + 1) (x : AdicCompletion m R) ∈
              (AdicCompletion.evalₐ m (n + 1)).toRingHom ''
                (↑(completionMaximalIdeal m ^ n) : Set (AdicCompletion m R)) :=
          Ideal.mem_image_of_mem_map_of_surjective
            (I := completionMaximalIdeal m ^ n)
            (f := (AdicCompletion.evalₐ m (n + 1)).toRingHom)
            (AdicCompletion.surjective_evalₐ m (n + 1)) hxmap
        rcases hximage with ⟨a, ha, h⟩
        exact ⟨a, ha, h⟩
      rcases hz with ⟨z, hz, hzx⟩
      let y : AdicCompletion m R := (x : AdicCompletion m R) - z
      have hy : y ∈ completionKernel m (n + 1) := by
        change AdicCompletion.evalₐ m (n + 1) y = 0
        simp [y, hzx]
      refine ⟨⟨y, hy⟩, ?_⟩
      change
        (Submodule.comap
            (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
            (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R))).mkQ
            ⟨y, completionKernel_succ_le m n hy⟩ =
          (Submodule.comap
            (completionKernel m n : Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
            (completionMaximalIdeal m ^ n : Submodule (AdicCompletion m R) (AdicCompletion m R))).mkQ x
      apply (Submodule.Quotient.eq _).2
      change ((x : AdicCompletion m R) - z) - (x : AdicCompletion m R) ∈
        completionMaximalIdeal m ^ n
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz

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
  refine ⟨?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    rw [completionKernelQuotientMap, Submodule.ker_mapQ]
    simp
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | _ a =>
        constructor
        · intro hzero
          have haK : a ∈ completionKernel m n := by
            change AdicCompletion.evalₐ m n a = 0
            simpa [completionQuotientToResidue] using hzero
          refine ⟨Submodule.Quotient.mk ⟨a, haK⟩, ?_⟩
          simp [completionKernelQuotientMap]
        · rintro ⟨b, hb⟩
          rw [← hb]
          induction b using Submodule.Quotient.induction_on with
          | _ x =>
              change (completionQuotientToResidue m n)
                  ((completionKernelQuotientMap m n)
                    (Submodule.Quotient.mk x)) = 0
              have hx0 : AdicCompletion.evalₐ m n (x : AdicCompletion m R) = 0 :=
                RingHom.mem_ker.mp x.property
              unfold completionKernelQuotientMap completionQuotientToResidue
              rw [Submodule.mapQ_apply]
              change AdicCompletion.evalₐ m n (x : AdicCompletion m R) = 0
              exact hx0
  · have hker : ∀ a : AdicCompletion m R, a ∈ completionMaximalIdeal m ^ n →
        AdicCompletion.evalₐ m n a = 0 := by
      intro a ha
      exact RingHom.mem_ker.mp (completionMaximalIdeal_pow_le_kernel m n ha)
    exact Ideal.Quotient.lift_surjective_of_surjective (completionMaximalIdeal m ^ n) hker
      (AdicCompletion.surjective_evalₐ m n)

/-- The inverse-limit/Mittag--Leffler criterion for completeness in the maximal-ideal topology. -/
theorem completion_is_completeAsCompletionModule_iff_kernel_eq_pow :
    completionIsCompleteAsCompletionModule m ↔
      ∀ n : ℕ, 1 ≤ n → completionKernel m n = completionMaximalIdeal m ^ n := by
  unfold completionIsCompleteAsCompletionModule
  have eval_zero_iff_val_zero (n : ℕ) (z : AdicCompletion m R) :
      AdicCompletion.evalₐ m n z = 0 ↔ z.val n = 0 := by
    constructor
    · intro hz
      have hfactor (k : ℕ) :
          Function.Injective
            (Ideal.Quotient.factor
              (show m ^ k • (⊤ : Ideal R) ≤ m ^ k by simp)) := by
        have heq : m ^ k • (⊤ : Ideal R) = m ^ k := by ext x; simp
        simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
          using Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
      have hz' : AdicCompletion.eval m R n z = 0 := by
        apply hfactor n
        calc
          Ideal.Quotient.factor
              (show m ^ n • (⊤ : Ideal R) ≤ m ^ n by simp)
              (AdicCompletion.eval m R n z) = AdicCompletion.evalₐ m n z :=
            AdicCompletion.factor_eval_eq_evalₐ m z (by simp)
          _ = 0 := hz
      rw [AdicCompletion.eval_apply] at hz'
      exact hz'
    · intro hz
      rw [← AdicCompletion.factor_eval_eq_evalₐ m z (by simp)]
      rw [AdicCompletion.eval_apply, hz]
      simp
  have hkernel_mono {i j : ℕ} (hij : i ≤ j) :
      completionKernel m j ≤ completionKernel m i := by
    intro z hz
    change AdicCompletion.evalₐ m i z = 0
    have hfactor (k : ℕ) :
        Function.Injective
          (Ideal.Quotient.factor
            (show m ^ k • (⊤ : Ideal R) ≤ m ^ k by simp)) := by
      have heq : m ^ k • (⊤ : Ideal R) = m ^ k := by ext x; simp
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
    have hz' : AdicCompletion.eval m R j z = 0 := by
      apply hfactor j
      calc
        Ideal.Quotient.factor
            (show m ^ j • (⊤ : Ideal R) ≤ m ^ j by simp)
            (AdicCompletion.eval m R j z) = AdicCompletion.evalₐ m j z :=
          AdicCompletion.factor_eval_eq_evalₐ m z (by simp)
        _ = 0 := hz
    have hi : AdicCompletion.eval m R i z = 0 := by
      calc
        AdicCompletion.eval m R i z = z.val i := AdicCompletion.eval_apply m R i z
        _ = AdicCompletion.transitionMap m R hij (z.val j) :=
          (AdicCompletion.transitionMap_comp_eval_apply m R hij z).symm
        _ = AdicCompletion.transitionMap m R hij
            (AdicCompletion.eval m R j z) := by
              rw [AdicCompletion.eval_apply]
        _ = 0 := by rw [hz']; simp
    calc
      AdicCompletion.evalₐ m i z =
          Ideal.Quotient.factor
            (show m ^ i • (⊤ : Ideal R) ≤ m ^ i by simp)
            (AdicCompletion.eval m R i z) :=
        (AdicCompletion.factor_eval_eq_evalₐ m z (by simp)).symm
      _ = 0 := by rw [hi]; simp
  constructor
  · intro hcomplete n hn
    apply le_antisymm
    · intro x hx
      classical
      let next : ∀ j : ℕ, completionKernel m (n + j) →
          completionKernel m (n + (j + 1)) := fun j z =>
        let w := Classical.choose
          (completionKernelTransition_surjective m (n + j)
            (Submodule.Quotient.mk z))
        ⟨w.1, by
          exact cast
            (congrArg (fun t => w.1 ∈ completionKernel m t)
              (Nat.add_assoc n j 1)) w.2⟩
      have next_spec (j : ℕ) (z : completionKernel m (n + j)) :
          completionKernelTransition m (n + j) (next j z) =
            Submodule.Quotient.mk z := by
        dsimp [next]
        simpa [Nat.add_assoc] using
          Classical.choose_spec
            (completionKernelTransition_surjective m (n + j)
              (Submodule.Quotient.mk z))
      let y : (j : ℕ) → completionKernel m (n + j) :=
        Nat.rec (motive := fun j => completionKernel m (n + j))
          ⟨x, hx⟩ (fun j z => next j z)
      have y_spec (j : ℕ) :
          completionKernelTransition m (n + j) (y (j + 1)) =
            Submodule.Quotient.mk (y j) := by
        simpa [y] using next_spec j (y j)
      have y_diff (j : ℕ) :
          ((y (j + 1)).1 : AdicCompletion m R) - (y j).1 ∈
            completionMaximalIdeal m ^ (n + j) := by
        have hq := y_spec j
        change
          (Submodule.comap
              (completionKernel m (n + j) :
                Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
              (completionMaximalIdeal m ^ (n + j) :
                Submodule (AdicCompletion m R) (AdicCompletion m R))).mkQ
              ⟨(y (j + 1)).1,
                completionKernel_succ_le m (n + j) (y (j + 1)).property⟩ =
            (Submodule.comap
              (completionKernel m (n + j) :
                Submodule (AdicCompletion m R) (AdicCompletion m R)).subtype
              (completionMaximalIdeal m ^ (n + j) :
                Submodule (AdicCompletion m R) (AdicCompletion m R))).mkQ (y j) at hq
        have hq' := (Submodule.Quotient.eq _).mp hq
        exact (Submodule.mem_comap.mp hq')
      have y_adj (r j : ℕ) (hr : r ≤ n + j) :
          (y j).1 ≡ (y (j + 1)).1
            [SMOD (completionMaximalIdeal m ^ r •
              (⊤ : Submodule (AdicCompletion m R) (AdicCompletion m R)))] := by
        apply SModEq.sub_mem.mpr
        have hpow : completionMaximalIdeal m ^ (n + j) ≤
            completionMaximalIdeal m ^ r :=
          Ideal.pow_le_pow_right hr
        have hmem := (completionMaximalIdeal m ^ (n + j)).neg_mem (y_diff j)
        have hmem' := hpow hmem
        simpa [smul_eq_mul, Ideal.mul_top] using hmem'
      have y_chain (r j : ℕ) (hr : r ≤ n) :
          (y 0).1 ≡ (y j).1
            [SMOD (completionMaximalIdeal m ^ r •
              (⊤ : Submodule (AdicCompletion m R) (AdicCompletion m R)))] := by
        induction j with
        | zero => exact SModEq.rfl
        | succ j ih =>
            exact ih.trans (y_adj r j (by omega))
      have y_cauchy : ∀ {i j : ℕ}, i ≤ j →
          (y i).1 ≡ (y j).1
            [SMOD (completionMaximalIdeal m ^ i •
              (⊤ : Submodule (AdicCompletion m R) (AdicCompletion m R)))] := by
        intro i j hij
        induction j, hij using Nat.le_induction with
        | base => exact SModEq.rfl
        | succ j hij ih =>
            exact ih.trans (y_adj i j (by omega))
      obtain ⟨L, hL⟩ := IsPrecomplete.prec hcomplete.toIsPrecomplete y_cauchy
      have hxL : (x : AdicCompletion m R) - L ∈ completionMaximalIdeal m ^ n := by
        have hzero := y_chain n n le_rfl
        have hconverge := hL n
        have hzero' : (y 0).1 - L ∈
            completionMaximalIdeal m ^ n := by
          have h1 := (SModEq.sub_mem.mp hzero)
          have h2 := (SModEq.sub_mem.mp hconverge)
          have h1' : (y 0).1 - (y n).1 ∈
              completionMaximalIdeal m ^ n := by
            simpa [smul_eq_mul, Ideal.mul_top] using h1
          have h2' : (y n).1 - L ∈
              completionMaximalIdeal m ^ n := by
            simpa [smul_eq_mul, Ideal.mul_top] using h2
          convert add_mem h1' h2' using 1; abel
        simpa [y] using hzero'
      have hL_kernel (k : ℕ) : L ∈ completionKernel m k := by
        have hconv := SModEq.sub_mem.mp (hL k)
        have hconv' : (y k).1 - L ∈
            completionMaximalIdeal m ^ k := by
          simpa [smul_eq_mul, Ideal.mul_top] using hconv
        have hyk : (y k).1 ∈ completionKernel m k := by
          exact hkernel_mono (by omega) (y k).property
        have hdiff : (y k).1 - L ∈ completionKernel m k := by
          exact completionMaximalIdeal_pow_le_kernel m k hconv'
        have := sub_mem hyk hdiff
        simpa only [sub_sub_cancel] using this
      have hLzero : L = 0 := by
        apply AdicCompletion.ext_evalₐ
        intro k
        exact hL_kernel k
      rw [hLzero, sub_zero] at hxL
      simpa [y] using hxL
    · exact completionMaximalIdeal_pow_le_kernel m n
  · intro hpow
    refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
    · intro z hz
      apply AdicCompletion.ext_evalₐ
      intro n
      have hk : z ∈ completionKernel m n := by
        cases n with
        | zero =>
            exact completionMaximalIdeal_pow_le_kernel m 0 (by simp)
        | succ n =>
            rw [hpow (n + 1) (by omega)]
            simpa [smul_eq_mul, Ideal.mul_top] using
              (SModEq.sub_mem.mp (hz (n + 1)))
      exact hk
    · intro f hf
      let L : AdicCompletion m R :=
        { val := fun n => (f n).val n
          property := by
            intro i j hij
            cases i with
            | zero =>
                have hsub : Subsingleton (R ⧸ (m ^ 0 • (⊤ : Ideal R))) := by
                  apply subsingleton_of_zero_eq_one
                  change Ideal.Quotient.mk (m ^ 0 • (⊤ : Ideal R)) 0 =
                    Ideal.Quotient.mk (m ^ 0 • (⊤ : Ideal R)) 1
                  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
                  simp
                exact @Subsingleton.elim _ hsub _ _
            | succ i =>
                have hmem : f (i + 1) - f j ∈ completionMaximalIdeal m ^ (i + 1) := by
                  simpa [smul_eq_mul, Ideal.mul_top] using
                    (SModEq.sub_mem.mp (hf hij))
                rw [← hpow (i + 1) (by omega)] at hmem
                have hval : (f (i + 1)).val (i + 1) = (f j).val (i + 1) := by
                  have hz : AdicCompletion.evalₐ m (i + 1) (f (i + 1) - f j) = 0 := hmem
                  have hv := (eval_zero_iff_val_zero (i + 1) (f (i + 1) - f j)).mp hz
                  exact sub_eq_zero.mp hv
                calc
                  AdicCompletion.transitionMap m R hij ((f j).val j) = (f j).val (i + 1) :=
                    AdicCompletion.transitionMap_comp_eval_apply m R hij (f j)
                  _ = (f (i + 1)).val (i + 1) := hval.symm }
      refine ⟨L, ?_⟩
      intro n
      apply SModEq.sub_mem.mpr
      cases n with
      | zero =>
          simp
      | succ n =>
          have hmem : f (n + 1) - L ∈ completionMaximalIdeal m ^ (n + 1) := by
            rw [← hpow (n + 1) (by omega)]
            change AdicCompletion.evalₐ m (n + 1) (f (n + 1) - L) = 0
            apply (eval_zero_iff_val_zero (n + 1) (f (n + 1) - L)).mpr
            change (f (n + 1)).val (n + 1) - (f (n + 1)).val (n + 1) = 0
            simp
          simpa [smul_eq_mul, Ideal.mul_top] using hmem

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
  have hker :
      RingHom.ker (MvPolynomial.constantCoeff : infinitePolynomialRing k →+* k) =
        infinitePolynomialMaximalIdeal k := by
    apply le_antisymm
    · intro p hp
      rw [RingHom.mem_ker] at hp
      change p ∈ MvPolynomial.idealOfVars ℕ k
      rw [MvPolynomial.idealOfVars, ← Set.image_univ]
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      have hm0 : m ≠ 0 := by
        intro h
        subst h
        exact (MvPolynomial.mem_support_iff.mp hm) hp
      have hm' : ∃ i, m i ≠ 0 := by
        by_contra h
        push Not at h
        apply hm0
        ext i
        exact h i
      obtain ⟨i, hi⟩ := hm'
      exact ⟨i, Set.mem_univ _, hi⟩
    · change MvPolynomial.idealOfVars ℕ k ≤ RingHom.ker
        (MvPolynomial.constantCoeff : infinitePolynomialRing k →+* k)
      rw [MvPolynomial.idealOfVars]
      apply Ideal.span_le.2
      rintro z ⟨i, rfl⟩
      simp [RingHom.mem_ker]
  have hsurj : Function.Surjective
      (MvPolynomial.constantCoeff : infinitePolynomialRing k →+* k) := by
    intro c
    exact ⟨MvPolynomial.C c, MvPolynomial.constantCoeff_C _ c⟩
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective
    (MvPolynomial.constantCoeff : infinitePolynomialRing k →+* k) hsurj

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
  rfl

/-- The series has zero constant term. -/
theorem infiniteVariableSeries_mem_completionMaximalIdeal :
    infiniteVariableSeries k ∈
      Formalization.Books.Examples.Unit07.completionMaximalIdeal
        (infinitePolynomialMaximalIdeal k) := by
  simp [completionMaximalIdeal, RingHom.mem_ker, infiniteVariableSeries,
    AdicCompletion.evalOneₐ, infiniteVariableSeriesPartial, infinitePolynomialMaximalIdeal]

/-- The series is not a finite `R`-linear combination of elements of the completion. -/
theorem infiniteVariableSeries_not_mem_extendedMaximalIdeal :
    infiniteVariableSeries k ∉
      (infinitePolynomialMaximalIdeal k).map
        (algebraMap (infinitePolynomialRing k)
          (AdicCompletion (infinitePolynomialMaximalIdeal k) (infinitePolynomialRing k))) := by
  classical
  intro h
  change infiniteVariableSeries k ∈
      Ideal.map
        (algebraMap (infinitePolynomialRing k)
          (AdicCompletion (infinitePolynomialMaximalIdeal k) (infinitePolynomialRing k)))
        (MvPolynomial.idealOfVars ℕ k) at h
  rw [MvPolynomial.idealOfVars, Ideal.map_span] at h
  obtain ⟨f, t, ht, hf, hsum⟩ :=
    (Submodule.mem_span_iff_exists_finset_subset.mp h)
  let index :
      AdicCompletion (infinitePolynomialMaximalIdeal k)
          (infinitePolynomialRing k) → ℕ :=
    fun a =>
      if ha : ∃ i : ℕ,
          algebraMap (infinitePolynomialRing k)
              (AdicCompletion (infinitePolynomialMaximalIdeal k)
                (infinitePolynomialRing k))
            (MvPolynomial.X i) = a then
        Classical.choose ha
      else 0
  have hindex (a : AdicCompletion (infinitePolynomialMaximalIdeal k)
      (infinitePolynomialRing k)) (ha : a ∈ t) :
      algebraMap (infinitePolynomialRing k)
          (AdicCompletion (infinitePolynomialMaximalIdeal k)
            (infinitePolynomialRing k))
        (MvPolynomial.X (index a)) = a := by
    have ha' : ∃ i : ℕ,
        algebraMap (infinitePolynomialRing k)
            (AdicCompletion (infinitePolynomialMaximalIdeal k)
              (infinitePolynomialRing k))
          (MvPolynomial.X i) = a := by
      rcases ht ha with ⟨p, ⟨i, rfl⟩, hpa⟩
      exact ⟨i, hpa⟩
    dsimp [index]
    rw [dif_pos ha']
    exact Classical.choose_spec ha'
  let u : Finset ℕ := t.image index
  let j : ℕ := u.sup id + 1
  have hindex_lt (a : AdicCompletion (infinitePolynomialMaximalIdeal k)
      (infinitePolynomialRing k)) (ha : a ∈ t) : index a < j := by
    have hua : index a ∈ u := Finset.mem_image.2 ⟨a, ha, rfl⟩
    dsimp [j]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hua)
  let q :
      AdicCompletion (infinitePolynomialMaximalIdeal k)
          (infinitePolynomialRing k) → infinitePolynomialRing k :=
    fun x => Classical.choose
      (Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2) x))
  have hq (x : AdicCompletion (infinitePolynomialMaximalIdeal k)
      (infinitePolynomialRing k)) :
      Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2)) (q x) =
        AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2) x := by
    exact Classical.choose_spec
      (Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2) x))
  have hgen (i : ℕ) :
      AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)
          (algebraMap (infinitePolynomialRing k)
            (AdicCompletion (infinitePolynomialMaximalIdeal k)
              (infinitePolynomialRing k))
            (MvPolynomial.X i)) =
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (MvPolynomial.X i) := by
    rfl
  have heval := congrArg
    (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) hsum
  simp only [smul_eq_mul, map_sum, map_mul] at heval
  rw [infiniteVariableSeries_coordinate] at heval
  have ha_eval (a : AdicCompletion (infinitePolynomialMaximalIdeal k)
      (infinitePolynomialRing k)) (ha : a ∈ t) :
      (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) a =
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (MvPolynomial.X (index a)) := by
    calc
      (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) a =
          (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2))
            ((algebraMap (infinitePolynomialRing k)
              (AdicCompletion (infinitePolynomialMaximalIdeal k)
                (infinitePolynomialRing k)))
              (MvPolynomial.X (index a))) := by
                rw [hindex a ha]
      _ = Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (MvPolynomial.X (index a)) := hgen _
  have hterm (a : AdicCompletion (infinitePolynomialMaximalIdeal k)
      (infinitePolynomialRing k)) (ha : a ∈ t) :
      (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) (f a) *
          (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) a =
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (q (f a) * MvPolynomial.X (index a)) := by
    calc
      (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) (f a) *
          (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) a =
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2)) (q (f a)) *
          (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) a := by
            rw [hq]
      _ = Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2)) (q (f a)) *
          Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
            (MvPolynomial.X (index a)) := by
            rw [ha_eval a ha]
      _ = Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (q (f a) * MvPolynomial.X (index a)) := by
            rw [map_mul]
  have heval' :
      (∑ a ∈ t,
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (q (f a) * MvPolynomial.X (index a))) =
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (infiniteVariableSeriesPartial k (j + 2)) := by
    calc
      (∑ a ∈ t,
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (q (f a) * MvPolynomial.X (index a))) =
        ∑ a ∈ t,
          (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) (f a) *
            (AdicCompletion.evalₐ (infinitePolynomialMaximalIdeal k) (j + 2)) a := by
              apply Finset.sum_congr rfl
              intro a ha
              exact (hterm a ha).symm
      _ = Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (infiniteVariableSeriesPartial k (j + 2)) := heval
  have hmk :
      Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (∑ a ∈ t, q (f a) * MvPolynomial.X (index a)) =
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (infiniteVariableSeriesPartial k (j + 2)) := by
    rw [map_sum]
    exact heval'
  have hmk' :
      Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (infiniteVariableSeriesPartial k (j + 2)) =
        Ideal.Quotient.mk (infinitePolynomialMaximalIdeal k ^ (j + 2))
          (∑ a ∈ t, q (f a) * MvPolynomial.X (index a)) :=
    hmk.symm
  have hmem :
      infiniteVariableSeriesPartial k (j + 2) -
          ∑ a ∈ t, q (f a) * MvPolynomial.X (index a) ∈
        infinitePolynomialMaximalIdeal k ^ (j + 2) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hmk'
    exact hmk'
  let d : ℕ →₀ ℕ := Finsupp.single j (j + 1)
  have hd : Finsupp.degree d < j + 2 := by
    simp [d]
  have hcoeff_mem :
      (infiniteVariableSeriesPartial k (j + 2) -
          ∑ a ∈ t, q (f a) * MvPolynomial.X (index a)).coeff d = 0 :=
    (MvPolynomial.mem_pow_idealOfVars_iff' (j + 2) _).mp hmem d hd
  have hterm_coeff (a : AdicCompletion (infinitePolynomialMaximalIdeal k)
      (infinitePolynomialRing k)) (ha : a ∈ t) :
      (q (f a) * MvPolynomial.X (index a)).coeff d = 0 := by
    rw [MvPolynomial.coeff_mul_X']
    have hne : index a ≠ j := Nat.ne_of_lt (hindex_lt a ha)
    simp [d, hne]
  have hsum_coeff :
      (∑ a ∈ t, q (f a) * MvPolynomial.X (index a)).coeff d = 0 := by
    rw [MvPolynomial.coeff_sum]
    exact Finset.sum_eq_zero (fun a ha => hterm_coeff a ha)
  have hpartial :
      (infiniteVariableSeriesPartial k (j + 2)).coeff d = 1 := by
    rw [infiniteVariableSeriesPartial, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single j]
    · simp [MvPolynomial.coeff_X_pow, d]
    · intro i hi hij
      rw [MvPolynomial.coeff_X_pow]
      simp only [d]
      split_ifs with heq
      · have heq' := congrArg (fun p : ℕ →₀ ℕ => p i) heq
        have : False := by
          simp [hij] at heq'
        exact this.elim
      · rfl
    · intro hj
      exfalso
      apply hj
      exact Finset.mem_range.mpr (by omega)
  rw [MvPolynomial.coeff_sub, hpartial, hsum_coeff] at hcoeff_mem
  rw [sub_zero] at hcoeff_mem
  exact one_ne_zero hcoeff_mem

theorem infinitePolynomial_maximalIdeal_not_extended :
    ¬ Formalization.Books.Examples.Unit07.maximalIdealIsExtended
        (infinitePolynomialMaximalIdeal k) := by
  sorry

/-- The series lies in `K₁`. -/
theorem infiniteVariableSeries_mem_completionKernel_one :
    infiniteVariableSeries k ∈
      Formalization.Books.Examples.Unit07.completionKernel
        (infinitePolynomialMaximalIdeal k) 1 := by
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
    (n d : ℕ) (hn : 0 < n) (hd : (d : k) ≠ 0) (hd_gt : 1 < d) :
    ∃ x : PrimeSpectrum (MvPolynomial (Fin n) k),
      PrimeSpectrum.zeroLocus (polynomialDerivativeIdeal k (powerSumPolynomial k n d)) = {x} := by
  sorry

theorem finiteProductSum_derivative_mem_factorIdeal
    {n t : ℕ} (f g : Fin t → MvPowerSeries (Fin n) k) (i : Fin n) :
    MvPowerSeries.pderiv k i (∑ j, f j * g j) ∈ powerSeriesFactorIdeal k f g := by
  sorry

theorem finiteProductSum_factor_locus_dimension
    {n t : ℕ} (f g : Fin t → MvPowerSeries (Fin n) k)
    (hzero : ∀ i, MvPowerSeries.constantCoeff (f i) = 0 ∧
      MvPowerSeries.constantCoeff (g i) = 0) :
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
