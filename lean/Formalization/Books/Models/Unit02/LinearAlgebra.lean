import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Int.Basic

/-!
# Linear algebra

Formal statements from Chapter 2 of *Semistable Reduction*.
-/

noncomputable section

namespace Formalization.Books.Models.Unit02

open scoped BigOperators

/-! The off-diagonal norm appearing in the two diagonal-dominance criteria. -/
def offDiagonalNormSum {n : ℕ} {α : Type*} [Norm α]
    (A : Matrix (Fin n) (Fin n) α) (i : Fin n) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun j => if j ≠ i then norm (A i j) else 0)

/-! Strict diagonal dominance implies nonsingularity. -/
theorem recurring_diagonal_dominance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hdominant : ∀ i, norm (A i i) > offDiagonalNormSum A i) :
    Matrix.det A ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hsum :
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖A i j‖) =
        (Finset.univ : Finset (Fin n)).sum
          (fun j => if j ≠ i then ‖A i j‖ else 0) := by
    rw [show (Finset.univ : Finset (Fin n)).erase i =
        (Finset.univ : Finset (Fin n)).filter (fun j => j ≠ i) by
      ext j
      simp]
    rw [Finset.sum_filter]
  exact hsum ▸ hdominant i

/-! The column-weighted matrix used in the proof of weighted diagonal dominance. -/
def weightedComplexMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (m : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A i j * (m j : ℂ)

/-! Determinant scaling for the weighted matrix. -/
theorem weightedComplexMatrix_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (m : Fin n → ℝ) :
    Matrix.det (weightedComplexMatrix A m) =
      (Finset.univ : Finset (Fin n)).prod (fun i => (m i : ℂ)) * Matrix.det A := by
  classical
  rw [show weightedComplexMatrix A m = A * Matrix.diagonal (fun j => (m j : ℂ)) by
    ext i j
    simp [weightedComplexMatrix, Matrix.mul_apply, Matrix.diagonal]]
  rw [Matrix.det_mul, Matrix.det_diagonal]
  exact (mul_comm (Matrix.det A)
    ((Finset.univ : Finset (Fin n)).prod (fun i => (m i : ℂ))))

/-! The weighted strict diagonal-dominance criterion. -/
theorem recurring_weighted_diagonal_dominance {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (m : Fin n → ℝ)
    (_hm : ∀ i, 0 < m i)
    (hdominant : ∀ i,
      norm (A i i * (m i : ℂ)) >
          (Finset.univ : Finset (Fin n)).sum
          (fun j => if j ≠ i then norm (A i j * (m j : ℂ)) else 0)) :
    Matrix.det A ≠ 0 := by
  intro hA
  apply (recurring_diagonal_dominance (weightedComplexMatrix A m) (by
    intro i
    simpa [offDiagonalNormSum, weightedComplexMatrix] using hdominant i))
  rw [weightedComplexMatrix_det, hA, mul_zero]

/-! The vector obtained by retaining the coordinates in a subset and weighting them by `m`. -/
def weightedSubsetVector {n : ℕ} (m : Fin n → ℝ) (I : Set (Fin n)) : Fin n → ℝ :=
  by
    classical
    exact fun i => if i ∈ I then m i else 0

/-! The equality condition for the real recurring-matrix lemma. -/
def kernelIndicatorCondition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n → ℝ) (I : Set (Fin n)) : Prop :=
  (∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) ∧
    ∀ i, i ∈ I →
      -A i i * m i =
        (Finset.univ : Finset (Fin n)).sum (fun j => if j ≠ i then A i j * m j else 0)

/-!
The kernel of a symmetric real recurring matrix is spanned by the equality
indicators. Symmetry is needed here: the one-sided cut condition from the
source does not by itself make an indicator vector a right-kernel vector.
-/
theorem recurring_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hm : ∀ i, 0 < m i)
    (hineq : ∀ i,
      -A i i * m i ≥
        (Finset.univ : Finset (Fin n)).sum (fun j => if j ≠ i then A i j * m j else 0)) :
    LinearMap.ker (Matrix.toLin' A) =
      Submodule.span ℝ {x : Fin n → ℝ |
        ∃ I : Set (Fin n), kernelIndicatorCondition A m I ∧
          x = weightedSubsetVector m I} := by
  classical
  let S : Set (Fin n → ℝ) := {x |
    ∃ I : Set (Fin n), kernelIndicatorCondition A m I ∧
      x = weightedSubsetVector m I}
  have hgen : ∀ I : Set (Fin n), kernelIndicatorCondition A m I →
      Matrix.toLin' A (weightedSubsetVector m I) = 0 := by
    intro I hI
    funext i
    change (∑ j, A i j * weightedSubsetVector m I j) = 0
    by_cases hi : i ∈ I
    · have hcut (j : Fin n) (hj : j ∉ I) : A i j = 0 := hI.1 hi hj
      have hsum :
          (∑ j, A i j * weightedSubsetVector m I j) =
            A i i * m i +
              ∑ j, if j ≠ i then A i j * m j else 0 := by
        have hsplit :
            (∑ j, A i j * weightedSubsetVector m I j) =
              ∑ j, (if j = i then A i j * m j else
                if j ≠ i then A i j * m j else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hje : j = i
          · subst j
            simp [weightedSubsetVector, hi]
          · by_cases hji : j ∈ I
            · simp [weightedSubsetVector, hji, hje]
            · simp [weightedSubsetVector, hji, hje, hcut j hji]
        rw [hsplit]
        calc
          (∑ j, (if j = i then A i j * m j else
              if j ≠ i then A i j * m j else 0)) =
              ∑ j, ((if j = i then A i j * m j else 0) +
                (if j ≠ i then A i j * m j else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i <;> simp [hji]
          _ = A i i * m i +
              ∑ j, if j ≠ i then A i j * m j else 0 := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hsum]
      linarith [hI.2 i hi]
    · have hzero (j : Fin n) (hj : j ∈ I) : A i j = 0 := by
        rw [hsymm i j]
        exact hI.1 hj hi
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hji : j ∈ I
      · simp [weightedSubsetVector, hji, hzero j hji]
      · simp [weightedSubsetVector, hji]
  have hspan : Submodule.span ℝ S ≤ LinearMap.ker (Matrix.toLin' A) := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨I, hI, rfl⟩
    change Matrix.toLin' A (weightedSubsetVector m I) = 0
    exact hgen I hI
  have hind : ∀ k : ℕ, ∀ x : Fin n → ℝ,
      (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ k →
      x ∈ LinearMap.ker (Matrix.toLin' A) → x ∈ Submodule.span ℝ S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxcard hxker
      by_cases hx0 : x = 0
      · subst x
        exact (Submodule.span ℝ S).zero_mem
      · let z : Fin n → ℝ := fun i => x i / m i
        let T : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)
        have hT : T.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hTempty
          apply hx0
          funext i
          have hi0 : x i = 0 := by
            by_contra hi
            have hiT : i ∈ T := by simp [T, hi]
            rw [hTempty] at hiT
            simpa using hiT
          exact hi0
        obtain ⟨r, hr, hrmax⟩ := Finset.exists_max_image T (fun i => |z i|) hT
        have hrx : x r ≠ 0 := by simpa [T] using (Finset.mem_filter.mp hr).2
        have hrz : z r ≠ 0 := by
          dsimp [z]
          exact div_ne_zero hrx (ne_of_gt (hm r))
        let y : Fin n → ℝ := if 0 < z r then x else -x
        let w : Fin n → ℝ := if 0 < z r then z else -z
        have hp : 0 < z r ∨ z r < 0 := lt_or_gt_of_ne hrz.symm
        have hwpos : 0 < w r := by
          rcases hp with hp | hp
          · simp [w, hp]
          · simp [w, hp, not_lt.mpr (le_of_lt hp)]
        have hmax (i : Fin n) : w i ≤ w r := by
          by_cases hiT : i ∈ T
          · have hi' := hrmax i hiT
            have hiabs := hrmax i hiT
            rcases hp with hp | hp
            · have hzi : z i ≤ |z i| := le_abs_self _
              simpa [w, hp] using (hzi.trans hiabs).trans_eq (abs_of_pos hp)
            · have hzi : -z i ≤ |z i| := neg_le_abs _
              have hzr : |z r| = -z r := abs_of_neg hp
              have : -z i ≤ -z r := (hzi.trans hiabs).trans_eq hzr
              simpa [w, hp, not_lt.mpr (le_of_lt hp)] using this
          · have hxi : x i = 0 := by
              by_contra hxi
              exact hiT (by simp [T, hxi])
            rcases hp with hp | hp
            · have : z i = 0 := by simp [z, hxi]
              simpa [w, hp, this] using (le_of_lt hp)
            · have : z i = 0 := by simp [z, hxi]
              simpa [w, hp, not_lt.mpr (le_of_lt hp), this] using hp.le
        have hyker : y ∈ LinearMap.ker (Matrix.toLin' A) := by
          rw [LinearMap.mem_ker] at hxker ⊢
          rcases hp with hp | hp
          · simpa [y, hp] using hxker
          · have hfx : (Matrix.toLin' A) (-x) = 0 := by
              rw [map_neg, LinearMap.mem_ker.mp hxker, neg_zero]
            simpa [y, hp, not_lt.mpr (le_of_lt hp)] using hfx
        let I : Set (Fin n) := {i | w i = w r}
        have hrI : r ∈ I := by
          dsimp [I]
        have hyw (i : Fin n) : y i = w i * m i := by
          by_cases hp' : 0 < z r
          · simp [y, w, hp', z]
            field_simp [ne_of_gt (hm i)]
          · simp [y, w, hp', z]
            field_simp [ne_of_gt (hm i)]
        have hrow (i : Fin n) (hi : i ∈ I) :
            -A i i * m i =
              (Finset.univ : Finset (Fin n)).sum
                (fun j => if j ≠ i then A i j * m j else 0) := by
          have hki := congrFun (LinearMap.mem_ker.mp hyker) i
          change (∑ j, A i j * y j) = 0 at hki
          have hsplit :
              ∑ j, A i j * y j = A i i * y i +
                ∑ j, if j ≠ i then A i j * y j else 0 := by
            have hsplit' :
                (∑ j, A i j * y j) =
                  ∑ j, (if j = i then A i j * y j else
                    if j ≠ i then A i j * y j else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hji : j = i <;> simp [hji]
            rw [hsplit']
            calc
              (∑ j, (if j = i then A i j * y j else
                  if j ≠ i then A i j * y j else 0)) =
                  ∑ j, ((if j = i then A i j * y j else 0) +
                    (if j ≠ i then A i j * y j else 0)) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j = i <;> simp [hji]
              _ = A i i * y i +
                  ∑ j, if j ≠ i then A i j * y j else 0 := by
                rw [Finset.sum_add_distrib]
                simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          have hle :
              (∑ j, if j ≠ i then A i j * m j else 0) ≤ -A i i * m i :=
            hineq i
          have hterm (j : Fin n) :
              A i j * m j * (w r - w j) ≥ 0 := by
            by_cases hji : j = i
            · have hi_eq : w i = w r := hi
              simp [hji, hi_eq]
            · have haj : 0 ≤ A i j * m j :=
                mul_nonneg (hoffdiag (Ne.symm hji)) (le_of_lt (hm j))
              have hwj := hmax j
              exact mul_nonneg haj (sub_nonneg.mpr hwj)
          have hsumle :
              (∑ j, if j ≠ i then A i j * m j * w j else 0) ≤
                w r * ∑ j, if j ≠ i then A i j * m j else 0 := by
            calc
              (∑ j, if j ≠ i then A i j * m j * w j else 0) ≤
                  ∑ j, if j ≠ i then w r * (A i j * m j) else 0 := by
                apply Finset.sum_le_sum
                intro j hj
                by_cases hji : j = i
                · simp [hji]
                · have ht := hterm j
                  simp [hji]
                  nlinarith
              _ = w r * ∑ j, if j ≠ i then A i j * m j else 0 := by
                simp [Finset.mul_sum, mul_ite]
          have hyi : y i = w r * m i := by
            rw [hyw i]
            exact congrArg (fun t => t * m i) hi
          have hkeq :
              -A i i * (w r * m i) =
                ∑ j, if j ≠ i then A i j * m j * w j else 0 := by
            have hki' : -A i i * y i =
                ∑ j, if j ≠ i then A i j * y j else 0 := by
              linarith [hki, hsplit]
            calc
              -A i i * (w r * m i) = -A i i * y i := by rw [hyi]
              _ = ∑ j, if j ≠ i then A i j * y j else 0 := hki'
              _ = ∑ j, if j ≠ i then A i j * m j * w j else 0 := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j = i
                · simp [hji]
                · rw [hyw j]
                  ring
          have hpos : 0 < w r := hwpos
          nlinarith
        have hcut (i : Fin n) (hi : i ∈ I) (j : Fin n) (hj : j ∉ I) :
            A i j = 0 := by
          have hji : i ≠ j := by
            intro hij
            apply hj
            simpa [hij] using hi
          have hcoef : 0 ≤ A i j * m j :=
            mul_nonneg (hoffdiag hji) (le_of_lt (hm j))
          have hne : w j ≠ w r := by
            intro h
            apply hj
            simpa [I] using h
          have hstrict' : w j < w r := lt_of_le_of_ne (hmax j) hne
          have hi_eq : w i = w r := hi
          have hstrict : w j < w i := by rw [hi_eq]; exact hstrict'
          have hki := congrFun (LinearMap.mem_ker.mp hyker) i
          change (∑ t, A i t * y t) = 0 at hki
          have hsplit :
              ∑ t, A i t * y t = A i i * y i +
                ∑ t, if t ≠ i then A i t * y t else 0 := by
            have hsplit' :
                (∑ t, A i t * y t) =
                  ∑ t, (if t = i then A i t * y t else
                    if t ≠ i then A i t * y t else 0) := by
              apply Finset.sum_congr rfl
              intro t ht
              by_cases hti : t = i <;> simp [hti]
            rw [hsplit']
            calc
              (∑ t, (if t = i then A i t * y t else
                  if t ≠ i then A i t * y t else 0)) =
                  ∑ t, ((if t = i then A i t * y t else 0) +
                    (if t ≠ i then A i t * y t else 0)) := by
                apply Finset.sum_congr rfl
                intro t ht
                by_cases hti : t = i <;> simp [hti]
              _ = A i i * y i +
                  ∑ t, if t ≠ i then A i t * y t else 0 := by
                rw [Finset.sum_add_distrib]
                simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          have hsumle :
              (∑ t, if t ≠ i then A i t * m t * w t else 0) ≤
                w i * ∑ t, if t ≠ i then A i t * m t else 0 := by
            calc
              (∑ t, if t ≠ i then A i t * m t * w t else 0) ≤
                  ∑ t, if t ≠ i then w i * (A i t * m t) else 0 := by
                apply Finset.sum_le_sum
                intro t ht
                by_cases hti : t = i
                · simp [hti]
                · have hcoef' : 0 ≤ A i t * m t :=
                    mul_nonneg (hoffdiag (Ne.symm hti)) (le_of_lt (hm t))
                  have htmax : w t ≤ w i := by rw [hi_eq]; exact hmax t
                  simp [hti]
                  nlinarith
              _ = w i * ∑ t, if t ≠ i then A i t * m t else 0 := by
                simp [Finset.mul_sum, mul_ite]
          have hkeq :
              -A i i * (w i * m i) =
                ∑ t, if t ≠ i then A i t * m t * w t else 0 := by
            have hki' : -A i i * y i =
                ∑ t, if t ≠ i then A i t * y t else 0 := by
              linarith [hki, hsplit]
            calc
              -A i i * (w i * m i) = -A i i * y i := by rw [hyw i]
              _ = ∑ t, if t ≠ i then A i t * y t else 0 := hki'
              _ = ∑ t, if t ≠ i then A i t * m t * w t else 0 := by
                apply Finset.sum_congr rfl
                intro t ht
                by_cases hti : t = i
                · simp [hti]
                · rw [hyw t]
                  ring
          have hrowi := hrow i hi
          have hi_eq : w i = w r := hi
          have hwposi : 0 < w i := by rw [hi_eq]; exact hwpos
          have hnonneg : 0 ≤ A i j * m j * (w i - w j) := by
            exact mul_nonneg hcoef (le_of_lt (sub_pos.mpr hstrict))
          have hsumzero :
              (∑ t, if t ≠ i then A i t * m t * (w i - w t) else 0) = 0 := by
            have hid :
                (∑ t, if t ≠ i then A i t * m t * (w i - w t) else 0) =
                  w i * (∑ t, if t ≠ i then A i t * m t else 0) -
                    ∑ t, if t ≠ i then A i t * m t * w t else 0 := by
              calc
                (∑ t, if t ≠ i then A i t * m t * (w i - w t) else 0) =
                    ∑ t, if t ≠ i then
                      (w i * (A i t * m t) - A i t * m t * w t) else 0 := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  by_cases hti : t = i <;> simp [hti] <;> ring
                _ = (∑ t, if t ≠ i then w i * (A i t * m t) else 0) -
                    ∑ t, if t ≠ i then A i t * m t * w t else 0 := by
                  have hsplit'' :
                      (∑ t, if t ≠ i then
                        (w i * (A i t * m t) - A i t * m t * w t) else 0) =
                        ∑ t, ((if t ≠ i then w i * (A i t * m t) else 0) -
                          (if t ≠ i then A i t * m t * w t else 0)) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    by_cases hti : t = i <;> simp [hti]
                  rw [hsplit'', Finset.sum_sub_distrib]
                _ = w i * (∑ t, if t ≠ i then A i t * m t else 0) -
                    ∑ t, if t ≠ i then A i t * m t * w t else 0 := by
                  congr 1
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro t ht
                  by_cases hti : t = i <;> simp [hti]
            rw [hid]
            have hmul : w i * (∑ t, if t ≠ i then A i t * m t else 0) =
                -A i i * (w i * m i) := by
              rw [← hrowi]
              ring
            rw [hmul, hkeq]
            ring
          have htermzero : A i j * m j * (w i - w j) = 0 := by
            let f : Fin n → ℝ := fun t =>
              if t ≠ i then A i t * m t * (w i - w t) else 0
            have hf : ∀ t ∈ (Finset.univ : Finset (Fin n)), 0 ≤ f t := by
              intro t ht
              by_cases hti : t = i
              · simp [f, hti]
              · have hcoef' : 0 ≤ A i t * m t :=
                  mul_nonneg (hoffdiag (Ne.symm hti)) (le_of_lt (hm t))
                have htmax : w t ≤ w i := by rw [hi_eq]; exact hmax t
                simp [f, hti]
                exact mul_nonneg hcoef' (sub_nonneg.mpr htmax)
            have htermle : f j ≤ ∑ t, f t := by
              exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
                (f := f) hf (Finset.mem_univ j)
            have hsumf : (∑ t, f t) = 0 := by simpa [f] using hsumzero
            have hfj : f j = 0 := by
              have hnonnegj := hf j (Finset.mem_univ j)
              rw [hsumf] at htermle
              exact le_antisymm htermle hnonnegj
            have hjneq : j ≠ i := Ne.symm hji
            simpa [f, hjneq] using hfj
          have : A i j * m j = 0 := by
            nlinarith
          exact (mul_eq_zero.mp this).resolve_right (ne_of_gt (hm j))
        have hcond : kernelIndicatorCondition A m I := by
          unfold kernelIndicatorCondition
          exact ⟨by
            intro i j hi hj
            exact hcut i hi j hj, by
            intro i hi
            exact hrow i hi⟩
        have hgenmem : weightedSubsetVector m I ∈ Submodule.span ℝ S := by
          apply Submodule.subset_span
          change ∃ J : Set (Fin n), kernelIndicatorCondition A m J ∧
            weightedSubsetVector m I = weightedSubsetVector m J
          exact ⟨I, hcond, rfl⟩
        let c := w r
        let x' : Fin n → ℝ := y - c • weightedSubsetVector m I
        have hx'ker : x' ∈ LinearMap.ker (Matrix.toLin' A) := by
          change Matrix.toLin' A (y - c • weightedSubsetVector m I) = 0
          rw [map_sub, map_smul, LinearMap.mem_ker.mp hyker,
            hgen I hcond, smul_zero, sub_zero]
        have hsupport :
            (Finset.univ.filter (fun i => x' i ≠ 0)).card <
              (Finset.univ.filter (fun i => x i ≠ 0)).card := by
          let T' := Finset.univ.filter (fun i => x' i ≠ 0)
          let T := Finset.univ.filter (fun i => x i ≠ 0)
          have hsub : T' ⊆ T := by
            intro i hi'
            have hxi : x i ≠ 0 := by
              intro hxi
              have hy0 : y i = 0 := by
                by_cases hp' : 0 < z r
                · simp [y, hp', hxi]
                · simp [y, hp', hxi]
              by_cases hiI : i ∈ I
              · have hwi : w i = w r := hiI
                have hrel := hyw i
                rw [hy0, hwi] at hrel
                have : w r = 0 := by
                  nlinarith [hrel, hm i]
                exact (ne_of_gt hwpos this).elim
              · have hx'i : x' i = 0 := by
                  dsimp [x', c]
                  simp [weightedSubsetVector, hiI, hy0]
                exact (Finset.mem_filter.mp hi').2 hx'i
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩
          have hrnot : r ∉ T' := by
            intro hr'
            have hrzero : x' r = 0 := by
              dsimp [x', c]
              rw [hyw r]
              simp [weightedSubsetVector, hrI]
            exact (Finset.mem_filter.mp hr').2 hrzero
          have hss : T' ⊂ T := by
            rw [Finset.ssubset_iff_subset_ne]
            exact ⟨hsub, by
              intro heq
              exact hrnot (heq ▸ Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, by simpa [T] using hrx⟩)⟩
          simpa [T', T] using Finset.card_lt_card hss
        have hlt : (Finset.univ.filter (fun i => x' i ≠ 0)).card < k :=
          lt_of_lt_of_le hsupport hxcard
        have hx'mem := ih _ hlt x' le_rfl hx'ker
        have hyspan : y ∈ Submodule.span ℝ S := by
          dsimp [x'] at hx'mem
          have := add_mem hx'mem (Submodule.smul_mem _ c hgenmem)
          simpa [sub_eq_add_neg] using this
        rcases hp with hp | hp
        · simpa [y, hp] using hyspan
        · have hnegspan : -y ∈ Submodule.span ℝ S :=
            (Submodule.span ℝ S).neg_mem hyspan
          simpa [y, hp, not_lt.mpr (le_of_lt hp)] using hnegspan
  apply le_antisymm
  · intro x hx
    exact hind ((Finset.univ.filter (fun i => x i ≠ 0)).card) x le_rfl hx
  · simpa [S] using hspan

/-! The off-diagonal energy identity used after normalizing the positive vector to one. -/
def symmetricRealOffDiagonalEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ((Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin n))).sum
    (fun p => if p.1 ≠ p.2 then -A p.1 p.2 * (x p.2 - x p.1) ^ 2 else 0)

/-! A corrected source-facing form of the displayed quadratic-energy identity. -/
theorem recurring_symmetric_real_energy_identity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (hrowsum : ∀ i,
      A i i +
          (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then A i j else 0) = 0) :
    symmetricRealOffDiagonalEnergy A x =
      2 * ((Finset.univ : Finset (Fin n)).sum
        (fun i => x i * (Matrix.mulVec A x) i)) := by
  classical
  unfold symmetricRealOffDiagonalEnergy
  change (∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)),
    if p.1 ≠ p.2 then -A p.1 p.2 * (x p.2 - x p.1) ^ 2 else 0) =
    2 * ∑ i, x i * (A.mulVec x) i
  rw [Finset.sum_product]
  change (∑ i, ∑ j, if i ≠ j then -A i j * (x j - x i) ^ 2 else 0) =
    2 * ∑ i, x i * (A.mulVec x) i
  have hpoly (a b c : ℝ) :
      -a * (b - c) ^ 2 =
        -(a * (b * b)) + (a * (c * b) + a * (c * b)) -
          a * (c * c) := by
    simp [pow_two, sub_eq_add_neg, mul_add,
      mul_comm,
      add_assoc, add_comm, add_left_comm]
  have hsum (i : Fin n) : ∑ j, A i j = 0 := by
    calc
      ∑ j, A i j =
          ∑ j, ((if j = i then A i j else 0) +
            (if j ≠ i then A i j else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j = i <;> simp [h]
      _ = (∑ j, if j = i then A i j else 0) +
          ∑ j, if j ≠ i then A i j else 0 := by
        rw [Finset.sum_add_distrib]
      _ = A i i + ∑ j, if j ≠ i then A i j else 0 := by simp
      _ = 0 := hrowsum i
  have hdiag :
      (∑ i, ∑ j, if i ≠ j then -A i j * (x j - x i) ^ 2 else 0) =
        ∑ i, ∑ j, -A i j * (x j - x i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : i = j <;> simp [h]
  rw [hdiag]
  simp_rw [hpoly, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have hcol (j : Fin n) : ∑ i, A i j = 0 := by
    calc
      ∑ i, A i j = ∑ i, A j i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsymm i j
      _ = 0 := hsum j
  have hleft :
      ∑ i, ∑ j, A i j * (x j * x j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_mul, hcol j, zero_mul]
  have hright :
      ∑ i, ∑ j, A i j * (x i * x i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hsum i, zero_mul]
  have hcross :
      ∑ i, ∑ j, A i j * (x i * x j) =
        ∑ i, x i * ∑ j, A i j * x j := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      ∑ j, A i j * (x i * x j) =
          ∑ j, x i * (A i j * x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ac_rfl
      _ = x i * ∑ j, A i j * x j := by
        rw [Finset.mul_sum]
  simp only [Matrix.mulVec_apply_eq_sum]
  simp [hleft, hright, hcross, two_mul]

/-! A connected symmetric recurring matrix is negative semidefinite with one-dimensional nullspace. -/
theorem recurring_symmetric_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n → ℝ) (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hm : ∀ i, 0 < m i) (hAm : Matrix.mulVec A m = 0)
    (hconnected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) :
    ∀ x : Fin n → ℝ,
      ((Finset.univ : Finset (Fin n)).sum fun i => x i * (Matrix.mulVec A x) i) ≤ 0 ∧
        (((Finset.univ : Finset (Fin n)).sum fun i => x i * (Matrix.mulVec A x) i) = 0 ↔
          ∃ c : ℝ, x = c • m) := by
  classical
  intro x
  let C : Matrix (Fin n) (Fin n) ℝ := fun i j => A i j * m i * m j
  let y : Fin n → ℝ := fun i => x i / m i
  have hAm_row (i : Fin n) : (Finset.univ : Finset (Fin n)).sum (fun j => A i j * m j) = 0 := by
    have hi := congrFun hAm i
    simpa [Matrix.mulVec_apply_eq_sum] using hi
  have hsplitA (i : Fin n) :
      (Finset.univ : Finset (Fin n)).sum (fun j => A i j * m j) =
        A i i * m i +
          (Finset.univ : Finset (Fin n)).sum (fun j => if j ≠ i then A i j * m j else 0) := by
    calc
      (Finset.univ : Finset (Fin n)).sum (fun j => A i j * m j) =
          ∑ j, ((if j = i then A i j * m j else 0) +
            (if j ≠ i then A i j * m j else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j = i <;> simp [hji]
      _ = (∑ j, if j = i then A i j * m j else 0) +
          ∑ j, if j ≠ i then A i j * m j else 0 := by
        rw [Finset.sum_add_distrib]
      _ = A i i * m i + ∑ j, if j ≠ i then A i j * m j else 0 := by simp
  have hCsym : ∀ i j, C i j = C j i := by
    intro i j
    dsimp [C]
    rw [hsymm i j]
    ring
  have hCoff : ∀ ⦃i j : Fin n⦄, i ≠ j → 0 ≤ C i j := by
    intro i j hne
    dsimp [C]
    exact mul_nonneg (mul_nonneg (hoffdiag hne) (le_of_lt (hm i))) (le_of_lt (hm j))
  have hCrowsum (i : Fin n) :
      C i i + (Finset.univ : Finset (Fin n)).sum
        (fun j => if j ≠ i then C i j else 0) = 0 := by
    dsimp [C]
    calc
      A i i * m i * m i + (∑ j, if j ≠ i then A i j * m i * m j else 0) =
          A i i * m i * m i + m i *
            (∑ j, if j ≠ i then A i j * m j else 0) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j ≠ i <;> simp [hji] <;> ring
      _ = m i * (A i i * m i + (∑ j, if j ≠ i then A i j * m j else 0)) := by ring
      _ = 0 := by rw [← hsplitA i, hAm_row i, mul_zero]
  have hquad :
      (Finset.univ : Finset (Fin n)).sum (fun i => y i * (Matrix.mulVec C y) i) =
        (Finset.univ : Finset (Fin n)).sum (fun i => x i * (Matrix.mulVec A x) i) := by
    simp only [Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [C, y]
    field_simp [ne_of_gt (hm i), ne_of_gt (hm j)]
  have henergy := recurring_symmetric_real_energy_identity C y hCsym hCrowsum
  have henergy_nonpos : symmetricRealOffDiagonalEnergy C y ≤ 0 := by
    unfold symmetricRealOffDiagonalEnergy
    apply Finset.sum_nonpos
    intro p hp
    by_cases hne : p.1 ≠ p.2
    · simpa [hne] using
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hCoff hne))
          (sq_nonneg (y p.2 - y p.1)))
    · simp [hne]
  have hquad_nonpos :
      (Finset.univ : Finset (Fin n)).sum (fun i => x i * (Matrix.mulVec A x) i) ≤ 0 := by
    nlinarith [henergy, hquad, henergy_nonpos]
  refine ⟨hquad_nonpos, ?_⟩
  constructor
  · intro hxzero
    have hEzero : symmetricRealOffDiagonalEnergy C y = 0 := by
      nlinarith [henergy, hquad, hxzero]
    let F : (Fin n × Fin n) → ℝ := fun p =>
      if p.1 ≠ p.2 then C p.1 p.2 * (y p.2 - y p.1) ^ 2 else 0
    have hFsum :
        ((Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin n))).sum F = 0 := by
      have hneg : symmetricRealOffDiagonalEnergy C y = -
          ((Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin n))).sum F := by
        unfold symmetricRealOffDiagonalEnergy
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hne : p.1 ≠ p.2 <;> simp [F, hne] <;> ring
      rw [hneg] at hEzero
      linarith
    have hFnonneg (p : Fin n × Fin n) (hp : p ∈
        (Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin n))) : 0 ≤ F p := by
        by_cases hne : p.1 ≠ p.2
        · simpa [F, hne] using (mul_nonneg (hCoff hne)
            (sq_nonneg (y p.2 - y p.1)))
        · have heq : p.1 = p.2 := not_ne_iff.mp hne
          simp [F, hne, heq]
    have hFterm (i j : Fin n) : F (i, j) = 0 := by
      have hp : (i, j) ∈
          (Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin n)) := by
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
      have hle : F (i, j) ≤
          ((Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin n))).sum F := by
        exact Finset.single_le_sum (fun p hp => hFnonneg p hp) hp
      have hnonneg := hFnonneg (i, j) hp
      rw [hFsum] at hle
      exact le_antisymm hle hnonneg
    have hCdiff (i j : Fin n) (hne : i ≠ j) : C i j * (y j - y i) = 0 := by
      have hz : C i j * (y j - y i) ^ 2 = 0 := by
        simpa [F, hne] using hFterm i j
      rcases mul_eq_zero.mp hz with hc | hz
      · simp [hc]
      · have hd : y j - y i = 0 := by nlinarith [hz]
        simp [hd]
    have hdiffsum (i : Fin n) :
        (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j * (y j - y i) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hne : j ≠ i
      · simp [hne, hCdiff i j hne.symm]
      · simp [hne]
    have hdiffexpand (i : Fin n) :
        (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j * (y j - y i) else 0) =
          (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j * y j else 0) -
          y i * (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j else 0) := by
      calc
        (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j * (y j - y i) else 0) =
            ∑ j, ((if j ≠ i then C i j * y j else 0) -
              (if j ≠ i then C i j * y i else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hne : j ≠ i <;> simp [hne] <;> ring
        _ = (Finset.univ : Finset (Fin n)).sum
              (fun j => if j ≠ i then C i j * y j else 0) -
            (Finset.univ : Finset (Fin n)).sum
              (fun j => if j ≠ i then C i j * y i else 0) := by
          rw [Finset.sum_sub_distrib]
        _ = (Finset.univ : Finset (Fin n)).sum
              (fun j => if j ≠ i then C i j * y j else 0) -
            y i * (Finset.univ : Finset (Fin n)).sum
              (fun j => if j ≠ i then C i j else 0) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hne : j ≠ i <;> simp [hne] <;> ring
    have hdecomp (i : Fin n) :
        (Finset.univ : Finset (Fin n)).sum (fun j => C i j * y j) =
          (C i i + (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j else 0)) * y i +
            (Finset.univ : Finset (Fin n)).sum
              (fun j => if j ≠ i then C i j * (y j - y i) else 0) := by
      have hsplit :
          (Finset.univ : Finset (Fin n)).sum (fun j => C i j * y j) =
            C i i * y i + (Finset.univ : Finset (Fin n)).sum
              (fun j => if j ≠ i then C i j * y j else 0) := by
        calc
          (Finset.univ : Finset (Fin n)).sum (fun j => C i j * y j) =
              ∑ j, ((if j = i then C i j * y j else 0) +
                (if j ≠ i then C i j * y j else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i <;> simp [hji]
          _ = C i i * y i + ∑ j, if j ≠ i then C i j * y j else 0 := by
            rw [Finset.sum_add_distrib]
            simp
      have hmulsum : y i * (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j else 0) =
          (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j * y i else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hne : j ≠ i <;> simp [hne] <;> ring
      rw [hsplit, hdiffexpand]
      ring
    have hCy : Matrix.mulVec C y = 0 := by
      funext i
      change (Finset.univ : Finset (Fin n)).sum (fun j => C i j * y j) = 0
      rw [hdecomp i, hCrowsum i, hdiffsum i]
      simp
    have hCone : Matrix.mulVec C (fun _ => (1 : ℝ)) = 0 := by
      funext i
      change (Finset.univ : Finset (Fin n)).sum (fun j => C i j * 1) = 0
      have hsplit :
          (Finset.univ : Finset (Fin n)).sum (fun j => C i j * 1) =
            C i i + (Finset.univ : Finset (Fin n)).sum
              (fun j => if j ≠ i then C i j else 0) := by
        calc
          (Finset.univ : Finset (Fin n)).sum (fun j => C i j * 1) =
              (Finset.univ : Finset (Fin n)).sum (fun j => C i j) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp
          _ = C i i + (Finset.univ : Finset (Fin n)).sum
              (fun j => if j ≠ i then C i j else 0) := by
            calc
              (Finset.univ : Finset (Fin n)).sum (fun j => C i j) =
                  ∑ j, ((if j = i then C i j else 0) +
                    (if j ≠ i then C i j else 0)) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j = i <;> simp [hji]
              _ = C i i + ∑ j, if j ≠ i then C i j else 0 := by
                rw [Finset.sum_add_distrib]
                simp
      rw [hsplit, hCrowsum i]
    have hconnC : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
        ∀ ⦃i j⦄, i ∈ I → j ∉ I → C i j = 0 := by
      intro h
      apply hconnected
      rcases h with ⟨I, hI, hIu, hcut⟩
      refine ⟨I, hI, hIu, ?_⟩
      intro i j hi hj
      have hz := hcut hi hj
      dsimp [C] at hz
      rcases mul_eq_zero.mp hz with hz | hz
      · rcases mul_eq_zero.mp hz with hz | hz
        · exact hz
        · exact False.elim ((ne_of_gt (hm i)) hz)
      · exact False.elim ((ne_of_gt (hm j)) hz)
    have hineqC : ∀ i,
        -C i i * (1 : ℝ) ≥
          (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j * (1 : ℝ) else 0) := by
      intro i
      simpa only [mul_one] using (show -C i i ≥
          (Finset.univ : Finset (Fin n)).sum
            (fun j => if j ≠ i then C i j else 0) by
        nlinarith [hCrowsum i])
    have hkerC := recurring_real C (fun _ => (1 : ℝ)) hCsym hCoff
      (fun _ => one_pos) hineqC
    have hyker : y ∈ LinearMap.ker (Matrix.toLin' C) := by
      change Matrix.mulVec C y = 0
      exact hCy
    rw [hkerC] at hyker
    have hspanone :
        Submodule.span ℝ {v : Fin n → ℝ |
          ∃ I : Set (Fin n), kernelIndicatorCondition C (fun _ => (1 : ℝ)) I ∧
            v = weightedSubsetVector (fun _ => (1 : ℝ)) I} ≤
          Submodule.span ℝ ({(fun _ => (1 : ℝ))} : Set (Fin n → ℝ)) := by
      rw [Submodule.span_le]
      intro v hv
      rcases hv with ⟨I, hI, rfl⟩
      by_cases hIn : I.Nonempty
      · by_cases hIu : I = (Set.univ : Set (Fin n))
        · subst I
          have hw : weightedSubsetVector (fun _ : Fin n => (1 : ℝ))
              (Set.univ : Set (Fin n)) = (fun _ : Fin n => (1 : ℝ)) := by
            funext j
            simp [weightedSubsetVector]
          apply Submodule.subset_span
          rw [hw]
          exact Set.mem_singleton _
        · exfalso
          apply hconnC
          exact ⟨I, hIn, hIu, hI.1⟩
      · have hI0 : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hIn
        subst I
        have hw : weightedSubsetVector (fun _ : Fin n => (1 : ℝ)) (∅ : Set (Fin n)) = 0 := by
          funext j
          simp [weightedSubsetVector]
        rw [hw]
        exact (Submodule.span ℝ ({(fun _ => (1 : ℝ))} : Set (Fin n → ℝ))).zero_mem
    have hyone : y ∈ Submodule.span ℝ ({(fun _ => (1 : ℝ))} : Set (Fin n → ℝ)) :=
      hspanone hyker
    rcases (Submodule.mem_span_singleton.mp hyone) with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    funext i
    have hi := congrFun hc i
    dsimp [y] at hi
    dsimp
    field_simp [ne_of_gt (hm i)] at hi
    simpa using hi.symm
  · rintro ⟨c, rfl⟩
    simp [Matrix.mulVec_smul, hAm]

theorem recurring_symmetric_real_range_finrank {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hm : ∀ i, 0 < m i) (hAm : Matrix.mulVec A m = 0)
    (hconnected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = n - 1 := by
  classical
  cases n with
  | zero =>
    have hrange : LinearMap.range (Matrix.toLin' A) = ⊥ := by
      apply le_antisymm
      · intro v hv
        rcases hv with ⟨x, rfl⟩
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        simp
      · exact bot_le
    rw [hrange]
    simp
  | succ n =>
    have hquad := recurring_symmetric_real A m hsymm hoffdiag hm hAm hconnected
    have hker : LinearMap.ker (Matrix.toLin' A) =
        Submodule.span ℝ ({m} : Set (Fin (Nat.succ n) → ℝ)) := by
      apply le_antisymm
      · intro v hv
        have hvA : Matrix.mulVec A v = 0 := by
          have hv' := LinearMap.mem_ker.mp hv
          change Matrix.mulVec A v = 0 at hv'
          exact hv'
        have hvzero :
            (Finset.univ : Finset (Fin (Nat.succ n))).sum
                (fun i => v i * (Matrix.mulVec A v) i) = 0 := by
          simp [hvA]
        rcases (hquad v).2.mp hvzero with ⟨c, hc⟩
        rw [hc]
        exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
      · rw [Submodule.span_le]
        intro v hv
        have hv' : v = m := by simpa using hv
        rw [hv']
        change Matrix.mulVec A m = 0
        exact hAm
    have hm0 : m ≠ 0 := by
      intro hmzero
      have hi : Fin (Nat.succ n) := ⟨0, Nat.zero_lt_succ n⟩
      have hz := congrFun hmzero hi
      have hp := hm hi
      simp at hz
      linarith
    have hkerfin : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) = 1 := by
      rw [hker, finrank_span_singleton hm0]
    have hdim := (Matrix.toLin' A).finrank_range_add_finrank_ker
    have hdom : Module.finrank ℝ (Fin (Nat.succ n) → ℝ) = Nat.succ n := by
      simp [Module.finrank_pi_fintype]
    rw [hkerfin, hdom] at hdim
    omega

/-! Positive definite integral bilinear forms on lattices. -/
def IsPositiveDefiniteIntegralForm {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : LinearMap.BilinForm ℤ M) : Prop :=
  B.IsSymm ∧ ∀ x, x ≠ 0 → 0 < B x x

/-! Unimodularity of the map from a lattice to its integral dual. -/
def IsUnimodularIntegralForm {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : LinearMap.BilinForm ℤ M) : Prop :=
  ∃ e : M ≃ₗ[ℤ] M →ₗ[ℤ] ℤ, ∀ x y, e x y = B x y

/-! The dual quotient attached to a sublattice and an integral form. -/
def latticeDualEmbedding {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : LinearMap.BilinForm ℤ M) (N : Submodule ℤ M) :=
  B.restrict N

abbrev moduleCokernel {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) : Type _ :=
  N ⧸ LinearMap.range f

abbrev latticeDualQuotient {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : LinearMap.BilinForm ℤ M) (N : Submodule ℤ M) : Type _ :=
  letI : Module ℤ N := N.module
  moduleCokernel (latticeDualEmbedding B N)

abbrev latticeDiscriminantQuotient {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : LinearMap.BilinForm ℤ M) : Type _ :=
  moduleCokernel B

abbrev orthogonalDirectSumQuotient {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : LinearMap.BilinForm ℤ M) (N : Submodule ℤ M) : Type _ :=
  M ⧸ (N ⊔ B.orthogonal N)

/-! The projection exact sequence underlying the orthogonal decomposition. -/
theorem orthogonal_projection_sequence
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L]
    [Module.Finite ℤ L] (B : LinearMap.BilinForm ℤ L)
    (hB : IsPositiveDefiniteIntegralForm B) (A : Submodule ℤ L)
    (hquotient : Module.IsTorsionFree ℤ (L ⧸ A)) :
    ∃ p : L →ₗ[ℤ] Module.Dual ℤ (B.orthogonal A),
      ∃ q : latticeDiscriminantQuotient B →ₗ[ℤ] moduleCokernel p,
        (∀ (x : L) (y : B.orthogonal A), p x y = B x (y : L)) ∧
          A = LinearMap.ker p ∧
          Function.Exact p (LinearMap.range p).mkQ ∧
            Function.Surjective (LinearMap.range p).mkQ ∧
              Function.Surjective q := by
  classical
  let W : Submodule ℤ L := B.orthogonal A
  let p := B.domRestrict₂ W
  letI : Module ℤ (L ⧸ A) := Submodule.Quotient.module A
  letI : Module.IsTorsionFree ℤ (L ⧸ A) := by
    change @Module.IsTorsionFree ℤ (L ⧸ A) _ _ (Submodule.Quotient.module A)
    have hmod : (Submodule.Quotient.module A : Module ℤ (L ⧸ A)) =
        AddCommGroup.toIntModule (L ⧸ A) := Subsingleton.elim _ _
    rw [hmod]
    exact hquotient
  letI : IsScalarTower ℤ ℤ L :=
    ⟨fun a b x => by simpa only [smul_eq_mul] using (smul_smul a b x).symm⟩
  letI : Module.Finite ℤ (L ⧸ A) :=
    Module.Finite.of_surjective (A.mkQ : L →ₗ[ℤ] (L ⧸ A)) A.mkQ_surjective
  have hAfree : Module.Free ℤ (L ⧸ A) := by infer_instance
  have hAproj : Module.Projective ℤ (L ⧸ A) := inferInstance
  have hBker : LinearMap.ker B = ⊥ := by
    apply le_antisymm
    intro x hx
    by_contra hne
    have hpos := hB.2 x hne
    have hzero := DFunLike.congr_fun hx x
    have hzero' : B x x = 0 := by simpa using hzero
    linarith
    exact bot_le
  letI : Module ℤ (L ⧸ W) := Submodule.Quotient.module W
  have hWtf : Module.IsTorsionFree ℤ (L ⧸ W) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro k z hz
    rcases z with ⟨x⟩
    by_cases hk : k = 0
    · exact Or.inl hk
    right
    apply (Submodule.Quotient.mk_eq_zero W).2
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro a ha
    have hka : k • B a x = 0 := by
      have hxW : k • x ∈ W := by
        apply (Submodule.Quotient.mk_eq_zero W).1
        change W.mkQ (k • x) = 0
        rw [← Int.cast_smul_eq_zsmul ℤ]
        rw [W.mkQ.map_smul]
        exact hz
      have h := hxW a ha
      rw [← Int.cast_smul_eq_zsmul ℤ] at h
      exact ((B a).map_smul k x).symm.trans h
    exact (smul_eq_zero.mp hka).resolve_left (by simpa using hk)
  letI : Module.IsTorsionFree ℤ (L ⧸ W) := hWtf
  letI : Module.Finite ℤ (L ⧸ W) :=
    Module.Finite.of_surjective (W.mkQ : L →ₗ[ℤ] (L ⧸ W)) W.mkQ_surjective
  have hWfree : Module.Free ℤ (L ⧸ W) := by infer_instance
  have hWproj : Module.Projective ℤ (L ⧸ W) := inferInstance
  have hBsmul : ∀ φ : Module.Dual ℤ L, ∃ d : ℤ, d ≠ 0 ∧ ∃ y : L, d • φ = B y := by
    intro φ
    let b := Module.Free.chooseBasis ℤ L
    letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ L)
    let e := b.toDualEquiv
    let f := e.symm.toLinearMap.comp B
    have hfker : LinearMap.ker f = ⊥ := by
      apply le_antisymm
      · intro x hx
        have hfx : f x = 0 := LinearMap.mem_ker.mp hx
        have hBx : B x = 0 := by
          apply e.symm.injective
          simpa [f] using hfx
        have hx' : x ∈ LinearMap.ker B := LinearMap.mem_ker.mpr hBx
        rw [hBker] at hx'
        exact hx'
      · exact bot_le
    have hdet : LinearMap.det f ≠ 0 := by
      intro hzero
      have hne := (LinearMap.det_eq_zero_iff_ker_ne_bot).1 hzero
      exact hne hfker
    let c := Matrix.cramer (LinearMap.toMatrix b b f) (b.equivFun (e.symm φ))
    let y := b.equivFun.symm c
    have hfy : f y = (LinearMap.det f) • e.symm φ := by
      apply b.equivFun.injective
      ext i
      have hmatrix := LinearMap.toMatrix_mulVec_repr b b f y
      have hcramer := Matrix.mulVec_cramer (LinearMap.toMatrix b b f)
        (b.equivFun (e.symm φ))
      change Matrix.mulVec (LinearMap.toMatrix b b f) (b.equivFun y) =
        b.equivFun (f y) at hmatrix
      have hy : b.equivFun y = c := b.equivFun.apply_symm_apply c
      rw [hy] at hmatrix
      have hcramer_i := congrFun hcramer i
      calc
        b.equivFun (f y) i =
            Matrix.mulVec (LinearMap.toMatrix b b f) c i := congrFun hmatrix.symm i
        _ = (((LinearMap.toMatrix b b f).det • b.equivFun (e.symm φ)) i) :=
          hcramer_i
        _ = b.equivFun (LinearMap.det f • e.symm φ) i := by
          rw [← LinearMap.det_toMatrix b]
          simp
    refine ⟨LinearMap.det f, hdet, y, ?_⟩
    apply e.symm.injective
    rw [e.symm.map_smul]
    simpa only [Int.cast_id, ← Int.cast_smul_eq_zsmul ℤ] using hfy.symm.trans (by rfl)
  have hAle : A ≤ LinearMap.ker p := by
    sorry
    /- Attempted approach:
    intro a ha
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    have hy := (LinearMap.BilinForm.mem_orthogonal_iff.mp y.property) a ha
    simpa [p] using hy
    -/
  have hkerle : LinearMap.ker p ≤ A := by
    intro x hx
    by_contra hxA
    obtain ⟨φ, hφx, hφA⟩ :=
      A.exists_dual_map_eq_bot_of_notMem hxA hAproj
    obtain ⟨d, hd, y, hyd⟩ := hBsmul φ
    have hyW : y ∈ W := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro a ha
      have hφa_mem : φ a ∈ (⊥ : Submodule ℤ ℤ) := by
        rw [← hφA]
        exact ⟨a, ha, rfl⟩
      have hφa : φ a = 0 := (Submodule.mem_bot ℤ).mp hφa_mem
      have hyd_a := congrArg (fun g : Module.Dual ℤ L => g a) hyd
      have hBya : B y a = 0 := by
        simpa [smul_eq_mul, hφa] using hyd_a.symm
      rw [hB.1.eq]
      exact hBya
    let yW : W := ⟨y, hyW⟩
    have hpx := DFunLike.congr_fun (LinearMap.mem_ker.mp hx) yW
    have hBxy : B x y = 0 := by
      sorry
      /- Attempted approach:
      simpa [p, yW, LinearMap.BilinForm.domRestrict₂_apply] using hpx
      -/
    have hByx : B y x = 0 := by
      rw [hB.1.eq]
      exact hBxy
    have hyd_x := congrArg (fun g : Module.Dual ℤ L => g x) hyd
    have hnonzero : B y x ≠ 0 := by
      intro hzero
      have hz : d * φ x = 0 := by
        calc
          d * φ x = B y x := by simpa [smul_eq_mul] using hyd_x
          _ = 0 := hzero
      exact (mul_ne_zero hd hφx) hz
    exact hnonzero hByx
  have hker : A = LinearMap.ker p := le_antisymm hAle hkerle
  sorry

/-! The dual-lattice injections associated with an orthogonal decomposition. -/
theorem orthogonal_direct_sum
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L]
    [Module.Finite ℤ L] (B : LinearMap.BilinForm ℤ L)
    (hB : IsPositiveDefiniteIntegralForm B) (A : Submodule ℤ L)
    (hquotient : Module.IsTorsionFree ℤ (L ⧸ A)) :
    ∃ f : orthogonalDirectSumQuotient B A →ₗ[ℤ] latticeDualQuotient B A,
      ∃ g : orthogonalDirectSumQuotient B A →ₗ[ℤ]
          latticeDualQuotient B (B.orthogonal A),
        Function.Injective f ∧ Function.Injective g ∧
          (∃ q : latticeDiscriminantQuotient B →ₗ[ℤ] moduleCokernel f,
            Function.Surjective q) ∧
          (∃ q : latticeDualQuotient B A →ₗ[ℤ] moduleCokernel f,
            Function.Surjective q ∧ Function.Exact f q) ∧
          (∃ q : latticeDiscriminantQuotient B →ₗ[ℤ] moduleCokernel g,
            Function.Surjective q) ∧
          (∃ q : latticeDualQuotient B (B.orthogonal A) →ₗ[ℤ] moduleCokernel g,
            Function.Surjective q ∧ Function.Exact g q) := by
  sorry

/-! The torsion-cokernel identification for an adjoint pair with unimodular source. -/
theorem coker
    (L₀ L₁ : Type*) [AddCommGroup L₀] [Module ℤ L₀]
    [AddCommGroup L₁] [Module ℤ L₁] [Module.Free ℤ L₀] [Module.Finite ℤ L₀]
    [Module.Free ℤ L₁] [Module.Finite ℤ L₁]
    (B₀ : LinearMap.BilinForm ℤ L₀) (B₁ : LinearMap.BilinForm ℤ L₁)
    (d : L₀ →ₗ[ℤ] L₁) (dstar : L₁ →ₗ[ℤ] L₀)
    (hB₀ : IsPositiveDefiniteIntegralForm B₀)
    (hB₁ : IsPositiveDefiniteIntegralForm B₁)
    (hadj : LinearMap.IsAdjointPair B₀ B₁ d dstar)
    (hunimod : IsUnimodularIntegralForm B₀) :
    Nonempty
      (Submodule.torsion ℤ (moduleCokernel (dstar.comp d)) ≃ₗ[ℤ]
        latticeDualQuotient B₁ (LinearMap.range d)) := by
  sorry

/-! The cokernel of an integer matrix. -/
abbrev matrixCokernel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Type _ :=
  moduleCokernel (Matrix.toLin' A)

/-! The `ell`-torsion subgroup of a matrix cokernel. -/
def matrixPrimaryTorsion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (ell : ℕ) :
    AddSubgroup (matrixCokernel A) :=
  AddSubgroup.torsionBy (matrixCokernel A) (ell : ℤ)

def matrixPrimaryTorsionFinrank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (ell : ℕ)
    (hell : Nat.Prime ell) : ℕ :=
  letI : Fact (Nat.Prime ell) := ⟨hell⟩
  letI : NeZero ell := ⟨hell.ne_zero⟩
  letI : Module (ZMod ell) (matrixPrimaryTorsion A ell) :=
    AddSubgroup.torsionBy.zmodModule
  Module.finrank (ZMod ell) (matrixPrimaryTorsion A ell)

def weightedIntegerMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (m : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => m i * A i j * m j

theorem weightedIntegerMatrix_comp {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ) :
    (Matrix.toLin' (Matrix.diagonal m)).comp
        ((Matrix.toLin' A).comp (Matrix.toLin' (Matrix.diagonal m))) =
      Matrix.toLin' (weightedIntegerMatrix A m) := by
  apply LinearMap.ext
  intro x
  funext i
  change (Matrix.diagonal m).mulVec (A.mulVec ((Matrix.diagonal m).mulVec x)) i =
    (weightedIntegerMatrix A m).mulVec x i
  simp [weightedIntegerMatrix, Matrix.mulVec_apply_eq_sum, Matrix.mul_apply,
    Matrix.diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ac_rfl

theorem diagonal_matrix_primary_torsion_finrank_zero {n : ℕ}
    (m : Fin n → ℤ) (ell : ℕ) (hell : Nat.Prime ell)
    (hcoprime : ∀ i, Nat.Coprime ell (Int.natAbs (m i))) :
    matrixPrimaryTorsionFinrank (Matrix.diagonal m) ell hell = 0 := by
  classical
  unfold matrixPrimaryTorsionFinrank
  let _ : Fact (Nat.Prime ell) := ⟨hell⟩
  let _ : NeZero ell := ⟨hell.ne_zero⟩
  let _ : Module (ZMod ell) (matrixPrimaryTorsion (Matrix.diagonal m) ell) :=
    AddSubgroup.torsionBy.zmodModule
  let _ : Subsingleton (matrixPrimaryTorsion (Matrix.diagonal m) ell) := by
    constructor
    intro x y
    apply Subtype.ext
    have hzero (q : matrixCokernel (Matrix.diagonal m))
        (hq : q ∈ matrixPrimaryTorsion (Matrix.diagonal m) ell) : q = 0 := by
      revert hq
      refine Submodule.Quotient.induction_on
        (LinearMap.range (Matrix.toLin' (Matrix.diagonal m))) q
        (C := fun q => q ∈ matrixPrimaryTorsion (Matrix.diagonal m) ell → q = 0) ?_
      intro z hz
      change (ell : ℤ) • (Submodule.Quotient.mk z :
        matrixCokernel (Matrix.diagonal m)) = 0 at hz
      have hzrange :
          (ell : ℤ) • z ∈ LinearMap.range (Matrix.toLin' (Matrix.diagonal m)) := by
        exact (Submodule.Quotient.mk_eq_zero _).mp (by
          simpa only [Submodule.Quotient.mk_smul] using hz)
      obtain ⟨w, hw⟩ := hzrange
      have hdiv : ∀ i, m i ∣ z i := by
        intro i
        have hcoord := congrFun hw i
        have hdivell : m i ∣ (ell : ℤ) * z i := by
          refine ⟨w i, ?_⟩
          simpa [Matrix.toLin'_apply, Matrix.mulVec_apply_eq_sum, Matrix.diagonal] using
            hcoord.symm
        have hc : IsCoprime (m i) (ell : ℤ) := by
          rw [Int.isCoprime_iff_nat_coprime]
          simpa using (hcoprime i).symm
        exact hc.dvd_of_dvd_mul_left hdivell
      choose v hv using hdiv
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨v, ?_⟩
      apply funext
      intro i
      simpa [Matrix.toLin'_apply, Matrix.mulVec_apply_eq_sum, Matrix.diagonal] using
        (hv i).symm
    exact (hzero x x.property).trans (hzero y y.property).symm
  exact Module.finrank_zero_of_subsingleton

/-! The vertex and edge lattices of the positive off-diagonal graph. -/
abbrev vertexLattice (n : ℕ) := Fin n → ℤ

abbrev positiveEdge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ 0 < A e.1 e.2}

abbrev edgeLattice {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :=
  positiveEdge A → ℤ

def edgeSource {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (e : positiveEdge A) : Fin n := e.1.1

def edgeTarget {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (e : positiveEdge A) : Fin n := e.1.2

def edgeWeight {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (e : positiveEdge A) : ℤ := A e.1.1 e.1.2

/-! The oriented incidence matrix and its edge-weighted companion. -/
def graphIncidenceMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (positiveEdge A) ℤ :=
  fun i e => if edgeSource e = i then 1 else if edgeTarget e = i then -1 else 0

def graphWeightedIncidenceMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (positiveEdge A) ℤ :=
  fun i e =>
    if edgeSource e = i then edgeWeight e
    else if edgeTarget e = i then -edgeWeight e
    else 0

/-! The incidence maps used in the graph proof of the integer lemma. -/
def graphBoundary {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    vertexLattice n →ₗ[ℤ] edgeLattice A :=
  (graphIncidenceMatrix A).transpose.mulVecLin

def graphCoboundary {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    edgeLattice A →ₗ[ℤ] vertexLattice n :=
  (graphWeightedIncidenceMatrix A).mulVecLin

/-! Coordinate pairings for the vertex and edge lattices. -/
def weightedCoordinateForm {ι : Type*} [Fintype ι] (w : ι → ℤ) :
    LinearMap.BilinForm ℤ (ι → ℤ) :=
  by
    classical
    exact (dotProductBilin ℤ ℤ).compl₂ ((Matrix.diagonal w).mulVecLin)

def graphVertexPairing (n : ℕ) :
    LinearMap.BilinForm ℤ (vertexLattice n) :=
  weightedCoordinateForm (fun _ => 1)

def graphEdgePairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    LinearMap.BilinForm ℤ (edgeLattice A) :=
  weightedCoordinateForm (edgeWeight (A := A))

/-! Source-facing formulas for the incidence maps and their pairings. -/
theorem graphBoundary_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x : vertexLattice n) (e : positiveEdge A) :
    graphBoundary A x e = x (edgeSource e) - x (edgeTarget e) := by
  classical
  simp [graphBoundary, graphIncidenceMatrix, edgeSource, edgeTarget,
    Matrix.mulVecLin, Matrix.transpose, Matrix.mulVec_apply_eq_sum]
  have hsum (a : Fin n) (f : Fin n → ℤ) :
      ∑ j, (if a = j then f j else 0) = f a := by
    simp
  have hne : edgeSource e ≠ edgeTarget e := by
    exact ne_of_lt e.2.1
  calc
    ∑ j, (if edgeSource e = j then 1
      else if edgeTarget e = j then -1 else 0) * x j =
        ∑ j, ((if edgeSource e = j then x j else 0) -
          (if edgeTarget e = j then x j else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h₁ : edgeSource e = j
      · by_cases h₂ : edgeTarget e = j
        · exact (hne (h₁.trans h₂.symm)).elim
        · simp [h₁, h₂]
      · by_cases h₂ : edgeTarget e = j <;> simp [h₁, h₂]
    _ = x (edgeSource e) - x (edgeTarget e) := by
      rw [Finset.sum_sub_distrib, hsum, hsum]

theorem graphCoboundary_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (y : edgeLattice A) (i : Fin n) :
    graphCoboundary A y i =
      (Finset.univ : Finset (positiveEdge A)).sum
        (fun e => if edgeSource e = i then edgeWeight e * y e
          else if edgeTarget e = i then -(edgeWeight e * y e) else 0) := by
  classical
  simp [graphCoboundary, graphWeightedIncidenceMatrix, Matrix.mulVecLin,
    Matrix.mulVec_apply_eq_sum]

theorem graphVertexPairing_positive_definite (n : ℕ) :
    IsPositiveDefiniteIntegralForm (graphVertexPairing n) := by
  classical
  unfold IsPositiveDefiniteIntegralForm graphVertexPairing weightedCoordinateForm
  constructor
  · exact ⟨fun x y => by
      simp [dotProductBilin, Matrix.diagonal, Matrix.mulVecLin,
        Matrix.mulVec_apply_eq_sum, dotProduct]
      ac_rfl⟩
  · intro x hx
    simp [dotProductBilin, Matrix.diagonal, Matrix.mulVecLin,
      Matrix.mulVec_apply_eq_sum, dotProduct]
    change 0 < ∑ i : Fin n, x i * x i
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      apply hx
      funext i
      by_contra hi'
      exact h ⟨i, hi'⟩
    have hpos : 0 < x i * x i := mul_self_pos.mpr hi
    have hle : x i * x i ≤ ∑ j : Fin n, x j * x j := by
      exact Finset.single_le_sum (fun j hj => mul_self_nonneg (x j))
        (Finset.mem_univ i)
    exact lt_of_lt_of_le hpos hle

theorem graphEdgePairing_positive_definite {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    IsPositiveDefiniteIntegralForm (graphEdgePairing A) := by
  classical
  unfold IsPositiveDefiniteIntegralForm graphEdgePairing weightedCoordinateForm
  constructor
  · refine ⟨fun x y => ?_⟩
    simp [dotProductBilin, Matrix.diagonal, Matrix.mulVecLin,
      Matrix.mulVec_apply_eq_sum, dotProduct]
    apply Finset.sum_congr rfl
    intro e he
    ac_rfl
  · intro x hx
    simp [dotProductBilin, Matrix.diagonal, Matrix.mulVecLin,
      Matrix.mulVec_apply_eq_sum, dotProduct]
    obtain ⟨e, he⟩ : ∃ e : positiveEdge A, x e ≠ 0 := by
      by_contra h
      apply hx
      funext e
      by_contra he'
      exact h ⟨e, he'⟩
    have hpos : 0 < x e * (edgeWeight e * x e) := by
      rw [show x e * (edgeWeight e * x e) = edgeWeight e * (x e * x e) by ac_rfl]
      exact mul_pos e.2.2 (mul_self_pos.mpr he)
    have hnonneg (f : positiveEdge A) :
        0 ≤ x f * (edgeWeight f * x f) := by
      rw [show x f * (edgeWeight f * x f) = edgeWeight f * (x f * x f) by ac_rfl]
      exact mul_nonneg (le_of_lt f.2.2) (mul_self_nonneg (x f))
    have hle : x e * (edgeWeight e * x e) ≤
        ∑ f : positiveEdge A, x f * (edgeWeight f * x f) := by
      exact Finset.single_le_sum (fun f hf => hnonneg f) (Finset.mem_univ e)
    exact lt_of_lt_of_le hpos hle

theorem graphBoundary_adjoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    LinearMap.IsAdjointPair (graphVertexPairing n) (graphEdgePairing A)
      (graphBoundary A) (graphCoboundary A) := by
  intro x y
  simp [graphVertexPairing, graphEdgePairing, weightedCoordinateForm,
    graphBoundary_apply, graphCoboundary_apply, dotProductBilin,
    Matrix.diagonal, Matrix.mulVecLin, Matrix.mulVec_apply_eq_sum, dotProduct]
  calc
    ∑ e : positiveEdge A, (x (edgeSource e) - x (edgeTarget e)) *
        (edgeWeight e * y e) =
        ∑ e : positiveEdge A, ∑ i : Fin n,
          x i * (if edgeSource e = i then edgeWeight e * y e
            else if edgeTarget e = i then -(edgeWeight e * y e) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      have hsum (a : Fin n) (f : Fin n → ℤ) :
          ∑ i, (if a = i then f i else 0) = f a := by
        simp
      have hne : edgeSource e ≠ edgeTarget e := ne_of_lt e.2.1
      symm
      calc
        ∑ i : Fin n, x i * (if edgeSource e = i then edgeWeight e * y e
            else if edgeTarget e = i then -(edgeWeight e * y e) else 0) =
            ∑ i : Fin n, ((if edgeSource e = i then
              x i * (edgeWeight e * y e) else 0) -
                (if edgeTarget e = i then
                  x i * (edgeWeight e * y e) else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h₁ : edgeSource e = i
            · by_cases h₂ : edgeTarget e = i
              · exact (hne (h₁.trans h₂.symm)).elim
              · simp [h₁, h₂]
            · by_cases h₂ : edgeTarget e = i <;> simp [h₁, h₂]
        _ = x (edgeSource e) * (edgeWeight e * y e) -
            x (edgeTarget e) * (edgeWeight e * y e) := by
          rw [Finset.sum_sub_distrib, hsum, hsum]
        _ = (x (edgeSource e) - x (edgeTarget e)) *
            (edgeWeight e * y e) := by
          simp [sub_mul, mul_sub, mul_comm, mul_left_comm]
    _ = ∑ i : Fin n, ∑ e : positiveEdge A,
        x i * (if edgeSource e = i then edgeWeight e * y e
          else if edgeTarget e = i then -(edgeWeight e * y e) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, x i *
        ∑ e : positiveEdge A, (if edgeSource e = i then edgeWeight e * y e
          else if edgeTarget e = i then -(edgeWeight e * y e) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-! The positive off-diagonal edge count of the graph attached to a symmetric matrix. -/
def positiveOffDiagonalEdgeCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  Fintype.card (positiveEdge A)

def graphEdgeWeightProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  (Finset.univ : Finset (positiveEdge A)).prod edgeWeight

theorem graph_coboundary_ker_eq_orthogonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    LinearMap.ker (graphCoboundary A) =
      (graphEdgePairing A).orthogonal (LinearMap.range (graphBoundary A)) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hz
    rintro y ⟨y, rfl⟩
    simpa [hz] using (graphBoundary_adjoint A y z)
  · intro hz
    apply funext
    intro i
    have horth := hz (graphBoundary A (Pi.single i (1 : ℤ)))
      ⟨Pi.single i (1 : ℤ), rfl⟩
    have hadj := graphBoundary_adjoint A (Pi.single i (1 : ℤ)) z
    have hcoord :
        graphVertexPairing n (Pi.single i (1 : ℤ)) (graphCoboundary A z) = 0 := by
      calc
        graphVertexPairing n (Pi.single i (1 : ℤ)) (graphCoboundary A z) =
            graphEdgePairing A (graphBoundary A (Pi.single i (1 : ℤ))) z :=
          hadj.symm
        _ = 0 := horth
    simpa [graphVertexPairing, weightedCoordinateForm, dotProductBilin,
      Matrix.diagonal, Matrix.mulVecLin, Matrix.mulVec_apply_eq_sum, dotProduct,
      Pi.single_apply] using hcoord

theorem graph_discriminant_product_annihilates {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    ∀ x : latticeDiscriminantQuotient (graphEdgePairing A),
      graphEdgeWeightProduct A • x = 0 := by
  sorry

theorem graph_cokernel_product_annihilated {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N)
    (q : latticeDiscriminantQuotient (graphEdgePairing A) →ₗ[ℤ]
      moduleCokernel f) (hq : Function.Surjective q) :
    ∀ x : moduleCokernel f, graphEdgeWeightProduct A • x = 0 := by
  intro x
  obtain ⟨y, rfl⟩ := hq x
  simpa using congrArg q (graph_discriminant_product_annihilates A y)

/-! The graph identities used to compare the matrix and incidence cokernels. -/
theorem graph_laplacian_eq_neg_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hrowsum : Matrix.mulVec A (1 : Fin n → ℤ) = 0) :
    (graphCoboundary A).comp (graphBoundary A) = -(Matrix.toLin' A) := by
  sorry

theorem graph_cokernel_equiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hrowsum : Matrix.mulVec A (1 : Fin n → ℤ) = 0) :
    Nonempty
      (moduleCokernel (Matrix.toLin' A) ≃ₗ[ℤ]
        moduleCokernel ((graphCoboundary A).comp (graphBoundary A))) := by
  have heq :
      (graphCoboundary A).comp (graphBoundary A) = -(Matrix.toLin' A) :=
    graph_laplacian_eq_neg_matrix A hsymm hoffdiag hrowsum
  have hrange :
      LinearMap.range (Matrix.toLin' A) =
        LinearMap.range ((graphCoboundary A).comp (graphBoundary A)) := by
    rw [heq]
    simp
  exact ⟨Submodule.quotEquivOfEq _ _ hrange⟩

theorem graph_kernel_quotient_torsion_free {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    Module.IsTorsionFree ℤ
      (edgeLattice A ⧸ LinearMap.ker (graphCoboundary A)) := by
  let : Module.IsTorsionFree ℤ (vertexLattice n) := inferInstance
  let : Module.IsTorsionFree ℤ (LinearMap.range (graphCoboundary A)) :=
    Subtype.coe_injective.moduleIsTorsionFree _ (by simp)
  refine Function.Injective.moduleIsTorsionFree
    (fun x : edgeLattice A ⧸ LinearMap.ker (graphCoboundary A) =>
      (graphCoboundary A).quotKerEquivRange x)
    (graphCoboundary A).quotKerEquivRange.injective ?_
  intro r x
  simp

/-! The image of an oriented graph incidence map is saturated. -/
theorem graph_image_quotient_torsion_free {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    Module.IsTorsionFree ℤ
      (edgeLattice A ⧸ LinearMap.range (graphBoundary A)) := by
  sorry

theorem graph_coboundary_kernel_finrank {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hn : 0 < n)
    (hconnected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) :
    Module.finrank ℤ (LinearMap.ker (graphCoboundary A)) =
      positiveOffDiagonalEdgeCount A + 1 - n := by
  sorry

/-!
Coprimality of the nonzero matrix and vector entries used in the integer
recurring lemma.  Zero coefficients impose no restriction on `ell`.
-/
def CoprimeToMatrixAndVector {n : ℕ} (ell : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ) : Prop :=
  (∀ i j, A i j ≠ 0 → Nat.Coprime ell (Int.natAbs (A i j))) ∧
    ∀ i, m i ≠ 0 → Nat.Coprime ell (Int.natAbs (m i))

/-! The finite-field dimension bound for the integer recurring matrix. -/
theorem recurring_symmetric_integer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (m : Fin n → ℤ) (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hm : ∀ i, 0 < m i) (hAm : Matrix.mulVec A m = 0)
    (hconnected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0)
    (ell : ℕ) (hell : Nat.Prime ell)
    (hcoprime : CoprimeToMatrixAndVector ell A m) :
    matrixPrimaryTorsionFinrank A ell hell ≤
      positiveOffDiagonalEdgeCount A + 1 - n := by
  sorry

end Formalization.Books.Models.Unit02
