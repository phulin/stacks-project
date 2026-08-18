import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
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

private theorem exists_bilinForm_smul_eq
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L]
    [Module.Finite ℤ L] (B : LinearMap.BilinForm ℤ L)
    (hBker : LinearMap.ker B = ⊥) :
    ∀ φ : Module.Dual ℤ L, ∃ d : ℤ, d ≠ 0 ∧ ∃ y : L, d • φ = B y := by
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

private theorem orthogonal_quotient_isTorsionFree
    (L : Type*) [AddCommGroup L] [Module ℤ L]
    (B : LinearMap.BilinForm ℤ L) (A : Submodule ℤ L) :
    @Module.IsTorsionFree ℤ (L ⧸ B.orthogonal A) _ _
      (Submodule.Quotient.module (B.orthogonal A)) := by
  let W : Submodule ℤ L := B.orthogonal A
  letI : Module ℤ (L ⧸ W) := Submodule.Quotient.module W
  change @Module.IsTorsionFree ℤ (L ⧸ W) _ _ (Submodule.Quotient.module W)
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

private theorem orthogonal_domRestrict_ker
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L]
    [Module.Finite ℤ L] (B : LinearMap.BilinForm ℤ L)
    (hB : IsPositiveDefiniteIntegralForm B) (A : Submodule ℤ L)
    (hquotient : Module.IsTorsionFree ℤ (L ⧸ A)) :
    A = LinearMap.ker (B.domRestrict₂ (B.orthogonal A)) := by
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
  have hBsmul := exists_bilinForm_smul_eq L B hBker
  have hAle : A ≤ LinearMap.ker p := by
    intro a ha
    apply LinearMap.mem_ker.mpr
    apply DFunLike.ext
    intro y
    rw [show p a y = B a (y : L) by rfl]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp y.property) a ha
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
      change B x y = 0
      exact hpx
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
  exact le_antisymm hAle hkerle

private theorem orthogonal_projection_data
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L]
    [Module.Finite ℤ L] (B : LinearMap.BilinForm ℤ L)
    (hB : IsPositiveDefiniteIntegralForm B) (A : Submodule ℤ L)
    (hquotient : Module.IsTorsionFree ℤ (L ⧸ A))
    (hker : A = LinearMap.ker (B.domRestrict₂ (B.orthogonal A))) :
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
  have hker' : A = LinearMap.ker p := by
    simpa [p, W] using hker
  letI : Module ℤ (L ⧸ W) := Submodule.Quotient.module W
  have hWtf : Module.IsTorsionFree ℤ (L ⧸ W) := by
    simpa [W] using orthogonal_quotient_isTorsionFree L B A
  letI : Module.IsTorsionFree ℤ (L ⧸ W) := hWtf
  letI : Module.Finite ℤ (L ⧸ W) :=
    Module.Finite.of_surjective (W.mkQ : L →ₗ[ℤ] (L ⧸ W)) W.mkQ_surjective
  have hWfree : Module.Free ℤ (L ⧸ W) := by infer_instance
  have hWproj : Module.Projective ℤ (L ⧸ W) := inferInstance
  letI : Module ℤ W := AddCommGroup.toIntModule W
  let pOut : L →ₗ[ℤ] Module.Dual ℤ W :=
    { toFun := fun x =>
        { toFun := fun y => B x (y : L)
          map_add' := by
            intro y z
            exact LinearMap.BilinForm.add_right x (y : L) (z : L)
          map_smul' := by
            intro k y
            change B x (k • (y : L)) = k • B x (y : L)
            rw [← Int.cast_smul_eq_zsmul ℤ]
            exact LinearMap.BilinForm.smul_right k x (y : L) }
      map_add' := by
        intro x z
        apply DFunLike.ext
        intro y
        exact LinearMap.BilinForm.add_left x z (y : L)
      map_smul' := by
        intro k x
        apply DFunLike.ext
        intro y
        dsimp
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          RingHom.id_apply, smul_eq_mul] using
          LinearMap.BilinForm.smul_left k x (y : L) }
  have hkerOut : A = LinearMap.ker pOut := by
    apply le_antisymm
    · intro a ha
      apply LinearMap.mem_ker.mpr
      apply DFunLike.ext
      intro y
      change B a (y : L) = 0
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp y.property) a ha
    · intro x hx
      have hxP : x ∈ LinearMap.ker p := by
        apply LinearMap.mem_ker.mpr
        apply DFunLike.ext
        intro y
        have hzero := DFunLike.congr_fun (LinearMap.mem_ker.mp hx) y
        change B x (y : L) = 0
        simpa [pOut] using hzero
      exact (le_of_eq hker'.symm) hxP
  let rOut : Module.Dual ℤ L →ₗ[ℤ] Module.Dual ℤ W :=
    { toFun := fun φ =>
        { toFun := fun y => φ (y : L)
          map_add' := by
            intro y z
            exact φ.map_add (y : L) (z : L)
          map_smul' := by
            intro k y
            change φ (k • (y : L)) = k • φ (y : L)
            rw [← Int.cast_smul_eq_zsmul ℤ]
            exact φ.map_smul k (y : L) }
      map_add' := by
        intro φ ψ
        apply DFunLike.ext
        intro y
        rfl
      map_smul' := by
        intro k φ
        apply DFunLike.ext
        intro y
        rfl }
  have hrOut : Function.Surjective rOut := by
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective
      (W.mkQ : L →ₗ[ℤ] (L ⧸ W))
      (LinearMap.range_eq_top.mpr W.mkQ_surjective)
    let t : L →ₗ[ℤ] L := LinearMap.id - s.comp W.mkQ
    have ht : ∀ x, t x ∈ W := by
      intro x
      apply (Submodule.Quotient.mk_eq_zero W).mp
      change W.mkQ (x - s (W.mkQ x)) = 0
      rw [map_sub]
      have hsx := DFunLike.congr_fun hs (W.mkQ x)
      exact sub_eq_zero.mpr hsx.symm
    let π : L →ₗ[ℤ] W :=
      { toFun := fun x => ⟨t x, ht x⟩
        map_add' := by
          intro x z
          apply Subtype.ext
          exact t.map_add x z
        map_smul' := by
          intro k x
          apply Subtype.ext
          dsimp
          exact (t.map_smul k x).trans (by
            simpa using Int.cast_smul_eq_zsmul ℤ k (t x)) }
    have hπ : ∀ w : W, π w = w := by
      intro w
      apply Subtype.ext
      change t (w : L) = (w : L)
      have hwq : W.mkQ (w : L) = 0 :=
        (Submodule.Quotient.mk_eq_zero W).mpr w.property
      change (w : L) - s (W.mkQ (w : L)) = (w : L)
      rw [hwq]
      simp
    intro φ
    refine ⟨π.dualMap φ, ?_⟩
    apply DFunLike.ext
    intro w
    change φ (π w) = φ w
    rw [hπ]
  have hBrOut : LinearMap.range B ≤
      LinearMap.ker ((LinearMap.range pOut).mkQ.comp rOut) := by
    rintro z ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range pOut)).mpr
    refine ⟨x, ?_⟩
    apply DFunLike.ext
    intro y
    rfl
  let qOut : latticeDiscriminantQuotient B →ₗ[ℤ] moduleCokernel pOut :=
    (LinearMap.range B).liftQ ((LinearMap.range pOut).mkQ.comp rOut) hBrOut
  have hqOut : Function.Surjective qOut := by
    intro z
    obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range pOut) z
    obtain ⟨φ, hφ⟩ := hrOut ψ
    refine ⟨Submodule.Quotient.mk φ, ?_⟩
    simp [qOut, hφ]
  let pFinal : L →ₗ[ℤ] Module.Dual ℤ (B.orthogonal A) := by
    exact pOut
  let qFinal : latticeDiscriminantQuotient B →ₗ[ℤ] moduleCokernel pFinal := by
    simpa [pFinal, pOut, W] using qOut
  refine ⟨pFinal, qFinal, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    change B x (y : L) = B x (y : L)
    rfl
  · simpa [pFinal, pOut, W] using hkerOut
  · simpa [pFinal, pOut, W] using LinearMap.exact_map_mkQ_range pOut
  · apply Submodule.mkQ_surjective
  · simpa [qFinal, pFinal, pOut, W] using hqOut

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
  have hker : A = LinearMap.ker p := by
    simpa [p, W] using orthogonal_domRestrict_ker L B hB A hquotient
  exact orthogonal_projection_data L B hB A hquotient
    (by simpa [p, W] using hker)

private theorem int_free_of_torsion_free_finite
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.IsTorsionFree ℤ M] [Module.Finite ℤ M] :
    Module.Free ℤ M := by
  infer_instance

private theorem int_finite_of_surjective
    (M P : Type*) [AddCommGroup M] [Module ℤ M]
    [AddCommGroup P] [Module ℤ P] [Module.Finite ℤ M]
    (f : M →ₗ[ℤ] P) (hf : Function.Surjective f) :
    Module.Finite ℤ P := by
  exact Module.Finite.of_surjective f hf

private theorem projective_of_free
    (M : Type*) [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] :
    Module.Projective ℤ M := by
  exact Module.Projective.of_free

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
  classical
  let C : Submodule ℤ L := A ⊔ B.orthogonal A
  obtain ⟨p, q, hp, hker, hex, hsur, hq⟩ :=
    orthogonal_projection_sequence L B hB A hquotient
  let _instA : Module ℤ A := A.module
  let pA : L →ₗ[ℤ] Module.Dual ℤ A := B.domRestrict₂ A
  have hkerpA : LinearMap.ker pA = B.orthogonal A := by
    ext x
    constructor
    · intro hx
      apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
      intro a ha
      have hxa := DFunLike.congr_fun (LinearMap.mem_ker.mp hx) ⟨a, ha⟩
      have hxa' : B x a = 0 := by
        change B x (a : L) = 0 at hxa
        exact hxa
      rw [hB.1.eq]
      exact hxa'
    · intro hx
      apply LinearMap.mem_ker.mpr
      apply DFunLike.ext
      intro a
      change B x (a : L) = 0
      rw [hB.1.eq]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) (a : L) a.property
  have hfzero : C ≤ LinearMap.ker
      ((LinearMap.range (B.restrict A)).mkQ.comp pA) := by
    refine sup_le ?_ ?_
    · intro a ha
      apply LinearMap.mem_ker.mpr
      apply (Submodule.Quotient.mk_eq_zero (LinearMap.range (B.restrict A))).mpr
      refine ⟨⟨a, ha⟩, ?_⟩
      apply DFunLike.ext
      intro y
      rfl
    · intro x hx
      apply LinearMap.mem_ker.mpr
      have hpx : pA x = 0 := by
        apply DFunLike.ext
        intro a
        change B x (a : L) = 0
        rw [hB.1.eq]
        exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) (a : L) a.property
      simp [hpx]
  let f : L ⧸ C →ₗ[ℤ] latticeDualQuotient B A :=
    { toFun := Quotient.lift (fun x => (LinearMap.range (B.restrict A)).mkQ (pA x)) (by
          intro x y hxy
          have hxy' : x - y ∈ C :=
            (Submodule.quotientRel_def C).mp hxy
          apply (Submodule.Quotient.eq (LinearMap.range (B.restrict A))).2
          have hmem := hfzero hxy'
          have hzero := LinearMap.mem_ker.mp hmem
          apply (Submodule.Quotient.mk_eq_zero
            (LinearMap.range (B.restrict A))).mp
          change (LinearMap.range (B.restrict A)).mkQ (pA (x - y)) = 0 at hzero
          have hzero' : (LinearMap.range (B.restrict A)).mkQ
              (pA x - pA y) = 0 := by
            calc
              (LinearMap.range (B.restrict A)).mkQ (pA x - pA y) =
                  (LinearMap.range (B.restrict A)).mkQ (pA (x - y)) :=
                congrArg _ (pA.map_sub x y).symm
              _ = 0 := hzero
          simpa only [Submodule.mkQ_apply] using hzero')
      map_add' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            change (LinearMap.range (B.restrict A)).mkQ (pA (x + y)) =
              (LinearMap.range (B.restrict A)).mkQ (pA x) +
                (LinearMap.range (B.restrict A)).mkQ (pA y)
            calc
              (LinearMap.range (B.restrict A)).mkQ (pA (x + y)) =
                  (LinearMap.range (B.restrict A)).mkQ (pA x + pA y) :=
                congrArg _ (pA.map_add x y)
              _ = (LinearMap.range (B.restrict A)).mkQ (pA x) +
                  (LinearMap.range (B.restrict A)).mkQ (pA y) := by
                rw [map_add]
      map_smul' := by
        intro k x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change (LinearMap.range (B.restrict A)).mkQ (pA (k • x)) =
            k • (LinearMap.range (B.restrict A)).mkQ (pA x)
          calc
            (LinearMap.range (B.restrict A)).mkQ (pA (k • x)) =
                (LinearMap.range (B.restrict A)).mkQ (k • pA x) :=
              congrArg _ (pA.toAddMonoidHom.map_zsmul k x)
            _ = k • (LinearMap.range (B.restrict A)).mkQ (pA x) := by
              exact (LinearMap.range (B.restrict A)).mkQ.toAddMonoidHom.map_zsmul k
                (pA x) }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := C.mkQ_surjective x
    obtain ⟨y, rfl⟩ := C.mkQ_surjective y
    have hzero : f (C.mkQ (x - y)) = 0 := by
      simpa only [map_sub] using (sub_eq_zero.mpr hxy)
    have hzero' : (LinearMap.range (B.restrict A)).mkQ (pA (x - y)) = 0 := by
      change (LinearMap.range (B.restrict A)).mkQ (pA (x - y)) = 0 at hzero
      exact hzero
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (B.restrict A))).mp hzero'
    have hpa : pA (x - y - (a : L)) = 0 := by
      rw [map_sub]
      have haa : pA (a : L) = B.restrict A a := by
        apply DFunLike.ext
        intro y
        rfl
      rw [haa]
      exact sub_eq_zero.mpr ha.symm
    have hW : x - y - (a : L) ∈ B.orthogonal A := by
      rw [← hkerpA]
      exact LinearMap.mem_ker.mpr hpa
    apply (Submodule.Quotient.eq C).2
    rw [Submodule.mem_sup]
    refine ⟨a, a.property, x - y - (a : L), hW, ?_⟩
    abel
  have hmod : (Submodule.Quotient.module A : Module ℤ (L ⧸ A)) =
      AddCommGroup.toIntModule (L ⧸ A) := Subsingleton.elim _ _
  have htfA : @Module.IsTorsionFree ℤ (L ⧸ A) _ _ (Submodule.Quotient.module A) := by
    rw [hmod]
    exact hquotient
  have htfA' : @Module.IsTorsionFree ℤ (L ⧸ A) _ _ (AddCommGroup.toIntModule (L ⧸ A)) := by
    rw [← hmod]
    exact htfA
  have hfiniteA : @Module.Finite ℤ (L ⧸ A) _ _ (Submodule.Quotient.module A) := by
    exact @int_finite_of_surjective L (L ⧸ A) _ _ _
      (Submodule.Quotient.module A) _ A.mkQ A.mkQ_surjective
  have hfiniteA' : @Module.Finite ℤ (L ⧸ A) _ _ (AddCommGroup.toIntModule (L ⧸ A)) := by
    rw [← hmod]
    exact hfiniteA
  have hAfree' : @Module.Free ℤ (L ⧸ A) _ _ (AddCommGroup.toIntModule (L ⧸ A)) := by
    exact @int_free_of_torsion_free_finite (L ⧸ A) _
      (AddCommGroup.toIntModule (L ⧸ A)) htfA' hfiniteA'
  have hAfree : @Module.Free ℤ (L ⧸ A) _ _ (Submodule.Quotient.module A) := by
    rw [hmod]
    exact hAfree'
  have hAproj' : @Module.Projective ℤ _ (L ⧸ A) _
      (AddCommGroup.toIntModule (L ⧸ A)) := by
    exact @projective_of_free (L ⧸ A) _
      (AddCommGroup.toIntModule (L ⧸ A)) hAfree'
  have hAproj : @Module.Projective ℤ _ (L ⧸ A) _ (Submodule.Quotient.module A) := by
    rw [hmod]
    exact hAproj'
  let rA := A.dualRestrict
  have hrA : Function.Surjective rA := by
    have hA_surj := A.mkQ_surjective
    have hA_range :=
      (@LinearMap.range_eq_top ℤ ℤ L (L ⧸ A) _ _ _ _ _
        (Submodule.Quotient.module A) (RingHom.id ℤ) _ A.mkQ).2 hA_surj
    obtain ⟨s, hs⟩ := @LinearMap.exists_rightInverse_of_surjective ℤ _
      (L ⧸ A) _ (Submodule.Quotient.module A) L _ _ hAproj A.mkQ
      hA_range
    let t : L →ₗ[ℤ] L := LinearMap.id - s.comp A.mkQ
    have ht : ∀ x, t x ∈ A := by
      intro x
      apply (Submodule.Quotient.mk_eq_zero A).mp
      change A.mkQ (x - s (A.mkQ x)) = 0
      rw [map_sub]
      have hsx := DFunLike.congr_fun hs (A.mkQ x)
      exact sub_eq_zero.mpr hsx.symm
    let π := t.codRestrict A ht
    have hπ : ∀ a : A, π a = a := by
      intro a
      apply Subtype.ext
      dsimp [π]
      have haq : A.mkQ (a : L) = 0 :=
        (Submodule.Quotient.mk_eq_zero A).mpr a.property
      simp [t, haq]
    intro φ
    refine ⟨π.dualMap φ, ?_⟩
    apply DFunLike.ext
    intro a
    change φ (π a) = φ a
    rw [hπ]
  let uF := (LinearMap.range (B.restrict A)).mkQ.comp rA
  let vF := (LinearMap.range f).mkQ.comp uF
  have hBF : LinearMap.range B ≤ LinearMap.ker vF := by
    rintro z ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr
    refine ⟨C.mkQ x, ?_⟩
    simp only [f]
    apply congrArg (LinearMap.range (B.restrict A)).mkQ
    apply DFunLike.ext
    intro a
    rfl
  let qF : latticeDiscriminantQuotient B →ₗ[ℤ] moduleCokernel f :=
    (LinearMap.range B).liftQ vF hBF
  have hqF : Function.Surjective qF := by
    intro z
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range f) z
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective
      (LinearMap.range (B.restrict A)) t
    obtain ⟨φ, hφ⟩ := hrA u
    refine ⟨Submodule.Quotient.mk φ, ?_⟩
    change (LinearMap.range f).mkQ
        ((LinearMap.range (B.restrict A)).mkQ (rA φ)) = Submodule.Quotient.mk t
    rw [hφ]
    simpa only [Submodule.mkQ_apply] using
      congrArg (LinearMap.range f).mkQ hu
  let _instW : Module ℤ (B.orthogonal A) := (B.orthogonal A).module
  let pW : L →ₗ[ℤ] Module.Dual ℤ (B.orthogonal A) :=
    B.domRestrict₂ (B.orthogonal A)
  have hpW : ∀ x y, pW x y = B x (y : L) := by
    intro x y
    rfl
  have hkerW : A = LinearMap.ker pW := by
    apply le_antisymm
    · intro a ha
      apply LinearMap.mem_ker.mpr
      apply DFunLike.ext
      intro y
      change B a (y : L) = 0
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp y.property) a ha
    · intro x hx
      rw [hker]
      apply LinearMap.mem_ker.mpr
      apply DFunLike.ext
      intro y
      have hzero := DFunLike.congr_fun (LinearMap.mem_ker.mp hx) y
      have hzero' : B x (y : L) = 0 := by
        calc
          B x (y : L) = pW x y := (hpW x y).symm
          _ = 0 := hzero
      exact (hp x y).trans hzero'
  have hgzero : C ≤ LinearMap.ker
      ((LinearMap.range (B.restrict (B.orthogonal A))).mkQ.comp pW) := by
    refine sup_le ?_ ?_
    · intro a ha
      have hpa : pW a = 0 := by
        have ha' : a ∈ LinearMap.ker pW := hkerW ▸ ha
        exact LinearMap.mem_ker.mp ha'
      apply LinearMap.mem_ker.mpr
      simp [hpa]
    · intro w hw
      apply LinearMap.mem_ker.mpr
      apply (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (B.restrict (B.orthogonal A)))).mpr
      refine ⟨⟨w, hw⟩, ?_⟩
      apply DFunLike.ext
      intro y
      exact hpW w y
  let g : L ⧸ C →ₗ[ℤ] latticeDualQuotient B (B.orthogonal A) :=
    { toFun := Quotient.lift
        (fun x => (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (pW x)) (by
          intro x y hxy
          have hxy' : x - y ∈ C :=
            (Submodule.quotientRel_def C).mp hxy
          apply (Submodule.Quotient.eq
            (LinearMap.range (B.restrict (B.orthogonal A)))).2
          have hmem := hgzero hxy'
          have hzero := LinearMap.mem_ker.mp hmem
          apply (Submodule.Quotient.mk_eq_zero
            (LinearMap.range (B.restrict (B.orthogonal A)))).mp
          change (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
              (pW (x - y)) = 0 at hzero
          have hzero' : (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
              (pW x - pW y) = 0 := by
            calc
              (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
                  (pW x - pW y) =
                  (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
                    (pW (x - y)) :=
                congrArg _ (pW.map_sub x y).symm
              _ = 0 := hzero
          simpa only [Submodule.mkQ_apply] using hzero')
      map_add' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            change (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
                (pW (x + y)) =
              (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (pW x) +
                (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (pW y)
            calc
              (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
                    (pW (x + y)) =
                  (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
                    (pW x + pW y) := congrArg _ (pW.map_add x y)
              _ = (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (pW x) +
                    (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (pW y) := by
                rw [map_add]
      map_smul' := by
        intro k x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
              (pW (k • x)) =
            k • (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (pW x)
          calc
            (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
                  (pW (k • x)) =
                (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (k • pW x) :=
              congrArg _ (pW.toAddMonoidHom.map_zsmul k x)
            _ = k • (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (pW x) :=
              by
                exact (LinearMap.range (B.restrict (B.orthogonal A))).mkQ.map_smul
                  k (pW x) }
  have hg_inj : Function.Injective g := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := C.mkQ_surjective x
    obtain ⟨y, rfl⟩ := C.mkQ_surjective y
    have hmk : C.mkQ (x - y) = C.mkQ x - C.mkQ y := by
      rw [map_sub]
    have hzero : g (C.mkQ (x - y)) = 0 := by
      rw [hmk, map_sub]
      exact sub_eq_zero.mpr hxy
    have hzero' : (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
        (pW (x - y)) = 0 := by
      change (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
          (pW (x - y)) = 0 at hzero
      exact hzero
    obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (B.restrict (B.orthogonal A)))).mp hzero'
    have hpzero : pW (x - y - (w : L)) = 0 := by
      rw [map_sub]
      apply sub_eq_zero.mpr
      apply DFunLike.ext
      intro z
      calc
        pW (x - y) z = (B.restrict (B.orthogonal A) w) z := by
          simpa using congrArg (fun φ => φ z) hw.symm
        _ = pW w z := by symm; exact hpW w z
    have hpzero' : p (x - y - (w : L)) = 0 := by
      apply DFunLike.ext
      intro z
      calc
        p (x - y - (w : L)) z = B (x - y - (w : L)) z := hp _ _
        _ = B (x - y) z - B w z := by
          rw [LinearMap.BilinForm.sub_left]
        _ = 0 := by
          have hpoint := congrArg (fun φ => φ z) hpzero
          have hpoint' : pW (x - y) z - pW w z = 0 := by
            calc
              pW (x - y) z - pW w z =
                  (pW (x - y) - pW w) z := by rfl
              _ = pW (x - y - (w : L)) z := by
                exact congrArg (fun φ => φ z)
                  (pW.map_sub (x - y) w).symm
              _ = 0 := by simpa using hpoint
          rw [← hpW (x - y) z, ← hpW w z]
          exact hpoint'
    have hA : x - y - (w : L) ∈ A := by
      have hkerWle : LinearMap.ker pW ≤ A := by
        exact le_of_eq hkerW.symm
      exact hkerWle (LinearMap.mem_ker.mpr hpzero)
    apply (Submodule.Quotient.eq C).2
    rw [Submodule.mem_sup]
    refine ⟨x - y - (w : L), hA, w, w.property, ?_⟩
    abel
  let uG := (LinearMap.range (B.restrict (B.orthogonal A))).mkQ
  let vG := (LinearMap.range g).mkQ.comp uG
  have hpg : LinearMap.range pW ≤ LinearMap.ker vG := by
    rintro z ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range g)).mpr
    refine ⟨C.mkQ x, ?_⟩
    change (LinearMap.range (B.restrict (B.orthogonal A))).mkQ (pW x) =
      uG (pW x)
    rfl
  let sG : moduleCokernel pW →ₗ[ℤ] moduleCokernel g :=
    (LinearMap.range pW).liftQ vG hpg
  have hsG : Function.Surjective sG := by
    intro z
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range g) z
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective
      (LinearMap.range (B.restrict (B.orthogonal A))) t
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    change (LinearMap.range g).mkQ (uG u) = Submodule.Quotient.mk t
    rw [← hu]
    rfl
  have hWmod : (Submodule.Quotient.module (B.orthogonal A) :
      Module ℤ (L ⧸ (B.orthogonal A))) =
      AddCommGroup.toIntModule (L ⧸ (B.orthogonal A)) := Subsingleton.elim _ _
  have hWtf : @Module.IsTorsionFree ℤ (L ⧸ (B.orthogonal A)) _ _
      (Submodule.Quotient.module (B.orthogonal A)) := by
    simpa using orthogonal_quotient_isTorsionFree L B A
  have hWtf' : @Module.IsTorsionFree ℤ (L ⧸ (B.orthogonal A)) _ _
      (AddCommGroup.toIntModule (L ⧸ (B.orthogonal A))) := by
    rw [← hWmod]
    exact hWtf
  have hWfinite : @Module.Finite ℤ (L ⧸ (B.orthogonal A)) _ _
      (Submodule.Quotient.module (B.orthogonal A)) := by
    exact @int_finite_of_surjective L (L ⧸ (B.orthogonal A)) _ _ _
      (Submodule.Quotient.module (B.orthogonal A)) _
      (B.orthogonal A).mkQ (B.orthogonal A).mkQ_surjective
  have hWfinite' : @Module.Finite ℤ (L ⧸ (B.orthogonal A)) _ _
      (AddCommGroup.toIntModule (L ⧸ (B.orthogonal A))) := by
    rw [← hWmod]
    exact hWfinite
  have hWfree' : @Module.Free ℤ (L ⧸ (B.orthogonal A)) _ _
      (AddCommGroup.toIntModule (L ⧸ (B.orthogonal A))) := by
    exact @int_free_of_torsion_free_finite (L ⧸ (B.orthogonal A)) _
      (AddCommGroup.toIntModule (L ⧸ (B.orthogonal A))) hWtf' hWfinite'
  have hWfree : @Module.Free ℤ (L ⧸ (B.orthogonal A)) _ _
      (Submodule.Quotient.module (B.orthogonal A)) := by
    rw [hWmod]
    exact hWfree'
  have hWproj' : @Module.Projective ℤ _ (L ⧸ (B.orthogonal A)) _
      (AddCommGroup.toIntModule (L ⧸ (B.orthogonal A))) := by
    exact @projective_of_free (L ⧸ (B.orthogonal A)) _
      (AddCommGroup.toIntModule (L ⧸ (B.orthogonal A))) hWfree'
  have hWproj : @Module.Projective ℤ _ (L ⧸ (B.orthogonal A)) _
      (Submodule.Quotient.module (B.orthogonal A)) := by
    rw [hWmod]
    exact hWproj'
  let rW := (B.orthogonal A).dualRestrict
  have hrW : Function.Surjective rW := by
    have hW_surj := (B.orthogonal A).mkQ_surjective
    have hW_range :=
      (@LinearMap.range_eq_top ℤ ℤ L (L ⧸ (B.orthogonal A)) _ _ _ _ _
        (Submodule.Quotient.module (B.orthogonal A)) (RingHom.id ℤ) _
        (B.orthogonal A).mkQ).2 hW_surj
    obtain ⟨s, hs⟩ := @LinearMap.exists_rightInverse_of_surjective ℤ _
      (L ⧸ (B.orthogonal A)) _ (Submodule.Quotient.module (B.orthogonal A))
      L _ _ hWproj (B.orthogonal A).mkQ hW_range
    let t : L →ₗ[ℤ] L := LinearMap.id - s.comp (B.orthogonal A).mkQ
    have ht : ∀ x, t x ∈ B.orthogonal A := by
      intro x
      apply (Submodule.Quotient.mk_eq_zero (B.orthogonal A)).mp
      change (B.orthogonal A).mkQ
          (x - s ((B.orthogonal A).mkQ x)) = 0
      rw [map_sub]
      have hsx := DFunLike.congr_fun hs ((B.orthogonal A).mkQ x)
      exact sub_eq_zero.mpr hsx.symm
    let π := t.codRestrict (B.orthogonal A) ht
    have hπ : ∀ w : B.orthogonal A, π w = w := by
      intro w
      apply Subtype.ext
      dsimp [π]
      change t (w : L) = (w : L)
      have hwq : (B.orthogonal A).mkQ (w : L) = 0 :=
        (Submodule.Quotient.mk_eq_zero (B.orthogonal A)).mpr w.property
      simp [t, hwq]
    intro φ
    refine ⟨π.dualMap φ, ?_⟩
    apply DFunLike.ext
    intro w
    change φ (π w) = φ w
    rw [hπ]
  have hBrW : LinearMap.range B ≤ LinearMap.ker
      ((LinearMap.range pW).mkQ.comp rW) := by
    rintro z ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range pW)).mpr
    refine ⟨x, ?_⟩
    apply DFunLike.ext
    intro y
    rfl
  let qW : latticeDiscriminantQuotient B →ₗ[ℤ] moduleCokernel pW :=
    (LinearMap.range B).liftQ ((LinearMap.range pW).mkQ.comp rW) hBrW
  have hqW : Function.Surjective qW := by
    intro z
    obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range pW) z
    obtain ⟨φ, hφ⟩ := hrW ψ
    refine ⟨Submodule.Quotient.mk φ, ?_⟩
    simp [qW, hφ]
  let qG : latticeDiscriminantQuotient B →ₗ[ℤ] moduleCokernel g := sG.comp qW
  refine ⟨f, g, hf_inj, hg_inj, ⟨qF, hqF⟩,
    ⟨Submodule.mkQ (LinearMap.range f), Submodule.mkQ_surjective _,
      LinearMap.exact_map_mkQ_range f⟩,
    ⟨qG, hsG.comp hqW⟩,
    ⟨Submodule.mkQ (LinearMap.range g), Submodule.mkQ_surjective _,
      LinearMap.exact_map_mkQ_range g⟩⟩

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
  classical
  let f := dstar.comp d
  letI : Module ℤ (L₀ ⧸ LinearMap.range f) :=
    Submodule.Quotient.module (LinearMap.range f)
  have hkerf : LinearMap.ker f = LinearMap.ker d := by
    apply le_antisymm
    · intro x hx
      apply LinearMap.mem_ker.mpr
      have hzero : B₁ (d x) (d x) = 0 := by
        calc
          B₁ (d x) (d x) = B₀ x (dstar (d x)) := hadj x (d x)
          _ = 0 := by
            have hfx : dstar (d x) = 0 := LinearMap.mem_ker.mp hx
            rw [hfx]
            simp
      exact (by_contra fun hne => (ne_of_gt (hB₁.2 (d x) hne)) hzero)
    · intro x hx
      apply LinearMap.mem_ker.mpr
      simp [f, LinearMap.mem_ker.mp hx]
  let K : Submodule ℤ L₀ := B₀.orthogonal (LinearMap.ker d)
  have hfrange : LinearMap.range f ≤ K := by
    rintro _ ⟨x, rfl⟩
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro k hk
    have h := hadj k (d x)
    rw [LinearMap.mem_ker.mp hk, map_zero] at h
    simpa [f] using h.symm
  obtain ⟨e, he⟩ := hunimod
  have heq : Function.Injective B₀ := by
    intro x y hxy
    apply e.injective
    apply DFunLike.ext
    intro z
    rw [he, he]
    exact DFunLike.congr_fun hxy z
  letI : Module ℤ (LinearMap.range d) := (LinearMap.range d).module
  letI : Module ℤ (L₀ ⧸ LinearMap.ker d) :=
    Submodule.Quotient.module (LinearMap.ker d)
  letI : Module ℤ K := K.module
  let eD : (L₀ ⧸ LinearMap.ker d) ≃ₗ[ℤ] LinearMap.range d :=
    d.quotKerEquivRange
  let bK : K →ₗ[ℤ] (LinearMap.ker d).dualAnnihilator :=
    (B₀.domRestrict K).codRestrict (LinearMap.ker d).dualAnnihilator (by
      intro x
      rw [Submodule.mem_dualAnnihilator]
      intro k hk
      have hx := LinearMap.BilinForm.mem_orthogonal_iff.mp x.property k hk
      rw [hB₀.1.eq] at hx
      exact hx)
  let bQ : K →ₗ[ℤ] Module.Dual ℤ (L₀ ⧸ LinearMap.ker d) :=
    (Submodule.dualQuotEquivDualAnnihilator (LinearMap.ker d)).symm.toLinearMap.comp bK
  let F : K →ₗ[ℤ] Module.Dual ℤ (LinearMap.range d) :=
    (eD.symm.toLinearMap.dualMap).comp bQ
  let p : LinearMap.range d →ₗ[ℤ] Module.Dual ℤ (LinearMap.range d) :=
    B₁.restrict (LinearMap.range d)
  have hF_eval (x : K) (z : L₀) :
      F x ⟨d z, LinearMap.mem_range_self d z⟩ = B₀ (x : L₀) z := by
    change bQ x (eD.symm ⟨d z, LinearMap.mem_range_self d z⟩) = B₀ (x : L₀) z
    have heDz : eD ((LinearMap.ker d).mkQ z) =
        ⟨d z, LinearMap.mem_range_self d z⟩ := by
      apply Subtype.ext
      rfl
    rw [← heDz, eD.symm_apply_apply]
    change (Submodule.dualQuotEquivDualAnnihilator (LinearMap.ker d)).symm
        (bK x) ((LinearMap.ker d).mkQ z) = B₀ (x : L₀) z
    change (Submodule.dualQuotEquivDualAnnihilator (LinearMap.ker d)).symm
        (bK x) (Submodule.Quotient.mk z) = B₀ (x : L₀) z
    rw [Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk]
    rfl
  have hF_inj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply heq
    apply DFunLike.ext
    intro z
    have hz := congrArg (fun ψ : Module.Dual ℤ (LinearMap.range d) =>
      ψ ⟨d z, LinearMap.mem_range_self d z⟩) hxy
    rw [hF_eval x z, hF_eval y z] at hz
    exact hz
  let fK : L₀ →ₗ[ℤ] K := f.codRestrict K
    (fun z => hfrange (LinearMap.mem_range_self f z))
  have hF_f (z : L₀) :
      F (fK z) = p ⟨d z, LinearMap.mem_range_self d z⟩ := by
    apply DFunLike.ext
    intro y
    obtain ⟨w, hw⟩ := y.property
    have hy : y = ⟨d w, LinearMap.mem_range_self d w⟩ := by
      apply Subtype.ext
      exact hw.symm
    rw [hy, hF_eval]
    change B₀ (f z) w = B₁ (d z) (d w)
    calc
      B₀ (f z) w = B₀ w (dstar (d z)) := by
        change B₀ (dstar (d z)) w = B₀ w (dstar (d z))
        exact hB₀.1.eq _ _
      _ = B₁ (d w) (d z) := (hadj w (d z)).symm
      _ = B₁ (d z) (d w) := hB₁.1.eq _ _
  have hF_surj : Function.Surjective F := by
    intro ψ
    let ψQ := eD.toLinearMap.dualMap ψ
    let ψA := Submodule.dualQuotEquivDualAnnihilator (LinearMap.ker d) ψQ
    obtain ⟨x, hx⟩ := e.surjective ψA
    have hxK : x ∈ K := by
      apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
      intro k hk
      have hψA : ψA k = 0 := by
        exact (Submodule.mem_dualAnnihilator ψA).mp ψA.property k hk
      rw [hB₀.1.eq]
      calc
        B₀ x k = e x k := (he x k).symm
        _ = ψA k := congrArg (fun φ : Module.Dual ℤ L₀ => φ k) hx
        _ = 0 := hψA
    refine ⟨⟨x, hxK⟩, ?_⟩
    apply DFunLike.ext
    intro y
    change bQ ⟨x, hxK⟩ (eD.symm y) = ψ y
    have hbK : bK ⟨x, hxK⟩ = ψA := by
      apply Subtype.ext
      apply DFunLike.ext
      intro z
      change B₀ x z = ψA z
      exact (he x z).symm.trans
        (congrArg (fun φ : Module.Dual ℤ L₀ => φ z) hx)
    have hbx : bQ ⟨x, hxK⟩ = ψQ := by
      apply DFunLike.ext
      intro z
      change (Submodule.dualQuotEquivDualAnnihilator (LinearMap.ker d)).symm
          (bK ⟨x, hxK⟩) z = ψQ z
      rw [hbK]
      exact congrArg (fun φ : Module.Dual ℤ (L₀ ⧸ LinearMap.ker d) => φ z)
        ((Submodule.dualQuotEquivDualAnnihilator (LinearMap.ker d)).symm_apply_apply ψQ)
    rw [hbx]
    change ψQ (eD.symm y) = ψ y
    change ψ (eD (eD.symm y)) = ψ y
    simp
  let qF : K →ₗ[ℤ] latticeDualQuotient B₁ (LinearMap.range d) :=
    (LinearMap.range p).mkQ.comp F
  have hqF : Function.Surjective qF := by
    intro z
    obtain ⟨ψ, rfl⟩ := (LinearMap.range p).mkQ_surjective z
    obtain ⟨x, hx⟩ := hF_surj ψ
    refine ⟨x, ?_⟩
    change (LinearMap.range p).mkQ (F x) = Submodule.Quotient.mk ψ
    rw [hx]
    rfl
  have hqF_f : LinearMap.range fK ≤ LinearMap.ker qF := by
    rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (LinearMap.range p).mkQ (F (fK z)) = 0
    rw [hF_f]
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range p)).mpr
    exact LinearMap.mem_range_self p _
  have hqF_ker : LinearMap.ker qF = LinearMap.range fK := by
    apply le_antisymm
    · intro x hx
      have hx' := LinearMap.mem_ker.mp hx
      change (LinearMap.range p).mkQ (F x) = 0 at hx'
      obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero
        (LinearMap.range p)).mp hx'
      obtain ⟨z, hz⟩ := w.property
      have hw' : w = ⟨d z, LinearMap.mem_range_self d z⟩ := by
        apply Subtype.ext
        exact hz.symm
      have hFz : F x = F (fK z) := by
        calc
          F x = p w := hw.symm
          _ = p ⟨d z, LinearMap.mem_range_self d z⟩ := by rw [hw']
          _ = F (fK z) := (hF_f z).symm
      have hxy : x = fK z := hF_inj hFz
      exact hxy ▸ LinearMap.mem_range_self fK z
    · exact hqF_f
  have hpker : LinearMap.ker p = ⊥ := by
    apply le_antisymm
    · intro x hx
      by_contra hne
      have hpos := hB₁.2 (x : L₁) (by
        intro hzero
        apply hne
        exact Subtype.ext hzero)
      have hzero : B₁ (x : L₁) (x : L₁) = 0 := by
        have hx' := DFunLike.congr_fun (LinearMap.mem_ker.mp hx) x
        exact hx'
      linarith
    · exact bot_le
  have hp_smul : ∀ ψ : Module.Dual ℤ (LinearMap.range d),
      ∃ n : ℤ, n ≠ 0 ∧ ∃ y : LinearMap.range d, n • ψ = p y := by
    simpa [p] using
      (exists_bilinForm_smul_eq (LinearMap.range d)
        (B₁.restrict (LinearMap.range d)) (by simpa [p] using hpker))
  have hTtors : Module.IsTorsion ℤ
      (latticeDualQuotient B₁ (LinearMap.range d)) := by
    intro t
    obtain ⟨ψ, rfl⟩ := (LinearMap.range p).mkQ_surjective t
    obtain ⟨n, hn, y, hy⟩ := hp_smul ψ
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    change (LinearMap.range p).mkQ (n • ψ) = 0
    rw [hy]
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range p)).mpr
      (LinearMap.mem_range_self p y)
  have hlift : LinearMap.range fK ≤ LinearMap.ker
      ((LinearMap.range f).mkQ.comp K.subtype) := by
    rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (LinearMap.range f).mkQ (f z) = 0
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr
      (LinearMap.mem_range_self f z)
  letI : Module ℤ (K ⧸ LinearMap.range fK) :=
    Submodule.Quotient.module (LinearMap.range fK)
  have hker_g : LinearMap.ker ((LinearMap.range f).mkQ.comp K.subtype) ≤
      LinearMap.range fK := by
    intro x hx
    have hx' := LinearMap.mem_ker.mp hx
    change (LinearMap.range f).mkQ (x : L₀) = 0 at hx'
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mp hx'
    apply LinearMap.mem_range.mpr
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz
  have hker_iKR : LinearMap.ker
      ((LinearMap.range fK).liftQ ((LinearMap.range f).mkQ.comp K.subtype) hlift) = ⊥ := by
    exact Submodule.ker_liftQ_eq_bot (LinearMap.range fK)
      ((LinearMap.range f).mkQ.comp K.subtype) hlift hker_g
  let iKR : (K ⧸ LinearMap.range fK) →ₗ[ℤ] moduleCokernel f :=
    (LinearMap.range fK).liftQ ((LinearMap.range f).mkQ.comp K.subtype) hlift
  have hiKR : Function.Injective iKR := by
    exact LinearMap.ker_eq_bot.mp (by simpa [iKR] using hker_iKR)
  let eK : (K ⧸ LinearMap.range fK) ≃ₗ[ℤ]
      latticeDualQuotient B₁ (LinearMap.range d) :=
    (Submodule.quotEquivOfEq (LinearMap.ker qF) (LinearMap.range fK) hqF_ker).symm.trans
      (qF.quotKerEquivOfSurjective hqF)
  have hKRtors : Module.IsTorsion ℤ (K ⧸ LinearMap.range fK) := by
    intro x
    obtain ⟨a, ha⟩ := hTtors (x := eK x)
    refine ⟨a, ?_⟩
    apply eK.injective
    have hsmul_x := @Submonoid.smul_def ℤ (K ⧸ LinearMap.range fK) _
      (DistribMulAction.toDistribSMul.toSMul) (nonZeroDivisors ℤ) a x
    have hsmul_e := @Submonoid.smul_def ℤ
      (latticeDualQuotient B₁ (LinearMap.range d)) _
      (DistribMulAction.toDistribSMul.toSMul) (nonZeroDivisors ℤ) a (eK x)
    exact (congrArg eK hsmul_x).trans
      ((eK.map_smul (a : ℤ) x).trans
        (hsmul_e.symm.trans (ha.trans eK.map_zero.symm)))
  let iS : (K ⧸ LinearMap.range fK) →ₗ[ℤ]
      Submodule.torsion ℤ (moduleCokernel f) :=
    iKR.codRestrict (Submodule.torsion ℤ (moduleCokernel f)) (by
      intro x
      rw [Submodule.mem_torsion_iff]
      obtain ⟨a, ha⟩ := hKRtors (x := x)
      refine ⟨a, ?_⟩
      have hsmul_x := @Submonoid.smul_def (ℤ) (K ⧸ LinearMap.range fK) _
        (DistribMulAction.toDistribSMul.toSMul) (nonZeroDivisors ℤ) a x
      have hsmul_c := @Submonoid.smul_def ℤ (moduleCokernel f) _
        (DistribMulAction.toDistribSMul.toSMul) (nonZeroDivisors ℤ) a (iKR x)
      exact hsmul_c.trans
        ((iKR.map_smul (a : ℤ) x).symm.trans
          ((congrArg iKR hsmul_x.symm).trans
            ((congrArg iKR ha).trans iKR.map_zero))))
  have hiS : Function.Injective iS := by
    intro x y hxy
    apply hiKR
    have hxy' := congrArg (fun z : Submodule.torsion ℤ (moduleCokernel f) =>
      (z : moduleCokernel f)) hxy
    exact hxy'
  have hiS_surj : Function.Surjective iS := by
    intro s
    obtain ⟨x, hx⟩ := (LinearMap.range f).mkQ_surjective (s : moduleCokernel f)
    have hs := s.property
    rw [Submodule.mem_torsion_iff] at hs
    obtain ⟨a, ha⟩ := hs
    have hsmul_s := @Submonoid.smul_def ℤ (moduleCokernel f) _
      (DistribMulAction.toDistribSMul.toSMul) (nonZeroDivisors ℤ) a
        (s : moduleCokernel f)
    have hq := (LinearMap.range f).mkQ.map_smul (a : ℤ) x
    rw [hx, ← hsmul_s, ha] at hq
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mp hq
    have haxK := hfrange (LinearMap.mem_range_self f z)
    rw [hz] at haxK
    have hxK : x ∈ K := by
      apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
      intro k hk
      have hka := LinearMap.BilinForm.mem_orthogonal_iff.mp haxK k hk
      rw [(B₀ k).map_smul] at hka
      exact (smul_eq_zero.mp hka).resolve_left (by simpa using a.property)
    refine ⟨Submodule.Quotient.mk ⟨x, hxK⟩, ?_⟩
    apply Subtype.ext
    change (LinearMap.range f).mkQ x = (s : moduleCokernel f)
    exact hx
  let eS : (K ⧸ LinearMap.range fK) ≃ₗ[ℤ]
      Submodule.torsion ℤ (moduleCokernel f) :=
    LinearEquiv.ofBijective iS ⟨hiS, hiS_surj⟩
  have hmod : (Submodule.Quotient.module (LinearMap.range f) :
      Module ℤ (moduleCokernel f)) =
      AddCommGroup.toIntModule (moduleCokernel f) := Subsingleton.elim _ _
  rw [← hmod]
  exact ⟨eS.symm.trans eK⟩

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
  intro x
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (graphEdgePairing A)) x
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range (graphEdgePairing A))).mpr
  let y : edgeLattice A := fun e =>
    φ (Pi.single e (1 : ℤ)) * (Finset.univ.erase e).prod edgeWeight
  refine ⟨y, ?_⟩
  apply DFunLike.ext
  intro z
  simp [graphEdgePairing, weightedCoordinateForm, dotProductBilin,
    Matrix.diagonal, Matrix.mulVecLin, Matrix.mulVec_apply_eq_sum, dotProduct, y]
  have hprod (e : positiveEdge A) :
      (Finset.univ.erase e).prod edgeWeight * edgeWeight e =
        graphEdgeWeightProduct A :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ e)
  have hsingle (e : positiveEdge A) :
      (Pi.single e (z e) : edgeLattice A) =
        z e • (Pi.single e (1 : ℤ)) := by
    ext f
    by_cases h : e = f <;> simp [h]
  have hphi : φ z = ∑ e : positiveEdge A, z e * φ (Pi.single e (1 : ℤ)) := by
    calc
      φ z = φ (∑ e : positiveEdge A, Pi.single e (z e)) := by
        rw [Finset.univ_sum_single]
      _ = ∑ e : positiveEdge A, φ (Pi.single e (z e)) := by
        rw [map_sum]
      _ = ∑ e : positiveEdge A, z e * φ (Pi.single e (1 : ℤ)) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hsingle e, map_smul]
        rfl
  have hleft :
      (∑ e : positiveEdge A,
        φ (Pi.single e (1 : ℤ)) * (Finset.univ.erase e).prod edgeWeight *
          (edgeWeight e * z e)) =
        ∑ e : positiveEdge A,
          graphEdgeWeightProduct A * (z e * φ (Pi.single e (1 : ℤ))) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [← hprod e]
    ring
  rw [hphi, hleft]
  exact (Finset.mul_sum _ _ _).symm

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
  classical
  apply LinearMap.ext
  intro x
  funext i
  simp [graphCoboundary_apply, graphBoundary_apply, Matrix.toLin'_apply,
    Matrix.mulVec_apply_eq_sum]
  have hsource (i : Fin n) :
      (∑ e : positiveEdge A,
        if edgeSource e = i then
          edgeWeight e * (x (edgeSource e) - x (edgeTarget e)) else 0) =
        ∑ j : Fin n, if i < j ∧ 0 < A i j then A i j * (x i - x j) else 0 := by
    let s : Finset (positiveEdge A) :=
      (Finset.univ : Finset (positiveEdge A)).filter (fun e => edgeSource e = i)
    let t : Finset (Fin n) :=
      (Finset.univ : Finset (Fin n)).filter (fun j => i < j ∧ 0 < A i j)
    have hs :
        (∑ e : positiveEdge A,
          if edgeSource e = i then
            edgeWeight e * (x (edgeSource e) - x (edgeTarget e)) else 0) =
          ∑ e ∈ s, edgeWeight e * (x (edgeSource e) - x (edgeTarget e)) := by
      dsimp [s]
      change
        (∑ e ∈ (Finset.univ : Finset (positiveEdge A)),
          if edgeSource e = i then
            edgeWeight e * (x (edgeSource e) - x (edgeTarget e)) else 0) =
          ∑ e ∈
            (Finset.univ : Finset (positiveEdge A)).filter
              (fun e => edgeSource e = i),
            edgeWeight e * (x (edgeSource e) - x (edgeTarget e))
      rw [← Finset.sum_filter]
    rw [hs]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij
      (s := (Finset.univ : Finset (positiveEdge A)).filter
        (fun e => edgeSource e = i))
      (t := (Finset.univ : Finset (Fin n)).filter
        (fun j => i < j ∧ 0 < A i j))
      (fun e _ => edgeTarget e) ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hsrc : e.1.1 = i := by simpa [edgeSource] using he
      exact ⟨by
          change i < e.1.2
          simpa [hsrc] using e.2.1,
        by
          change 0 < A i e.1.2
          simpa [hsrc] using e.2.2⟩
    · intro e₁ h₁ e₂ h₂ hEq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      apply Subtype.ext
      apply Prod.ext
      · simpa [edgeSource] using h₁.trans h₂.symm
      · exact hEq
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      let e : positiveEdge A := ⟨(i, j), hj⟩
      refine ⟨e, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · rfl
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      have he' : e.1.1 = i := by simpa [edgeSource] using he
      simp [edgeSource, edgeTarget, edgeWeight, he']
  have htarget (i : Fin n) :
      (∑ e : positiveEdge A,
        if edgeTarget e = i then
          -(edgeWeight e * (x (edgeSource e) - x (edgeTarget e))) else 0) =
        ∑ j : Fin n, if j < i ∧ 0 < A j i then
          -(A j i * (x j - x i)) else 0 := by
    let s : Finset (positiveEdge A) :=
      (Finset.univ : Finset (positiveEdge A)).filter (fun e => edgeTarget e = i)
    let t : Finset (Fin n) :=
      (Finset.univ : Finset (Fin n)).filter (fun j => j < i ∧ 0 < A j i)
    have hs :
        (∑ e : positiveEdge A,
          if edgeTarget e = i then
            -(edgeWeight e * (x (edgeSource e) - x (edgeTarget e))) else 0) =
          ∑ e ∈ s, -(edgeWeight e * (x (edgeSource e) - x (edgeTarget e))) := by
      dsimp [s]
      change
        (∑ e ∈ (Finset.univ : Finset (positiveEdge A)),
          if edgeTarget e = i then
            -(edgeWeight e * (x (edgeSource e) - x (edgeTarget e))) else 0) =
          ∑ e ∈
            (Finset.univ : Finset (positiveEdge A)).filter
              (fun e => edgeTarget e = i),
            -(edgeWeight e * (x (edgeSource e) - x (edgeTarget e)))
      rw [← Finset.sum_filter]
    rw [hs]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij
      (s := (Finset.univ : Finset (positiveEdge A)).filter
        (fun e => edgeTarget e = i))
      (t := (Finset.univ : Finset (Fin n)).filter
        (fun j => j < i ∧ 0 < A j i))
      (fun e _ => edgeSource e) ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have htgt : e.1.2 = i := by simpa [edgeTarget] using he
      exact ⟨by
          change e.1.1 < i
          simpa [htgt] using e.2.1,
        by
          change 0 < A e.1.1 i
          simpa [htgt] using e.2.2⟩
    · intro e₁ h₁ e₂ h₂ hEq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      apply Subtype.ext
      apply Prod.ext
      · exact hEq
      · simpa [edgeTarget] using h₁.trans h₂.symm
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      let e : positiveEdge A := ⟨(j, i), hj⟩
      refine ⟨e, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · rfl
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      have he' : e.1.2 = i := by simpa [edgeTarget] using he
      simp [edgeSource, edgeTarget, edgeWeight, he']
  have hsplit :
      (∑ e : positiveEdge A,
        if edgeSource e = i then
          edgeWeight e * (x (edgeSource e) - x (edgeTarget e))
        else if edgeTarget e = i then
          -(edgeWeight e * (x (edgeSource e) - x (edgeTarget e))) else 0) =
        (∑ e : positiveEdge A,
          if edgeSource e = i then
            edgeWeight e * (x (edgeSource e) - x (edgeTarget e)) else 0) +
        (∑ e : positiveEdge A,
          if edgeTarget e = i then
            -(edgeWeight e * (x (edgeSource e) - x (edgeTarget e))) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : edgeSource e = i
    · have ht : ¬ edgeTarget e = i := by
        intro ht
        exact (ne_of_lt e.2.1) (hs.trans ht.symm)
      simp [hs, ht]
    · by_cases ht : edgeTarget e = i <;> simp [hs, ht]
  have hsource' (i : Fin n) :
      (∑ j : Fin n, if i < j ∧ 0 < A i j then A i j * (x i - x j) else 0) =
        ∑ j : Fin n, if i < j then A i j * (x i - x j) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · have hnonneg : 0 ≤ A i j := hoffdiag (ne_of_lt hij)
      by_cases hpos : 0 < A i j
      · simp [hij, hpos]
      · have hz : A i j = 0 := le_antisymm (not_lt.mp hpos) hnonneg
        simp [hij, hpos, hz]
    · simp [hij]
  have htarget' (i : Fin n) :
      (∑ j : Fin n, if j < i ∧ 0 < A j i then
          -(A j i * (x j - x i)) else 0) =
        ∑ j : Fin n, if j < i then A i j * (x i - x j) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j < i
    · have hnonneg : 0 ≤ A j i := hoffdiag (ne_of_lt hji)
      by_cases hpos : 0 < A j i
      · rw [hsymm j i]
        have hpos' : 0 < A i j := by simpa [hsymm j i] using hpos
        simp only [hji, hpos', and_self, if_true]
        ring
      · have hz : A j i = 0 := le_antisymm (not_lt.mp hpos) hnonneg
        have hz' : A i j = 0 := by simpa [hsymm j i] using hz
        simp [hji, hpos, hz, hz']
    · simp [hji]
  have hjoin :
      (∑ j : Fin n, if i < j then A i j * (x i - x j) else 0) +
          (∑ j : Fin n, if j < i then A i j * (x i - x j) else 0) =
        ∑ j : Fin n, if j ≠ i then A i j * (x i - x j) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · rcases lt_or_gt_of_ne hji with hlt | hgt
      · have hnot : ¬i < j := not_lt_of_ge (le_of_lt hlt)
        simp [hji, hlt, hnot]
      · have hnot : ¬j < i := not_lt_of_ge (le_of_lt hgt)
        simp [hji, hgt, hnot]
  rw [hsplit, hsource, htarget, hsource', htarget', hjoin]
  have hrow : (∑ j : Fin n, A i j) = 0 := by
    simpa [Matrix.mulVec_apply_eq_sum] using congrFun hrowsum i
  have hdecomp :
      (∑ j : Fin n, if j ≠ i then A i j * (x i - x j) else 0) =
        (∑ j : Fin n, A i j * x i) - ∑ j : Fin n, A i j * x j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, mul_sub]
  have hfirst : (∑ j : Fin n, A i j * x i) = 0 := by
    calc
      (∑ j : Fin n, A i j * x i) = (∑ j : Fin n, A i j) * x i := by
        rw [Finset.sum_mul]
      _ = 0 := by rw [hrow, zero_mul]
  rw [hdecomp, hfirst]
  simp

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
  classical
  let edgeRel : Fin n → Fin n → Prop := fun i j =>
    ∃ e : positiveEdge A,
      (edgeSource e = i ∧ edgeTarget e = j) ∨
        (edgeSource e = j ∧ edgeTarget e = i)
  let s : Setoid (Fin n) :=
    { r := Relation.EqvGen edgeRel
      iseqv := {
        refl := fun x => Relation.EqvGen.refl x
        symm := fun {x y} h => Relation.EqvGen.symm x y h
        trans := fun {x y z} hxy hyz => Relation.EqvGen.trans x y z hxy hyz } }
  let rep : Fin n → Fin n :=
    fun i => Quotient.out (Quotient.mk' i)
  have hrep (i : Fin n) : Relation.EqvGen edgeRel i (rep i) := by
    have hq : (Quotient.mk' (rep i) : Quotient s) = Quotient.mk' i :=
      Quotient.out_eq _
    have h := @Quotient.exact (Fin n) s (rep i) i hq
    change Relation.EqvGen edgeRel (rep i) i at h
    exact Relation.EqvGen.symm (rep i) i h
  have hrep_eq {i j : Fin n} (h : Relation.EqvGen edgeRel i j) :
      rep i = rep j := by
    apply congrArg Quotient.out
    apply Quotient.sound
    exact h
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro k z hz
  rcases z with ⟨v⟩
  by_cases hk : k = 0
  · exact Or.inl hk
  right
  have hv : k • v ∈ LinearMap.range (graphBoundary A) := by
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (graphBoundary A))).mp
    change (LinearMap.range (graphBoundary A)).mkQ (k • v) = 0
    change k • (LinearMap.range (graphBoundary A)).mkQ v = 0 at hz
    simpa only [map_smul] using hz
  rcases hv with ⟨y, hy⟩
  have hedge_dvd {i j : Fin n} (h : edgeRel i j) :
      (k : ℤ) ∣ y i - y j := by
    rcases h with ⟨e, hforward | hreverse⟩
    · rcases hforward with ⟨hs, ht⟩
      refine ⟨v e, ?_⟩
      have he := congrFun hy e
      rw [graphBoundary_apply] at he
      simpa [smul_eq_mul, hs, ht] using he
    · rcases hreverse with ⟨hs, ht⟩
      refine ⟨-v e, ?_⟩
      have he := congrFun hy e
      rw [graphBoundary_apply] at he
      have he' := congrArg Neg.neg he
      simpa [smul_eq_mul, hs, ht, sub_eq_add_neg] using he'
  have heqv_dvd : ∀ i j, Relation.EqvGen edgeRel i j →
      (k : ℤ) ∣ y i - y j := by
    intro i j h
    induction h with
    | refl i =>
        exact ⟨0, by simp⟩
    | rel i j h =>
        exact hedge_dvd h
    | symm i j h ih =>
        rcases ih with ⟨q, hq⟩
        refine ⟨-q, ?_⟩
        calc
          y j - y i = -(y i - y j) := by ring
          _ = -(k * q) := by rw [hq]
          _ = k * (-q) := by ring
    | trans i j l h₁ h₂ ih₁ ih₂ =>
        rcases ih₁ with ⟨q₁, hq₁⟩
        rcases ih₂ with ⟨q₂, hq₂⟩
        refine ⟨q₁ + q₂, ?_⟩
        calc
          y i - y l = (y i - y j) + (y j - y l) := by ring
          _ = k * q₁ + k * q₂ := by rw [hq₁, hq₂]
          _ = k * (q₁ + q₂) := by ring
  have hdiv (i : Fin n) : ∃ q : ℤ, y i - y (rep i) = k * q :=
    heqv_dvd i (rep i) (hrep i)
  let w : vertexLattice n := fun i => Classical.choose (hdiv i)
  have hw (i : Fin n) : y i - y (rep i) = k * w i :=
    Classical.choose_spec (hdiv i)
  have hrep_edge (e : positiveEdge A) :
      rep (edgeSource e) = rep (edgeTarget e) := by
    apply hrep_eq
    apply Relation.EqvGen.rel
    exact ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  have hboundary : graphBoundary A w = v := by
    funext e
    have he := congrFun hy e
    rw [graphBoundary_apply] at he
    have hs := hw (edgeSource e)
    have ht := hw (edgeTarget e)
    have hr := hrep_edge e
    have hcoord :
        k * (w (edgeSource e) - w (edgeTarget e)) = k * v e := by
      calc
        k * (w (edgeSource e) - w (edgeTarget e)) =
            (y (edgeSource e) - y (rep (edgeSource e))) -
              (y (edgeTarget e) - y (rep (edgeTarget e))) := by
                rw [hs, ht]
                ring
        _ = y (edgeSource e) - y (edgeTarget e) := by rw [hr]; ring
        _ = k * v e := by simpa [smul_eq_mul] using he
    have hzero :
        k * ((w (edgeSource e) - w (edgeTarget e)) - v e) = 0 := by
      calc
        k * ((w (edgeSource e) - w (edgeTarget e)) - v e) =
            k * (w (edgeSource e) - w (edgeTarget e)) - k * v e := by ring
        _ = 0 := sub_eq_zero.mpr hcoord
    have hdiff :
        (w (edgeSource e) - w (edgeTarget e)) - v e = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hk
    rw [graphBoundary_apply]
    exact sub_eq_zero.mp hdiff
  apply (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (graphBoundary A))).mpr
  exact ⟨w, hboundary⟩

theorem graph_coboundary_kernel_finrank {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hn : 0 < n)
    (hconnected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) :
    Module.finrank ℤ (LinearMap.ker (graphCoboundary A)) =
      positiveOffDiagonalEdgeCount A + 1 - n := by
  classical
  let root : Fin n := ⟨0, hn⟩
  let edgeRel : Fin n → Fin n → Prop := fun i j =>
    ∃ e : positiveEdge A,
      (edgeSource e = i ∧ edgeTarget e = j) ∨
        (edgeSource e = j ∧ edgeTarget e = i)
  have hedge {i j : Fin n} (hij : i ≠ j) (hpos : A i j ≠ 0) :
      edgeRel i j := by
    have hnonneg : 0 ≤ A i j := hoffdiag hij
    have hpos' : 0 < A i j := by omega
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨⟨(i, j), hlt, hpos'⟩, Or.inl ⟨rfl, rfl⟩⟩
    · have hpos'' : 0 < A j i := by rw [hsymm j i]; exact hpos'
      exact ⟨⟨(j, i), hlt, hpos''⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hconn : ∀ i : Fin n, Relation.EqvGen edgeRel root i := by
    let I : Set (Fin n) := {j | Relation.EqvGen edgeRel root j}
    have hI : I.Nonempty := ⟨root, Relation.EqvGen.refl root⟩
    have hcut : ∀ ⦃i j : Fin n⦄, i ∈ I → j ∉ I → A i j = 0 := by
      intro i j hi hj
      by_contra hne
      have hrel : edgeRel i j := hedge (by
        intro hij
        apply hj
        simpa [I, hij] using hi) hne
      apply hj
      change Relation.EqvGen edgeRel root j
      exact Relation.EqvGen.trans root i j hi (Relation.EqvGen.rel i j hrel)
    have hIu : I = Set.univ := by
      apply Set.eq_univ_of_forall
      intro i
      by_contra hi
      apply hconnected
      have hne : I ≠ Set.univ := by
        intro h
        apply hi
        rw [h]
        exact Set.mem_univ i
      exact ⟨I, hI, hne, hcut⟩
    intro i
    have hi : i ∈ I := hIu ▸ Set.mem_univ i
    exact hi
  have hkerB :
      LinearMap.ker (graphBoundary A) =
        Submodule.span ℤ ({(1 : vertexLattice n)} : Set (vertexLattice n)) := by
    apply le_antisymm
    · intro x hx
      have hxedge (e : positiveEdge A) :
          x (edgeSource e) = x (edgeTarget e) := by
        have he := congrFun (LinearMap.mem_ker.mp hx) e
        rw [graphBoundary_apply] at he
        exact sub_eq_zero.mp he
      have heq : ∀ {i j : Fin n}, Relation.EqvGen edgeRel i j → x i = x j := by
        intro i j hpath
        induction hpath with
        | refl i => rfl
        | rel i j h =>
            rcases h with ⟨e, hforward | hreverse⟩
            · simpa [hforward.1, hforward.2] using hxedge e
            · simpa [hreverse.1, hreverse.2] using (hxedge e).symm
        | symm i j h ih => exact ih.symm
        | trans i j k h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
      have hconst : x = x root • (1 : vertexLattice n) := by
        funext i
        simpa using (heq (hconn i)).symm
      rw [hconst]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_singleton (1 : vertexLattice n)))
    · rw [Submodule.span_le]
      intro v hv
      have hv' : v = (1 : vertexLattice n) := by simpa using hv
      rw [hv']
      apply LinearMap.mem_ker.mpr
      funext e
      rw [graphBoundary_apply]
      simp
  let fone : ℤ →ₗ[ℤ] vertexLattice n :=
    { toFun := fun z => z • (1 : vertexLattice n)
      map_add' := by intro x y; simp [add_smul]
      map_smul' := by intro a x; simp }
  have hfone : Function.Injective fone := by
    intro x y hxy
    have hcoord := congrFun hxy root
    simpa [fone] using hcoord
  have hspan : LinearMap.range fone =
      Submodule.span ℤ ({(1 : vertexLattice n)} : Set (vertexLattice n)) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_singleton (1 : vertexLattice n)))
    · rw [Submodule.span_le]
      intro v hv
      have hv' : v = (1 : vertexLattice n) := by simpa using hv
      rw [hv']
      exact LinearMap.mem_range_self fone 1
  have hkerfin : Module.finrank ℤ (LinearMap.ker (graphBoundary A)) = 1 := by
    rw [hkerB, ← hspan, LinearMap.finrank_range_of_inj hfone]
    simp
  have hdimB := (LinearMap.ker (graphBoundary A)).finrank_quotient_add_finrank
  rw [(graphBoundary A).quotKerEquivRange.finrank_eq] at hdimB
  simp [hkerfin] at hdimB
  obtain ⟨p, q, hp, hkerp, hex, hsur, hq⟩ :=
    orthogonal_projection_sequence (edgeLattice A) (graphEdgePairing A)
      (graphEdgePairing_positive_definite A)
      (LinearMap.range (graphBoundary A))
      (graph_image_quotient_torsion_free A)
  have hP : graphEdgeWeightProduct A ≠ 0 := by
    unfold graphEdgeWeightProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    exact ne_of_gt e.2.2
  have hT : Module.IsTorsion ℤ
      (latticeDiscriminantQuotient (graphEdgePairing A)) := by
    intro x
    refine ⟨⟨graphEdgeWeightProduct A,
      mem_nonZeroDivisors_of_ne_zero hP⟩, ?_⟩
    exact graph_discriminant_product_annihilates A x
  have hTc : Module.IsTorsion ℤ (moduleCokernel p) := by
    intro z
    obtain ⟨x, hx⟩ := hq z
    obtain ⟨a, ha⟩ := hT (x := x)
    refine ⟨a, ?_⟩
    calc
      a • z = a • q x := by rw [hx]
      _ = q (a • x) := (q.map_smul (a : ℤ) x).symm
      _ = 0 := by rw [ha, q.map_zero]
  have hTcfin : Module.finrank ℤ (moduleCokernel p) = 0 :=
    Module.IsTorsion.finrank_eq_zero hTc
  have hdimP := (LinearMap.range p).finrank_quotient_add_finrank
  rw [hTcfin, zero_add] at hdimP
  have hdimKp := (LinearMap.ker p).finrank_quotient_add_finrank
  rw [p.quotKerEquivRange.finrank_eq] at hdimKp
  have hdual : Module.finrank ℤ
      (Module.Dual ℤ ↥((graphEdgePairing A).orthogonal (LinearMap.range (graphBoundary A)))) =
      Module.finrank ℤ ↥((graphEdgePairing A).orthogonal (LinearMap.range (graphBoundary A))) := by
    apply Nat.cast_injective (R := Cardinal)
    change (Module.finrank ℤ
        (Module.Dual ℤ ↥((graphEdgePairing A).orthogonal
          (LinearMap.range (graphBoundary A)))) : Cardinal) =
      (Module.finrank ℤ ↥((graphEdgePairing A).orthogonal
        (LinearMap.range (graphBoundary A))) : Cardinal)
    rw [Module.finrank_eq_rank, Submodule.finrank_eq_rank]
    simpa using (Module.Basis.dual_rank_eq
      (Module.Free.chooseBasis ℤ ↥((graphEdgePairing A).orthogonal
        (LinearMap.range (graphBoundary A)))))
  have hkerfinp : Module.finrank ℤ ↥(LinearMap.ker p) =
      Module.finrank ℤ ↥(LinearMap.range (graphBoundary A)) :=
    congrArg (fun S : Submodule ℤ (edgeLattice A) => Module.finrank ℤ S) hkerp.symm
  have horthfin : Module.finrank ℤ
      ↥((graphEdgePairing A).orthogonal (LinearMap.range (graphBoundary A))) =
      Module.finrank ℤ ↥(LinearMap.ker (graphCoboundary A)) :=
    congrArg (fun S : Submodule ℤ (edgeLattice A) => Module.finrank ℤ S)
      (graph_coboundary_ker_eq_orthogonal A).symm
  rw [hdimP, hdual] at hdimKp
  rw [horthfin, hkerfinp] at hdimKp
  simp [edgeLattice, positiveOffDiagonalEdgeCount] at hdimKp
  let b : ℕ := Module.finrank ℤ ↥(LinearMap.ker (graphCoboundary A))
  let c : ℕ := Module.finrank ℤ ↥(LinearMap.range (graphBoundary A))
  let d : ℕ := Fintype.card (positiveEdge A)
  have hB' : c + 1 = n := by
    simpa [c] using hdimB
  have hK' : b + c = d := by
    simpa [b, c, d] using hdimKp
  have harith : b = d + 1 - n := by
    omega
  simpa [b, d, positiveOffDiagonalEdgeCount] using harith

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
