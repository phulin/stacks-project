import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Free
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
  sorry

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
  sorry

theorem recurring_symmetric_real_range_finrank {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hm : ∀ i, 0 < m i) (hAm : Matrix.mulVec A m = 0)
    (hconnected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = n - 1 := by
  sorry

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
