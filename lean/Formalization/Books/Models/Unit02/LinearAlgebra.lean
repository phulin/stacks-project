import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

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
  sorry

/-! The weighted strict diagonal-dominance criterion. -/
theorem recurring_weighted_diagonal_dominance {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i)
    (hdominant : ∀ i,
      norm (A i i * (m i : ℂ)) >
        (Finset.univ : Finset (Fin n)).sum
          (fun j => if j ≠ i then norm (A i j * (m j : ℂ)) else 0)) :
    Matrix.det A ≠ 0 := by
  sorry

/-! The column-weighted matrix used in the proof of weighted diagonal dominance. -/
def weightedComplexMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (m : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A i j * (m j : ℂ)

/-! Determinant scaling for the weighted matrix. -/
theorem weightedComplexMatrix_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (m : Fin n → ℝ) :
    Matrix.det (weightedComplexMatrix A m) =
      (Finset.univ : Finset (Fin n)).prod (fun i => (m i : ℂ)) * Matrix.det A := by
  sorry

/-! The vector obtained by retaining the coordinates in a subset and weighting them by `m`. -/
def weightedSubsetVector {n : ℕ} (m : Fin n → ℝ) (I : Set (Fin n)) : Fin n → ℝ :=
  by
    classical
    exact fun i => if i ∈ I then m i else 0

/-!
The equality condition for the real recurring-matrix lemma.  The two displayed
zero conditions express the symmetric cut condition needed for the kernel
description when the matrix is not assumed symmetric.
-/
def kernelIndicatorCondition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n → ℝ) (I : Set (Fin n)) : Prop :=
  (∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) ∧
    (∀ ⦃i j⦄, i ∉ I → j ∈ I → A i j = 0) ∧
    ∀ i, i ∈ I →
      -A i i * m i =
        (Finset.univ : Finset (Fin n)).sum (fun j => if j ≠ i then A i j * m j else 0)

/-! The kernel of a real recurring matrix is spanned by the equality indicators. -/
theorem recurring_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ)
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

def submoduleInclusionRange {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M) : Submodule ℤ M :=
  by
    letI : Module ℤ N := N.module
    exact LinearMap.range N.subtype

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

/-! The projection exact sequence underlying the orthogonal decomposition. -/
theorem orthogonal_projection_sequence
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L]
    [Module.Finite ℤ L] (B : LinearMap.BilinForm ℤ L)
    (hB : IsPositiveDefiniteIntegralForm B) (A : Submodule ℤ L)
    (hquotient : Module.IsTorsionFree ℤ (L ⧸ A)) :
    ∃ p : L →ₗ[ℤ] Module.Dual ℤ (B.orthogonal A),
      submoduleInclusionRange A = LinearMap.ker p ∧
        Function.Exact p (LinearMap.range p).mkQ ∧
          Function.Surjective (LinearMap.range p).mkQ := by
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

/-! The `ell`-primary torsion submodule of a matrix cokernel. -/
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

/-! The diagonal rescaling used to reduce the integer lemma to `m = 1`. -/
def integerDiagonalMatrix {n : ℕ} (m : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  by
    classical
    exact Matrix.diagonal m

def weightedIntegerMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (m : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => m i * A i j * m j

theorem weightedIntegerMatrix_comp {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ) :
    (Matrix.toLin' (integerDiagonalMatrix m)).comp
        ((Matrix.toLin' A).comp (Matrix.toLin' (integerDiagonalMatrix m))) =
      Matrix.toLin' (weightedIntegerMatrix A m) := by
  sorry

theorem diagonal_matrix_primary_torsion_finrank_zero {n : ℕ}
    (m : Fin n → ℤ) (ell : ℕ) (hell : Nat.Prime ell)
    (hcoprime : ∀ i, Nat.Coprime ell (Int.natAbs (m i))) :
    matrixPrimaryTorsionFinrank (integerDiagonalMatrix m) ell hell = 0 := by
  sorry

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
  sorry

theorem graphCoboundary_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (y : edgeLattice A) (i : Fin n) :
    graphCoboundary A y i =
      (Finset.univ : Finset (positiveEdge A)).sum
        (fun e => if edgeSource e = i then edgeWeight e * y e
          else if edgeTarget e = i then -(edgeWeight e * y e) else 0) := by
  sorry

theorem graphVertexPairing_positive_definite (n : ℕ) :
    IsPositiveDefiniteIntegralForm (graphVertexPairing n) := by
  sorry

theorem graphEdgePairing_positive_definite {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    IsPositiveDefiniteIntegralForm (graphEdgePairing A) := by
  sorry

theorem graphBoundary_adjoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    LinearMap.IsAdjointPair (graphVertexPairing n) (graphEdgePairing A)
      (graphBoundary A) (graphCoboundary A) := by
  sorry

/-! The positive off-diagonal edge count of the graph attached to a symmetric matrix. -/
def positiveOffDiagonalEdgeCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  Fintype.card (positiveEdge A)

def graphEdgeWeightProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  (Finset.univ : Finset (positiveEdge A)).prod edgeWeight

theorem graph_coboundary_ker_eq_orthogonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    LinearMap.ker (graphCoboundary A) =
      (graphEdgePairing A).orthogonal (LinearMap.range (graphBoundary A)) := by
  sorry

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
  sorry

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
  sorry

theorem graph_kernel_quotient_torsion_free {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) :
    Module.IsTorsionFree ℤ
      (edgeLattice A ⧸ LinearMap.ker (graphCoboundary A)) := by
  sorry

theorem graph_image_quotient_torsion_free {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hconnected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) :
    Module.IsTorsionFree ℤ
      (edgeLattice A ⧸ LinearMap.range (graphBoundary A)) := by
  sorry

theorem graph_coboundary_kernel_finrank {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : ∀ i j, A i j = A j i)
    (hoffdiag : ∀ ⦃i j⦄, i ≠ j → 0 ≤ A i j)
    (hconnected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃i j⦄, i ∈ I → j ∉ I → A i j = 0) :
    Module.finrank ℤ (LinearMap.ker (graphCoboundary A)) =
      1 - n + positiveOffDiagonalEdgeCount A := by
  sorry

/-! The literal coprimality condition used in the integer recurring lemma. -/
def CoprimeToMatrixAndVector {n : ℕ} (ell : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ) : Prop :=
  (∀ i j, Nat.Coprime ell (Int.natAbs (A i j))) ∧
    ∀ i, Nat.Coprime ell (Int.natAbs (m i))

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
      1 - n + positiveOffDiagonalEdgeCount A := by
  sorry

end Formalization.Books.Models.Unit02
