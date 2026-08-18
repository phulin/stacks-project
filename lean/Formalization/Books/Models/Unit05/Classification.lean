import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Formalization.Books.Models.Unit03.NumericalTypes

/-!
# Classification of proper subgraphs

Formal statements from Chapter 5 of *Semistable Reduction*.  The source uses
indices `1, ..., n`; this file uses `Fin n`.  The local data of a subgraph is
kept separate from the ambient numerical type so that the displayed matrices
can be used directly in later proofs.
-/

noncomputable section

open scoped BigOperators

namespace Formalization.Books.Models.Unit05

open Formalization.Books.Models.Unit03

/-! A finite piece of the `m`, `a`, and `w` data. -/
structure LocalNumericalData (k : ℕ) where
  m : Fin k → ℤ
  a : Matrix (Fin k) (Fin k) ℤ
  w : Fin k → ℤ

/-! An ordered collection of distinct `(-2)`-indices in a numerical type. -/
structure MinusTwoSubgraph (T : NumericalType) (k : ℕ) where
  index : Fin k → Fin T.n
  index_injective : Function.Injective index
  minus_two : ∀ i, IsMinusTwoIndex T (index i)

/-! The local `m`, `a`, and `w` data induced by a subgraph. -/
def localData {T : NumericalType} {k : ℕ} (S : MinusTwoSubgraph T k) :
    LocalNumericalData k :=
  { m := fun i => T.m (S.index i)
    a := fun i j => T.a (S.index i) (S.index j)
    w := fun i => T.w (S.index i) }

/-! The full numerical type viewed as local data. -/
def ambientData (T : NumericalType) : LocalNumericalData T.n :=
  { m := T.m, a := T.a, w := T.w }

def ambientDataAt {T : NumericalType} {k : ℕ} (h : T.n = k) :
    LocalNumericalData k :=
  h ▸ ambientData T

theorem local_m_pos {T : NumericalType} {k : ℕ} (S : MinusTwoSubgraph T k) :
    ∀ i, 0 < (localData S).m i := by
  intro i
  exact T.m_pos (S.index i)

theorem local_w_pos {T : NumericalType} {k : ℕ} (S : MinusTwoSubgraph T k) :
    ∀ i, 0 < (localData S).w i := by
  intro i
  exact T.w_pos (S.index i)

theorem local_a_symmetric {T : NumericalType} {k : ℕ} (S : MinusTwoSubgraph T k) :
    ∀ i j, (localData S).a i j = (localData S).a j i := by
  intro i j
  exact T.a_symmetric _ _

/-! Reordering all three kinds of local data by the same permutation. -/
def reindexLocalData {k : ℕ} (D : LocalNumericalData k) (e : Fin k ≃ Fin k) :
    LocalNumericalData k :=
  { m := fun i => D.m (e i)
    a := fun i j => D.a (e i) (e j)
    w := fun i => D.w (e i) }

def UpToReordering {k : ℕ} (D : LocalNumericalData k)
    (P : LocalNumericalData k → Prop) : Prop :=
  ∃ e : Fin k ≃ Fin k, P (reindexLocalData D e)

/-! The source's “up to reversing the order” convention. -/
def UpToReversal {k : ℕ} (D : LocalNumericalData k)
    (P : LocalNumericalData k → Prop) : Prop :=
  P D ∨ ∃ e : Fin k ≃ Fin k,
    (∀ i, (e i).val + i.val + 1 = k) ∧ P (reindexLocalData D e)

/-! Matrix and vector scaling used to write all displayed configurations. -/
def scalarMatrix {k : ℕ} (C : Matrix (Fin k) (Fin k) ℤ) (r : ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j => r * C i j

def scalarVector {k : ℕ} (v : Fin k → ℤ) (r : ℤ) : Fin k → ℤ :=
  fun i => r * v i

def realizesPattern {k : ℕ} (D : LocalNumericalData k)
    (C : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ)
    (mCondition : (Fin k → ℤ) → Prop) : Prop :=
  ∃ r : ℤ, 0 < r ∧ D.a = scalarMatrix C r ∧
    D.w = scalarVector v r ∧ (∀ i, 0 < D.m i) ∧ mCondition D.m

def realizesAW {k : ℕ} (D : LocalNumericalData k)
    (C : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ) : Prop :=
  ∃ r : ℤ, 0 < r ∧ D.a = scalarMatrix C r ∧ D.w = scalarVector v r ∧
    ∀ i, 0 < D.m i

/-! Small matrix constructors.  Their entries are indexed by natural values. -/
def pathMatrix (k : ℕ) (diagonal : Fin k → ℤ) (edge : ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal i
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then edge else 0

def pathLastMatrix (k : ℕ) (diagonal : ℤ) (lastDiagonal : ℤ)
    (edge : ℤ) (lastEdge : ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then
      if i.val + 1 = k then lastDiagonal else diagonal
    else if i.val + 1 = j.val then
      if j.val + 1 = k then lastEdge else edge
    else if j.val + 1 = i.val then
      if i.val + 1 = k then lastEdge else edge
    else 0

def pathFirstMatrix (k : ℕ) (diagonal : Fin k → ℤ) (firstEdge edge : ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal i
    else if i.val + 1 = j.val then
      if i.val = 0 then firstEdge else edge
    else if j.val + 1 = i.val then
      if j.val = 0 then firstEdge else edge
    else 0

def starMatrix (k center : ℕ) (diagonal : Fin k → ℤ) (edge : ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal i
    else if i.val = center ∨ j.val = center then edge else 0

def branchPrefixMatrix (k center leaf₁ leaf₂ : ℕ) (diagonal : ℤ) (edge : ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal
    else if (i.val + 1 = j.val ∧ j.val ≤ center) ∨
        (j.val + 1 = i.val ∧ i.val ≤ center) then edge
    else if (i.val = center ∧ j.val = leaf₁) ∨
        (i.val = leaf₁ ∧ j.val = center) then edge
    else if (i.val = center ∧ j.val = leaf₂) ∨
        (i.val = leaf₂ ∧ j.val = center) then edge
    else 0

def pathUntilLeafMatrix (k stop center leaf : ℕ) (diagonal : ℤ) (edge : ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal
    else if (i.val + 1 = j.val ∧ j.val ≤ stop) ∨
        (j.val + 1 = i.val ∧ i.val ≤ stop) then edge
    else if (i.val = center ∧ j.val = leaf) ∨
        (i.val = leaf ∧ j.val = center) then edge
    else 0

def doubleTripleMatrix (t : ℕ) : Matrix (Fin (t + 2)) (Fin (t + 2)) ℤ :=
  fun i j =>
    if i = j then -2
    else if (i.val + 1 = j.val ∧ 1 ≤ i.val ∧ j.val ≤ t) ∨
        (j.val + 1 = i.val ∧ 1 ≤ j.val ∧ i.val ≤ t) then 1
    else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) then 1
    else if (i.val = t - 1 ∧ j.val = t + 1) ∨
        (i.val = t + 1 ∧ j.val = t - 1) then 1
    else 0

def constantVector {k : ℕ} (c : ℤ) : Fin k → ℤ := fun _ => c

def lastVector (k : ℕ) (c last : ℤ) : Fin k → ℤ :=
  fun i => if i.val + 1 = k then last else c

def firstRestVector (k : ℕ) (first rest : ℤ) : Fin k → ℤ :=
  fun i => if i.val = k - 1 then rest else first

/-! The integer inequalities on the `m`-coordinates in the finite cases. -/
def mConditionA2 (m : Fin 2 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0

def mConditionB2 (m : Fin 2 → ℤ) : Prop :=
  m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0

def mConditionG2 (m : Fin 2 → ℤ) : Prop :=
  2 * m 0 ≥ 3 * m 1 ∧ 2 * m 1 ≥ m 0

def mConditionA3 (m : Fin 3 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧ 2 * m 2 ≥ m 1

def mConditionC3 (m : Fin 3 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + 2 * m 2 ∧ 2 * m 2 ≥ m 1

def mConditionB3 (m : Fin 3 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧ m 2 ≥ m 1

def mConditionA4 (m : Fin 4 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧
    2 * m 2 ≥ m 1 + m 3 ∧ 2 * m 3 ≥ m 2

def mConditionC4 (m : Fin 4 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧
    2 * m 2 ≥ m 1 + 2 * m 3 ∧ 2 * m 3 ≥ m 2

def mConditionB4 (m : Fin 4 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧
    2 * m 2 ≥ m 1 + m 3 ∧ m 3 ≥ m 2

def mConditionF4 (m : Fin 4 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + 2 * m 2 ∧
    2 * m 2 ≥ m 1 + m 3 ∧ 2 * m 3 ≥ m 2

def mConditionD4 (m : Fin 4 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 + m 2 + m 3 ∧ 2 * m 1 ≥ m 0 ∧
    2 * m 2 ≥ m 0 ∧ 2 * m 3 ≥ m 0

def mConditionA5 (m : Fin 5 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧
    2 * m 2 ≥ m 1 + m 3 ∧ 2 * m 3 ≥ m 2 + m 4 ∧ 2 * m 4 ≥ m 3

def mConditionC5 (m : Fin 5 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧
    2 * m 2 ≥ m 1 + 2 * m 3 ∧ 2 * m 3 ≥ m 2 + m 4 ∧ 2 * m 4 ≥ m 3

def mConditionB5 (m : Fin 5 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧
    2 * m 2 ≥ m 1 + m 3 ∧ 2 * m 3 ≥ m 2 + m 4 ∧ m 4 ≥ m 3

def mConditionD5 (m : Fin 5 → ℤ) : Prop :=
  2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧
    2 * m 2 ≥ m 1 + m 3 + m 4 ∧ 2 * m 3 ≥ m 2 ∧ 2 * m 4 ≥ m 2

/-! The configurations in the first five classification lemmas. -/
def isA2 (D : LocalNumericalData 2) : Prop :=
  realizesPattern D (pathMatrix 2 (constantVector (-2)) 1) (constantVector 1) mConditionA2

def isB2 (D : LocalNumericalData 2) : Prop :=
  realizesPattern D (pathLastMatrix 2 (-2) (-4) 2 2) (lastVector 2 1 2) mConditionB2

def isG2 (D : LocalNumericalData 2) : Prop :=
  realizesPattern D (pathLastMatrix 2 (-2) (-6) 3 3) (lastVector 2 1 3) mConditionG2

/-! The two full (genus-one) singular configurations discussed before the
proper-subgraph lemma. -/
def isTwoCycle (D : LocalNumericalData 2) : Prop :=
  realizesAW D (pathMatrix 2 (constantVector (-2)) 2) (constantVector 1)

def isUp4 (D : LocalNumericalData 2) : Prop :=
  realizesAW D (pathLastMatrix 2 (-2) (-4) 4 4) (lastVector 2 1 4)

def isA3 (D : LocalNumericalData 3) : Prop :=
  realizesPattern D (pathMatrix 3 (constantVector (-2)) 1) (constantVector 1) mConditionA3

def isC3 (D : LocalNumericalData 3) : Prop :=
  realizesPattern D (pathLastMatrix 3 (-2) (-4) 1 2) (lastVector 3 1 2) mConditionC3

def isB3 (D : LocalNumericalData 3) : Prop :=
  realizesPattern D (pathLastMatrix 3 (-4) (-2) 2 2) (lastVector 3 2 1) mConditionB3

def isA4 (D : LocalNumericalData 4) : Prop :=
  realizesPattern D (pathMatrix 4 (constantVector (-2)) 1) (constantVector 1) mConditionA4

def isC4 (D : LocalNumericalData 4) : Prop :=
  realizesPattern D (pathLastMatrix 4 (-2) (-4) 1 2) (lastVector 4 1 2) mConditionC4

def isB4 (D : LocalNumericalData 4) : Prop :=
  realizesPattern D (pathLastMatrix 4 (-4) (-2) 2 2) (lastVector 4 2 1) mConditionB4

def isF4 (D : LocalNumericalData 4) : Prop :=
  realizesPattern D (pathFirstMatrix 4 (fun i => if i.val < 2 then -2 else -4) 1 2)
    (fun i => if i.val < 2 then 1 else 2) mConditionF4

def isD4 (D : LocalNumericalData 4) : Prop :=
  realizesPattern D (starMatrix 4 0 (constantVector (-2)) 1) (constantVector 1) mConditionD4

def isA5 (D : LocalNumericalData 5) : Prop :=
  realizesPattern D (pathMatrix 5 (constantVector (-2)) 1) (constantVector 1) mConditionA5

def isC5 (D : LocalNumericalData 5) : Prop :=
  realizesPattern D (pathLastMatrix 5 (-2) (-4) 1 2) (lastVector 5 1 2) mConditionC5

def isB5 (D : LocalNumericalData 5) : Prop :=
  realizesPattern D (pathLastMatrix 5 (-4) (-2) 2 2) (lastVector 5 2 1) mConditionB5

def isD5 (D : LocalNumericalData 5) : Prop :=
  realizesPattern D (branchPrefixMatrix 5 2 3 4 (-2) 1) (constantVector 1) mConditionD5

/-! The unbounded path and branch configurations. -/
def isAn {k : ℕ} (D : LocalNumericalData k) : Prop :=
  realizesAW D (pathMatrix k (constantVector (-2)) 1) (constantVector 1)

def isCn {k : ℕ} (D : LocalNumericalData k) : Prop :=
  realizesAW D (pathLastMatrix k (-2) (-4) 1 2) (lastVector k 1 2)

def isBn {k : ℕ} (D : LocalNumericalData k) : Prop :=
  realizesAW D (pathLastMatrix k (-4) (-2) 2 2) (lastVector k 2 1)

def isDn {k : ℕ} (D : LocalNumericalData k) : Prop :=
  realizesAW D (pathUntilLeafMatrix k (k - 2) (k - 3) (k - 1) (-2) 1)
    (constantVector 1)

def isE6 (D : LocalNumericalData 6) : Prop :=
  realizesPattern D (pathUntilLeafMatrix 6 4 2 5 (-2) 1) (constantVector 1)
    (fun m => 2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧
      2 * m 2 ≥ m 1 + m 3 + m 5 ∧ 2 * m 3 ≥ m 2 + m 4 ∧
      2 * m 4 ≥ m 2 ∧ 2 * m 5 ≥ m 2)

def isE7 (D : LocalNumericalData 7) : Prop :=
  realizesPattern D (pathUntilLeafMatrix 7 5 3 6 (-2) 1) (constantVector 1)
    (fun m => 2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧ 2 * m 2 ≥ m 1 + m 3 ∧
      2 * m 3 ≥ m 2 + m 4 + m 6 ∧ 2 * m 4 ≥ m 3 + m 5 ∧
      2 * m 5 ≥ m 4 ∧ 2 * m 6 ≥ m 3)

def isE8 (D : LocalNumericalData 8) : Prop :=
  realizesPattern D (pathUntilLeafMatrix 8 6 4 7 (-2) 1) (constantVector 1)
    (fun m => 2 * m 0 ≥ m 1 ∧ 2 * m 1 ≥ m 0 + m 2 ∧ 2 * m 2 ≥ m 1 + m 3 ∧
      2 * m 3 ≥ m 2 + m 4 ∧ 2 * m 4 ≥ m 3 + m 5 + m 7 ∧
      2 * m 5 ≥ m 4 + m 6 ∧ 2 * m 6 ≥ m 5 ∧ 2 * m 7 ≥ m 4)

/-! Edge-pattern predicates used by the hypotheses and nonexistence lemmas. -/
def hasEdgeAt {k : ℕ} (D : LocalNumericalData k) (p q : ℕ) : Prop :=
  ∃ i j : Fin k, i.val = p ∧ j.val = q ∧ 0 < D.a i j

def hasPathEdges {k : ℕ} (D : LocalNumericalData k) : Prop :=
  ∀ ⦃i j : Fin k⦄, i.val + 1 = j.val → 0 < D.a i j

def hasTripleAtLeastTwoEdges (D : LocalNumericalData 3) : Prop :=
  (hasEdgeAt D 0 1 ∧ hasEdgeAt D 0 2) ∨
    (hasEdgeAt D 0 1 ∧ hasEdgeAt D 1 2) ∨
      (hasEdgeAt D 0 2 ∧ hasEdgeAt D 1 2)

def hasStarEdges5 (D : LocalNumericalData 5) : Prop :=
  hasEdgeAt D 0 1 ∧ hasEdgeAt D 0 2 ∧ hasEdgeAt D 0 3 ∧ hasEdgeAt D 0 4

def hasD5Edges (D : LocalNumericalData 5) : Prop :=
  hasEdgeAt D 0 1 ∧ hasEdgeAt D 1 2 ∧ hasEdgeAt D 2 3 ∧ hasEdgeAt D 2 4

def hasE6Edges (D : LocalNumericalData 6) : Prop :=
  hasEdgeAt D 0 1 ∧ hasEdgeAt D 1 2 ∧ hasEdgeAt D 2 3 ∧
    hasEdgeAt D 3 4 ∧ hasEdgeAt D 2 5

def hasE7Edges (D : LocalNumericalData 7) : Prop :=
  hasEdgeAt D 0 1 ∧ hasEdgeAt D 1 2 ∧ hasEdgeAt D 2 3 ∧
    hasEdgeAt D 3 4 ∧ hasEdgeAt D 4 5 ∧ hasEdgeAt D 3 6

def hasE8Edges (D : LocalNumericalData 8) : Prop :=
  hasEdgeAt D 0 1 ∧ hasEdgeAt D 1 2 ∧ hasEdgeAt D 2 3 ∧
    hasEdgeAt D 3 4 ∧ hasEdgeAt D 4 5 ∧ hasEdgeAt D 5 6 ∧ hasEdgeAt D 4 7

def hasE6CompletedEdges (D : LocalNumericalData 7) : Prop :=
  hasEdgeAt D 0 1 ∧ hasEdgeAt D 1 2 ∧ hasEdgeAt D 3 4 ∧
    hasEdgeAt D 4 2 ∧ hasEdgeAt D 5 6 ∧ hasEdgeAt D 6 2

def hasE7CompletedEdges (D : LocalNumericalData 8) : Prop :=
  hasEdgeAt D 0 1 ∧ hasEdgeAt D 1 2 ∧ hasEdgeAt D 2 3 ∧
    hasEdgeAt D 3 4 ∧ hasEdgeAt D 4 5 ∧ hasEdgeAt D 5 6 ∧ hasEdgeAt D 7 3

def hasE8CompletedEdges (D : LocalNumericalData 9) : Prop :=
  hasEdgeAt D 0 1 ∧ hasEdgeAt D 1 2 ∧ hasEdgeAt D 2 3 ∧
    hasEdgeAt D 3 4 ∧ hasEdgeAt D 4 5 ∧ hasEdgeAt D 5 6 ∧
      hasEdgeAt D 6 7 ∧ hasEdgeAt D 8 4

def hasDoubleTripleEdges {t : ℕ} (D : LocalNumericalData (t + 2)) : Prop :=
  (∀ ⦃i j : Fin (t + 2)⦄, i.val + 1 = j.val → 1 ≤ i.val → j.val ≤ t →
      0 < D.a i j) ∧
    hasEdgeAt D 0 2 ∧ hasEdgeAt D (t - 1) (t + 1)

/-! Rational ratios appearing in the determinant computations. -/
def edgeRatio {k : ℕ} (D : LocalNumericalData k) (i j : Fin k) : ℚ :=
  (D.a i j : ℚ) ^ 2 / ((D.w i : ℚ) * (D.w j : ℚ))

def tripleProductRatio (D : LocalNumericalData 3) : ℚ :=
  (D.a 0 1 : ℚ) * D.a 0 2 * D.a 1 2 /
    ((D.w 0 : ℚ) * D.w 1 * D.w 2)

def fourProductRatio (D : LocalNumericalData 4) : ℚ :=
  (D.a 0 1 : ℚ) * D.a 0 3 * D.a 1 2 * D.a 2 3 /
    ((D.w 0 : ℚ) * D.w 1 * D.w 2 * D.w 3)

def fiveProductRatio (D : LocalNumericalData 5) : ℚ :=
  (D.a 0 1 : ℚ) * D.a 1 2 * D.a 2 3 * D.a 3 4 * D.a 0 4 /
    ((D.w 0 : ℚ) * D.w 1 * D.w 2 * D.w 3 * D.w 4)

/-! Raw determinant expansions from the source footnotes. -/
theorem determinant_two_by_two_formula (D : LocalNumericalData 2)
    (hdiag : ∀ i, D.a i i = -2 * D.w i) (hsymm : ∀ i j, D.a i j = D.a j i) :
    Matrix.det D.a = 4 * D.w 0 * D.w 1 - D.a 0 1 ^ 2 := by
  simp [Matrix.det_fin_two, hdiag, hsymm]
  ring

theorem determinant_three_by_three_formula (D : LocalNumericalData 3)
    (hdiag : ∀ i, D.a i i = -2 * D.w i) (hsymm : ∀ i j, D.a i j = D.a j i) :
    Matrix.det D.a =
      -8 * D.w 0 * D.w 1 * D.w 2 + 2 * D.a 0 1 ^ 2 * D.w 2 +
        2 * D.a 1 2 ^ 2 * D.w 0 + 2 * D.a 0 2 ^ 2 * D.w 1 +
        2 * D.a 0 1 * D.a 0 2 * D.a 1 2 := by
  simp [Matrix.det_fin_three, hdiag, hsymm]
  ring

theorem determinant_four_by_four_formula (D : LocalNumericalData 4)
    (hdiag : ∀ i, D.a i i = -2 * D.w i) (hsymm : ∀ i j, D.a i j = D.a j i)
    (_hzero : D.a 0 2 = 0 ∧ D.a 1 3 = 0) :
    Matrix.det D.a =
      16 * D.w 0 * D.w 1 * D.w 2 * D.w 3 -
        4 * D.a 0 1 ^ 2 * D.w 2 * D.w 3 -
        4 * D.a 1 2 ^ 2 * D.w 0 * D.w 3 -
        4 * D.a 2 3 ^ 2 * D.w 0 * D.w 1 -
        4 * D.a 0 3 ^ 2 * D.w 1 * D.w 2 +
        D.a 0 1 ^ 2 * D.a 2 3 ^ 2 + D.a 1 2 ^ 2 * D.a 0 3 ^ 2 -
        2 * D.a 0 1 * D.a 0 3 * D.a 1 2 * D.a 2 3 := by
  rcases _hzero with ⟨h02, h13⟩
  have h10 : D.a 1 0 = D.a 0 1 := hsymm 1 0
  have h21 : D.a 2 1 = D.a 1 2 := hsymm 2 1
  have h32 : D.a 3 2 = D.a 2 3 := hsymm 3 2
  have h30 : D.a 3 0 = D.a 0 3 := hsymm 3 0
  have h20 : D.a 2 0 = 0 := (hsymm 2 0).trans h02
  have h31 : D.a 3 1 = 0 := (hsymm 3 1).trans h13
  simp [Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three, Fin.succAbove,
    Fin.sum_univ_succ, hdiag, h02, h13, h10, h21, h32, h30, h20, h31] <;> ring

theorem determinant_five_by_five_formula (D : LocalNumericalData 5)
    (hdiag : ∀ i, D.a i i = -2 * D.w i) (hsymm : ∀ i j, D.a i j = D.a j i)
    (_hzero : D.a 0 2 = 0 ∧ D.a 0 3 = 0 ∧ D.a 1 3 = 0 ∧
      D.a 1 4 = 0 ∧ D.a 2 4 = 0) :
    Matrix.det D.a =
      -32 * D.w 0 * D.w 1 * D.w 2 * D.w 3 * D.w 4 +
        8 * D.a 0 1 ^ 2 * D.w 2 * D.w 3 * D.w 4 +
        8 * D.a 1 2 ^ 2 * D.w 0 * D.w 3 * D.w 4 +
        8 * D.a 2 3 ^ 2 * D.w 0 * D.w 1 * D.w 4 +
        8 * D.a 3 4 ^ 2 * D.w 0 * D.w 1 * D.w 2 +
        8 * D.a 0 4 ^ 2 * D.w 1 * D.w 2 * D.w 3 -
        2 * D.a 0 1 ^ 2 * D.a 2 3 ^ 2 * D.w 4 -
        2 * D.a 0 1 ^ 2 * D.a 3 4 ^ 2 * D.w 1 -
        2 * D.a 1 2 ^ 2 * D.a 3 4 ^ 2 * D.w 0 -
        2 * D.a 0 4 ^ 2 * D.a 1 2 ^ 2 * D.w 3 -
        2 * D.a 0 4 ^ 2 * D.a 2 3 ^ 2 * D.w 1 +
        2 * D.a 0 1 * D.a 1 2 * D.a 2 3 * D.a 3 4 * D.a 0 4 := by
  sorry

theorem star_four_by_four_determinant_formula (D : LocalNumericalData 4)
    (hdiag : ∀ i, D.a i i = -2 * D.w i) (hsymm : ∀ i j, D.a i j = D.a j i)
    (_hzero : D.a 1 2 = 0 ∧ D.a 1 3 = 0 ∧ D.a 2 3 = 0) :
    Matrix.det D.a =
      16 * D.w 0 * D.w 1 * D.w 2 * D.w 3 -
        4 * D.a 0 1 ^ 2 * D.w 2 * D.w 3 -
        4 * D.a 0 2 ^ 2 * D.w 1 * D.w 3 -
        4 * D.a 0 3 ^ 2 * D.w 1 * D.w 2 := by
  rcases _hzero with ⟨h12, h13, h23⟩
  have h10 : D.a 1 0 = D.a 0 1 := hsymm 1 0
  have h20 : D.a 2 0 = D.a 0 2 := hsymm 2 0
  have h30 : D.a 3 0 = D.a 0 3 := hsymm 3 0
  have h21 : D.a 2 1 = 0 := (hsymm 2 1).trans h12
  have h31 : D.a 3 1 = 0 := (hsymm 3 1).trans h13
  have h32 : D.a 3 2 = 0 := (hsymm 3 2).trans h23
  simp [Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three, Fin.succAbove,
    Fin.sum_univ_succ, hdiag, h12, h13, h23, h10, h20, h30, h21, h31, h32]
  ring

/-! The base-case observation and the source's determinant identities. -/
theorem singleton_minus_two_constraints (T : NumericalType) :
    ∀ i, IsMinusTwoIndex T i → T.w i ∣ T.a i i ∧ T.a i i < 0 := by
  intro i hi
  rcases hi with ⟨_, ha⟩
  constructor
  · rw [ha]
    use -2
    ring
  · rw [ha]
    nlinarith [T.w_pos i]

theorem pair_singular_ratio_equation (D : LocalNumericalData 2)
    (hdiag : ∀ i, D.a i i = -2 * D.w i)
    (hsymm : ∀ i j, D.a i j = D.a j i)
    (hw : ∀ i, 0 < D.w i) (hdet : Matrix.det D.a = 0) :
    4 = edgeRatio D 0 1 := by
  have hformula := determinant_two_by_two_formula D hdiag hsymm
  rw [hformula] at hdet
  have ha : D.a 0 1 ^ 2 = 4 * D.w 0 * D.w 1 := by omega
  unfold edgeRatio
  have hw0 : (D.w 0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 0))
  have hw1 : (D.w 1 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 1))
  field_simp
  exact_mod_cast ha.symm

theorem pair_full_singular_cases (T : NumericalType) (hn : T.n = 2)
    (hall : ∀ i, IsMinusTwoIndex T i)
    (hpos : 0 < (ambientDataAt hn).a 0 1) :
    UpToReordering (ambientDataAt hn) (fun D => isTwoCycle D ∨ isUp4 D) ∧
      genus T = 1 := by
  sorry

theorem triple_singular_ratio_equation (D : LocalNumericalData 3)
    (hdiag : ∀ i, D.a i i = -2 * D.w i)
    (hsymm : ∀ i j, D.a i j = D.a j i)
    (hw : ∀ i, 0 < D.w i) (hdet : Matrix.det D.a = 0) :
    4 = edgeRatio D 0 1 + edgeRatio D 1 2 + edgeRatio D 0 2 +
      tripleProductRatio D := by
  rw [determinant_three_by_three_formula D hdiag hsymm] at hdet
  unfold edgeRatio tripleProductRatio
  have hw0 : (D.w 0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 0))
  have hw1 : (D.w 1 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 1))
  have hw2 : (D.w 2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 2))
  field_simp
  norm_cast
  ring_nf at hdet
  linarith only [hdet]

theorem triple_product_ratio_square (D : LocalNumericalData 3)
    (hw : ∀ i, 0 < D.w i) :
    (tripleProductRatio D) ^ 2 = edgeRatio D 0 1 * edgeRatio D 1 2 * edgeRatio D 0 2 := by
  unfold tripleProductRatio edgeRatio
  have hw0 : (D.w 0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 0))
  have hw1 : (D.w 1 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 1))
  have hw2 : (D.w 2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 2))
  field_simp

theorem four_singular_ratio_equation (D : LocalNumericalData 4)
    (hdiag : ∀ i, D.a i i = -2 * D.w i)
    (hsymm : ∀ i j, D.a i j = D.a j i)
    (_hzero : D.a 0 2 = 0 ∧ D.a 1 3 = 0)
    (hw : ∀ i, 0 < D.w i) (hdet : Matrix.det D.a = 0) :
    16 + edgeRatio D 0 1 * edgeRatio D 2 3 + edgeRatio D 1 2 * edgeRatio D 0 3 =
      4 * edgeRatio D 0 1 + 4 * edgeRatio D 1 2 + 4 * edgeRatio D 2 3 +
        4 * edgeRatio D 0 3 + 2 * fourProductRatio D := by
  rw [determinant_four_by_four_formula D hdiag hsymm _hzero] at hdet
  unfold edgeRatio fourProductRatio
  have hw0 : (D.w 0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 0))
  have hw1 : (D.w 1 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 1))
  have hw2 : (D.w 2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 2))
  have hw3 : (D.w 3 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 3))
  field_simp
  norm_cast
  ring_nf at hdet
  linarith only [hdet]

theorem four_product_ratio_square (D : LocalNumericalData 4)
    (hw : ∀ i, 0 < D.w i) :
    (fourProductRatio D) ^ 2 =
      edgeRatio D 0 1 * edgeRatio D 1 2 * edgeRatio D 2 3 * edgeRatio D 0 3 := by
  unfold fourProductRatio edgeRatio
  have hw0 : (D.w 0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 0))
  have hw1 : (D.w 1 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 1))
  have hw2 : (D.w 2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 2))
  have hw3 : (D.w 3 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 3))
  field_simp

theorem five_singular_ratio_equation (D : LocalNumericalData 5)
    (hdiag : ∀ i, D.a i i = -2 * D.w i)
    (hsymm : ∀ i j, D.a i j = D.a j i)
    (_hzero : D.a 0 2 = 0 ∧ D.a 0 3 = 0 ∧ D.a 1 3 = 0 ∧
      D.a 1 4 = 0 ∧ D.a 2 4 = 0)
    (hw : ∀ i, 0 < D.w i) (hdet : Matrix.det D.a = 0) :
    16 + edgeRatio D 0 1 * edgeRatio D 2 3 + edgeRatio D 0 1 * edgeRatio D 3 4 +
        edgeRatio D 1 2 * edgeRatio D 3 4 + edgeRatio D 0 4 * edgeRatio D 1 2 +
        edgeRatio D 0 4 * edgeRatio D 2 3 =
      4 * edgeRatio D 0 1 + 4 * edgeRatio D 1 2 + 4 * edgeRatio D 2 3 +
        4 * edgeRatio D 3 4 + 4 * edgeRatio D 0 4 + fiveProductRatio D := by
  rcases _hzero with ⟨h02, h03, h13, h14, h24⟩
  have h10 : D.a 1 0 = D.a 0 1 := hsymm 1 0
  have h21 : D.a 2 1 = D.a 1 2 := hsymm 2 1
  have h32 : D.a 3 2 = D.a 2 3 := hsymm 3 2
  have h43 : D.a 4 3 = D.a 3 4 := hsymm 4 3
  have h40 : D.a 4 0 = D.a 0 4 := hsymm 4 0
  have h20 : D.a 2 0 = 0 := (hsymm 2 0).trans h02
  have h30 : D.a 3 0 = 0 := (hsymm 3 0).trans h03
  have h31 : D.a 3 1 = 0 := (hsymm 3 1).trans h13
  have h41 : D.a 4 1 = 0 := (hsymm 4 1).trans h14
  have h42 : D.a 4 2 = 0 := (hsymm 4 2).trans h24
  simp [Matrix.det_succ_row_zero, Fin.succAbove, Fin.sum_univ_succ,
    hdiag, h02, h03, h13, h14, h24, h10, h21, h32, h43, h40, h20, h30, h31,
    h41, h42] at hdet
  unfold edgeRatio fiveProductRatio
  have hw0 : (D.w 0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 0))
  have hw1 : (D.w 1 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 1))
  have hw2 : (D.w 2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 2))
  have hw3 : (D.w 3 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 3))
  have hw4 : (D.w 4 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 4))
  field_simp
  norm_cast
  ring_nf at hdet
  linarith only [hdet]

theorem five_product_ratio_square (D : LocalNumericalData 5)
    (hw : ∀ i, 0 < D.w i) :
    (fiveProductRatio D) ^ 2 =
      edgeRatio D 0 1 * edgeRatio D 1 2 * edgeRatio D 2 3 *
        edgeRatio D 3 4 * edgeRatio D 0 4 := by
  unfold fiveProductRatio edgeRatio
  have hw0 : (D.w 0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 0))
  have hw1 : (D.w 1 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 1))
  have hw2 : (D.w 2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 2))
  have hw3 : (D.w 3 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 3))
  have hw4 : (D.w 4 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw 4))
  field_simp

theorem star_five_matrix_singular (r : ℤ) :
    Matrix.det (scalarMatrix (starMatrix 5 0 (constantVector (-2)) 1) r) = 0 := by
  simp [scalarMatrix, starMatrix, constantVector, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem double_triple_matrix_singular (t : ℕ) (ht : 4 ≤ t) (r : ℤ) :
    Matrix.det (scalarMatrix (doubleTripleMatrix t) r) = 0 := by
  sorry

theorem e6_matrix_determinant (r : ℤ) :
    Matrix.det (scalarMatrix (pathUntilLeafMatrix 6 4 2 5 (-2) 1) r) = 3 * r ^ 6 := by
  simp [scalarMatrix, pathUntilLeafMatrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem e7_matrix_determinant (r : ℤ) :
    Matrix.det (scalarMatrix (pathUntilLeafMatrix 7 5 3 6 (-2) 1) r) = -2 * r ^ 7 := by
  simp [scalarMatrix, pathUntilLeafMatrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring

/-! A genus-one consequence used repeatedly in the chapter's discussion. -/
theorem all_minus_two_genus_one (T : NumericalType)
    (hall : ∀ i, IsMinusTwoIndex T i) :
    genus T = 1 := by
  have hg : ∀ i, T.g i = 0 := fun i => (hall i).1
  have ha : ∀ i, T.a i i = -2 * T.w i := fun i => (hall i).2
  have hs : ∀ i, (T.m i : ℚ) *
      ((T.w i : ℚ) * ((T.g i : ℚ) - 1) - (T.a i i : ℚ) / 2) = 0 := by
    intro i
    rw [hg i, ha i]
    push_cast
    ring
  have hq : (genus T : ℚ) = (1 : ℚ) := by
    rw [genus_formula]
    simp [genusExpression, hs]
  exact_mod_cast hq

theorem minimal_genus_one_is_minus_two (T : NumericalType)
    (hminimal : IsMinimal T) (hgenus : genus T = 1) (hn : 1 < T.n) :
    ∀ i, IsMinusTwoIndex T i := by
  have hnonneg : ∀ j, 0 ≤ genusContribution T j := by
    intro j
    by_contra h
    have hneg : genusContribution T j < 0 := lt_of_not_ge h
    exact hminimal ⟨j, minus_one_contribution T 1 hgenus hn hneg⟩
  intro i
  apply (minus_two_index_iff_not_positive_contribution T hminimal hn i).2
  intro hpos
  have hsum : 0 < ∑ j : Fin T.n, genusContribution T j := by
    apply Finset.sum_pos'
    · intro j hj
      exact hnonneg j
    · exact ⟨i, Finset.mem_univ i, hpos⟩
  have hgenusQ : (genus T : ℚ) = (1 : ℚ) := by
    exact_mod_cast hgenus
  rw [genus_formula] at hgenusQ
  unfold genusExpression at hgenusQ
  have hsum' : 0 < ∑ j : Fin T.n,
      (T.m j : ℚ) * ((T.w j : ℚ) * ((T.g j : ℚ) - 1) - (T.a j j : ℚ) / 2) := by
    simpa [genusContribution] using hsum
  linarith

/-! The two-by-two classification (`A₂`, `B₂`, and `G₂`). -/
theorem lemma_two_by_two (T : NumericalType) (S : MinusTwoSubgraph T 2)
    (hn : 2 < T.n) (hedge : 0 < (localData S).a 0 1) :
    UpToReordering (localData S) (fun D => isA2 D ∨ isB2 D ∨ isG2 D) := by
  sorry

/-! The three-by-three classification (`A₃`, `C₃`, and `B₃`). -/
theorem lemma_three_by_three (T : NumericalType) (S : MinusTwoSubgraph T 3)
    (hn : 3 < T.n) (hedges : hasTripleAtLeastTwoEdges (localData S)) :
    UpToReordering (localData S) (fun D => isA3 D ∨ isC3 D ∨ isB3 D) := by
  sorry

/-! The four-by-four path classification. -/
theorem lemma_four_by_four (T : NumericalType) (S : MinusTwoSubgraph T 4)
    (hn : 4 < T.n)
    (hedges : hasEdgeAt (localData S) 0 1 ∧ hasEdgeAt (localData S) 1 2 ∧
      hasEdgeAt (localData S) 2 3) :
    UpToReordering (localData S) (fun D => isA4 D ∨ isC4 D ∨ isB4 D ∨ isF4 D) := by
  sorry

/-! The four-index three-arm classification (`D₄`). -/
theorem lemma_D4 (T : NumericalType) (S : MinusTwoSubgraph T 4)
    (hn : 4 < T.n)
    (hedges : hasEdgeAt (localData S) 0 1 ∧ hasEdgeAt (localData S) 0 2 ∧
      hasEdgeAt (localData S) 0 3) :
    UpToReordering (localData S) (fun D => isD4 D) := by
  sorry

/-! The five-by-five path classification. -/
theorem lemma_five_by_five (T : NumericalType) (S : MinusTwoSubgraph T 5)
    (hn : 5 < T.n)
    (hedges : hasEdgeAt (localData S) 0 1 ∧ hasEdgeAt (localData S) 1 2 ∧
      hasEdgeAt (localData S) 2 3 ∧ hasEdgeAt (localData S) 3 4) :
    UpToReordering (localData S) (fun D => isA5 D ∨ isC5 D ∨ isB5 D) := by
  sorry

/-! A proper subgraph cannot contain the fourfold star. -/
theorem lemma_fourfold (T : NumericalType) (S : MinusTwoSubgraph T 5)
    (hn : 5 < T.n) (hedges : hasStarEdges5 (localData S)) : False := by
  sorry

/-! The five-index branch classification (`D₅`). -/
theorem lemma_D5 (T : NumericalType) (S : MinusTwoSubgraph T 5)
    (hn : 5 < T.n) (hedges : hasD5Edges (localData S)) :
    UpToReordering (localData S) (fun D => isD5 D) := by
  sorry

/-! The three long-path possibilities (`Aₙ`, `Cₙ`, and `Bₙ`). -/
theorem lemma_long {t : ℕ} (T : NumericalType) (S : MinusTwoSubgraph T t)
    (ht : 5 < t) (hn : t < T.n) (hedges : hasPathEdges (localData S)) :
    UpToReversal (localData S) (fun D => isAn D ∨ isCn D ∨ isBn D) := by
  sorry

/-! The extended branch classification (`Dₙ`). -/
theorem lemma_Dn {t : ℕ} (T : NumericalType) (S : MinusTwoSubgraph T (t + 1))
    (ht : 4 < t) (hn : t + 1 < T.n)
    (hedges : (∀ ⦃i j : Fin (t + 1)⦄, i.val + 1 = j.val → j.val ≤ t - 1 →
        0 < (localData S).a i j) ∧ hasEdgeAt (localData S) (t - 2) t) :
    isDn (localData S) := by
  sorry

/-! The six-index `E₆` configuration. -/
theorem lemma_E6 (T : NumericalType) (S : MinusTwoSubgraph T 6)
    (hn : 6 < T.n) (hedges : hasE6Edges (localData S)) :
    UpToReordering (localData S) (fun D => isE6 D) := by
  sorry

theorem lemma_E6_not_full (T : NumericalType) (S : MinusTwoSubgraph T 6)
    (hn : T.n = 6) (hedges : hasE6Edges (localData S))
    (hpattern : isE6 (localData S)) : False := by
  sorry

/-! The double-triple pattern is not proper. -/
theorem lemma_double_triple {t : ℕ} (T : NumericalType)
    (S : MinusTwoSubgraph T (t + 2)) (ht : 4 ≤ t) (hn : t + 2 < T.n)
    (hedges : hasDoubleTripleEdges (localData S)) : False := by
  sorry

theorem double_triple_full_genus_one {t : ℕ} (T : NumericalType)
    (S : MinusTwoSubgraph T (t + 2)) (hn : T.n = t + 2) :
    genus T = 1 := by
  let f : Fin (t + 2) → Fin (t + 2) := fun i => Fin.cast hn (S.index i)
  have hf : Function.Injective f := by
    intro i j hij
    apply S.index_injective
    exact Fin.cast_injective hn hij
  have hfs : Function.Surjective f := Finite.surjective_of_injective hf
  have hall : ∀ j : Fin T.n, IsMinusTwoIndex T j := by
    intro j
    obtain ⟨i, hi⟩ := hfs (Fin.cast hn j)
    have hij : S.index i = j := by
      apply Fin.cast_injective hn
      simpa [f] using hi
    rw [← hij]
    exact S.minus_two i
  exact all_minus_two_genus_one T hall

/-! The completed `E₆` pattern is not proper. -/
theorem lemma_E6_completed (T : NumericalType) (S : MinusTwoSubgraph T 7)
    (hn : 7 < T.n) (hedges : hasE6CompletedEdges (localData S)) : False := by
  sorry

theorem e6_completed_full_genus_one (T : NumericalType) (S : MinusTwoSubgraph T 7)
    (hn : T.n = 7) :
    genus T = 1 := by
  let f : Fin 7 → Fin 7 := fun i => Fin.cast hn (S.index i)
  have hf : Function.Injective f := by
    intro i j hij
    apply S.index_injective
    exact Fin.cast_injective hn hij
  have hfs : Function.Surjective f := Finite.surjective_of_injective hf
  have hall : ∀ j : Fin T.n, IsMinusTwoIndex T j := by
    intro j
    obtain ⟨i, hi⟩ := hfs (Fin.cast hn j)
    have hij : S.index i = j := by
      apply Fin.cast_injective hn
      simpa [f] using hi
    rw [← hij]
    exact S.minus_two i
  exact all_minus_two_genus_one T hall

/-! The seven-index `E₇` configuration. -/
theorem lemma_E7 (T : NumericalType) (S : MinusTwoSubgraph T 7)
    (hn : 7 < T.n) (hedges : hasE7Edges (localData S)) :
    UpToReordering (localData S) (fun D => isE7 D) := by
  sorry

theorem lemma_E7_not_full (T : NumericalType) (S : MinusTwoSubgraph T 7)
    (hn : T.n = 7) (hedges : hasE7Edges (localData S))
    (hpattern : isE7 (localData S)) : False := by
  sorry

/-! The eight-index `E₈` configuration. -/
theorem lemma_E8 (T : NumericalType) (S : MinusTwoSubgraph T 8)
    (hn : 8 < T.n) (hedges : hasE8Edges (localData S)) :
    UpToReordering (localData S) (fun D => isE8 D) := by
  sorry

/-! The completed `E₇` pattern is not proper. -/
theorem lemma_E7_completed (T : NumericalType) (S : MinusTwoSubgraph T 8)
    (hn : 8 < T.n) (hedges : hasE7CompletedEdges (localData S)) : False := by
  sorry

/-! The completed `E₈` pattern is not proper. -/
theorem lemma_E8_completed (T : NumericalType) (S : MinusTwoSubgraph T 9)
    (hn : 9 < T.n) (hedges : hasE8CompletedEdges (localData S)) : False := by
  sorry

theorem e8_completed_full_genus_one (T : NumericalType) (S : MinusTwoSubgraph T 9)
    (hn : T.n = 9) :
    genus T = 1 := by
  let f : Fin 9 → Fin 9 := fun i => Fin.cast hn (S.index i)
  have hf : Function.Injective f := by
    intro i j hij
    apply S.index_injective
    exact Fin.cast_injective hn hij
  have hfs : Function.Surjective f := Finite.surjective_of_injective hf
  have hall : ∀ j : Fin T.n, IsMinusTwoIndex T j := by
    intro j
    obtain ⟨i, hi⟩ := hfs (Fin.cast hn j)
    have hij : S.index i = j := by
      apply Fin.cast_injective hn
      simpa [f] using hi
    rw [← hij]
    exact S.minus_two i
  exact all_minus_two_genus_one T hall

/-! The source's final “up to reordering” classification, stated with the
proper subset represented by an ordered injection. -/
def IsConnectedLocalIndexSet {T : NumericalType} {k : ℕ}
    (S : MinusTwoSubgraph T k) : Prop :=
  ¬ ∃ J : Set (Fin k), J.Nonempty ∧ J ≠ Set.univ ∧
    ∀ ⦃i j : Fin k⦄, i ∈ J → j ∉ J → (localData S).a i j = 0

def ListedProperConfiguration {k : ℕ} (D : LocalNumericalData k) : Prop :=
  (∃ h : k = 2, UpToReordering (h ▸ D)
      (fun E => isA2 E ∨ isB2 E ∨ isG2 E)) ∨
    (∃ h : k = 3, UpToReordering (h ▸ D)
      (fun E => isA3 E ∨ isC3 E ∨ isB3 E)) ∨
    (∃ h : k = 4, UpToReordering (h ▸ D)
      (fun E => isA4 E ∨ isC4 E ∨ isB4 E ∨ isF4 E ∨ isD4 E)) ∨
    (∃ h : k = 5, UpToReordering (h ▸ D)
      (fun E => isA5 E ∨ isC5 E ∨ isB5 E ∨ isD5 E)) ∨
    (6 ≤ k ∧ (UpToReversal D (fun E => isAn E ∨ isCn E ∨ isBn E) ∨
        isDn D)) ∨
    (∃ h : k = 6, UpToReordering (h ▸ D) (fun E => isE6 E)) ∨
    (∃ h : k = 7, UpToReordering (h ▸ D) (fun E => isE7 E)) ∨
    (∃ h : k = 8, UpToReordering (h ▸ D) (fun E => isE8 E))

theorem proposition_classify_subgraphs (T : NumericalType) {k : ℕ}
    (S : MinusTwoSubgraph T k) (hcard : 2 ≤ k) (hproper : k < T.n)
    (hconnected : IsConnectedLocalIndexSet S) :
    ListedProperConfiguration (localData S) := by
  sorry

/-! Realizability of the listed proper configurations by genus-one numerical
types, as asserted at the end of the source discussion. -/
def OccursInGenusOne {k : ℕ} (P : LocalNumericalData k → Prop) : Prop :=
  ∃ T : NumericalType, genus T = 1 ∧ k < T.n ∧
    ∃ S : MinusTwoSubgraph T k, UpToReordering (localData S) P

theorem listed_configurations_occur_in_genus_one :
    OccursInGenusOne isA2 ∧ OccursInGenusOne isB2 ∧ OccursInGenusOne isG2 ∧
    OccursInGenusOne isA3 ∧ OccursInGenusOne isC3 ∧ OccursInGenusOne isB3 ∧
    OccursInGenusOne isA4 ∧ OccursInGenusOne isC4 ∧ OccursInGenusOne isB4 ∧
    OccursInGenusOne isF4 ∧ OccursInGenusOne isD4 ∧ OccursInGenusOne isA5 ∧
    OccursInGenusOne isC5 ∧ OccursInGenusOne isB5 ∧ OccursInGenusOne isD5 ∧
    OccursInGenusOne isE6 ∧ OccursInGenusOne isE7 ∧ OccursInGenusOne isE8 := by
  sorry

theorem long_configurations_occur_in_genus_one (k : ℕ) (hk : 6 ≤ k) :
    OccursInGenusOne (isAn : LocalNumericalData k → Prop) ∧
      OccursInGenusOne (isCn : LocalNumericalData k → Prop) ∧
      OccursInGenusOne (isBn : LocalNumericalData k → Prop) ∧
      OccursInGenusOne (isDn : LocalNumericalData k → Prop) := by
  sorry

end Formalization.Books.Models.Unit05
