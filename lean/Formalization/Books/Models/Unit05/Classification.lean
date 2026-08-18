import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Matrix.PosDef
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

private theorem square_factorization (x p q u v : ℤ)
    (h₁ : x = p * u) (h₂ : x = q * v) :
    x ^ 2 = p * q * (u * v) := by
  calc
    x ^ 2 = x * x := by ring
    _ = (p * u) * x := by rw [h₁]
    _ = (p * u) * (q * v) := by rw [h₂]
    _ = p * q * (u * v) := by ring

private theorem positive_int_product_one (p q : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p * q = 1) :
    p = 1 ∧ q = 1 := by
  constructor <;> nlinarith

private theorem positive_int_product_pos (p q : ℤ)
    (hp : 0 < p) (hq : 0 < q) : 0 < p * q :=
  mul_pos hp hq

private theorem cancel_left_int (w : ℤ) (hw : 0 < w) (a b : ℤ)
    (h : w * b ≤ w * a) : b ≤ a := by
  by_contra hnot
  have hlt : a < b := lt_of_not_ge hnot
  have hmul : w * a < w * b := Int.mul_lt_mul_of_pos_left hlt hw
  linarith

private theorem positive_sum_lt_four_cases (r1 r2 : ℤ)
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hsum : r1 + r2 < 4) :
    (r1 = 1 ∧ r2 = 1) ∨ (r1 = 1 ∧ r2 = 2) ∨
      (r1 = 2 ∧ r2 = 1) := by omega

private theorem positive_int_product_two (p q : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p * q = 2) :
    (p = 1 ∧ q = 2) ∨ (p = 2 ∧ q = 1) := by
  have hp' : p ≤ 2 := by nlinarith
  have hq' : q ≤ 2 := by nlinarith
  have hp_cases : p = 1 ∨ p = 2 := by omega
  have hq_cases : q = 1 ∨ q = 2 := by omega
  rcases hp_cases with hp1 | hp2
  · rcases hq_cases with hq1 | hq2
    · norm_num [hp1, hq1] at hpq
    · exact Or.inl ⟨hp1, hq2⟩
  · rcases hq_cases with hq1 | hq2
    · exact Or.inr ⟨hp2, hq1⟩
    · norm_num [hp2, hq2] at hpq

private theorem three_ratio_sum_lt_four
    (w0 w1 w2 a01 a12 : ℝ) (p1 q1 p2 q2 : ℤ)
    (hw : 0 < w0 * w1 * w2)
    (hdet : -8 * w0 * w1 * w2 + 2 * a01 ^ 2 * w2 +
        2 * a12 ^ 2 * w0 < 0)
    (hsq1 : a01 ^ 2 = (p1 * q1 : ℝ) * (w0 * w1))
    (hsq2 : a12 ^ 2 = (p2 * q2 : ℝ) * (w1 * w2)) :
    (p1 * q1 : ℝ) + (p2 * q2 : ℝ) < 4 := by
  have hfactor :
      -8 * w0 * w1 * w2 + 2 * a01 ^ 2 * w2 + 2 * a12 ^ 2 * w0 =
        2 * ((p1 * q1 : ℝ) + (p2 * q2 : ℝ) - 4) *
          (w0 * w1 * w2) := by
    rw [hsq1, hsq2]
    ring
  rw [hfactor] at hdet
  nlinarith

private theorem upToReordering_reindex {k : ℕ} (D : LocalNumericalData k)
    (P : LocalNumericalData k → Prop) (e : Fin k ≃ Fin k)
    (h : UpToReordering (reindexLocalData D e) P) :
    UpToReordering D P := by
  rcases h with ⟨f, hf⟩
  refine ⟨f.trans e, ?_⟩
  simpa [reindexLocalData] using hf

private theorem classify_three_path
    (D : LocalNumericalData 3)
    (hpos : ∀ i, 0 < D.w i) (hmp : ∀ i, 0 < D.m i)
    (hdiag : ∀ i, D.a i i = -2 * D.w i)
    (hsymm : ∀ i j, D.a i j = D.a j i)
    (hzero : D.a 0 2 = 0)
    (hdet : -8 * (D.w 0 : ℝ) * D.w 1 * D.w 2 +
      2 * (D.a 0 1 : ℝ) ^ 2 * D.w 2 +
      2 * (D.a 1 2 : ℝ) ^ 2 * D.w 0 < 0)
    (hbound01 : 0 < 4 * (D.w 0 : ℝ) * D.w 1 - D.a 0 1 ^ 2)
    (hbound12 : 0 < 4 * (D.w 1 : ℝ) * D.w 2 - D.a 1 2 ^ 2)
    (ha01 : 0 < D.a 0 1) (ha12 : 0 < D.a 1 2)
    (hquot : ∀ i j, 0 < D.a i j →
      0 < 4 * (D.w i : ℝ) * D.w j - D.a i j ^ 2 →
      ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ D.a i j = p * D.w i ∧
        D.a i j = q * D.w j ∧ p * q < 4)
    (hrow : ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
      2 * D.w i * D.m i ≥ D.a i j * D.m j + D.a i k * D.m k)
    (realizeA : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.w 2 = r →
      E.a 0 0 = -2 * r → E.a 1 1 = -2 * r → E.a 2 2 = -2 * r →
      E.a 0 1 = r → E.a 1 0 = r → E.a 1 2 = r → E.a 2 1 = r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionA3 E.m → isA3 E)
    (realizeC : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.w 2 = 2 * r →
      E.a 0 0 = -2 * r → E.a 1 1 = -2 * r → E.a 2 2 = -4 * r →
      E.a 0 1 = r → E.a 1 0 = r → E.a 1 2 = 2 * r → E.a 2 1 = 2 * r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionC3 E.m → isC3 E)
    (realizeB : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = 2 * r → E.w 1 = 2 * r → E.w 2 = r →
      E.a 0 0 = -4 * r → E.a 1 1 = -4 * r → E.a 2 2 = -2 * r →
      E.a 0 1 = 2 * r → E.a 1 0 = 2 * r → E.a 1 2 = 2 * r → E.a 2 1 = 2 * r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionB3 E.m → isB3 E) :
    UpToReordering D (fun E => isA3 E ∨ isC3 E ∨ isB3 E) := by
  obtain ⟨p1, q1, hp1, hq1, hpa1, hqa1, hpq1⟩ := hquot 0 1 ha01 hbound01
  obtain ⟨p2, q2, hp2, hq2, hpa2, hqa2, hpq2⟩ := hquot 1 2 ha12 hbound12
  have hsq1 : D.a 0 1 ^ 2 = p1 * q1 * (D.w 0 * D.w 1) :=
    square_factorization _ _ _ _ _ hpa1 hqa1
  have hsq2 : D.a 1 2 ^ 2 = p2 * q2 * (D.w 1 * D.w 2) :=
    square_factorization _ _ _ _ _ hpa2 hqa2
  have hsq1R : (D.a 0 1 : ℝ) ^ 2 =
      (p1 * q1 : ℝ) * ((D.w 0 : ℝ) * D.w 1) := by exact_mod_cast hsq1
  have hsq2R : (D.a 1 2 : ℝ) ^ 2 =
      (p2 * q2 : ℝ) * ((D.w 1 : ℝ) * D.w 2) := by exact_mod_cast hsq2
  have hw0R : (0 : ℝ) < D.w 0 := by exact_mod_cast hpos 0
  have hw1R : (0 : ℝ) < D.w 1 := by exact_mod_cast hpos 1
  have hw2R : (0 : ℝ) < D.w 2 := by exact_mod_cast hpos 2
  have hratioR := three_ratio_sum_lt_four
    ((D.w 0 : ℝ)) (D.w 1 : ℝ) (D.w 2 : ℝ) (D.a 0 1 : ℝ) (D.a 1 2 : ℝ)
    p1 q1 p2 q2 (mul_pos (mul_pos hw0R hw1R) hw2R) hdet hsq1R hsq2R
  have hratio : p1 * q1 + p2 * q2 < (4 : ℤ) := by exact_mod_cast hratioR
  have hr1 : 0 < p1 * q1 := positive_int_product_pos p1 q1 hp1 hq1
  have hr2 : 0 < p2 * q2 := positive_int_product_pos p2 q2 hp2 hq2
  have hrcases := positive_sum_lt_four_cases (p1 * q1) (p2 * q2) hr1 hr2 hratio
  have hdiag0 := hdiag 0
  have hdiag1 := hdiag 1
  have hdiag2 := hdiag 2
  have h10 := hsymm 1 0
  have h21 := hsymm 2 1
  have h20 := hsymm 2 0
  rcases hrcases with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
  · have hpq1 := positive_int_product_one p1 q1 hp1 hq1 hr1
    have hpq2 := positive_int_product_one p2 q2 hp2 hq2 hr2
    have ha01p : D.a 0 1 = D.w 0 := by simpa [hpq1.1] using hpa1
    have ha01q : D.a 0 1 = D.w 1 := by simpa [hpq1.2] using hqa1
    have ha12p : D.a 1 2 = D.w 1 := by simpa [hpq2.1] using hpa2
    have ha12q : D.a 1 2 = D.w 2 := by simpa [hpq2.2] using hqa2
    have hw01 : D.w 1 = D.w 0 := ha01q.symm.trans ha01p
    have hw12 : D.w 2 = D.w 1 := ha12q.symm.trans ha12p
    have hm0 : 2 * D.m 0 ≥ D.m 1 := by
      have h := hrow 0 1 2 (by decide) (by decide) (by decide)
      rw [ha01p, hzero] at h
      exact cancel_left_int (D.w 0) (hpos 0) _ _ (by linarith)
    have hm1 : 2 * D.m 1 ≥ D.m 0 + D.m 2 := by
      have h := hrow 1 0 2 (by decide) (by decide) (by decide)
      rw [h10, ha01q, ha12p] at h
      exact cancel_left_int (D.w 1) (hpos 1) _ _ (by linarith)
    have hm2 : 2 * D.m 2 ≥ D.m 1 := by
      have h := hrow 2 0 1 (by decide) (by decide) (by decide)
      rw [h20, hzero, h21, ha12q] at h
      exact cancel_left_int (D.w 2) (hpos 2) _ _ (by linarith)
    have hmc : mConditionA3 D.m := ⟨hm0, hm1, hm2⟩
    refine ⟨Equiv.refl _, ?_⟩
    left
    exact realizeA D (D.w 0) (hpos 0) rfl hw01 (hw12.trans hw01)
      (by simpa [hw01] using hdiag0) (by simpa [hw01] using hdiag1)
      (by simpa [hw01, hw12] using hdiag2) ha01p (h10.trans ha01p)
      (ha12p.trans hw01) (h21.trans ha12p |>.trans hw01) hzero
      (h20.trans hzero) hmp hmc
  · have hpq1 := positive_int_product_one p1 q1 hp1 hq1 hr1
    have hpq2 := positive_int_product_two p2 q2 hp2 hq2 hr2
    rcases hpq2 with ⟨hp2, hq2⟩ | ⟨hp2, hq2⟩
    · have ha01p : D.a 0 1 = D.w 0 := by simpa [hpq1.1] using hpa1
      have ha01q : D.a 0 1 = D.w 1 := by simpa [hpq1.2] using hqa1
      have ha12p : D.a 1 2 = D.w 1 := by simpa [hp2] using hpa2
      have ha12q : D.a 1 2 = 2 * D.w 2 := by simpa [hq2] using hqa2
      have hw01 : D.w 1 = D.w 0 := ha01q.symm.trans ha01p
      have hw12 : D.w 1 = 2 * D.w 2 := ha12p.symm.trans ha12q
      have hw02 : D.w 0 = 2 * D.w 2 := hw01.symm.trans hw12
      have hm0 : 2 * D.m 0 ≥ D.m 1 := by
        have h := hrow 0 1 2 (by decide) (by decide) (by decide)
        rw [ha01p, hzero] at h
        exact cancel_left_int (D.w 0) (hpos 0) _ _ (by linarith)
      have hm1 : 2 * D.m 1 ≥ D.m 0 + D.m 2 := by
        have h := hrow 1 0 2 (by decide) (by decide) (by decide)
        rw [h10, ha01q, ha12p] at h
        exact cancel_left_int (D.w 1) (hpos 1) _ _ (by linarith)
      have hm2' : 2 * D.m 2 ≥ 2 * D.m 1 := by
        have h := hrow 2 0 1 (by decide) (by decide) (by decide)
        rw [h20, hzero, h21, ha12q] at h
        exact cancel_left_int (D.w 2) (hpos 2) _ _ (by linarith)
      have hm2 : D.m 2 ≥ D.m 1 := by linarith
      have hmc : mConditionB3 D.m := ⟨hm0, hm1, hm2⟩
      refine ⟨Equiv.refl _, ?_⟩
      right
      right
      exact realizeB D (D.w 2) (hpos 2)
        hw02 hw12 rfl
        (by calc
          D.a 0 0 = -2 * D.w 0 := hdiag0
          _ = -4 * D.w 2 := by rw [hw02]; ring)
        (by calc
          D.a 1 1 = -2 * D.w 1 := hdiag1
          _ = -4 * D.w 2 := by rw [hw12]; ring)
        hdiag2
        (ha01p.trans hw02)
        ((h10.trans ha01p).trans hw02)
        (ha12p.trans hw12)
        ((h21.trans ha12p).trans hw12) hzero (h20.trans hzero) hmp hmc
    · have ha01p : D.a 0 1 = D.w 0 := by simpa [hpq1.1] using hpa1
      have ha01q : D.a 0 1 = D.w 1 := by simpa [hpq1.2] using hqa1
      have ha12p : D.a 1 2 = 2 * D.w 1 := by simpa [hp2] using hpa2
      have ha12q : D.a 1 2 = D.w 2 := by simpa [hq2] using hqa2
      have hw01 : D.w 1 = D.w 0 := ha01q.symm.trans ha01p
      have hw12 : D.w 2 = 2 * D.w 1 := ha12q.symm.trans ha12p
      have hw02 : D.w 2 = 2 * D.w 0 := by
        calc
          D.w 2 = 2 * D.w 1 := hw12
          _ = 2 * D.w 0 := by rw [hw01]
      have ha12r : D.a 1 2 = 2 * D.w 0 := by
        calc
          D.a 1 2 = 2 * D.w 1 := ha12p
          _ = 2 * D.w 0 := by rw [hw01]
      have ha21r : D.a 2 1 = 2 * D.w 0 := by
        calc
          D.a 2 1 = D.a 1 2 := h21
          _ = 2 * D.w 0 := ha12r
      have hm0 : 2 * D.m 0 ≥ D.m 1 := by
        have h := hrow 0 1 2 (by decide) (by decide) (by decide)
        rw [ha01p, hzero] at h
        exact cancel_left_int (D.w 0) (hpos 0) _ _ (by linarith)
      have hm1' : 2 * D.m 1 ≥ D.m 0 + 2 * D.m 2 := by
        have h := hrow 1 0 2 (by decide) (by decide) (by decide)
        rw [h10, ha01q, ha12p] at h
        exact cancel_left_int (D.w 1) (hpos 1) _ _ (by linarith)
      have hm2 : 2 * D.m 2 ≥ D.m 1 := by
        have h := hrow 2 0 1 (by decide) (by decide) (by decide)
        rw [h20, hzero, h21, ha12q] at h
        exact cancel_left_int (D.w 2) (hpos 2) _ _ (by linarith)
      have hmc : mConditionC3 D.m := ⟨hm0, hm1', hm2⟩
      refine ⟨Equiv.refl _, ?_⟩
      right
      left
      exact realizeC D (D.w 0) (hpos 0) rfl hw01 hw02
        hdiag0 (by calc
          D.a 1 1 = -2 * D.w 1 := hdiag1
          _ = -2 * D.w 0 := by rw [hw01])
        (by calc
          D.a 2 2 = -2 * D.w 2 := hdiag2
          _ = -4 * D.w 0 := by rw [hw02]; ring)
        ha01p (h10.trans ha01p) ha12r ha21r hzero (h20.trans hzero) hmp hmc
  · have hpq1 := positive_int_product_two p1 q1 hp1 hq1 hr1
    have hpq2 := positive_int_product_one p2 q2 hp2 hq2 hr2
    rcases hpq1 with ⟨hp1, hq1⟩ | ⟨hp1, hq1⟩
    · have ha01p : D.a 0 1 = D.w 0 := by simpa [hp1] using hpa1
      have ha01q : D.a 0 1 = 2 * D.w 1 := by simpa [hq1] using hqa1
      have ha12p : D.a 1 2 = D.w 1 := by simpa [hpq2.1] using hpa2
      have ha12q : D.a 1 2 = D.w 2 := by simpa [hpq2.2] using hqa2
      have hw01 : D.w 0 = 2 * D.w 1 := ha01p.symm.trans ha01q
      have hw12 : D.w 2 = D.w 1 := ha12q.symm.trans ha12p
      have hm0 : 2 * D.m 2 ≥ D.m 1 := by
        have h := hrow 2 0 1 (by decide) (by decide) (by decide)
        rw [h20, hzero, h21, ha12p] at h
        exact cancel_left_int (D.w 1) (hpos 1) _ _ (by
          rw [hw12] at h
          linarith)
      have hm1 : 2 * D.m 1 ≥ D.m 2 + 2 * D.m 0 := by
        have h := hrow 1 0 2 (by decide) (by decide) (by decide)
        rw [h10, ha01q, ha12p] at h
        exact cancel_left_int (D.w 1) (hpos 1) _ _ (by linarith)
      have hm2 : 2 * D.m 0 ≥ D.m 1 := by
        have h := hrow 0 1 2 (by decide) (by decide) (by decide)
        rw [ha01p, hzero] at h
        exact cancel_left_int (D.w 0) (hpos 0) _ _ (by linarith)
      let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
      let E : LocalNumericalData 3 := reindexLocalData D e
      have he0 : e 0 = (2 : Fin 3) := by simp [e, Equiv.swap_apply_left]
      have he1 : e 1 = (1 : Fin 3) := by
        change (Equiv.swap 0 2) 1 = (1 : Fin 3)
        decide
      have he2 : e 2 = (0 : Fin 3) := by simp [e, Equiv.swap_apply_right]
      have hEpos : ∀ i, 0 < E.w i := by
        intro i
        change 0 < D.w (e i)
        exact hpos (e i)
      have hEmp : ∀ i, 0 < E.m i := by
        intro i
        change 0 < D.m (e i)
        exact hmp (e i)
      have hEdiag : ∀ i, E.a i i = -2 * E.w i := by
        intro i
        change D.a (e i) (e i) = -2 * D.w (e i)
        exact hdiag (e i)
      have hEsym : ∀ i j, E.a i j = E.a j i := by
        intro i j
        change D.a (e i) (e j) = D.a (e j) (e i)
        exact hsymm (e i) (e j)
      have hEzero : E.a 0 2 = 0 := by
        change D.a (e 0) (e 2) = 0
        rw [he0, he2]
        exact h20.trans hzero
      have hmcE : mConditionC3 E.m := by
        change 2 * D.m 2 ≥ D.m 1 ∧
          2 * D.m 1 ≥ D.m 2 + 2 * D.m 0 ∧ 2 * D.m 0 ≥ D.m 1
        exact ⟨hm0, hm1, hm2⟩
      refine ⟨e, ?_⟩
      right
      left
      exact realizeC E (D.w 1) (hpos 1) hw12 rfl hw01
        (by calc
          E.a 0 0 = D.a 2 2 := by
            change D.a (e 0) (e 0) = D.a 2 2
            rw [he0]
          _ = -2 * D.w 2 := hdiag2
          _ = -2 * D.w 1 := by rw [hw12])
        hdiag1
        (by calc
          E.a 2 2 = D.a 0 0 := by
            change D.a (e 2) (e 2) = D.a 0 0
            rw [he2]
          _ = -2 * D.w 0 := hdiag0
          _ = -4 * D.w 1 := by rw [hw01]; ring)
        (by calc
          E.a 0 1 = D.a 2 1 := by
            change D.a (e 0) (e 1) = D.a 2 1
            rw [he0, he1]
          _ = D.a 1 2 := h21
          _ = D.w 1 := ha12p)
        ha12p
        (by calc
          E.a 1 2 = D.a 1 0 := by
            change D.a (e 1) (e 2) = D.a 1 0
            rw [he1, he2]
          _ = D.a 0 1 := h10
          _ = D.w 0 := ha01p
          _ = 2 * D.w 1 := hw01)
        (by calc
          E.a 2 1 = D.a 0 1 := by
            change D.a (e 2) (e 1) = D.a 0 1
            rw [he2, he1]
          _ = D.w 0 := ha01p
          _ = 2 * D.w 1 := hw01)
        hEzero (by
          change D.a 0 2 = 0
          exact hzero)
        hEmp hmcE
    · have ha01p : D.a 0 1 = 2 * D.w 0 := by simpa [hp1] using hpa1
      have ha01q : D.a 0 1 = D.w 1 := by simpa [hq1] using hqa1
      have ha12p : D.a 1 2 = D.w 1 := by simpa [hpq2.1] using hpa2
      have ha12q : D.a 1 2 = D.w 2 := by simpa [hpq2.2] using hqa2
      have hw01 : D.w 1 = 2 * D.w 0 := ha01q.symm.trans ha01p
      have hw12 : D.w 2 = D.w 1 := ha12q.symm.trans ha12p
      have hw02 : D.w 2 = 2 * D.w 0 := by
        calc
          D.w 2 = D.w 1 := hw12
          _ = 2 * D.w 0 := hw01
      have hm0 : 2 * D.m 2 ≥ D.m 1 := by
        have h := hrow 2 0 1 (by decide) (by decide) (by decide)
        rw [h20, hzero, h21, ha12p, hw12] at h
        exact cancel_left_int (D.w 1) (hpos 1) _ _ (by linarith)
      have hm1 : 2 * D.m 1 ≥ D.m 2 + D.m 0 := by
        have h := hrow 1 0 2 (by decide) (by decide) (by decide)
        rw [h10, ha01q, ha12p] at h
        exact cancel_left_int (D.w 1) (hpos 1) _ _ (by linarith)
      have hm2 : D.m 0 ≥ D.m 1 := by
        have h := hrow 0 1 2 (by decide) (by decide) (by decide)
        rw [ha01p, hzero] at h
        exact cancel_left_int (D.w 0) (hpos 0) _ _ (by linarith)
      let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
      let E : LocalNumericalData 3 := reindexLocalData D e
      have he0 : e 0 = (2 : Fin 3) := by simp [e, Equiv.swap_apply_left]
      have he1 : e 1 = (1 : Fin 3) := by
        change (Equiv.swap 0 2) 1 = (1 : Fin 3)
        decide
      have he2 : e 2 = (0 : Fin 3) := by simp [e, Equiv.swap_apply_right]
      have hEmp : ∀ i, 0 < E.m i := by
        intro i
        change 0 < D.m (e i)
        exact hmp (e i)
      have hmcE : mConditionB3 E.m := by
        change 2 * D.m 2 ≥ D.m 1 ∧
          2 * D.m 1 ≥ D.m 2 + D.m 0 ∧ D.m 0 ≥ D.m 1
        exact ⟨hm0, hm1, hm2⟩
      refine ⟨e, ?_⟩
      right
      right
      exact realizeB E (D.w 0) (hpos 0)
        (by calc
          E.w 0 = D.w 2 := by
            change D.w (e 0) = D.w 2
            rw [he0]
          _ = 2 * D.w 0 := hw02)
        (by calc
          E.w 1 = D.w 1 := by
            change D.w (e 1) = D.w 1
            rw [he1]
          _ = 2 * D.w 0 := hw01)
        (by
          change D.w (e 2) = D.w 0
          rw [he2])
        (by calc
          E.a 0 0 = D.a 2 2 := by
            change D.a (e 0) (e 0) = D.a 2 2
            rw [he0]
          _ = -2 * D.w 2 := hdiag2
          _ = -4 * D.w 0 := by rw [hw02]; ring)
        (by calc
          E.a 1 1 = D.a 1 1 := by
            change D.a (e 1) (e 1) = D.a 1 1
            rw [he1]
          _ = -2 * D.w 1 := hdiag1
          _ = -4 * D.w 0 := by rw [hw01]; ring)
        hdiag0
        (by calc
          E.a 0 1 = D.a 2 1 := by
            change D.a (e 0) (e 1) = D.a 2 1
            rw [he0, he1]
          _ = D.a 1 2 := h21
          _ = D.w 1 := ha12p
          _ = 2 * D.w 0 := hw01)
        (by calc
          E.a 1 0 = D.a 1 2 := by
            change D.a (e 1) (e 0) = D.a 1 2
            rw [he1, he0]
          _ = D.w 1 := ha12p
          _ = 2 * D.w 0 := hw01)
        (by calc
          E.a 1 2 = D.a 1 0 := by
            change D.a (e 1) (e 2) = D.a 1 0
            rw [he1, he2]
          _ = D.a 0 1 := h10
          _ = 2 * D.w 0 := ha01p)
        (by calc
          E.a 2 1 = D.a 0 1 := by
            change D.a (e 2) (e 1) = D.a 0 1
            rw [he2, he1]
          _ = 2 * D.w 0 := ha01p)
        (by
          change D.a 2 0 = 0
          exact h20.trans hzero)
        (by
          change D.a 0 2 = 0
          exact hzero)
        hEmp hmcE

private theorem classify_three_two_edges
    (D : LocalNumericalData 3)
    (hpos : ∀ i, 0 < D.w i) (hmp : ∀ i, 0 < D.m i)
    (hdiag : ∀ i, D.a i i = -2 * D.w i)
    (hsymm : ∀ i j, D.a i j = D.a j i)
    (hdet : -8 * (D.w 0 : ℝ) * D.w 1 * D.w 2 +
      2 * (D.a 0 1 : ℝ) ^ 2 * D.w 2 +
      2 * (D.a 1 2 : ℝ) ^ 2 * D.w 0 +
      2 * (D.a 0 2 : ℝ) ^ 2 * D.w 1 +
      2 * (D.a 0 1 : ℝ) * D.a 0 2 * D.a 1 2 < 0)
    (hbound01 : 0 < 4 * (D.w 0 : ℝ) * D.w 1 - D.a 0 1 ^ 2)
    (hbound02 : 0 < 4 * (D.w 0 : ℝ) * D.w 2 - D.a 0 2 ^ 2)
    (ha01 : 0 < D.a 0 1) (ha02 : 0 < D.a 0 2)
    (hzero : D.a 1 2 = 0)
    (hquot : ∀ i j, 0 < D.a i j →
      0 < 4 * (D.w i : ℝ) * D.w j - D.a i j ^ 2 →
      ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ D.a i j = p * D.w i ∧
        D.a i j = q * D.w j ∧ p * q < 4)
    (hrow : ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
      2 * D.w i * D.m i ≥ D.a i j * D.m j + D.a i k * D.m k)
    (realizeA : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.w 2 = r →
      E.a 0 0 = -2 * r → E.a 1 1 = -2 * r → E.a 2 2 = -2 * r →
      E.a 0 1 = r → E.a 1 0 = r → E.a 1 2 = r → E.a 2 1 = r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionA3 E.m → isA3 E)
    (realizeC : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.w 2 = 2 * r →
      E.a 0 0 = -2 * r → E.a 1 1 = -2 * r → E.a 2 2 = -4 * r →
      E.a 0 1 = r → E.a 1 0 = r → E.a 1 2 = 2 * r → E.a 2 1 = 2 * r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionC3 E.m → isC3 E)
    (realizeB : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = 2 * r → E.w 1 = 2 * r → E.w 2 = r →
      E.a 0 0 = -4 * r → E.a 1 1 = -4 * r → E.a 2 2 = -2 * r →
      E.a 0 1 = 2 * r → E.a 1 0 = 2 * r → E.a 1 2 = 2 * r → E.a 2 1 = 2 * r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionB3 E.m → isB3 E) :
    UpToReordering D (fun E => isA3 E ∨ isC3 E ∨ isB3 E) := by
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
  let E : LocalNumericalData 3 := reindexLocalData D e
  have he0 : e 0 = (1 : Fin 3) := by simp [e, Equiv.swap_apply_left]
  have he1 : e 1 = (0 : Fin 3) := by simp [e, Equiv.swap_apply_right]
  have he2 : e 2 = (2 : Fin 3) := by
    change (Equiv.swap 0 1) 2 = (2 : Fin 3)
    decide
  have hEpos : ∀ i, 0 < E.w i := by
    intro i
    change 0 < D.w (e i)
    exact hpos (e i)
  have hEmp : ∀ i, 0 < E.m i := by
    intro i
    change 0 < D.m (e i)
    exact hmp (e i)
  have hEdiag : ∀ i, E.a i i = -2 * E.w i := by
    intro i
    change D.a (e i) (e i) = -2 * D.w (e i)
    exact hdiag (e i)
  have hEsym : ∀ i j, E.a i j = E.a j i := by
    intro i j
    change D.a (e i) (e j) = D.a (e j) (e i)
    exact hsymm (e i) (e j)
  have hEzero : E.a 0 2 = 0 := by
    change D.a (e 0) (e 2) = 0
    rw [he0, he2]
    exact hzero
  have hEdet : -8 * (E.w 0 : ℝ) * E.w 1 * E.w 2 +
      2 * (E.a 0 1 : ℝ) ^ 2 * E.w 2 +
      2 * (E.a 1 2 : ℝ) ^ 2 * E.w 0 < 0 := by
    change -8 * (D.w (e 0) : ℝ) * D.w (e 1) * D.w (e 2) +
        2 * (D.a (e 0) (e 1) : ℝ) ^ 2 * D.w (e 2) +
        2 * (D.a (e 1) (e 2) : ℝ) ^ 2 * D.w (e 0) < 0
    rw [he0, he1, he2, hsymm 1 0]
    have hdet' := hdet
    rw [hzero] at hdet'
    convert hdet' using 1 <;> ring
  have hEbound01 : 0 < 4 * (E.w 0 : ℝ) * E.w 1 - E.a 0 1 ^ 2 := by
    change 0 < 4 * (D.w (e 0) : ℝ) * D.w (e 1) - D.a (e 0) (e 1) ^ 2
    rw [he0, he1, hsymm 1 0]
    convert hbound01 using 1 <;> ring
  have hEbound12 : 0 < 4 * (E.w 1 : ℝ) * E.w 2 - E.a 1 2 ^ 2 := by
    change 0 < 4 * (D.w (e 1) : ℝ) * D.w (e 2) - D.a (e 1) (e 2) ^ 2
    rw [he1, he2]
    exact hbound02
  have hEa01 : 0 < E.a 0 1 := by
    change 0 < D.a (e 0) (e 1)
    rw [he0, he1, hsymm 1 0]
    exact ha01
  have hEa12 : 0 < E.a 1 2 := by
    change 0 < D.a (e 1) (e 2)
    rw [he1, he2]
    exact ha02
  have hEquot : ∀ i j, 0 < E.a i j →
      0 < 4 * (E.w i : ℝ) * E.w j - E.a i j ^ 2 →
      ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ E.a i j = p * E.w i ∧
        E.a i j = q * E.w j ∧ p * q < 4 := by
    intro i j hij hb
    change 0 < D.a (e i) (e j) at hij
    change 0 < 4 * (D.w (e i) : ℝ) * D.w (e j) - D.a (e i) (e j) ^ 2 at hb
    obtain ⟨p, q, hp, hq, hpa, hqa, hpq⟩ := hquot (e i) (e j) hij hb
    exact ⟨p, q, hp, hq, hpa, hqa, hpq⟩
  have hErow : ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
      2 * E.w i * E.m i ≥ E.a i j * E.m j + E.a i k * E.m k := by
    intro i j k hij hik hjk
    change 2 * D.w (e i) * D.m (e i) ≥
      D.a (e i) (e j) * D.m (e j) + D.a (e i) (e k) * D.m (e k)
    apply hrow (e i) (e j) (e k)
    · intro h
      exact hij (e.injective h)
    · intro h
      exact hik (e.injective h)
    · intro h
      exact hjk (e.injective h)
  apply upToReordering_reindex D
    (fun F => isA3 F ∨ isC3 F ∨ isB3 F) e
  apply classify_three_path E hEpos hEmp hEdiag hEsym hEzero hEdet
    hEbound01 hEbound12 hEa01 hEa12 hEquot hErow
    realizeA realizeC realizeB

private theorem classify_three_two_edges_right
    (D : LocalNumericalData 3)
    (hpos : ∀ i, 0 < D.w i) (hmp : ∀ i, 0 < D.m i)
    (hdiag : ∀ i, D.a i i = -2 * D.w i)
    (hsymm : ∀ i j, D.a i j = D.a j i)
    (hdet : -8 * (D.w 0 : ℝ) * D.w 1 * D.w 2 +
      2 * (D.a 0 1 : ℝ) ^ 2 * D.w 2 +
      2 * (D.a 1 2 : ℝ) ^ 2 * D.w 0 +
      2 * (D.a 0 2 : ℝ) ^ 2 * D.w 1 +
      2 * (D.a 0 1 : ℝ) * D.a 0 2 * D.a 1 2 < 0)
    (hbound02 : 0 < 4 * (D.w 0 : ℝ) * D.w 2 - D.a 0 2 ^ 2)
    (hbound12 : 0 < 4 * (D.w 1 : ℝ) * D.w 2 - D.a 1 2 ^ 2)
    (ha02 : 0 < D.a 0 2) (ha12 : 0 < D.a 1 2)
    (hzero : D.a 0 1 = 0)
    (hquot : ∀ i j, 0 < D.a i j →
      0 < 4 * (D.w i : ℝ) * D.w j - D.a i j ^ 2 →
      ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ D.a i j = p * D.w i ∧
        D.a i j = q * D.w j ∧ p * q < 4)
    (hrow : ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
      2 * D.w i * D.m i ≥ D.a i j * D.m j + D.a i k * D.m k)
    (realizeA : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.w 2 = r →
      E.a 0 0 = -2 * r → E.a 1 1 = -2 * r → E.a 2 2 = -2 * r →
      E.a 0 1 = r → E.a 1 0 = r → E.a 1 2 = r → E.a 2 1 = r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionA3 E.m → isA3 E)
    (realizeC : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.w 2 = 2 * r →
      E.a 0 0 = -2 * r → E.a 1 1 = -2 * r → E.a 2 2 = -4 * r →
      E.a 0 1 = r → E.a 1 0 = r → E.a 1 2 = 2 * r → E.a 2 1 = 2 * r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionC3 E.m → isC3 E)
    (realizeB : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = 2 * r → E.w 1 = 2 * r → E.w 2 = r →
      E.a 0 0 = -4 * r → E.a 1 1 = -4 * r → E.a 2 2 = -2 * r →
      E.a 0 1 = 2 * r → E.a 1 0 = 2 * r → E.a 1 2 = 2 * r → E.a 2 1 = 2 * r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionB3 E.m → isB3 E) :
    UpToReordering D (fun E => isA3 E ∨ isC3 E ∨ isB3 E) := by
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
  let E : LocalNumericalData 3 := reindexLocalData D e
  have he0 : e 0 = (0 : Fin 3) := by
    change (Equiv.swap 1 2) 0 = (0 : Fin 3)
    decide
  have he1 : e 1 = (2 : Fin 3) := by
    simp [e, Equiv.swap_apply_left]
  have he2 : e 2 = (1 : Fin 3) := by
    simp [e, Equiv.swap_apply_right]
  have hEpos : ∀ i, 0 < E.w i := by
    intro i
    change 0 < D.w (e i)
    exact hpos (e i)
  have hEmp : ∀ i, 0 < E.m i := by
    intro i
    change 0 < D.m (e i)
    exact hmp (e i)
  have hEdiag : ∀ i, E.a i i = -2 * E.w i := by
    intro i
    change D.a (e i) (e i) = -2 * D.w (e i)
    exact hdiag (e i)
  have hEsym : ∀ i j, E.a i j = E.a j i := by
    intro i j
    change D.a (e i) (e j) = D.a (e j) (e i)
    exact hsymm (e i) (e j)
  have hEzero : E.a 0 2 = 0 := by
    change D.a (e 0) (e 2) = 0
    rw [he0, he2]
    exact hzero
  have hEdet : -8 * (E.w 0 : ℝ) * E.w 1 * E.w 2 +
      2 * (E.a 0 1 : ℝ) ^ 2 * E.w 2 +
      2 * (E.a 1 2 : ℝ) ^ 2 * E.w 0 < 0 := by
    change -8 * (D.w (e 0) : ℝ) * D.w (e 1) * D.w (e 2) +
        2 * (D.a (e 0) (e 1) : ℝ) ^ 2 * D.w (e 2) +
        2 * (D.a (e 1) (e 2) : ℝ) ^ 2 * D.w (e 0) < 0
    rw [he0, he1, he2, hsymm 2 1]
    have hdet' := hdet
    rw [hzero] at hdet'
    convert hdet' using 1 <;> ring
  have hEbound01 : 0 < 4 * (E.w 0 : ℝ) * E.w 1 - E.a 0 1 ^ 2 := by
    change 0 < 4 * (D.w (e 0) : ℝ) * D.w (e 1) - D.a (e 0) (e 1) ^ 2
    rw [he0, he1]
    convert hbound02 using 1 <;> ring
  have hEbound12 : 0 < 4 * (E.w 1 : ℝ) * E.w 2 - E.a 1 2 ^ 2 := by
    change 0 < 4 * (D.w (e 1) : ℝ) * D.w (e 2) - D.a (e 1) (e 2) ^ 2
    rw [he1, he2, hsymm 2 1]
    convert hbound12 using 1 <;> ring
  have hEa01 : 0 < E.a 0 1 := by
    change 0 < D.a (e 0) (e 1)
    rw [he0, he1]
    exact ha02
  have hEa12 : 0 < E.a 1 2 := by
    change 0 < D.a (e 1) (e 2)
    rw [he1, he2, hsymm 2 1]
    exact ha12
  have hEquot : ∀ i j, 0 < E.a i j →
      0 < 4 * (E.w i : ℝ) * E.w j - E.a i j ^ 2 →
      ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ E.a i j = p * E.w i ∧
        E.a i j = q * E.w j ∧ p * q < 4 := by
    intro i j hij hb
    change 0 < D.a (e i) (e j) at hij
    change 0 < 4 * (D.w (e i) : ℝ) * D.w (e j) - D.a (e i) (e j) ^ 2 at hb
    obtain ⟨p, q, hp, hq, hpa, hqa, hpq⟩ := hquot (e i) (e j) hij hb
    exact ⟨p, q, hp, hq, hpa, hqa, hpq⟩
  have hErow : ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
      2 * E.w i * E.m i ≥ E.a i j * E.m j + E.a i k * E.m k := by
    intro i j k hij hik hjk
    change 2 * D.w (e i) * D.m (e i) ≥
      D.a (e i) (e j) * D.m (e j) + D.a (e i) (e k) * D.m (e k)
    apply hrow (e i) (e j) (e k)
    · intro h
      exact hij (e.injective h)
    · intro h
      exact hik (e.injective h)
    · intro h
      exact hjk (e.injective h)
  apply upToReordering_reindex D
    (fun F => isA3 F ∨ isC3 F ∨ isB3 F) e
  apply classify_three_path E hEpos hEmp hEdiag hEsym hEzero hEdet
    hEbound01 hEbound12 hEa01 hEa12 hEquot hErow
    realizeA realizeC realizeB

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
        2 * D.a 0 1 ^ 2 * D.a 3 4 ^ 2 * D.w 2 -
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
  classical
  let v : Fin (t + 2) → ℤ := fun i =>
    if i.val ≤ 1 then 1 else if i.val < t then 2 else 1
  have hkernel : Matrix.mulVec (doubleTripleMatrix t) v = 0 := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum]
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := by
        apply Fin.ext
        simpa using hi0
      subst i
      have hsum : (∑ j : Fin (t + 2), doubleTripleMatrix t 0 j * v j) =
          -2 * v 0 + v 2 := by
        calc
          (∑ j : Fin (t + 2), doubleTripleMatrix t 0 j * v j) =
              ∑ j, ((if j = 0 then -2 * v j else 0) +
                (if j = 2 then v j else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases h0 : j = 0
            · subst j
              have h02 : ¬ (0 : Fin (t + 2)) = 2 := by
                intro h
                have hv := congrArg Fin.val h
                have h2lt : 2 < t + 2 := by omega
                have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                norm_num at hv
                rw [h2mod] at hv
                omega
              simp [doubleTripleMatrix, h02]
            · by_cases h2 : j = 2
              · subst j
                simp [doubleTripleMatrix]
                split <;> omega
              · simp [doubleTripleMatrix, h0, h2]
                have hj0 : j.val ≠ 0 := by
                  intro hj
                  apply h0
                  apply Fin.ext
                  simpa using hj
                have hj2 : j.val ≠ 2 := by
                  intro hj
                  apply h2
                  apply Fin.ext
                  have h2lt : 2 < t + 2 := by omega
                  have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                  simpa [h2mod] using hj
                have h0' : (0 : Fin (t + 2)) ≠ j := by
                  intro h
                  exact h0 h.symm
                have ht1 : t - 1 ≠ 0 := by omega
                have ht1' : 0 ≠ t - 1 := Ne.symm ht1
                simp [doubleTripleMatrix, hj0, hj2, h0', ht1, ht1', ht]
          _ = -2 * v 0 + v 2 := by
            simp [Finset.sum_add_distrib]
      rw [hsum]
      have h2lt : 2 < t + 2 := by omega
      have h2val : (2 : Fin (t + 2)).val = 2 := by
        simp [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt h2lt]
      have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
      have h2t : 2 < t := by omega
      simp [v, ht, h2lt, h2val, h2mod, h2t]
    · by_cases hi1 : i.val = 1
      · have hi : i = 1 := by
          apply Fin.ext
          simpa using hi1
        subst i
        have hsum : (∑ j : Fin (t + 2), doubleTripleMatrix t 1 j * v j) =
            -2 * v 1 + v 2 := by
          calc
            (∑ j : Fin (t + 2), doubleTripleMatrix t 1 j * v j) =
                ∑ j, ((if j = 1 then -2 * v j else 0) +
                  (if j = 2 then v j else 0)) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases h1 : j = 1
              · subst j
                have h12 : ¬ (1 : Fin (t + 2)) = 2 := by
                  intro h
                  have hv := congrArg Fin.val h
                  have h2lt : 2 < t + 2 := by omega
                  have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                  norm_num at hv
                  rw [h2mod] at hv
                  omega
                simp [doubleTripleMatrix, h12]
              · by_cases h2 : j = 2
                · subst j
                  have h2lt : 2 < t + 2 := by omega
                  have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                  have h2le : 2 ≤ t := by omega
                  have h12 : (1 : Fin (t + 2)) ≠ 2 := by
                    intro h
                    have hv := congrArg Fin.val h
                    norm_num at hv
                    rw [h2mod] at hv
                    omega
                  simp [doubleTripleMatrix, ht, h2mod, h2le, h12, h12.symm]
                · have hj1 : j.val ≠ 1 := by
                    intro hj'
                    apply h1
                    apply Fin.ext
                    simpa using hj'
                  have hj2 : j.val ≠ 2 := by
                    intro hj'
                    apply h2
                    apply Fin.ext
                    have h2lt : 2 < t + 2 := by omega
                    have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                    simpa [h2mod] using hj'
                  have h2lt : 2 < t + 2 := by omega
                  have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                  have h0val : (0 : Fin (t + 2)).val = 0 := by simp
                  have h1val : (1 : Fin (t + 2)).val = 1 := by
                    simp [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by omega : 1 < t + 2)]
                  have h2val : (2 : Fin (t + 2)).val = 2 := by
                    simp [Fin.coe_ofNat_eq_mod, h2mod]
                  have h2le : 2 ≤ t := by omega
                  have h1rev : (1 : Fin (t + 2)) ≠ j := by
                    intro h
                    exact h1 h.symm
                  have h2rev : (2 : Fin (t + 2)).val ≠ j.val := by
                    intro h
                    apply hj2
                    symm
                    simpa [h2val, h2mod] using h
                  have h1j : (1 : Fin (t + 2)).val ≠ j.val := by
                    intro h
                    apply hj1
                    symm
                    exact h
                  have h2rev' : 2 ≠ j.val := by
                    simpa [h2mod] using h2rev
                  have hbranch : ¬ (2 = j.val ∧ j.val ≤ t ∨
                      j = 0 ∧ 1 ≤ j.val ∧ 1 ≤ t) := by
                    intro h
                    rcases h with h | h
                    · exact h2rev' h.1
                    · have := h.2.1
                      have hj0 : j.val = 0 := by
                        simpa using congrArg Fin.val h.1
                      omega
                  have hend : ¬ (1 = t - 1 ∧ j.val = t + 1 ∨
                      t = 0 ∧ j.val = t - 1) := by
                    intro h
                    rcases h with h | h <;> omega
                  simp [doubleTripleMatrix, h1, h2, hj1, hj2, ht, h2mod,
                    h0val, h1val, h2val, h2le, h1rev, h2rev, h1j,
                    hbranch, hend]
            _ = -2 * v 1 + v 2 := by
              simp [Finset.sum_add_distrib]
        rw [hsum]
        have h1val : (1 : Fin (t + 2)).val = 1 := by
          simp [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by omega : 1 < t + 2)]
        have h2lt : 2 < t + 2 := by omega
        have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
        have h2t : 2 < t := by omega
        simp [v, ht, h1val, h2mod, h2t]
      · by_cases hi2 : i.val = 2
        · have hi : i = 2 := by
            apply Fin.ext
            have h2lt : 2 < t + 2 := by omega
            have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
            simpa [h2mod] using hi2
          subst i
          have hsum : (∑ j : Fin (t + 2), doubleTripleMatrix t 2 j * v j) =
              -2 * v 2 + v 0 + v 1 + v 3 := by
            calc
              (∑ j : Fin (t + 2), doubleTripleMatrix t 2 j * v j) =
                  ∑ j, ((if j = 2 then -2 * v j else 0) +
                    (if j = 0 then v j else 0) +
                    (if j = 1 then v j else 0) +
                    (if j = 3 then v j else 0)) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases h2 : j = 2
                · subst j
                  have h23 : ¬ (2 : Fin (t + 2)) = 3 := by
                    intro h
                    have hv := congrArg Fin.val h
                    have h2lt : 2 < t + 2 := by omega
                    have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                    have h3lt : 3 < t + 2 := by omega
                    have h3mod : 3 % (t + 2) = 3 := Nat.mod_eq_of_lt h3lt
                    norm_num at hv
                    rw [h2mod, h3mod] at hv
                    omega
                  have h20 : ¬ (2 : Fin (t + 2)) = 0 := by
                    intro h
                    have hv := congrArg Fin.val h
                    have h2lt : 2 < t + 2 := by omega
                    have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                    norm_num at hv
                    rw [h2mod] at hv
                    omega
                  have h21 : ¬ (2 : Fin (t + 2)) = 1 := by
                    intro h
                    have hv := congrArg Fin.val h
                    have h2lt : 2 < t + 2 := by omega
                    have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                    norm_num at hv
                    rw [h2mod] at hv
                    omega
                  simp [doubleTripleMatrix, h23, h20, h21]
                · by_cases h0 : j = 0
                  · subst j
                    have h2lt : 2 < t + 2 := by omega
                    have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                    have h3lt : 3 < t + 2 := by omega
                    have h3mod : 3 % (t + 2) = 3 := Nat.mod_eq_of_lt h3lt
                    have htpos : 0 < t := by omega
                    have h03 : ¬ (0 : Fin (t + 2)) = 3 := by
                      intro h
                      have hv := congrArg Fin.val h
                      norm_num at hv
                      rw [h3mod] at hv
                      omega
                    simp [doubleTripleMatrix, h2mod, h3mod, htpos, ht, h03]
                    split <;> omega
                  · by_cases h1 : j = 1
                    · subst j
                      have h2lt : 2 < t + 2 := by omega
                      have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                      have h3lt : 3 < t + 2 := by omega
                      have h3mod : 3 % (t + 2) = 3 := Nat.mod_eq_of_lt h3lt
                      have h2le : 2 ≤ t := by omega
                      have h13 : ¬ (1 : Fin (t + 2)) = 3 := by
                        intro h
                        have hv := congrArg Fin.val h
                        norm_num at hv
                        rw [h3mod] at hv
                        omega
                      simp [doubleTripleMatrix, ht, h2mod, h3mod, h2le, h13]
                      split <;> omega
                    · by_cases h3 : j = 3
                      · subst j
                        have h3lt : 3 < t + 2 := by omega
                        have h3mod : 3 % (t + 2) = 3 := Nat.mod_eq_of_lt h3lt
                        have h3le : 3 ≤ t := by omega
                        have h2lt : 2 < t + 2 := by omega
                        have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                        have h23 : ¬ (2 : Fin (t + 2)) = 3 := by
                          intro h
                          have hv := congrArg Fin.val h
                          norm_num at hv
                          rw [h2mod, h3mod] at hv
                          omega
                        have h30 : ¬ (3 : Fin (t + 2)) = 0 := by
                          intro h
                          have hv := congrArg Fin.val h
                          norm_num at hv
                          rw [h3mod] at hv
                          omega
                        have h31 : ¬ (3 : Fin (t + 2)) = 1 := by
                          intro h
                          have hv := congrArg Fin.val h
                          norm_num at hv
                          rw [h3mod] at hv
                          omega
                        have h32 : ¬ (3 : Fin (t + 2)) = 2 := by
                          intro h
                          have hv := congrArg Fin.val h
                          norm_num at hv
                          rw [h2mod, h3mod] at hv
                          omega
                        simp [doubleTripleMatrix, ht, h2mod, h3mod, h3le,
                          h23, h30, h31, h32]
                      · have hj0 : j.val ≠ 0 := by
                          intro hj'
                          apply h0
                          apply Fin.ext
                          simpa using hj'
                        have hj1 : j.val ≠ 1 := by
                          intro hj'
                          apply h1
                          apply Fin.ext
                          simpa using hj'
                        have hj2 : j.val ≠ 2 := by
                          intro hj'
                          apply h2
                          apply Fin.ext
                          have h2lt : 2 < t + 2 := by omega
                          have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                          simpa [h2mod] using hj'
                        have hj3 : j.val ≠ 3 := by
                          intro hj'
                          apply h3
                          apply Fin.ext
                          have h3lt : 3 < t + 2 := by omega
                          have h3mod : 3 % (t + 2) = 3 := Nat.mod_eq_of_lt h3lt
                          simpa [h3mod] using hj'
                        have h3lt : 3 < t + 2 := by omega
                        have h3mod : 3 % (t + 2) = 3 := Nat.mod_eq_of_lt h3lt
                        have h3val : (3 : Fin (t + 2)).val = 3 := by
                          simp [Fin.coe_ofNat_eq_mod, h3mod]
                        have h2lt : 2 < t + 2 := by omega
                        have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                        have h2rev : (2 : Fin (t + 2)) ≠ j := by
                          intro h
                          exact h2 h.symm
                        have hpath : ¬ (2 % (t + 2) + 1 = j.val ∧
                            1 ≤ 2 % (t + 2) ∧ j.val ≤ t ∨
                            j.val + 1 = 2 % (t + 2) ∧ 1 ≤ j.val ∧
                              2 % (t + 2) ≤ t) := by
                          rw [h2mod]
                          intro h
                          rcases h with h | h <;> omega
                        have hend : ¬ (2 % (t + 2) = t - 1 ∧ j.val = t + 1 ∨
                            2 % (t + 2) = t + 1 ∧ j.val = t - 1) := by
                          rw [h2mod]
                          intro h
                          rcases h with h | h <;> omega
                        have hbranch : ¬ (j.val = 3 ∧ 1 ≤ 2 ∧ j.val ≤ t ∨
                            j.val + 1 = 2 ∧ 1 ≤ j.val ∧ 2 ≤ t ∨
                            j.val = 0 ∧ 2 = 2 ∨
                            2 = t - 1 ∧ j.val = t + 1) := by
                          intro h
                          rcases h with h | h | h | h <;> omega
                        simp [doubleTripleMatrix, h0, h1, h2, h3, hj0, hj1,
                          hj2, hj3, ht, h2mod, h3mod, h3val, h2rev, hpath,
                          hend, hbranch]
                        split <;> simp_all <;> omega
              _ = -2 * v 2 + v 0 + v 1 + v 3 := by
                simp [Finset.sum_add_distrib]
          rw [hsum]
          have h2lt : 2 < t + 2 := by omega
          have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
          have h2val : (2 : Fin (t + 2)).val = 2 := by
            simp [Fin.coe_ofNat_eq_mod, h2mod]
          have h3lt : 3 < t + 2 := by omega
          have h3mod : 3 % (t + 2) = 3 := Nat.mod_eq_of_lt h3lt
          have h3val : (3 : Fin (t + 2)).val = 3 := by
            simp [Fin.coe_ofNat_eq_mod, h3mod]
          have h2t : 2 < t := by omega
          have h3t : 3 < t := by omega
          simp [v, ht, h2mod, h2val, h3mod, h3val, h2t, h3t]
        · by_cases hit : i.val = t
          · let it : Fin (t + 2) := ⟨t, by omega⟩
            let im1 : Fin (t + 2) := ⟨t - 1, by omega⟩
            have hi : i = it := by
              apply Fin.ext
              simpa [it] using hit
            rw [hi]
            have hsum : (∑ j : Fin (t + 2), doubleTripleMatrix t it j * v j) =
                -2 * v it + v im1 := by
              calc
                (∑ j : Fin (t + 2), doubleTripleMatrix t it j * v j) =
                    ∑ j, ((if j = it then -2 * v j else 0) +
                      (if j = im1 then v j else 0)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  by_cases hjt : j = it
                  · subst j
                    simp [doubleTripleMatrix, it, im1]
                    have hne : t ≠ t - 1 := by omega
                    simp [hne]
                  · by_cases hjm : j = im1
                    · subst j
                      simp [doubleTripleMatrix, it, im1]
                      split <;> omega
                    · have hjt' : j.val ≠ t := by
                        intro h
                        apply hjt
                        apply Fin.ext
                        simpa [it] using h
                      have hjm' : j.val ≠ t - 1 := by
                        intro h
                        apply hjm
                        apply Fin.ext
                        simpa [im1] using h
                      have hpath : ¬ ((t + 1 = j.val ∧ 1 ≤ t ∧ j.val ≤ t) ∨
                          (j.val + 1 = t ∧ 1 ≤ j.val ∧ t ≤ t)) := by
                        intro h
                        rcases h with h | h <;> omega
                      have hend : ¬ ((t = t - 1 ∧ j.val = t + 1) ∨
                          (t - 1 = t + 1 ∧ j.val = t)) := by
                        omega
                      have hdiag : it ≠ j := by
                        intro h
                        exact hjt h.symm
                      have hpath' : ¬ ((t + 1 = j.val ∧ 1 ≤ t ∧ j.val ≤ t) ∨
                          (j.val + 1 = t ∧ 1 ≤ j.val)) := by
                        intro h
                        rcases h with h | h <;> omega
                      have hspecial : ¬ (t = 0 ∧ j.val = 2 ∨
                          t = 2 ∧ j = 0) := by
                        intro h
                        rcases h with h | h <;> omega
                      have hend' : ¬ (t = t - 1 ∧ j.val = t + 1) := by
                        omega
                      simp [doubleTripleMatrix, it, im1, hjt, hjm, hjt', hjm',
                        hpath, hend, hdiag, hpath', hspecial, hend', ht]
                _ = -2 * v it + v im1 := by
                  simp [Finset.sum_add_distrib]
            rw [hsum]
            have htle : ¬ t ≤ 2 := by omega
            have htpos : 0 < t := by omega
            simp [v, it, im1, ht, htle, htpos]
          · by_cases hit1 : i.val = t + 1
            · let it1 : Fin (t + 2) := ⟨t + 1, by omega⟩
              let im1 : Fin (t + 2) := ⟨t - 1, by omega⟩
              have hi : i = it1 := by
                apply Fin.ext
                simpa [it1] using hit1
              rw [hi]
              have hsum : (∑ j : Fin (t + 2), doubleTripleMatrix t it1 j * v j) =
                  -2 * v it1 + v im1 := by
                calc
                  (∑ j : Fin (t + 2), doubleTripleMatrix t it1 j * v j) =
                      ∑ j, ((if j = it1 then -2 * v j else 0) +
                        (if j = im1 then v j else 0)) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    by_cases hjt : j = it1
                    · subst j
                      simp [doubleTripleMatrix, it1, im1]
                      have hne : t + 1 ≠ t - 1 := by omega
                      simp [hne]
                    · by_cases hjm : j = im1
                      · subst j
                        simp [doubleTripleMatrix, it1, im1]
                        have hne : t + 1 ≠ t - 1 := by omega
                        simp [hne]
                      · have hjt' : j.val ≠ t + 1 := by
                          intro h
                          apply hjt
                          apply Fin.ext
                          simpa [it1] using h
                        have hjm' : j.val ≠ t - 1 := by
                          intro h
                          apply hjm
                          apply Fin.ext
                          simpa [im1] using h
                        have hpath : ¬ ((t + 2 = j.val ∧ 1 ≤ t + 1 ∧ j.val ≤ t) ∨
                            (j.val + 1 = t + 1 ∧ 1 ≤ j.val ∧ t + 1 ≤ t)) := by
                          intro h
                          rcases h with h | h <;> omega
                        have hend : ¬ ((t + 1 = t - 1 ∧ j.val = t + 1) ∨
                            (t - 1 = t + 1 ∧ j.val = t + 1)) := by
                          omega
                        have hdiag : it1 ≠ j := by
                          intro h
                          exact hjt h.symm
                        have hpath' : ¬ (t + 1 + 1 = j.val ∧ j.val ≤ t) := by
                          intro h
                          omega
                        have hspecial : ¬ (t = 1 ∧ j = 0) := by
                          intro h
                          omega
                        have hend' : ¬ (t + 1 = t - 1 ∧ j.val = t + 1) := by
                          omega
                        simp [doubleTripleMatrix, it1, im1, hjt, hjm, hjt', hjm',
                          hpath, hend, hdiag, hpath', hspecial, hend', ht]
                  _ = -2 * v it1 + v im1 := by
                    simp [Finset.sum_add_distrib]
              rw [hsum]
              have htle : ¬ t ≤ 2 := by omega
              have htpos : 0 < t := by omega
              simp [v, it1, im1, ht, htle, htpos]
            · by_cases hitm : i.val = t - 1
              · let im1 : Fin (t + 2) := ⟨t - 1, by omega⟩
                let im2 : Fin (t + 2) := ⟨t - 2, by omega⟩
                let it : Fin (t + 2) := ⟨t, by omega⟩
                let it1 : Fin (t + 2) := ⟨t + 1, by omega⟩
                have hi : i = im1 := by
                  apply Fin.ext
                  simpa [im1] using hitm
                rw [hi]
                have hsum : (∑ j : Fin (t + 2), doubleTripleMatrix t im1 j * v j) =
                    -2 * v im1 + v im2 + v it + v it1 := by
                  calc
                    (∑ j : Fin (t + 2), doubleTripleMatrix t im1 j * v j) =
                        ∑ j, ((if j = im1 then -2 * v j else 0) +
                          (if j = im2 then v j else 0) +
                          (if j = it then v j else 0) +
                          (if j = it1 then v j else 0)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      by_cases hjm1 : j = im1
                      · subst j
                        simp [doubleTripleMatrix, im1, im2, it, it1]
                        split <;> omega
                      · by_cases hjm2 : j = im2
                        · subst j
                          simp [doubleTripleMatrix, im1, im2, it, it1]
                          split <;> omega
                        · by_cases hjt : j = it
                          · subst j
                            simp [doubleTripleMatrix, im1, im2, it, it1]
                            split <;> omega
                          · by_cases hjt1 : j = it1
                            · subst j
                              simp [doubleTripleMatrix, im1, im2, it, it1]
                              split <;> omega
                            · have hjm1' : j.val ≠ t - 1 := by
                                intro h
                                apply hjm1
                                apply Fin.ext
                                simpa [im1] using h
                              have hjm2' : j.val ≠ t - 2 := by
                                intro h
                                apply hjm2
                                apply Fin.ext
                                simpa [im2] using h
                              have hjt' : j.val ≠ t := by
                                intro h
                                apply hjt
                                apply Fin.ext
                                simpa [it] using h
                              have hjt1' : j.val ≠ t + 1 := by
                                intro h
                                apply hjt1
                                apply Fin.ext
                                simpa [it1] using h
                              have hpath : ¬ ((t - 1 + 1 = j.val ∧
                                  1 ≤ t - 1 ∧ j.val ≤ t) ∨
                                  (j.val + 1 = t - 1 ∧ 1 ≤ j.val ∧ t - 1 ≤ t)) := by
                                intro h
                                rcases h with h | h <;> omega
                              have hend : ¬ ((t - 1 = t - 1 ∧ j.val = t + 1) ∨
                                  (t + 1 = t - 1 ∧ j.val = t - 1)) := by
                                intro h
                                rcases h with h | h <;> omega
                              have hdiag : im1 ≠ j := by
                                intro h
                                exact hjm1 h.symm
                              have hpath' : ¬ ((t - 1 + 1 = j.val ∧ j.val ≤ t) ∨
                                  (j.val + 1 = t - 1 ∧ 1 ≤ j.val)) := by
                                intro h
                                rcases h with h | h <;> omega
                              have hpath2 : ¬ ((t - 1 + 1 = j.val ∧
                                  1 ≤ t - 1 ∧ j.val ≤ t) ∨
                                  (j.val + 1 = t - 1 ∧ 1 ≤ j.val)) := by
                                intro h
                                rcases h with h | h <;> omega
                              have hspecial : ¬ (t - 1 = 0 ∧ j.val = 2 ∨
                                  t = 3 ∧ j = 0) := by
                                intro h
                                rcases h with h | h <;> omega
                              simp [doubleTripleMatrix, im1, im2, it, it1,
                                hjm1, hjm2, hjt, hjt1, hjm1', hjm2', hjt',
                                hjt1', hpath, hpath2, hend, hdiag, hpath',
                                hspecial, ht]
                    _ = -2 * v im1 + v im2 + v it + v it1 := by
                      simp [Finset.sum_add_distrib]
                rw [hsum]
                have htle : ¬ t ≤ 2 := by omega
                have ht3 : ¬ t ≤ 3 := by omega
                have htpos : 0 < t := by omega
                simp [v, im1, im2, it, it1, ht, htle, ht3, htpos]
              · have hi3 : 3 ≤ i.val := by omega
                have hitwo : i.val ≤ t - 2 := by omega
                let im : Fin (t + 2) := ⟨i.val - 1, by omega⟩
                let ip : Fin (t + 2) := ⟨i.val + 1, by omega⟩
                have hsum : (∑ j : Fin (t + 2), doubleTripleMatrix t i j * v j) =
                    -2 * v i + v im + v ip := by
                  calc
                    (∑ j : Fin (t + 2), doubleTripleMatrix t i j * v j) =
                        ∑ j, ((if j = i then -2 * v j else 0) +
                          (if j = im then v j else 0) +
                          (if j = ip then v j else 0)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      by_cases hji : j = i
                      · subst j
                        have him : i ≠ im := by
                          intro h
                          have hv := congrArg Fin.val h
                          simp [im] at hv
                          omega
                        have hip : i ≠ ip := by
                          intro h
                          have hv := congrArg Fin.val h
                          simp [ip] at hv
                        simp [doubleTripleMatrix, him, hip]
                      · by_cases hjm : j = im
                        · subst j
                          have hmi : im ≠ i := by
                            intro h
                            have hv := congrArg Fin.val h
                            simp [im] at hv
                            omega
                          have hmip : im ≠ ip := by
                            intro h
                            have hv := congrArg Fin.val h
                            simp [im, ip] at hv
                          simp [doubleTripleMatrix, im, ip, hmi, hmip]
                          split <;> omega
                        · by_cases hjp : j = ip
                          · subst j
                            have hpi : ip ≠ i := by
                              intro h
                              have hv := congrArg Fin.val h
                              simp [ip] at hv
                            have hpim : ip ≠ im := by
                              intro h
                              have hv := congrArg Fin.val h
                              simp [im, ip] at hv
                              omega
                            simp [doubleTripleMatrix, im, ip, hpi, hpim]
                            split <;> omega
                          · have hji' : j.val ≠ i.val := by
                              intro h
                              apply hji
                              apply Fin.ext
                              exact h
                            have hjm' : j.val ≠ i.val - 1 := by
                              intro h
                              apply hjm
                              apply Fin.ext
                              simpa [im] using h
                            have hjp' : j.val ≠ i.val + 1 := by
                              intro h
                              apply hjp
                              apply Fin.ext
                              simpa [ip] using h
                            have hpath : ¬ ((i.val + 1 = j.val ∧
                                1 ≤ i.val ∧ j.val ≤ t) ∨
                                (j.val + 1 = i.val ∧ 1 ≤ j.val ∧ i.val ≤ t)) := by
                              intro h
                              rcases h with h | h <;> omega
                            have hspecial : ¬ ((i.val = 0 ∧ j.val = 2) ∨
                                (i.val = 2 ∧ j.val = 0)) := by
                              intro h
                              rcases h with h | h <;> omega
                            have hend : ¬ ((i.val = t - 1 ∧ j.val = t + 1) ∨
                                (i.val = t + 1 ∧ j.val = t - 1)) := by
                              intro h
                              rcases h with h | h <;> omega
                            have hdiag : i ≠ j := by
                              intro h
                              exact hji h.symm
                            have hi0' : i ≠ 0 := by
                              intro h
                              have hv := congrArg Fin.val h
                              norm_num at hv
                              have hi0val : i.val = 0 := by simpa using hv
                              omega
                            have hi2' : i ≠ 2 := by
                              intro h
                              have hv := congrArg Fin.val h
                              have h2lt : 2 < t + 2 := by omega
                              have h2mod : 2 % (t + 2) = 2 := Nat.mod_eq_of_lt h2lt
                              have hi2val : i.val = 2 := by simpa [h2mod] using hv
                              omega
                            have hpath' : ¬ ((i.val + 1 = j.val ∧
                                1 ≤ i.val ∧ j.val ≤ t) ∨
                                (j.val + 1 = i.val ∧ 1 ≤ j.val ∧ i.val ≤ t)) := hpath
                            simp [doubleTripleMatrix, im, ip, hji, hjm, hjp,
                              hji', hjm', hjp', hpath, hpath', hspecial, hend,
                              hi3, hitwo, hi0', hi2', hi2, hdiag]
                    _ = -2 * v i + v im + v ip := by
                      simp [Finset.sum_add_distrib]
                rw [hsum]
                have hi_le_one : ¬ i.val ≤ 1 := by omega
                have hi_le_two : ¬ i.val ≤ 2 := by omega
                have hi_lt_t : i.val < t := by omega
                have him_ge_two : 2 ≤ i.val - 1 := by omega
                have him_lt_t : i.val - 1 < t := by omega
                have hip_lt_t : i.val + 1 < t := by omega
                have hi0fin : i ≠ 0 := by
                  intro h
                  have hv := congrArg Fin.val h
                  have hi0val : i.val = 0 := by simpa using hv
                  omega
                change -2 * v i + v im + v ip = 0
                simp [v, im, ip, hi3, hitwo, hi_le_one, hi_le_two, hi_lt_t,
                  him_ge_two, him_lt_t, hip_lt_t, hi0fin]
  have hkernel' : Matrix.mulVec (scalarMatrix (doubleTripleMatrix t) r) v = 0 := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [scalarMatrix]
    rw [show (∑ x, (r * doubleTripleMatrix t i x) * v x) =
        r * (∑ x, doubleTripleMatrix t i x * v x) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring]
    change r * (∑ x, doubleTripleMatrix t i x * v x) = 0
    have hi := congrFun hkernel i
    change (∑ x, doubleTripleMatrix t i x * v x) = 0 at hi
    rw [hi]
    simp
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (i := ⟨0, by omega⟩) hkernel' (by simp [v])

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
  classical
  let D := localData S
  let i : Fin T.n := S.index 0
  let j : Fin T.n := S.index 1
  have hij : i ≠ j := by
    intro h
    have h01 : (0 : Fin 2) = 1 := S.index_injective h
    norm_num at h01
  have hAm : Matrix.mulVec (fun p q => (T.a p q : ℝ))
      (fun p => (T.m p : ℝ)) = 0 := by
    funext p
    change (∑ q, (T.a p q : ℝ) * (T.m q : ℝ)) = 0
    exact_mod_cast T.row_sum p
  have hconnected : ¬ ∃ I : Set (Fin T.n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃p q⦄, p ∈ I → q ∉ I → (T.a p q : ℝ) = 0 := by
    intro h
    apply T.connected
    rcases h with ⟨I, hI, hne, hcross⟩
    refine ⟨I, hI, hne, ?_⟩
    intro p q hp hq
    exact_mod_cast hcross hp hq
  have hreal := Formalization.Books.Models.Unit02.recurring_symmetric_real
    (fun p q => (T.a p q : ℝ)) (fun p => (T.m p : ℝ))
    (fun p q => by exact_mod_cast T.a_symmetric p q)
    (by intro p q h; exact_mod_cast T.a_offdiag_nonneg h)
    (by intro p; exact_mod_cast T.m_pos p) hAm hconnected
  have hDdiag0 : D.a 0 0 = -2 * D.w 0 := by
    simpa [D, localData] using (S.minus_two 0).2
  have hDdiag1 : D.a 1 1 = -2 * D.w 1 := by
    simpa [D, localData] using (S.minus_two 1).2
  have hDedge : D.a 0 1 = T.a i j := by rfl
  have hDwi : D.w 0 = T.w i := by rfl
  have hDwj : D.w 1 = T.w j := by rfl
  have hDsym : ∀ a b, D.a a b = D.a b a := by
    intro a b
    simpa [D] using local_a_symmetric S a b
  have hwi : 0 < D.w 0 := local_w_pos S 0
  have hwj : 0 < D.w 1 := local_w_pos S 1
  have hai : T.a i i = -2 * T.w i := by
    simpa [i] using (S.minus_two 0).2
  have haj : T.a j j = -2 * T.w j := by
    simpa [j] using (S.minus_two 1).2
  have haij : 0 < T.a i j := by simpa [D, localData, i, j] using hedge
  let x : Fin T.n → ℝ := fun k =>
    if k = i then (T.a i j : ℝ) else if k = j then 2 * (T.w i : ℝ) else 0
  have hquad := (hreal x).1
  have hquad_formula :
      (∑ k : Fin T.n, x k * Matrix.mulVec (fun p q => (T.a p q : ℝ)) x k) =
        2 * (T.w i : ℝ) *
          ((T.a i j : ℝ) ^ 2 - 4 * (T.w i : ℝ) * (T.w j : ℝ)) := by
    dsimp [x]
    let inner : Fin T.n → ℝ := fun k =>
      ∑ l : Fin T.n, (T.a k l : ℝ) *
        (if l = i then (T.a i j : ℝ) else if l = j then 2 * (T.w i : ℝ) else 0)
    change (∑ k : Fin T.n,
      (if k = i then (T.a i j : ℝ) else if k = j then 2 * (T.w i : ℝ) else 0) *
      inner k) = 2 * (T.w i : ℝ) *
        ((T.a i j : ℝ) ^ 2 - 4 * (T.w i : ℝ) * (T.w j : ℝ))
    have hinner (k : Fin T.n) : inner k =
        (T.a k i : ℝ) * (T.a i j : ℝ) +
          (T.a k j : ℝ) * (2 * (T.w i : ℝ)) := by
      dsimp [inner]
      calc
        (∑ l : Fin T.n, (T.a k l : ℝ) *
            (if l = i then (T.a i j : ℝ) else if l = j then 2 * (T.w i : ℝ) else 0)) =
            ∑ l : Fin T.n,
              ((if l = i then (T.a k l : ℝ) * (T.a i j : ℝ) else 0) +
                (if l = j then (T.a k l : ℝ) * (2 * (T.w i : ℝ)) else 0)) := by
          apply Finset.sum_congr rfl
          intro l hl
          by_cases hli : l = i <;> by_cases hlj : l = j <;>
            simp [hli, hlj, hij, hij.symm]
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp [hij]
    have houter :
        (∑ k : Fin T.n,
          (if k = i then (T.a i j : ℝ) else if k = j then 2 * (T.w i : ℝ) else 0) *
            inner k) =
          (T.a i j : ℝ) * inner i + (2 * (T.w i : ℝ)) * inner j := by
      calc
        (∑ k : Fin T.n,
            (if k = i then (T.a i j : ℝ) else if k = j then 2 * (T.w i : ℝ) else 0) *
              inner k) =
            ∑ k : Fin T.n,
              ((if k = i then (T.a i j : ℝ) * inner k else 0) +
                (if k = j then (2 * (T.w i : ℝ)) * inner k else 0)) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hki : k = i <;> by_cases hkj : k = j <;>
            simp [hki, hkj, hij, hij.symm]
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp [hij]
    rw [houter, hinner i, hinner j]
    have hAii : (T.a i i : ℝ) = -2 * (T.w i : ℝ) := by exact_mod_cast hai
    have hAjj : (T.a j j : ℝ) = -2 * (T.w j : ℝ) := by exact_mod_cast haj
    have hAji : (T.a j i : ℝ) = (T.a i j : ℝ) := by
      exact_mod_cast T.a_symmetric j i
    rw [hAii, hAjj, hAji]
    ring
  have hquad' : 2 * (T.w i : ℝ) *
      ((T.a i j : ℝ) ^ 2 - 4 * (T.w i : ℝ) * (T.w j : ℝ)) ≤ 0 := by
    rw [← hquad_formula]
    exact hquad
  have hdet_nonneg : 0 ≤ 4 * D.w 0 * D.w 1 - D.a 0 1 ^ 2 := by
    have hq : 0 ≤ 4 * (T.w i : ℝ) * (T.w j : ℝ) -
        (T.a i j : ℝ) ^ 2 := by
      have hwiR : (0 : ℝ) < (T.w i : ℝ) := by exact_mod_cast T.w_pos i
      nlinarith [hquad', hwiR]
    exact_mod_cast hq
  have hdet_pos : 0 < 4 * D.w 0 * D.w 1 - D.a 0 1 ^ 2 := by
    have hdet_nonnegR : 0 ≤ 4 * (T.w i : ℝ) * (T.w j : ℝ) -
        (T.a i j : ℝ) ^ 2 := by
      exact_mod_cast hdet_nonneg
    have hdet_posR : 0 < 4 * (T.w i : ℝ) * (T.w j : ℝ) -
        (T.a i j : ℝ) ^ 2 := by
      have hwiR : (0 : ℝ) < (T.w i : ℝ) := by exact_mod_cast T.w_pos i
      by_contra hnot
      have hzero : 4 * (T.w i : ℝ) * (T.w j : ℝ) -
          (T.a i j : ℝ) ^ 2 = 0 := by
        apply le_antisymm
        · exact le_of_not_gt hnot
        · exact hdet_nonnegR
      have henergy :
          (∑ k : Fin T.n, x k *
            Matrix.mulVec (fun p q => (T.a p q : ℝ)) x k) = 0 := by
        rw [hquad_formula]
        nlinarith [hzero, hwiR]
      rcases (hreal x).2.mp henergy with ⟨c, hcx⟩
      have hijval : i.val ≠ j.val := by
        intro h
        exact hij (Fin.ext h)
      let k : Fin T.n :=
        if i.val = 0 then
          if j.val = 1 then ⟨2, by omega⟩ else ⟨1, by omega⟩
        else if i.val = 1 then
          if j.val = 0 then ⟨2, by omega⟩ else ⟨0, by omega⟩
        else if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hki : k ≠ i := by
        apply Fin.ne_of_val_ne
        dsimp [k]
        split_ifs <;> simp only [Fin.val_mk] at * <;> omega
      have hkj : k ≠ j := by
        apply Fin.ne_of_val_ne
        dsimp [k]
        split_ifs <;> simp only [Fin.val_mk] at * <;> omega
      have hck := congrFun hcx k
      have hck' : (0 : ℝ) = c * (T.m k : ℝ) := by
        simpa [x, hki, hkj] using hck
      have hmkR : (0 : ℝ) < (T.m k : ℝ) := by exact_mod_cast T.m_pos k
      have hc0 : c = 0 := by nlinarith [hck', hmkR]
      have hci := congrFun hcx i
      have hci' : (T.a i j : ℝ) = c * (T.m i : ℝ) := by
        simpa [x, hij] using hci
      have haijR : (0 : ℝ) < (T.a i j : ℝ) := by exact_mod_cast haij
      rw [hc0, zero_mul] at hci'
      nlinarith [hci', haijR]
    exact_mod_cast hdet_posR
  have hdivi : D.w 0 ∣ D.a 0 1 := by
    simpa [D, localData, i, j] using T.w_dvd i j
  have hdivj : D.w 1 ∣ D.a 0 1 := by
    have h := T.w_dvd j i
    simpa [D, localData, i, j, T.a_symmetric j i] using h
  let p : ℤ := D.a 0 1 / D.w 0
  let q : ℤ := D.a 0 1 / D.w 1
  have hp : 0 < p := by
    dsimp [p]
    exact Int.ediv_pos_of_pos_of_dvd (by simpa [D] using hedge) (le_of_lt hwi) hdivi
  have hq : 0 < q := by
    dsimp [q]
    exact Int.ediv_pos_of_pos_of_dvd (by simpa [D] using hedge) (le_of_lt hwj) hdivj
  have hpa : D.a 0 1 = p * D.w 0 := by
    dsimp [p]
    exact (Int.ediv_mul_cancel hdivi).symm
  have hqa : D.a 0 1 = q * D.w 1 := by
    dsimp [q]
    exact (Int.ediv_mul_cancel hdivj).symm
  have hwpq : 0 < D.w 0 * D.w 1 := mul_pos hwi hwj
  have hpq_lt : p * q < 4 := by
    have hsq : D.a 0 1 ^ 2 = p * q * (D.w 0 * D.w 1) := by
      calc
        D.a 0 1 ^ 2 = D.a 0 1 * D.a 0 1 := by ring
        _ = (p * D.w 0) * D.a 0 1 := by rw [hpa]
        _ = (p * D.w 0) * (q * D.w 1) := by rw [hqa]
        _ = p * q * (D.w 0 * D.w 1) := by ring
    have hlt : p * q * (D.w 0 * D.w 1) < 4 * (D.w 0 * D.w 1) := by
      nlinarith [hdet_pos, hsq]
    nlinarith [hlt, hwpq]
  have hp_le : p ≤ 3 := by nlinarith [hp, hpq_lt]
  have hq_le : q ≤ 3 := by nlinarith [hq, hpq_lt]
  have hrow0T : T.a i i * T.m i + T.a i j * T.m j ≤ 0 := by
    let rest : Finset (Fin T.n) :=
      (Finset.univ.erase i).erase j
    have hrest : 0 ≤ rest.sum (fun k => T.a i k * T.m k) := by
      apply Finset.sum_nonneg
      intro k hk
      have hk' := Finset.mem_erase.mp hk
      have hki := (Finset.mem_erase.mp hk'.2).1
      have ha : 0 ≤ T.a i k := T.a_offdiag_nonneg hki.symm
      have hm : 0 ≤ T.m k := le_of_lt (T.m_pos k)
      exact mul_nonneg ha hm
    have hs1 := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin T.n)))
      (f := fun k => T.a i k * T.m k) (Finset.mem_univ i)
    have hmem : j ∈ (Finset.univ : Finset (Fin T.n)).erase i := by
      rw [Finset.mem_erase]
      exact ⟨hij.symm, Finset.mem_univ _⟩
    have hs2 := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin T.n)).erase i)
      (f := fun k => T.a i k * T.m k) hmem
    rw [T.row_sum i] at hs1
    dsimp [rest] at hrest
    linarith [hs1, hs2, hrest]
  have hrow1T : T.a j j * T.m j + T.a j i * T.m i ≤ 0 := by
    let rest : Finset (Fin T.n) :=
      (Finset.univ.erase j).erase i
    have hrest : 0 ≤ rest.sum (fun k => T.a j k * T.m k) := by
      apply Finset.sum_nonneg
      intro k hk
      have hk' := Finset.mem_erase.mp hk
      have hkj := (Finset.mem_erase.mp hk'.2).1
      have ha : 0 ≤ T.a j k := T.a_offdiag_nonneg hkj.symm
      have hm : 0 ≤ T.m k := le_of_lt (T.m_pos k)
      exact mul_nonneg ha hm
    have hs1 := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin T.n)))
      (f := fun k => T.a j k * T.m k) (Finset.mem_univ j)
    have hmem : i ∈ (Finset.univ : Finset (Fin T.n)).erase j := by
      rw [Finset.mem_erase]
      exact ⟨hij, Finset.mem_univ _⟩
    have hs2 := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin T.n)).erase j)
      (f := fun k => T.a j k * T.m k) hmem
    rw [T.row_sum j] at hs1
    dsimp [rest] at hrest
    linarith [hs1, hs2, hrest]
  have hrow0 : 2 * D.w 0 * D.m 0 ≥ D.a 0 1 * D.m 1 := by
    have h := hrow0T
    rw [hai] at h
    have h' : 2 * T.w i * T.m i ≥ T.a i j * T.m j := by linarith [h]
    change 2 * T.w i * T.m i ≥ T.a i j * T.m j
    exact h'
  have hrow1 : 2 * D.w 1 * D.m 1 ≥ D.a 0 1 * D.m 0 := by
    have h := hrow1T
    rw [haj, T.a_symmetric j i] at h
    have h' : 2 * T.w j * T.m j ≥ T.a i j * T.m i := by linarith [h]
    change 2 * T.w j * T.m j ≥ T.a i j * T.m i
    exact h'
  have hcancel_left : ∀ (w : ℤ), 0 < w → ∀ a b : ℤ,
      w * b ≤ w * a → b ≤ a := by
    intro w hw a b hab
    by_contra hnot
    have hlt : a < b := lt_of_not_ge hnot
    have hmul : w * a < w * b := Int.mul_lt_mul_of_pos_left hlt hw
    linarith
  have realizeA : ∀ (E : LocalNumericalData 2) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.a 0 0 = -2 * r → E.a 1 1 = -2 * r →
      E.a 0 1 = r → E.a 1 0 = r → (∀ i, 0 < E.m i) →
      mConditionA2 E.m → isA2 E := by
    intro E r hr hw0 hw1 haa0 haa1 hae01 hae10 hmp hmc
    unfold isA2 realizesPattern
    refine ⟨r, hr, ?_, ?_, hmp, hmc⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [scalarMatrix, pathMatrix, constantVector, hw0, hw1, haa0,
          haa1, hae01, hae10] <;> ring
    · funext a
      fin_cases a <;> simp [scalarVector, constantVector, hw0, hw1]
  have realizeB : ∀ (E : LocalNumericalData 2) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = 2 * r → E.a 0 0 = -2 * r →
      E.a 1 1 = -4 * r → E.a 0 1 = 2 * r → E.a 1 0 = 2 * r →
      (∀ i, 0 < E.m i) → mConditionB2 E.m → isB2 E := by
    intro E r hr hw0 hw1 haa0 haa1 hae01 hae10 hmp hmc
    unfold isB2 realizesPattern
    refine ⟨r, hr, ?_, ?_, hmp, hmc⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [scalarMatrix, pathLastMatrix, lastVector, hw0, hw1, haa0,
          haa1, hae01, hae10] <;> ring
    · funext a
      fin_cases a <;> simp [scalarVector, lastVector, hw0, hw1] <;> ring
  have realizeG : ∀ (E : LocalNumericalData 2) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = 3 * r → E.a 0 0 = -2 * r →
      E.a 1 1 = -6 * r → E.a 0 1 = 3 * r → E.a 1 0 = 3 * r →
      (∀ i, 0 < E.m i) → mConditionG2 E.m → isG2 E := by
    intro E r hr hw0 hw1 haa0 haa1 hae01 hae10 hmp hmc
    unfold isG2 realizesPattern
    refine ⟨r, hr, ?_, ?_, hmp, hmc⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [scalarMatrix, pathLastMatrix, lastVector, hw0, hw1, haa0,
          haa1, hae01, hae10] <;> ring
    · funext a
      fin_cases a <;> simp [scalarVector, lastVector, hw0, hw1] <;> ring
  have hp_cases : p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases hp_cases with hp1 | hp23
  · have hq_cases : q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases hq_cases with hq1 | hq23
    · have ha0 : D.a 0 1 = D.w 0 := by simpa [hp1] using hpa
      have ha1 : D.a 0 1 = D.w 1 := by simpa [hq1] using hqa
      have hw_eq : D.w 0 = D.w 1 := ha0.symm.trans ha1
      have haa1 : D.a 1 1 = -2 * D.w 0 := by
        calc
          D.a 1 1 = -2 * D.w 1 := hDdiag1
          _ = -2 * D.w 0 := by rw [← hw_eq]
      have hae10 : D.a 1 0 = D.w 0 := by
        calc
          D.a 1 0 = D.a 0 1 := hDsym 1 0
          _ = D.w 0 := ha0
      have hmc : mConditionA2 D.m := by
        have h0 := hrow0
        have h1 := hrow1
        rw [ha0] at h0
        rw [ha1] at h1
        change 2 * D.m 0 ≥ D.m 1 ∧ 2 * D.m 1 ≥ D.m 0
        constructor
        · apply hcancel_left (D.w 0) hwi (2 * D.m 0) (D.m 1)
          linarith
        · apply hcancel_left (D.w 1) hwj (2 * D.m 1) (D.m 0)
          linarith
      refine ⟨Equiv.refl _, ?_⟩
      left
      change isA2 D
      exact realizeA D (D.w 0) hwi rfl hw_eq.symm hDdiag0 haa1 ha0 hae10
        (local_m_pos S) hmc
    · rcases hq23 with hq2 | hq3
      · have ha0 : D.a 0 1 = D.w 0 := by simpa [hp1] using hpa
        have ha1 : D.a 0 1 = 2 * D.w 1 := by simpa [hq2] using hqa
        have hw02 : D.w 0 = 2 * D.w 1 := ha0.symm.trans ha1
        let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
        let E : LocalNumericalData 2 := reindexLocalData D e
        have he0 : e 0 = (1 : Fin 2) := by
          simp only [e, Equiv.swap_apply_left]
        have he1 : e 1 = (0 : Fin 2) := by
          simp only [e, Equiv.swap_apply_right]
        have hEw0 : E.w 0 = D.w 1 := by
          change D.w (e 0) = D.w 1
          rw [he0]
        have hEw1 : E.w 1 = 2 * D.w 1 := by
          calc
            E.w 1 = D.w 0 := by
              change D.w (e 1) = D.w 0
              rw [he1]
            _ = 2 * D.w 1 := hw02
        have hEaa0 : E.a 0 0 = -2 * D.w 1 := by
          change D.a (e 0) (e 0) = -2 * D.w 1
          rw [he0]
          exact hDdiag1
        have hEaa1 : E.a 1 1 = -4 * D.w 1 := by
          calc
            E.a 1 1 = D.a 0 0 := by
              change D.a (e 1) (e 1) = D.a 0 0
              rw [he1]
            _ = -2 * D.w 0 := hDdiag0
            _ = -4 * D.w 1 := by rw [hw02]; ring
        have hEae01 : E.a 0 1 = 2 * D.w 1 := by
          calc
            E.a 0 1 = D.a 1 0 := by
              change D.a (e 0) (e 1) = D.a 1 0
              rw [he0, he1]
            _ = D.a 0 1 := hDsym 1 0
            _ = 2 * D.w 1 := ha1
        have hEae10 : E.a 1 0 = 2 * D.w 1 := by
          calc
            E.a 1 0 = D.a 0 1 := by
              change D.a (e 1) (e 0) = D.a 0 1
              rw [he1, he0]
            _ = 2 * D.w 1 := ha1
        have hmpE : ∀ z, 0 < E.m z := by
          intro z
          change 0 < D.m (e z)
          simpa [D] using local_m_pos S (e z)
        have hm01 : D.m 1 ≥ D.m 0 := by
          have h := hrow1
          rw [ha1] at h
          apply hcancel_left (D.w 1) hwj (D.m 1) (D.m 0)
          linarith
        have hm10 : 2 * D.m 0 ≥ D.m 1 := by
          have h := hrow0
          rw [ha0, hw02] at h
          apply hcancel_left (D.w 1) hwj (2 * D.m 0) (D.m 1)
          linarith
        have hmcE : mConditionB2 E.m := by
          change D.m (e 0) ≥ D.m (e 1) ∧ 2 * D.m (e 1) ≥ D.m (e 0)
          rw [he0, he1]
          exact And.intro hm01 hm10
        refine ⟨e, ?_⟩
        right
        left
        change isB2 E
        exact realizeB E (D.w 1) hwj hEw0 hEw1 hEaa0 hEaa1 hEae01 hEae10
          hmpE hmcE
      · have ha0 : D.a 0 1 = D.w 0 := by simpa [hp1] using hpa
        have ha1 : D.a 0 1 = 3 * D.w 1 := by simpa [hq3] using hqa
        have hw03 : D.w 0 = 3 * D.w 1 := ha0.symm.trans ha1
        let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
        let E : LocalNumericalData 2 := reindexLocalData D e
        have he0 : e 0 = (1 : Fin 2) := by
          simp only [e, Equiv.swap_apply_left]
        have he1 : e 1 = (0 : Fin 2) := by
          simp only [e, Equiv.swap_apply_right]
        have hEw0 : E.w 0 = D.w 1 := by
          change D.w (e 0) = D.w 1
          rw [he0]
        have hEw1 : E.w 1 = 3 * D.w 1 := by
          calc
            E.w 1 = D.w 0 := by
              change D.w (e 1) = D.w 0
              rw [he1]
            _ = 3 * D.w 1 := hw03
        have hEaa0 : E.a 0 0 = -2 * D.w 1 := by
          change D.a (e 0) (e 0) = -2 * D.w 1
          rw [he0]
          exact hDdiag1
        have hEaa1 : E.a 1 1 = -6 * D.w 1 := by
          calc
            E.a 1 1 = D.a 0 0 := by
              change D.a (e 1) (e 1) = D.a 0 0
              rw [he1]
            _ = -2 * D.w 0 := hDdiag0
            _ = -6 * D.w 1 := by rw [hw03]; ring
        have hEae01 : E.a 0 1 = 3 * D.w 1 := by
          calc
            E.a 0 1 = D.a 1 0 := by
              change D.a (e 0) (e 1) = D.a 1 0
              rw [he0, he1]
            _ = D.a 0 1 := hDsym 1 0
            _ = 3 * D.w 1 := ha1
        have hEae10 : E.a 1 0 = 3 * D.w 1 := by
          calc
            E.a 1 0 = D.a 0 1 := by
              change D.a (e 1) (e 0) = D.a 0 1
              rw [he1, he0]
            _ = 3 * D.w 1 := ha1
        have hmpE : ∀ z, 0 < E.m z := by
          intro z
          change 0 < D.m (e z)
          simpa [D] using local_m_pos S (e z)
        have hm01 : 2 * D.m 1 ≥ 3 * D.m 0 := by
          have h := hrow1
          rw [ha1] at h
          apply hcancel_left (D.w 1) hwj (2 * D.m 1) (3 * D.m 0)
          linarith
        have hm10 : 2 * D.m 0 ≥ D.m 1 := by
          have h := hrow0
          rw [ha0, hw03] at h
          apply hcancel_left (D.w 1) hwj (2 * D.m 0) (D.m 1)
          linarith
        have hmcE : mConditionG2 E.m := by
          change 2 * D.m (e 0) ≥ 3 * D.m (e 1) ∧
            2 * D.m (e 1) ≥ D.m (e 0)
          rw [he0, he1]
          exact And.intro hm01 hm10
        refine ⟨e, ?_⟩
        right
        right
        change isG2 E
        exact realizeG E (D.w 1) hwj hEw0 hEw1 hEaa0 hEaa1 hEae01 hEae10
          hmpE hmcE
  · rcases hp23 with hp2 | hp3
    · have ha0 : D.a 0 1 = 2 * D.w 0 := by simpa [hp2] using hpa
      have hpq2 : 2 * q < 4 := by simpa [hp2] using hpq_lt
      have hq1 : q = 1 := by omega
      have ha1 : D.a 0 1 = D.w 1 := by simpa [hq1] using hqa
      have hw1 : D.w 1 = 2 * D.w 0 := ha1.symm.trans ha0
      have hm0 : D.m 1 ≤ D.m 0 := by
        have h := hrow0
        rw [ha0] at h
        apply hcancel_left (D.w 0) hwi (D.m 0) (D.m 1)
        linarith
      have hm1 : 2 * D.m 1 ≥ D.m 0 := by
        have h := hrow1
        rw [ha1, hw1] at h
        apply hcancel_left (D.w 0) hwi (2 * D.m 1) (D.m 0)
        linarith
      have hmc : mConditionB2 D.m := by
        change D.m 0 ≥ D.m 1 ∧ 2 * D.m 1 ≥ D.m 0
        exact ⟨hm0, hm1⟩
      have haa1 : D.a 1 1 = -4 * D.w 0 := by
        calc
          D.a 1 1 = -2 * D.w 1 := hDdiag1
          _ = -4 * D.w 0 := by rw [hw1]; ring
      have hae10 : D.a 1 0 = 2 * D.w 0 := by
        calc
          D.a 1 0 = D.a 0 1 := hDsym 1 0
          _ = 2 * D.w 0 := ha0
      refine ⟨Equiv.refl _, ?_⟩
      right
      left
      change isB2 D
      exact realizeB D (D.w 0) hwi rfl hw1 hDdiag0 haa1 ha0 hae10
        (local_m_pos S) hmc
    · have ha0 : D.a 0 1 = 3 * D.w 0 := by simpa [hp3] using hpa
      have hpq3 : 3 * q < 4 := by simpa [hp3] using hpq_lt
      have hq1 : q = 1 := by omega
      have ha1 : D.a 0 1 = D.w 1 := by simpa [hq1] using hqa
      have hw1 : D.w 1 = 3 * D.w 0 := ha1.symm.trans ha0
      have hm0 : 3 * D.m 1 ≤ 2 * D.m 0 := by
        have h := hrow0
        rw [ha0] at h
        apply hcancel_left (D.w 0) hwi (2 * D.m 0) (3 * D.m 1)
        linarith
      have hm1 : 2 * D.m 1 ≥ D.m 0 := by
        have h := hrow1
        rw [ha1, hw1] at h
        apply hcancel_left (D.w 0) hwi (2 * D.m 1) (D.m 0)
        linarith
      have hmc : mConditionG2 D.m := by
        change 2 * D.m 0 ≥ 3 * D.m 1 ∧ 2 * D.m 1 ≥ D.m 0
        exact ⟨hm0, hm1⟩
      have haa1 : D.a 1 1 = -6 * D.w 0 := by
        calc
          D.a 1 1 = -2 * D.w 1 := hDdiag1
          _ = -6 * D.w 0 := by rw [hw1]; ring
      have hae10 : D.a 1 0 = 3 * D.w 0 := by
        calc
          D.a 1 0 = D.a 0 1 := hDsym 1 0
          _ = 3 * D.w 0 := ha0
      refine ⟨Equiv.refl _, ?_⟩
      right
      right
      change isG2 D
      exact realizeG D (D.w 0) hwi rfl hw1 hDdiag0 haa1 ha0 hae10
        (local_m_pos S) hmc

/-! The three-by-three classification (`A₃`, `C₃`, and `B₃`). -/
theorem lemma_three_by_three (T : NumericalType) (S : MinusTwoSubgraph T 3)
    (hn : 3 < T.n) (hedges : hasTripleAtLeastTwoEdges (localData S)) :
    UpToReordering (localData S) (fun D => isA3 D ∨ isC3 D ∨ isB3 D) := by
  classical
  let D := localData S
  have hAm : Matrix.mulVec (fun p q => (T.a p q : ℝ))
      (fun p => (T.m p : ℝ)) = 0 := by
    funext p
    change (∑ q, (T.a p q : ℝ) * (T.m q : ℝ)) = 0
    exact_mod_cast T.row_sum p
  have hconnected : ¬ ∃ I : Set (Fin T.n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃p q⦄, p ∈ I → q ∉ I → (T.a p q : ℝ) = 0 := by
    intro h
    apply T.connected
    rcases h with ⟨I, hI, hne, hcross⟩
    refine ⟨I, hI, hne, ?_⟩
    intro p q hp hq
    exact_mod_cast hcross hp hq
  have hreal := Formalization.Books.Models.Unit02.recurring_symmetric_real
    (fun p q => (T.a p q : ℝ)) (fun p => (T.m p : ℝ))
    (fun p q => by exact_mod_cast T.a_symmetric p q)
    (by intro p q h; exact_mod_cast T.a_offdiag_nonneg h)
    (by intro p; exact_mod_cast T.m_pos p) hAm hconnected
  have h01 : S.index (0 : Fin 3) ≠ S.index 1 := by
    intro h
    have h' : (0 : Fin 3) = 1 := S.index_injective h
    norm_num at h'
  have h02 : S.index (0 : Fin 3) ≠ S.index 2 := by
    intro h
    have h' : (0 : Fin 3) = 2 := S.index_injective h
    omega
  have h12 : S.index (1 : Fin 3) ≠ S.index 2 := by
    intro h
    have h' : (1 : Fin 3) = 2 := S.index_injective h
    omega
  have hrestrict (x : Fin 3 → ℝ) :
      (∑ p : Fin T.n, (if p = S.index 0 then x 0 else
        if p = S.index 1 then x 1 else if p = S.index 2 then x 2 else 0) *
        Matrix.mulVec (fun p q => (T.a p q : ℝ))
          (fun p => if p = S.index 0 then x 0 else
            if p = S.index 1 then x 1 else if p = S.index 2 then x 2 else 0) p) =
      ∑ i : Fin 3, x i * Matrix.mulVec
        (fun i j => (T.a (S.index i) (S.index j) : ℝ)) x i := by
    let y : Fin T.n → ℝ := fun p =>
      if p = S.index 0 then x 0 else
        if p = S.index 1 then x 1 else if p = S.index 2 then x 2 else 0
    have hinner (r : Fin T.n) :
        Matrix.mulVec (fun u v => (T.a u v : ℝ)) y r =
          ((T.a r (S.index 0) : ℤ) : ℝ) * x 0 +
            ((T.a r (S.index 1) : ℤ) : ℝ) * x 1 +
              ((T.a r (S.index 2) : ℤ) : ℝ) * x 2 := by
      change (∑ q : Fin T.n, (T.a r q : ℝ) * y q) = _
      dsimp [y]
      calc
        (∑ q : Fin T.n, (T.a r q : ℝ) *
            (if q = S.index 0 then x 0 else
              if q = S.index 1 then x 1 else if q = S.index 2 then x 2 else 0)) =
            ∑ q : Fin T.n,
              ((if q = S.index 0 then (T.a r q : ℝ) * x 0 else 0) +
                (if q = S.index 1 then (T.a r q : ℝ) * x 1 else 0) +
                  (if q = S.index 2 then (T.a r q : ℝ) * x 2 else 0)) := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases hq0 : q = S.index 0 <;>
            by_cases hq1 : q = S.index 1 <;>
              by_cases hq2 : q = S.index 2 <;>
                simp [hq0, hq1, hq2, h01, h02, h12, h01.symm, h02.symm,
                  h12.symm] <;> ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp [y, h01, h02, h12, h01.symm, h02.symm, h12.symm]
    have houter :
        (∑ p : Fin T.n, y p * Matrix.mulVec
          (fun p q => (T.a p q : ℝ)) y p) =
          x 0 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 0) +
            x 1 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 1) +
              x 2 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 2) := by
      dsimp [y]
      calc
        (∑ p : Fin T.n, (if p = S.index 0 then x 0 else
            if p = S.index 1 then x 1 else if p = S.index 2 then x 2 else 0) *
            Matrix.mulVec (fun p q => (T.a p q : ℝ)) y p) =
            ∑ p : Fin T.n,
              ((if p = S.index 0 then x 0 * Matrix.mulVec
                (fun p q => (T.a p q : ℝ)) y p else 0) +
                (if p = S.index 1 then x 1 * Matrix.mulVec
                  (fun p q => (T.a p q : ℝ)) y p else 0) +
                  (if p = S.index 2 then x 2 * Matrix.mulVec
                    (fun p q => (T.a p q : ℝ)) y p else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hp0 : p = S.index 0 <;>
            by_cases hp1 : p = S.index 1 <;>
              by_cases hp2 : p = S.index 2 <;>
                simp [hp0, hp1, hp2, h01, h02, h12, h01.symm, h02.symm,
                  h12.symm] <;> ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          change _ = x 0 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 0) +
            x 1 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 1) +
              x 2 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 2)
          simp [h01, h02, h12, h01.symm, h02.symm, h12.symm]
    change (∑ p : Fin T.n, y p * Matrix.mulVec
      (fun p q => (T.a p q : ℝ)) y p) = _
    calc
      _ = x 0 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 0) +
          x 1 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 1) +
            x 2 * Matrix.mulVec (fun p q => (T.a p q : ℝ)) y (S.index 2) := houter
      _ = x 0 * (((T.a (S.index 0) (S.index 0) : ℤ) : ℝ) * x 0 +
          ((T.a (S.index 0) (S.index 1) : ℤ) : ℝ) * x 1 +
            ((T.a (S.index 0) (S.index 2) : ℤ) : ℝ) * x 2) +
          x 1 * (((T.a (S.index 1) (S.index 0) : ℤ) : ℝ) * x 0 +
            ((T.a (S.index 1) (S.index 1) : ℤ) : ℝ) * x 1 +
              ((T.a (S.index 1) (S.index 2) : ℤ) : ℝ) * x 2) +
            x 2 * (((T.a (S.index 2) (S.index 0) : ℤ) : ℝ) * x 0 +
              ((T.a (S.index 2) (S.index 1) : ℤ) : ℝ) * x 1 +
                ((T.a (S.index 2) (S.index 2) : ℤ) : ℝ) * x 2) := by
          rw [hinner (S.index 0), hinner (S.index 1), hinner (S.index 2)]
      _ = _ := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        ring
  have hstrict : ∀ x : Fin 3 → ℝ, x ≠ 0 →
      ∑ i : Fin 3, x i * Matrix.mulVec
        (fun i j => (T.a (S.index i) (S.index j) : ℝ)) x i < 0 := by
    intro x hx
    let y : Fin T.n → ℝ := fun p =>
      if p = S.index 0 then x 0 else
        if p = S.index 1 then x 1 else if p = S.index 2 then x 2 else 0
    have hle : ∑ i : Fin 3, x i * Matrix.mulVec
        (fun i j => (T.a (S.index i) (S.index j) : ℝ)) x i ≤ 0 := by
      have hq := (hreal y).1
      rw [← hrestrict x]
      exact hq
    by_contra hnot
    have hzero : ∑ i : Fin 3, x i * Matrix.mulVec
        (fun i j => (T.a (S.index i) (S.index j) : ℝ)) x i = 0 := by
      apply le_antisymm hle
      exact le_of_not_gt hnot
    have hy : ∃ c : ℝ, y = c • (fun p => (T.m p : ℝ)) :=
      (hreal y).2.mp (by
        have hzero' : ∑ i : Fin T.n, y i * Matrix.mulVec
            (fun p q => (T.a p q : ℝ)) y i = 0 := by
          calc
            _ = ∑ i : Fin 3, x i * Matrix.mulVec
                (fun i j => (T.a (S.index i) (S.index j) : ℝ)) x i := by
              simpa [y] using (hrestrict x)
            _ = 0 := hzero
        exact hzero')
    let I : Finset (Fin T.n) := {S.index 0, S.index 1, S.index 2}
    have hI : I ≠ Finset.univ := by
      intro hI
      have hc := congrArg Finset.card hI
      simp [I, h01, h02, h12] at hc
      have hc' : 3 = T.n := by simpa using hc
      omega
    have hcomp : Iᶜ ≠ ∅ := by
      intro hzero
      apply hI
      exact (Finset.compl_eq_empty_iff I).mp hzero
    obtain ⟨k, hk⟩ : Iᶜ.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hcomp
    rcases hy with ⟨c, hcy⟩
    have hck := congrFun hcy k
    have hmk : (0 : ℝ) < T.m k := by exact_mod_cast T.m_pos k
    have hkI : k ∉ I := Finset.mem_compl.mp hk
    have hk0 : k ≠ S.index 0 := by
      intro h
      apply hkI
      simp [I, h]
    have hk1 : k ≠ S.index 1 := by
      intro h
      apply hkI
      simp [I, h]
    have hk2 : k ≠ S.index 2 := by
      intro h
      apply hkI
      simp [I, h]
    have hck' : (0 : ℝ) = c * (T.m k : ℝ) := by
      simpa [y, hk0, hk1, hk2] using hck
    have hc0 : c = 0 := by nlinarith
    have hx0 : x = 0 := by
      funext i
      fin_cases i
      · have hi := congrFun hcy (S.index 0)
        simpa [y, h01, h02, h01.symm, h02.symm, h12.symm, hc0] using hi
      · have hi := congrFun hcy (S.index 1)
        simpa [y, h01, h02, h01.symm, h02.symm, h12.symm, hc0] using hi
      · have hi := congrFun hcy (S.index 2)
        simpa [y, h01, h02, h01.symm, h02.symm, h12.symm, hc0] using hi
    exact hx hx0
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => (T.a (S.index i) (S.index j) : ℝ)
  let B : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => -((T.a (S.index i) (S.index j) : ℤ) : ℝ)
  have hBpos : B.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · rw [Matrix.isHermitian_iff_isSymm]
      apply Matrix.IsSymm.ext
      intro i j
      change -((T.a (S.index j) (S.index i) : ℤ) : ℝ) =
        -((T.a (S.index i) (S.index j) : ℤ) : ℝ)
      exact_mod_cast congrArg Neg.neg
        (T.a_symmetric (S.index j) (S.index i))
    · intro x hx
      have hq := hstrict x hx
      have hq' : 0 < -∑ i : Fin 3, x i * Matrix.mulVec
            (fun i j => (T.a (S.index i) (S.index j) : ℝ)) x i := by
        linarith
      calc
        0 < -∑ i : Fin 3, x i * Matrix.mulVec
            (fun i j => (T.a (S.index i) (S.index j) : ℝ)) x i := hq'
        _ = dotProduct (star x) (Matrix.mulVec B x) := by
          simp [B, Matrix.mulVec, dotProduct]
  have hBA : B = -A := by
    ext i j
    change -((T.a (S.index i) (S.index j) : ℤ) : ℝ) =
      -((T.a (S.index i) (S.index j) : ℤ) : ℝ)
    rfl
  have hdetB : 0 < Matrix.det B := Matrix.PosDef.det_pos hBpos
  have hdetlocal : Matrix.det A < 0 := by
    have hdetneg := Matrix.det_neg A
    norm_num at hdetneg
    rw [hBA, hdetneg] at hdetB
    linarith
  let e01 : Fin 2 → Fin 3 := fun i => if i = 0 then 0 else 1
  let e12 : Fin 2 → Fin 3 := fun i => if i = 0 then 1 else 2
  let e02 : Fin 2 → Fin 3 := fun i => if i = 0 then 0 else 2
  have he01 : Function.Injective e01 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [e01] at h ⊢
  have he12 : Function.Injective e12 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [e12] at h ⊢
  have he02 : Function.Injective e02 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [e02] at h ⊢
  have hdiag0 : T.a (S.index 0) (S.index 0) = -2 * T.w (S.index 0) :=
    (S.minus_two 0).2
  have hdiag1 : T.a (S.index 1) (S.index 1) = -2 * T.w (S.index 1) :=
    (S.minus_two 1).2
  have hdiag2 : T.a (S.index 2) (S.index 2) = -2 * T.w (S.index 2) :=
    (S.minus_two 2).2
  have hs01 : T.a (S.index 1) (S.index 0) = T.a (S.index 0) (S.index 1) :=
    T.a_symmetric _ _
  have hs12 : T.a (S.index 2) (S.index 1) = T.a (S.index 1) (S.index 2) :=
    T.a_symmetric _ _
  have hs02 : T.a (S.index 2) (S.index 0) = T.a (S.index 0) (S.index 2) :=
    T.a_symmetric _ _
  have hbound01 : 0 < 4 * (D.w 0 : ℝ) * D.w 1 - D.a 0 1 ^ 2 := by
    have h := Matrix.PosDef.det_pos (hBpos.submatrix he01)
    have h' : (D.a 0 1 : ℝ) * D.a 0 1 <
        2 * (D.w 0 : ℝ) * (2 * D.w 1) := by
      simpa [e01, B, Matrix.det_fin_two, Matrix.submatrix, D, localData,
        hdiag0, hdiag1, hs01] using h
    nlinarith
  have hbound12 : 0 < 4 * (D.w 1 : ℝ) * D.w 2 - D.a 1 2 ^ 2 := by
    have h := Matrix.PosDef.det_pos (hBpos.submatrix he12)
    have h' : (D.a 1 2 : ℝ) * D.a 1 2 <
        2 * (D.w 1 : ℝ) * (2 * D.w 2) := by
      simpa [e12, B, Matrix.det_fin_two, Matrix.submatrix, D, localData,
        hdiag1, hdiag2, hs12] using h
    nlinarith
  have hbound02 : 0 < 4 * (D.w 0 : ℝ) * D.w 2 - D.a 0 2 ^ 2 := by
    have h := Matrix.PosDef.det_pos (hBpos.submatrix he02)
    have h' : (D.a 0 2 : ℝ) * D.a 0 2 <
        2 * (D.w 0 : ℝ) * (2 * D.w 2) := by
      simpa [e02, B, Matrix.det_fin_two, Matrix.submatrix, D, localData,
        hdiag0, hdiag2, hs02] using h
    nlinarith
  have hDdiag : ∀ i, D.a i i = -2 * D.w i := by
    intro i
    simpa [D, localData] using (S.minus_two i).2
  have hDsym : ∀ i j, D.a i j = D.a j i := by
    intro i j
    simpa [D] using local_a_symmetric S i j
  have hdetformula := determinant_three_by_three_formula D hDdiag hDsym
  have hdetcast : (D.a.det : ℝ) = A.det := by
    have hmap : Matrix.map D.a (fun x : ℤ => (x : ℝ)) = A := by
      ext i j
      rw [Matrix.map_apply]
      change (T.a (S.index i) (S.index j) : ℝ) =
        (T.a (S.index i) (S.index j) : ℝ)
      rfl
    have hcast := (Int.cast_det D.a : (D.a.det : ℝ) = _)
    rw [hmap] at hcast
    exact hcast
  have hdetreal : (D.a.det : ℝ) < 0 := by
    rw [hdetcast]
    exact hdetlocal
  have hquot : ∀ (i j : Fin 3), 0 < D.a i j →
      0 < 4 * (D.w i : ℝ) * D.w j - D.a i j ^ 2 →
      ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ D.a i j = p * D.w i ∧
        D.a i j = q * D.w j ∧ p * q < 4 := by
    intro i j hij hb
    have hdivi : D.w i ∣ D.a i j := by
      simpa [D, localData] using T.w_dvd (S.index i) (S.index j)
    have hdivj : D.w j ∣ D.a i j := by
      have h := T.w_dvd (S.index j) (S.index i)
      simpa [D, localData, T.a_symmetric (S.index j) (S.index i)] using h
    have hwi : 0 < D.w i := local_w_pos S i
    have hwj : 0 < D.w j := local_w_pos S j
    let p : ℤ := D.a i j / D.w i
    let q : ℤ := D.a i j / D.w j
    have hp : 0 < p := by
      dsimp [p]
      exact Int.ediv_pos_of_pos_of_dvd hij (le_of_lt hwi) hdivi
    have hq : 0 < q := by
      dsimp [q]
      exact Int.ediv_pos_of_pos_of_dvd hij (le_of_lt hwj) hdivj
    have hpa : D.a i j = p * D.w i := by
      dsimp [p]
      exact (Int.ediv_mul_cancel hdivi).symm
    have hqa : D.a i j = q * D.w j := by
      dsimp [q]
      exact (Int.ediv_mul_cancel hdivj).symm
    have hbZ : 0 < 4 * D.w i * D.w j - D.a i j ^ 2 := by
      exact_mod_cast hb
    have hsq : D.a i j ^ 2 = p * q * (D.w i * D.w j) := by
      calc
        D.a i j ^ 2 = D.a i j * D.a i j := by ring
        _ = (p * D.w i) * D.a i j := by rw [hpa]
        _ = (p * D.w i) * (q * D.w j) := by rw [hqa]
        _ = p * q * (D.w i * D.w j) := by ring
    have hwpq : 0 < D.w i * D.w j := mul_pos hwi hwj
    have hpq : p * q < 4 := by
      nlinarith [hbZ, hsq]
    exact ⟨p, q, hp, hq, hpa, hqa, hpq⟩
  have hrowT : ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
      T.a (S.index i) (S.index i) * T.m (S.index i) +
        T.a (S.index i) (S.index j) * T.m (S.index j) +
        T.a (S.index i) (S.index k) * T.m (S.index k) ≤ 0 := by
    intro i j k hij hik hjk
    let rest : Finset (Fin T.n) :=
      ((Finset.univ.erase (S.index i)).erase (S.index j)).erase (S.index k)
    have hrest : 0 ≤ rest.sum (fun l => T.a (S.index i) l * T.m l) := by
      apply Finset.sum_nonneg
      intro k hk
      have hk' := Finset.mem_erase.mp hk
      have hkj := (Finset.mem_erase.mp hk'.2).1
      have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk'.2).2).1
      have ha : 0 ≤ T.a (S.index i) k := T.a_offdiag_nonneg hki.symm
      have hm : 0 ≤ T.m k := le_of_lt (T.m_pos k)
      exact mul_nonneg ha hm
    have hs1 := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin T.n)))
      (a := S.index i)
      (f := fun k => T.a (S.index i) k * T.m k)
      (Finset.mem_univ _)
    have hm1 : S.index j ∈
        (Finset.univ : Finset (Fin T.n)).erase (S.index i) := by
      rw [Finset.mem_erase]
      exact ⟨fun h => hij (S.index_injective h.symm), Finset.mem_univ _⟩
    have hs2 := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin T.n)).erase (S.index i))
      (a := S.index j)
      (f := fun k => T.a (S.index i) k * T.m k) hm1
    have hm2 : S.index k ∈
        ((Finset.univ : Finset (Fin T.n)).erase (S.index i)).erase
          (S.index j) := by
      rw [Finset.mem_erase]
      exact ⟨fun h => hjk (S.index_injective h.symm), by
        rw [Finset.mem_erase]
        exact ⟨fun h => hik (S.index_injective h.symm), Finset.mem_univ _⟩⟩
    have hs3 := Finset.sum_erase_add
      (s := ((Finset.univ : Finset (Fin T.n)).erase (S.index i)).erase
        (S.index j))
      (a := S.index k)
      (f := fun k => T.a (S.index i) k * T.m k) hm2
    have hs3' : rest.sum (fun l => T.a (S.index i) l * T.m l) +
        T.a (S.index i) (S.index k) * T.m (S.index k) =
        (((Finset.univ : Finset (Fin T.n)).erase (S.index i)).erase
          (S.index j)).sum
          (fun l => T.a (S.index i) l * T.m l) := by
      change rest.sum (fun l => T.a (S.index i) l * T.m l) +
          T.a (S.index i) (S.index k) * T.m (S.index k) =
        ((Finset.univ.erase (S.index i)).erase (S.index j)).sum
          (fun l => T.a (S.index i) l * T.m l)
      exact hs3
    rw [T.row_sum (S.index i)] at hs1
    linarith [hs1, hs2, hs3', hrest]
  have hrow : ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
      2 * D.w i * D.m i ≥ D.a i j * D.m j + D.a i k * D.m k := by
    intro i j k hij hik hjk
    have h := hrowT i j k hij hik hjk
    rw [(S.minus_two i).2] at h
    change 2 * T.w (S.index i) * T.m (S.index i) ≥
      T.a (S.index i) (S.index j) * T.m (S.index j) +
        T.a (S.index i) (S.index k) * T.m (S.index k)
    linarith [h]
  have hrow0 := hrow 0 1 2 (by decide) (by decide) (by decide)
  have hrow1 := hrow 1 0 2 (by decide) (by decide) (by decide)
  have hrow2 := hrow 2 0 1 (by decide) (by decide) (by decide)
  have realizeA3 : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.w 2 = r →
      E.a 0 0 = -2 * r → E.a 1 1 = -2 * r → E.a 2 2 = -2 * r →
      E.a 0 1 = r → E.a 1 0 = r → E.a 1 2 = r → E.a 2 1 = r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionA3 E.m → isA3 E := by
    intro E r hr hw0 hw1 hw2 haa0 haa1 haa2 hae01 hae10 hae12 hae21 hae02 hae20 hmp hmc
    unfold isA3 realizesPattern
    refine ⟨r, hr, ?_, ?_, hmp, hmc⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [scalarMatrix, pathMatrix, constantVector, hw0, hw1, hw2,
          haa0, haa1, haa2, hae01, hae10, hae12, hae21, hae02, hae20] <;> ring
    · funext a
      fin_cases a <;> simp [scalarVector, constantVector, hw0, hw1, hw2]
  have realizeC3 : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = r → E.w 1 = r → E.w 2 = 2 * r →
      E.a 0 0 = -2 * r → E.a 1 1 = -2 * r → E.a 2 2 = -4 * r →
      E.a 0 1 = r → E.a 1 0 = r → E.a 1 2 = 2 * r → E.a 2 1 = 2 * r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionC3 E.m → isC3 E := by
    intro E r hr hw0 hw1 hw2 haa0 haa1 haa2 hae01 hae10 hae12 hae21 hae02 hae20 hmp hmc
    unfold isC3 realizesPattern
    refine ⟨r, hr, ?_, ?_, hmp, hmc⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [scalarMatrix, pathLastMatrix, lastVector, hw0, hw1, hw2,
          haa0, haa1, haa2, hae01, hae10, hae12, hae21, hae02, hae20] <;> ring
    · funext a
      fin_cases a <;> simp [scalarVector, lastVector, hw0, hw1, hw2] <;> ring
  have realizeB3 : ∀ (E : LocalNumericalData 3) (r : ℤ),
      0 < r → E.w 0 = 2 * r → E.w 1 = 2 * r → E.w 2 = r →
      E.a 0 0 = -4 * r → E.a 1 1 = -4 * r → E.a 2 2 = -2 * r →
      E.a 0 1 = 2 * r → E.a 1 0 = 2 * r → E.a 1 2 = 2 * r → E.a 2 1 = 2 * r →
      E.a 0 2 = 0 → E.a 2 0 = 0 → (∀ i, 0 < E.m i) →
      mConditionB3 E.m → isB3 E := by
    intro E r hr hw0 hw1 hw2 haa0 haa1 haa2 hae01 hae10 hae12 hae21 hae02 hae20 hmp hmc
    unfold isB3 realizesPattern
    refine ⟨r, hr, ?_, ?_, hmp, hmc⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [scalarMatrix, pathLastMatrix, lastVector, hw0, hw1, hw2,
          haa0, haa1, haa2, hae01, hae10, hae12, hae21, hae02, hae20] <;> ring
    · funext a
      fin_cases a <;> simp [scalarVector, lastVector, hw0, hw1, hw2] <;> ring
  have hnonneg : ∀ i j : Fin 3, i ≠ j → 0 ≤ D.a i j := by
    intro i j hij
    change 0 ≤ T.a (S.index i) (S.index j)
    apply T.a_offdiag_nonneg
    intro h
    exact hij (S.index_injective h)
  have hEdge : ∀ i j : Fin 3, hasEdgeAt D i.val j.val → 0 < D.a i j := by
    intro i j h
    rcases h with ⟨i', j', hi, hj, hp⟩
    have hi' : i' = i := Fin.ext hi
    have hj' : j' = j := Fin.ext hj
    simpa [hi', hj'] using hp
  have hdetR : (D.a.det : ℝ) =
      -8 * (D.w 0 : ℝ) * D.w 1 * D.w 2 +
        2 * (D.a 0 1 : ℝ) ^ 2 * D.w 2 +
        2 * (D.a 1 2 : ℝ) ^ 2 * D.w 0 +
        2 * (D.a 0 2 : ℝ) ^ 2 * D.w 1 +
        2 * (D.a 0 1 : ℝ) * D.a 0 2 * D.a 1 2 := by
    exact_mod_cast hdetformula
  have hdetI :
      -8 * (D.w 0 : ℝ) * D.w 1 * D.w 2 +
          2 * (D.a 0 1 : ℝ) ^ 2 * D.w 2 +
          2 * (D.a 1 2 : ℝ) ^ 2 * D.w 0 +
          2 * (D.a 0 2 : ℝ) ^ 2 * D.w 1 +
          2 * (D.a 0 1 : ℝ) * D.a 0 2 * D.a 1 2 < 0 := by
    rw [← hdetR]
    exact hdetreal
  have hpairlower : ∀ i j : Fin 3, 0 < D.a i j →
      0 < 4 * (D.w i : ℝ) * D.w j - D.a i j ^ 2 →
      (D.w i : ℝ) ≤ D.a i j ∧ (D.w j : ℝ) ≤ D.a i j := by
    intro i j hij hb
    obtain ⟨p, q, hp, hq, hpa, hqa, hpq⟩ := hquot i j hij hb
    have hpR : (1 : ℝ) ≤ p := by
      exact_mod_cast (show (1 : ℤ) ≤ p by omega)
    have hqR : (1 : ℝ) ≤ q := by
      exact_mod_cast (show (1 : ℤ) ≤ q by omega)
    have hpaR : (D.a i j : ℝ) = (p : ℝ) * D.w i := by
      exact_mod_cast hpa
    have hqaR : (D.a i j : ℝ) = (q : ℝ) * D.w j := by
      exact_mod_cast hqa
    have hwi : (0 : ℝ) < D.w i := by exact_mod_cast local_w_pos S i
    have hwj : (0 : ℝ) < D.w j := by exact_mod_cast local_w_pos S j
    constructor <;> nlinarith
  have htriangle : ¬ (0 < D.a 0 1 ∧ 0 < D.a 0 2 ∧ 0 < D.a 1 2) := by
    rintro ⟨ha01, ha02, ha12⟩
    have hl01 := hpairlower 0 1 ha01 hbound01
    have hl02 := hpairlower 0 2 ha02 hbound02
    have hl12 := hpairlower 1 2 ha12 hbound12
    have ha01R : (0 : ℝ) < D.a 0 1 := by exact_mod_cast ha01
    have ha02R : (0 : ℝ) < D.a 0 2 := by exact_mod_cast ha02
    have ha12R : (0 : ℝ) < D.a 1 2 := by exact_mod_cast ha12
    have hw0 : (0 : ℝ) ≤ D.w 0 := le_of_lt (by exact_mod_cast local_w_pos S 0)
    have hw1 : (0 : ℝ) ≤ D.w 1 := le_of_lt (by exact_mod_cast local_w_pos S 1)
    have hw2 : (0 : ℝ) ≤ D.w 2 := le_of_lt (by exact_mod_cast local_w_pos S 2)
    have hs01 : (D.w 0 : ℝ) * D.w 1 ≤ (D.a 0 1 : ℝ) ^ 2 := by
        simpa [pow_two] using
        (mul_le_mul hl01.1 hl01.2 hw1 (le_of_lt ha01R))
    have hs02 : (D.w 0 : ℝ) * D.w 2 ≤ (D.a 0 2 : ℝ) ^ 2 := by
        simpa [pow_two] using
        (mul_le_mul hl02.1 hl02.2 hw2 (le_of_lt ha02R))
    have hs12 : (D.w 1 : ℝ) * D.w 2 ≤ (D.a 1 2 : ℝ) ^ 2 := by
        simpa [pow_two] using
        (mul_le_mul hl12.1 hl12.2 hw2 (le_of_lt ha12R))
    have hp12 : (D.w 1 : ℝ) * D.w 2 ≤
        (D.a 1 2 : ℝ) * D.a 0 2 := by
      calc
        (D.w 1 : ℝ) * D.w 2 ≤ D.a 1 2 * D.w 2 :=
          mul_le_mul_of_nonneg_right hl12.1 hw2
        _ ≤ D.a 1 2 * D.a 0 2 :=
          mul_le_mul_of_nonneg_left hl02.2 (le_of_lt ha12R)
    have hprod : (D.w 0 : ℝ) * D.w 1 * D.w 2 ≤
        (D.a 0 1 : ℝ) * D.a 0 2 * D.a 1 2 := by
      calc
        (D.w 0 : ℝ) * D.w 1 * D.w 2 ≤
            D.w 0 * (D.a 1 2 * D.a 0 2) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hp12 hw0
        _ ≤ D.a 0 1 * (D.a 1 2 * D.a 0 2) := by
          exact mul_le_mul_of_nonneg_right hl01.1
            (mul_nonneg (le_of_lt ha12R) (le_of_lt ha02R))
        _ = D.a 0 1 * D.a 0 2 * D.a 1 2 := by ring
    have hs01' : (D.w 0 : ℝ) * D.w 1 * D.w 2 ≤
        (D.a 0 1 : ℝ) ^ 2 * D.w 2 :=
      mul_le_mul_of_nonneg_right hs01 hw2
    have hs02' : (D.w 0 : ℝ) * D.w 1 * D.w 2 ≤
        (D.a 0 2 : ℝ) ^ 2 * D.w 1 := by
      calc
        (D.w 0 : ℝ) * D.w 1 * D.w 2 =
            (D.w 0 * D.w 2) * D.w 1 := by ring
        _ ≤ (D.a 0 2 : ℝ) ^ 2 * D.w 1 :=
          mul_le_mul_of_nonneg_right hs02 hw1
    have hs12' : (D.w 0 : ℝ) * D.w 1 * D.w 2 ≤
        (D.a 1 2 : ℝ) ^ 2 * D.w 0 :=
      by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right hs12 hw0
    nlinarith [hdetI, hs01', hs02', hs12', hprod]
  rcases hedges with ⟨he01, he02⟩ | ⟨he01, he12⟩ | ⟨he02, he12⟩
  · have ha01 : 0 < D.a 0 1 := hEdge 0 1 he01
    have ha02 : 0 < D.a 0 2 := hEdge 0 2 he02
    have ha12 : D.a 1 2 = 0 := by
      have h := hnonneg 1 2 (by decide)
      by_contra hne
      have : 0 < D.a 1 2 := lt_of_le_of_ne h (Ne.symm hne)
      exact htriangle ⟨ha01, ha02, this⟩
    exact classify_three_two_edges D (local_w_pos S) (local_m_pos S)
      hDdiag hDsym hdetI hbound01 hbound02 ha01 ha02 ha12 hquot hrow
      realizeA3 realizeC3 realizeB3
  · have ha01 : 0 < D.a 0 1 := hEdge 0 1 he01
    have ha12 : 0 < D.a 1 2 := hEdge 1 2 he12
    have ha02 : D.a 0 2 = 0 := by
      have h := hnonneg 0 2 (by decide)
      by_contra hne
      have : 0 < D.a 0 2 := lt_of_le_of_ne h (Ne.symm hne)
      exact htriangle ⟨ha01, this, ha12⟩
    apply classify_three_path D (local_w_pos S) (local_m_pos S) hDdiag hDsym ha02
    · simpa [ha02] using hdetI
    · exact hbound01
    · exact hbound12
    · exact ha01
    · exact ha12
    · exact hquot
    · exact hrow
    · exact realizeA3
    · exact realizeC3
    · exact realizeB3
  · have ha02 : 0 < D.a 0 2 := hEdge 0 2 he02
    have ha12 : 0 < D.a 1 2 := hEdge 1 2 he12
    have ha01 : D.a 0 1 = 0 := by
      have h := hnonneg 0 1 (by decide)
      by_contra hne
      have : 0 < D.a 0 1 := lt_of_le_of_ne h (Ne.symm hne)
      exact htriangle ⟨this, ha02, ha12⟩
    exact classify_three_two_edges_right D (local_w_pos S) (local_m_pos S)
      hDdiag hDsym hdetI hbound02 hbound12 ha02 ha12 ha01 hquot hrow
      realizeA3 realizeC3 realizeB3

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
    (6 ≤ k ∧ (UpToReordering D (fun E => isAn E ∨ isCn E ∨ isBn E) ∨
        UpToReordering D (fun E => isDn E))) ∨
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
