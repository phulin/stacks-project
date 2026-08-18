import Formalization.Books.Models.Unit05.Classification

/-!
# Classification of minimal type for genus zero and one

Formal statements from Section 6 of *Semistable Reduction*.  The numerical
types in the source are indexed by `1, ..., n`; this file uses `Fin n`.
-/

noncomputable section

namespace Formalization.Books.Models.Unit06

open Formalization.Books.Models.Unit03
open Formalization.Books.Models.Unit05

/-! The genus coordinate of an ambient numerical type after changing its
indexing type. -/
def ambientGenusAt {T : NumericalType} {k : ℕ} (h : T.n = k) : Fin k → ℤ :=
  h ▸ T.g

/-! A displayed four-coordinate configuration, with independent positive
parameters for the multiplicities and weights.  The positivity of the
coordinates in the ambient `NumericalType` is recorded by `m` and `w`.
-/
def realizesTypePattern {k : ℕ} (T : NumericalType) (h : T.n = k)
    (mBase : Fin k → ℤ) (aBase : Matrix (Fin k) (Fin k) ℤ)
    (wBase gBase : Fin k → ℤ) : Prop :=
  ∃ m w : ℤ, 0 < m ∧ 0 < w ∧
    (ambientDataAt h).m = scalarVector mBase m ∧
      (ambientDataAt h).a = scalarMatrix aBase w ∧
        (ambientDataAt h).w = scalarVector wBase w ∧
          ambientGenusAt h = gBase

def hasTypePattern {k : ℕ} (T : NumericalType)
    (mBase : Fin k → ℤ) (aBase : Matrix (Fin k) (Fin k) ℤ)
    (wBase gBase : Fin k → ℤ) : Prop :=
  ∃ h : T.n = k, realizesTypePattern T h mBase aBase wBase gBase

/-! Matrix constructors for the chains, cycles, and branches occurring in the
source list.  The edge function is evaluated at the lower-index endpoint. -/
def pathMatrixByEdge (k : ℕ) (diagonal edge : Fin k → ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal i
    else if i.val + 1 = j.val then edge i
    else if j.val + 1 = i.val then edge j
    else 0

def cycleMatrix (k : ℕ) (diagonal edge wrap : ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then edge
    else if (i.val = 0 ∧ j.val + 1 = k) ∨
        (j.val = 0 ∧ i.val + 1 = k) then wrap
    else 0

def branchPathMatrix (k center leaf₁ leaf₂ : ℕ)
    (diagonal pathEdge : Fin k → ℤ) (leafEdge : ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal i
    else if i.val + 1 = j.val ∧ j.val ≤ center then pathEdge i
    else if j.val + 1 = i.val ∧ i.val ≤ center then pathEdge j
    else if (i.val = center ∧ j.val = leaf₁) ∨
        (i.val = leaf₁ ∧ j.val = center) then leafEdge
    else if (i.val = center ∧ j.val = leaf₂) ∨
        (i.val = leaf₂ ∧ j.val = center) then leafEdge
    else 0

def starMatrixByEdge (k center : ℕ) (diagonal edge : Fin k → ℤ) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then diagonal i
    else if i.val = center then edge j
    else if j.val = center then edge i
    else 0

def undirectedEdgeMatrix (k : ℕ) (edges : ℕ → ℕ → Prop)
    (diagonal edge : ℤ) : Matrix (Fin k) (Fin k) ℤ := by
  classical
  exact fun i j => if i = j then diagonal else if edges i.val j.val then edge else 0

def negativeTwoDiagonal {k : ℕ} (wBase : Fin k → ℤ) : Fin k → ℤ :=
  fun i => -2 * wBase i

def zeroGenusVector {k : ℕ} : Fin k → ℤ :=
  constantVector 0

/-! The genus-zero normal form. -/
def IsGenusZeroNormalForm (T : NumericalType) : Prop :=
  T.n = 1 ∧
    T.m (firstIndex T) = 1 ∧
      T.a (firstIndex T) (firstIndex T) = 0 ∧
        T.w (firstIndex T) = 1 ∧ T.g (firstIndex T) = 0

/-! The first twenty-four finite genus-one configurations. -/
def IsGenusOneItemOne (T : NumericalType) : Prop :=
  hasTypePattern (k := 1) T
    (constantVector 1)
    (fun _ _ => 0)
    (constantVector 1)
    (constantVector 1)

def IsGenusOneTwoCycle (T : NumericalType) : Prop :=
  hasTypePattern (k := 2) T
    (constantVector 1)
    (cycleMatrix 2 (-2) 2 2)
    (constantVector 1)
    zeroGenusVector

def IsGenusOneUp4 (T : NumericalType) : Prop :=
  hasTypePattern (k := 2) T
    (fun i => if i.val = 0 then 2 else 1)
    (pathMatrixByEdge 2 (fun i => if i.val = 0 then -2 else -8) (fun _ => 4))
    (fun i => if i.val = 0 then 1 else 4)
    zeroGenusVector

def IsGenusOneThreeCycle (T : NumericalType) : Prop :=
  hasTypePattern (k := 3) T
    (constantVector 1)
    (cycleMatrix 3 (-2) 1 1)
    (constantVector 1)
    zeroGenusVector

def IsGenusOneEqualUp3 (T : NumericalType) : Prop :=
  hasTypePattern (k := 3) T
    (fun i => if i.val = 1 then 2 else 1)
    (pathMatrixByEdge 3
      (fun i => if i.val = 2 then -6 else -2)
      (fun i => if i.val = 0 then 1 else 3))
    (fun i => if i.val = 2 then 3 else 1)
    zeroGenusVector

def IsGenusOneEqualDown3 (T : NumericalType) : Prop :=
  hasTypePattern (k := 3) T
    (fun i => if i.val = 2 then 3 else if i.val = 1 then 2 else 1)
    (pathMatrixByEdge 3
      (fun i => if i.val = 2 then -2 else -6)
      (fun _ => 3))
    (fun i => if i.val = 2 then 1 else 3)
    zeroGenusVector

def IsGenusOneUpUp (T : NumericalType) : Prop :=
  hasTypePattern (k := 3) T
    (fun i => if i.val < 2 then 2 else 1)
    (pathMatrixByEdge 3
      (fun i => if i.val = 0 then -2 else if i.val = 1 then -4 else -8)
      (fun i => if i.val = 0 then 2 else 4))
    (fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else 4)
    zeroGenusVector

def IsGenusOneUpDown (T : NumericalType) : Prop :=
  hasTypePattern (k := 3) T
    (constantVector 1)
    (pathMatrixByEdge 3
      (fun i => if i.val = 1 then -4 else -2)
      (fun _ => 2))
    (fun i => if i.val = 1 then 2 else 1)
    zeroGenusVector

def IsGenusOneDownUp (T : NumericalType) : Prop :=
  hasTypePattern (k := 3) T
    (fun i => if i.val = 1 then 2 else 1)
    (pathMatrixByEdge 3
      (fun i => if i.val = 1 then -2 else -4)
      (fun _ => 2))
    (fun i => if i.val = 1 then 1 else 2)
    zeroGenusVector

def IsGenusOneFourCycle (T : NumericalType) : Prop :=
  hasTypePattern (k := 4) T
    (constantVector 1)
    (cycleMatrix 4 (-2) 1 1)
    (constantVector 1)
    zeroGenusVector

def IsGenusOneUpEqualUp (T : NumericalType) : Prop :=
  hasTypePattern (k := 4) T
    (fun i => if i.val < 3 then 2 else 1)
    (pathMatrixByEdge 4
      (fun i => if i.val = 0 then -2 else if i.val < 3 then -4 else -8)
      (fun i => if i.val < 2 then 2 else 4))
    (fun i => if i.val = 0 then 1 else if i.val < 3 then 2 else 4)
    zeroGenusVector

def IsGenusOneUpEqualDown (T : NumericalType) : Prop :=
  hasTypePattern (k := 4) T
    (constantVector 1)
    (pathMatrixByEdge 4
      (fun i => if i.val = 0 then -2 else if i.val = 3 then -2 else -4)
      (fun _ => 2))
    (fun i => if i.val = 0 ∨ i.val = 3 then 1 else 2)
    zeroGenusVector

def IsGenusOneDownEqualUp (T : NumericalType) : Prop :=
  hasTypePattern (k := 4) T
    (fun i => if i.val = 0 ∨ i.val = 3 then 1 else 2)
    (pathMatrixByEdge 4
      (fun i => if i.val = 0 ∨ i.val = 3 then -4 else -2)
      (fun i => if i.val = 0 ∨ i.val = 2 then 2 else 1))
    (fun i => if i.val = 0 ∨ i.val = 3 then 2 else 1)
    zeroGenusVector

def IsGenusOneTripleWithUp (T : NumericalType) : Prop :=
  hasTypePattern (k := 4) T
    (fun i => if i.val = 0 then 2 else 1)
    (starMatrixByEdge 4 0
      (fun i => if i.val = 3 then -4 else -2)
      (fun i => if i.val = 3 then 2 else 1))
    (constantVector 1)
    zeroGenusVector

def IsGenusOneTripleWithDown (T : NumericalType) : Prop :=
  hasTypePattern (k := 4) T
    (fun i => if i.val = 0 ∨ i.val = 3 then 2 else 1)
    (starMatrixByEdge 4 0
      (fun i => if i.val = 3 then -2 else -4)
      (fun _ => 2))
    (fun i => if i.val = 3 then 1 else 2)
    zeroGenusVector

def IsGenusOneFiveCycle (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (constantVector 1)
    (cycleMatrix 5 (-2) 1 1)
    (constantVector 1)
    zeroGenusVector

def IsGenusOneEqualEqualUpEqual (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (fun i =>
      if i.val = 0 ∨ i.val = 4 then 1
      else if i.val = 1 ∨ i.val = 3 then 2
      else 3)
    (pathMatrixByEdge 5
      (fun i => if i.val < 3 then -2 else -4)
      (fun i => if i.val < 2 then 1 else 2))
    (fun i => if i.val < 3 then 1 else 2)
    zeroGenusVector

def IsGenusOneEqualEqualDownEqual (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (fun i => if i.val = 4 then 2 else i.val + 1)
    (pathMatrixByEdge 5
      (fun i => if i.val < 3 then -4 else -2)
      (fun i => if i.val < 3 then 2 else 1))
    (fun i => if i.val < 3 then 2 else 1)
    zeroGenusVector

def IsGenusOneUpEqualEqualUp (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (fun i => if i.val < 4 then 2 else 1)
    (pathMatrixByEdge 5
      (fun i => if i.val = 0 then -2 else if i.val < 4 then -4 else -8)
      (fun i => if i.val < 3 then 2 else 4))
    (fun i => if i.val = 0 then 1 else if i.val < 4 then 2 else 4)
    zeroGenusVector

def IsGenusOneUpEqualEqualDown (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (constantVector 1)
    (pathMatrixByEdge 5
      (fun i => if i.val = 0 ∨ i.val = 4 then -2 else -4)
      (fun _ => 2))
    (fun i => if i.val = 0 ∨ i.val = 4 then 1 else 2)
    zeroGenusVector

def IsGenusOneDownEqualEqualUp (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (fun i => if i.val = 0 ∨ i.val = 4 then 1 else 2)
    (pathMatrixByEdge 5
      (fun i => if i.val = 0 ∨ i.val = 4 then -4 else -2)
      (fun i => if i.val = 0 ∨ i.val = 3 then 2 else 1))
    (fun i => if i.val = 0 ∨ i.val = 4 then 2 else 1)
    zeroGenusVector

def IsGenusOneQuadruple (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (fun i => if i.val = 0 then 2 else 1)
    (starMatrix 5 0 (constantVector (-2)) 1)
    (constantVector 1)
    zeroGenusVector

def IsGenusOneTripleExtendedUp (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (fun i => if i.val = 0 then 1 else if i.val < 3 then 2 else 1)
    (branchPathMatrix 5 2 3 4
      (fun i => if i.val = 0 then -4 else -2)
      (fun i => if i.val = 0 then 2 else 1)
      1)
    (fun i => if i.val = 0 then 2 else 1)
    zeroGenusVector

def IsGenusOneTripleExtendedDown (T : NumericalType) : Prop :=
  hasTypePattern (k := 5) T
    (fun i => if i.val < 3 then 2 else 1)
    (branchPathMatrix 5 2 3 4
      (fun i => if i.val = 0 then -2 else -4)
      (fun _ => 2)
      2)
    (fun i => if i.val = 0 then 1 else 2)
    zeroGenusVector

/-! The seven unbounded and completed configurations. -/
def nCycleM (k : ℕ) : Fin k → ℤ :=
  constantVector 1

def nCycleW (k : ℕ) : Fin k → ℤ :=
  constantVector 1

def nCycleA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  cycleMatrix k (-2) 1 1

def upChainEqualUpM (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val + 1 = k then 1 else 2

def upChainEqualUpW (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val = 0 then 1 else if i.val + 1 = k then 4 else 2

def upChainEqualUpA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  pathMatrixByEdge k
    (negativeTwoDiagonal (upChainEqualUpW k))
    (fun i => if i.val + 2 = k then 4 else 2)

def upChainEqualDownM (k : ℕ) : Fin k → ℤ :=
  constantVector 1

def upChainEqualDownW (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val = 0 ∨ i.val + 1 = k then 1 else 2

def upChainEqualDownA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  pathMatrixByEdge k (negativeTwoDiagonal (upChainEqualDownW k)) (fun _ => 1)

def downChainEqualUpM (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val = 0 ∨ i.val + 1 = k then 1 else 2

def downChainEqualUpW (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val = 0 ∨ i.val + 1 = k then 2 else 1

def downChainEqualUpA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  pathMatrixByEdge k
    (negativeTwoDiagonal (downChainEqualUpW k))
    (fun i => if i.val = 0 ∨ i.val + 2 = k then 2 else 1)

def dnExtendedUpM (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val = 0 ∨ i.val + 2 ≥ k then 1 else 2

def dnExtendedUpW (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val = 0 then 2 else 1

def dnExtendedUpA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  branchPathMatrix k (k - 3) (k - 2) (k - 1)
    (negativeTwoDiagonal (dnExtendedUpW k))
    (fun i => if i.val = 0 then 2 else 1)
    1

def dnExtendedDownM (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val + 2 ≥ k then 1 else 2

def dnExtendedDownW (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val = 0 then 1 else 2

def dnExtendedDownA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  branchPathMatrix k (k - 3) (k - 2) (k - 1)
    (negativeTwoDiagonal (dnExtendedDownW k))
    (fun _ => 2)
    2

def doubleTripleM (k : ℕ) : Fin k → ℤ :=
  fun i => if i.val < 2 ∨ i.val + 2 ≥ k then 1 else 2

def doubleTripleW (k : ℕ) : Fin k → ℤ :=
  constantVector 1

def doubleTripleA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if i = j then -2
    else if (i.val + 1 = j.val ∧ 1 ≤ i.val ∧ j.val ≤ k - 2) ∨
        (j.val + 1 = i.val ∧ 1 ≤ j.val ∧ i.val ≤ k - 2) then 1
    else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) then 1
    else if (i.val = k - 3 ∧ j.val = k - 1) ∨
        (i.val = k - 1 ∧ j.val = k - 3) then 1
    else 0

def IsGenusOneNCycle (T : NumericalType) : Prop :=
  ∃ k : ℕ, 6 ≤ k ∧
    hasTypePattern (k := k) T
      (nCycleM k) (nCycleA k) (nCycleW k) (zeroGenusVector)

def IsGenusOneUpChainEqualUp (T : NumericalType) : Prop :=
  ∃ k : ℕ, 6 ≤ k ∧
    hasTypePattern (k := k) T
      (upChainEqualUpM k) (upChainEqualUpA k) (upChainEqualUpW k)
      (zeroGenusVector)

def IsGenusOneUpChainEqualDown (T : NumericalType) : Prop :=
  ∃ k : ℕ, 6 ≤ k ∧
    hasTypePattern (k := k) T
      (upChainEqualDownM k) (upChainEqualDownA k) (upChainEqualDownW k)
      (zeroGenusVector)

def IsGenusOneDownChainEqualUp (T : NumericalType) : Prop :=
  ∃ k : ℕ, 6 ≤ k ∧
    hasTypePattern (k := k) T
      (downChainEqualUpM k) (downChainEqualUpA k) (downChainEqualUpW k)
      (zeroGenusVector)

def IsGenusOneDnExtendedUp (T : NumericalType) : Prop :=
  ∃ k : ℕ, 6 ≤ k ∧
    hasTypePattern (k := k) T
      (dnExtendedUpM k) (dnExtendedUpA k) (dnExtendedUpW k)
      (zeroGenusVector)

def IsGenusOneDnExtendedDown (T : NumericalType) : Prop :=
  ∃ k : ℕ, 6 ≤ k ∧
    hasTypePattern (k := k) T
      (dnExtendedDownM k) (dnExtendedDownA k) (dnExtendedDownW k)
      (zeroGenusVector)

def IsGenusOneDoubleTriple (T : NumericalType) : Prop :=
  ∃ k : ℕ, 6 ≤ k ∧
    hasTypePattern (k := k) T
      (doubleTripleM k) (doubleTripleA k) (doubleTripleW k)
      (zeroGenusVector)

def e6CompletedMatrix : Matrix (Fin 7) (Fin 7) ℤ :=
  undirectedEdgeMatrix 7
    (fun i j =>
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) ∨
      (i = 2 ∧ j = 6) ∨ (i = 6 ∧ j = 2) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
      (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5))
    (-2) 1

def e7CompletedMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  undirectedEdgeMatrix 8
    (fun i j =>
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
      (i = 3 ∧ j = 7) ∨ (i = 7 ∧ j = 3) ∨
      (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
      (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5))
    (-2) 1

def e8CompletedMatrix : Matrix (Fin 9) (Fin 9) ℤ :=
  undirectedEdgeMatrix 9
    (fun i j =>
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
      (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
      (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
      (i = 5 ∧ j = 8) ∨ (i = 8 ∧ j = 5) ∨
      (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6))
    (-2) 1

def IsGenusOneE6Completed (T : NumericalType) : Prop :=
  hasTypePattern (k := 7) T
    (fun i =>
      if i.val = 0 ∨ i.val = 3 ∨ i.val = 5 then 1
      else if i.val = 1 ∨ i.val = 4 ∨ i.val = 6 then 2
      else 3)
    e6CompletedMatrix
    (constantVector 1)
    zeroGenusVector

def IsGenusOneE7Completed (T : NumericalType) : Prop :=
  hasTypePattern (k := 8) T
    (fun i =>
      if i.val = 0 ∨ i.val = 6 then 1
      else if i.val = 1 ∨ i.val = 5 ∨ i.val = 7 then 2
      else if i.val = 2 ∨ i.val = 4 then 3
      else 4)
    e7CompletedMatrix
    (constantVector 1)
    zeroGenusVector

def IsGenusOneE8Completed (T : NumericalType) : Prop :=
  hasTypePattern (k := 9) T
    (fun i =>
      if i.val = 0 then 1
      else if i.val = 1 ∨ i.val = 7 then 2
      else if i.val = 2 ∨ i.val = 8 then 3
      else if i.val = 3 then 4
      else if i.val = 4 then 5
      else if i.val = 6 then 4 else 6)
    e8CompletedMatrix
    (constantVector 1)
    zeroGenusVector

/-! The disjunction of all normal forms in the source list. -/
def IsGenusOneNormalForm (T : NumericalType) : Prop :=
  IsGenusOneItemOne T ∨
    IsGenusOneTwoCycle T ∨
      IsGenusOneUp4 T ∨
        IsGenusOneThreeCycle T ∨
          IsGenusOneEqualUp3 T ∨
            IsGenusOneEqualDown3 T ∨
              IsGenusOneUpUp T ∨
                IsGenusOneUpDown T ∨
                  IsGenusOneDownUp T ∨
                    IsGenusOneFourCycle T ∨
                      IsGenusOneUpEqualUp T ∨
                        IsGenusOneUpEqualDown T ∨
                          IsGenusOneDownEqualUp T ∨
                            IsGenusOneTripleWithUp T ∨
                              IsGenusOneTripleWithDown T ∨
                                IsGenusOneFiveCycle T ∨
                                  IsGenusOneEqualEqualUpEqual T ∨
                                    IsGenusOneEqualEqualDownEqual T ∨
                                      IsGenusOneUpEqualEqualUp T ∨
                                        IsGenusOneUpEqualEqualDown T ∨
                                          IsGenusOneDownEqualEqualUp T ∨
                                            IsGenusOneQuadruple T ∨
                                              IsGenusOneTripleExtendedUp T ∨
                                                IsGenusOneTripleExtendedDown T ∨
                                                  IsGenusOneNCycle T ∨
                                                    IsGenusOneUpChainEqualUp T ∨
                                                      IsGenusOneUpChainEqualDown T ∨
                                                        IsGenusOneDownChainEqualUp T ∨
                                                          IsGenusOneDnExtendedUp T ∨
                                                            IsGenusOneDnExtendedDown T ∨
                                                              IsGenusOneDoubleTriple T ∨
                                                                IsGenusOneE6Completed T ∨
                                                                  IsGenusOneE7Completed T ∨
                                                                    IsGenusOneE8Completed T

/-! The source's two classification assertions. -/
theorem minimal_genus_zero_classification (T : NumericalType)
    (hminimal : IsMinimal T) (hgenus : IsOfGenus T 0) :
    IsGenusZeroNormalForm T := by
  sorry

theorem genus_zero_normal_form_is_minimal_and_genus_zero (T : NumericalType)
    (hpattern : IsGenusZeroNormalForm T) :
    IsMinimal T ∧ genus T = 0 := by
  sorry

theorem minimal_genus_one_classification (T : NumericalType)
    (hminimal : IsMinimal T) (hgenus : IsOfGenus T 1) :
    ∃ T' : NumericalType, EquivalentNumericalType T T' ∧
      IsGenusOneNormalForm T' := by
  sorry

/-! Every displayed normal form is intended as a minimal numerical type of
genus one whenever it is realized by a `NumericalType`. -/
theorem genus_one_normal_form_is_minimal_and_genus_one (T : NumericalType)
    (hpattern : IsGenusOneNormalForm T) :
    IsMinimal T ∧ genus T = 1 := by
  sorry

end Formalization.Books.Models.Unit06
