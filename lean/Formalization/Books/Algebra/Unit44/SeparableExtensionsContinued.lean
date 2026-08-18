import Formalization.Books.Algebra.Unit43.GeometricallyReduced
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Commutative Algebra, Chapter 44: Separable extensions, continued

The source's separating transcendence bases use Mathlib's canonical
`IsTranscendenceBasis` and `Algebra.IsSeparable`.  The characteristic-
`p` root extension is Mathlib's `AdjoinPthRoots`, and the perfect closure
inside an algebraic closure is Mathlib's `perfectClosure`.
-/

namespace Formalization.Books.Algebra.Unit44

open Set
open scoped TensorProduct

universe u v w

noncomputable section

open Formalization.Books.Algebra.Unit42
open Formalization.Books.Algebra.Unit43

/-! ## Separating transcendence bases -/

/- A separating transcendence basis is a basis for which the remaining
   algebraic extension is separable.  This source-facing conjunction is
   needed because Unit42's `IsSeparablyGenerated` packages existence of
   such a basis rather than a chosen basis. -/
/-- A separating transcendence basis for a field extension. -/
def IsSeparatingTranscendenceBasis
    (k : Type u) (K : Type v) {ι : Type w} (x : ι → K)
    [Field k] [Field K] [Algebra k K] : Prop :=
  IsTranscendenceBasis k x ∧
    Algebra.IsSeparable (IntermediateField.adjoin k (range x)) K

/-- The mini-separability argument produces a separating transcendence basis
by omitting one element from the displayed finite generating family. -/
theorem exists_isSeparatingTranscendenceBasis_of_mini_separability
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p n : ℕ) (hp : 1 < p) [CharP k p]
    (x : Fin (n + 1) → K)
    (hbasis : IsTranscendenceBasis k (fun i : Fin n => x i.castSucc))
    (hgen : IntermediateField.adjoin k (range x) = ⊤)
    (hpow : ∀ (s : Finset K),
      LinearIndepOn k id (s : Set K) →
        LinearIndepOn k (· ^ p) (s : Set K)) :
    ∃ j : Fin (n + 1),
      IsSeparatingTranscendenceBasis k K
        (fun i : Fin n => x (Fin.succAbove j i)) := by
  sorry

/-! The source's `k^(1/p)` is represented by Mathlib's canonical
`AdjoinPthRoots k`, which also handles the characteristic-zero case using
the field's exponential characteristic. -/

/-- For a positive-characteristic field extension, separability, the
Frobenius linear-independence test, reducedness after the canonical
`p`-th-root base change, and geometric reducedness are equivalent. -/
theorem isSeparableExtension_iff_frobenius_linearIndependent_iff_tensorProduct_reduced_iff_geometricallyReduced
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) [CharP k p] :
    (IsSeparableExtension k K ↔
      (∀ (s : Finset K),
        LinearIndepOn k id (s : Set K) →
          LinearIndepOn k (· ^ p) (s : Set K))) ∧
      ((∀ (s : Finset K),
        LinearIndepOn k id (s : Set K) →
          LinearIndepOn k (· ^ p) (s : Set K)) ↔
        IsReduced (K ⊗[k] AdjoinPthRoots k)) ∧
      (IsReduced (K ⊗[k] AdjoinPthRoots k) ↔
        IsGeometricallyReduced k K) := by
  sorry

/-- A separably generated field extension is separable. -/
theorem isSeparableExtension_of_isSeparablyGenerated
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hK : IsSeparablyGenerated k K) :
    IsSeparableExtension k K := by
  sorry

/-! ## Geometric reducedness and purely inseparable extensions -/

/- The source's `k^(perf)` is the relative perfect closure of `k` in its
   canonical algebraic closure.  This is a field in its own right and has
   the induced `k`-algebra structure. -/

/-- Geometric reducedness can be tested by finite purely inseparable base
changes, by `k^(1/p)`, by the perfect closure, or by an algebraic closure. -/
theorem isGeometricallyReduced_iff_finitePurelyInseparable_iff_pthRoot_iff_perfectClosure_iff_algebraicClosure
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    ((∀ (k' : Type w) [Field k'] [Algebra k k']
      [FiniteDimensional k k'] [IsPurelyInseparable k k'],
      IsReduced (k' ⊗[k] S)) ↔
        IsReduced (AdjoinPthRoots k ⊗[k] S)) ∧
      (IsReduced (AdjoinPthRoots k ⊗[k] S) ↔
        IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S)) ∧
      (IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S) ↔
        IsReduced (AlgebraicClosure k ⊗[k] S)) ∧
      (IsReduced (AlgebraicClosure k ⊗[k] S) ↔
        IsGeometricallyReduced k S) := by
  sorry

end

end Formalization.Books.Algebra.Unit44
