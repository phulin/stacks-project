import Formalization.Books.Algebra.Unit43.GeometricallyReduced
import Formalization.Books.Algebra.Unit47.GeometricallyIrreducible
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 49: Geometrically integral algebras

The geometric integral predicate is expressed using Mathlib's `IsDomain`,
with the same field-base-change tensor-product orientation as Chapters 43 and
47.  The characterization lemmas retain the source's finite-extension and
algebraic-closure tests.
-/

namespace Formalization.Books.Algebra.Unit49

open scoped TensorProduct

open Formalization.Books.Algebra.Unit43
open Formalization.Books.Algebra.Unit47

universe u v w

noncomputable section

/-! ## Geometrically integral algebras -/

/-- An algebra over a field is geometrically integral when every field base
change is an integral domain. -/
def IsGeometricallyIntegral (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop :=
  ∀ (K : Type w) [Field K] [Algebra k K],
    IsDomain (K ⊗[k] S)

/-- Geometric integrality is equivalent to geometric irreducibility together
with geometric reducedness. -/
theorem isGeometricallyIntegral_iff_geometricallyIrreducible_and_geometricallyReduced
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    IsGeometricallyIntegral k S ↔
      IsGeometricallyIrreducible k S ∧ IsGeometricallyReduced k S := by
  sorry

/-- Geometric integrality can be tested after finite field extensions and
after passage to an algebraic closure. -/
theorem isGeometricallyIntegral_iff_finiteExtension_iff_algebraicClosure
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    (IsGeometricallyIntegral k S ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k']
        [FiniteDimensional k k'],
        IsDomain (k' ⊗[k] S)) ∧
      ((∀ (k' : Type u) [Field k'] [Algebra k k']
        [FiniteDimensional k k'],
        IsDomain (k' ⊗[k] S)) ↔
        IsDomain (AlgebraicClosure k ⊗[k] S)) := by
  sorry

/-- Tensoring a geometrically integral algebra with an integral-domain
`k`-algebra remains an integral domain. -/
theorem isGeometricallyIntegral_any_integral_base_change
    {k : Type u} {S : Type v} {R : Type w}
    [Field k] [CommRing S] [CommRing R] [Algebra k S] [Algebra k R]
    [IsDomain R] (hS : IsGeometricallyIntegral k S) :
    IsDomain (R ⊗[k] S) := by
  sorry

end

end Formalization.Books.Algebra.Unit49
