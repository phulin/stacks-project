import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit42.SeparableExtensions
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 165: Geometrically normal algebras

The source-facing declarations use the normal-ring predicate from Chapter 37,
the arbitrary separable-extension interface from Chapter 42, and the
canonical finite-type, finite-dimensional, purely inseparable,
perfect-closure, and tensor-product APIs.
-/

namespace Formalization.Books.Algebra.Unit165

open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit42
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Geometrically normal algebras -/

/- The four conditions below are equivalent by the main lemma.  The definition
   uses the first one, which is the direct field-base-change formulation. -/
/-- A `k`-algebra is geometrically normal when every field base change is a
normal ring. -/
def IsGeometricallyNormal
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    IsNormalRing (K ⊗[k] A)

/-- The four equivalent tests for geometric normality: arbitrary field base
changes, finitely generated field extensions, finite purely inseparable field
extensions, and the relative perfect closure. -/
theorem isGeometricallyNormal_iff_finiteType_iff_finitePurelyInseparable_iff_perfectClosure
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] :
    List.TFAE
      [ IsGeometricallyNormal k A,
        ∀ (k' : Type u) [Field k'] [Algebra k k']
          [Algebra.FiniteType k k'],
          IsNormalRing (k' ⊗[k] A),
        ∀ (k' : Type u) [Field k'] [Algebra k k']
          [FiniteDimensional k k'] [IsPurelyInseparable k k'],
          IsNormalRing (k' ⊗[k] A),
        IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A) ] := by
  sorry

/- The localization statement is written with an explicit submonoid, as in
   the canonical geometric-reducedness interface from Chapter 43. -/
/-- Localization preserves geometric normality. -/
theorem isGeometricallyNormal_localization
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    (hR : IsGeometricallyNormal k R) (M : Submonoid R) :
    IsGeometricallyNormal k (Localization M) := by
  sorry

/-- A separable field extension is geometrically normal over its base field. -/
theorem isSeparableExtension_isGeometricallyNormal
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hK : IsSeparableExtension k K) :
    IsGeometricallyNormal k K := by
  sorry

/-- Tensoring a geometrically normal algebra with a normal algebra gives a
normal ring. -/
theorem isGeometricallyNormal_tensorProduct_isNormalRing
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (hA : IsGeometricallyNormal k A) (hB : IsNormalRing B) :
    IsNormalRing (A ⊗[k] B) := by
  sorry

/-- Geometric normality is unchanged after replacing the base field by a
separable algebraic extension. -/
theorem isGeometricallyNormal_iff_of_separable_algebraic
    {k : Type u} {k' : Type v} {A : Type w} [Field k] [Field k'] [CommRing A]
    [Algebra k k'] [Algebra k' A] [Algebra k A]
    [IsScalarTower k k' A]
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k'] :
    IsGeometricallyNormal k A ↔ IsGeometricallyNormal k' A := by
  sorry

/- The displayed tensor identity in the proof of the preceding source lemma
   is provided by Mathlib's `Algebra.TensorProduct.cancelBaseChange`; it does
   not require a parallel chapter-local bridge declaration. -/

end

end Formalization.Books.Algebra.Unit165
