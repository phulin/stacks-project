import Formalization.Books.StacksProperties.Unit01.Surjective

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 6

The chapter's five presentations of quasi-compactness are exposed as named
criteria.  The local stack model records the source-side scheme and
algebraic-space conditions needed by those criteria.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

def IsQuasiCompactStack {S : Scheme.{u}} (X : AlgebraicStack S) : Prop :=
  X.quasiCompact

structure QuasiCompactStackChart {S : Scheme.{u}}
    {X : AlgebraicStack S} extends StackChart X where
  affineSource : Prop
  quasiCompactSchemeSource : Prop
  quasiCompactAlgebraicSpaceSource : Prop

def HasChartSourceProperty {S : Scheme.{u}} {X : AlgebraicStack S}
    (P : Scheme.{u} → Prop) (c : StackChart X) : Prop :=
  P c.source

def HasAffineSmoothCover {S : Scheme.{u}} (X : AlgebraicStack S) : Prop :=
  ∃ c : QuasiCompactStackChart (X := X),
    c.surjective ∧ c.smooth ∧ c.affineSource

def HasQuasiCompactSchemeSmoothCover {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  ∃ c : QuasiCompactStackChart (X := X),
    c.surjective ∧ c.smooth ∧ c.quasiCompactSchemeSource

def HasQuasiCompactSpaceSmoothCover {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  ∃ c : QuasiCompactStackChart (X := X),
    c.surjective ∧ c.smooth ∧ c.quasiCompactAlgebraicSpaceSource

def HasQuasiCompactStackCover {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  ∃ (U : AlgebraicStack S) (f : StackMorphism U X),
    IsSurjective f ∧ IsQuasiCompactStack U

theorem quasiCompact_stack_iff {S : Scheme.{u}} (X : AlgebraicStack S) :
    IsQuasiCompactStack X ↔
      HasAffineSmoothCover X ∧
        HasQuasiCompactSchemeSmoothCover X ∧
          HasQuasiCompactSpaceSmoothCover X ∧ HasQuasiCompactStackCover X := by
  sorry

structure FiniteDisjointUnionData {S : Scheme.{u}} {n : ℕ}
    (X : Fin n → AlgebraicStack S) where
  carrier : AlgebraicStack S
  inclusion : ∀ i, StackMorphism (X i) carrier
  isDisjointUnion : Prop

theorem finite_disjoint_union_quasi_compact {S : Scheme.{u}} {n : ℕ}
    (X : Fin n → AlgebraicStack S) (D : FiniteDisjointUnionData X)
    (hX : ∀ i, IsQuasiCompactStack (X i)) :
    IsQuasiCompactStack D.carrier := by
  sorry

end Formalization.Books.StacksProperties.Unit01
