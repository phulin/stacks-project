import Formalization.Books.StacksProperties.Unit01.LocalIrreducibility

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 14

Quasi-compactness of a field-valued representative is expressed through the
point it represents.  The two predicates below make the source's
“some/any representative” equivalence explicit.
-/

noncomputable section

universe u

namespace Formalization.Books.StacksProperties.Unit01

def IsQuasiCompactFieldValuedMorphism {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : FieldValuedMorphism X) : Prop :=
  p.quasiCompact

def SomeQuasiCompactRepresentative {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) : Prop :=
  ∃ p : FieldValuedMorphism X,
    stackPointOfFieldValuedMorphism p = x ∧
      IsQuasiCompactFieldValuedMorphism p

def EveryQuasiCompactRepresentative {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) : Prop :=
  ∀ p : FieldValuedMorphism X,
    stackPointOfFieldValuedMorphism p = x →
      IsQuasiCompactFieldValuedMorphism p

theorem quasi_compact_representative_invariant {S : Scheme.{u}}
    {X : AlgebraicStack S} (p q : FieldValuedMorphism X)
    (heq : stackPointOfFieldValuedMorphism p =
      stackPointOfFieldValuedMorphism q) :
    IsQuasiCompactFieldValuedMorphism p ↔
      IsQuasiCompactFieldValuedMorphism q := by
  sorry

theorem quasi_compact_point_iff {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) :
    SomeQuasiCompactRepresentative x ↔
      EveryQuasiCompactRepresentative x := by
  sorry

def IsQuasiCompactPoint {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) : Prop :=
  SomeQuasiCompactRepresentative x

end Formalization.Books.StacksProperties.Unit01
