import Formalization.Books.StacksProperties.Unit13.LocalIrreducibility

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 14

Quasi-compactness of a field-valued representative is expressed through the
point it represents.  The two predicates below make the source's
“some/any representative” equivalence explicit.
-/

noncomputable section

universe u

open AlgebraicGeometry

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
      stackPointOfFieldValuedMorphism q)
    (hinvariant : ∀ (p q : FieldValuedMorphism X),
      stackPointOfFieldValuedMorphism p =
        stackPointOfFieldValuedMorphism q →
      p.quasiCompact ↔ q.quasiCompact) :
    IsQuasiCompactFieldValuedMorphism p ↔
      IsQuasiCompactFieldValuedMorphism q := by
  unfold IsQuasiCompactFieldValuedMorphism
  have hi := hinvariant p q
  constructor
  · intro hp
    exact hi.mp (fun _ => hp)
  · intro hq
    exact (hi.mpr hq) heq

theorem quasi_compact_point_iff {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X)
    (hrepr : ∃ p : FieldValuedMorphism X,
      stackPointOfFieldValuedMorphism p = x)
    (hinvariant : ∀ (p q : FieldValuedMorphism X),
      stackPointOfFieldValuedMorphism p =
        stackPointOfFieldValuedMorphism q →
      p.quasiCompact ↔ q.quasiCompact) :
    SomeQuasiCompactRepresentative x ↔
      EveryQuasiCompactRepresentative x := by
  unfold SomeQuasiCompactRepresentative EveryQuasiCompactRepresentative
    IsQuasiCompactFieldValuedMorphism
  constructor
  · rintro ⟨p, hp, hcompact⟩ q hq
    have hi := hinvariant p q
    exact hi.mp (fun _ => hcompact)
  · intro hevery
    rcases hrepr with ⟨p, hp⟩
    exact ⟨p, hp, hevery p hp⟩

def IsQuasiCompactPoint {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) : Prop :=
  SomeQuasiCompactRepresentative x

end Formalization.Books.StacksProperties.Unit01
