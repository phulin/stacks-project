import Formalization.Books.SpacesGroupoids.Unit29.Foundations

/-!
# Groupoids in Algebraic Spaces, Chapter 29: separation conditions

The source section contains the diagonal diagram and its three separation-property equivalences.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Formalization.Books.SpacesGroupoids.Unit29

variable {S B : AlgebraicSpace.{u}}

/-- The displayed diagonal diagram is commutative, its two left maps are
isomorphisms, and its right square is cartesian. -/
theorem diagram_diagonal (𝒢 : GroupoidInAlgebraicSpaces S B) :
    (𝒢.diagonalTopLeft ≫ 𝒢.diagonalMiddle =
        𝒢.diagonalLeft ≫ 𝒢.diagonalBottomLeft) ∧
      IsIso 𝒢.diagonalTopLeft ∧
      IsIso 𝒢.diagonalBottomLeft ∧
      IsPullback 𝒢.diagonalTopRight 𝒢.diagonalMiddle
        𝒢.stabilizerIdentity 𝒢.diagonalBottomRight := by
  sorry

/-- Three propositions are equivalent in their displayed order. -/
def PairwiseEquivalent (P Q R : Prop) : Prop := (P ↔ Q) ∧ (Q ↔ R)

/-!
The three clauses below are the three numbered equivalence assertions in the
source lemma.  The morphism-property classes are Mathlib's canonical
definitions for schemes, and the groupoid maps are the chapter-local maps
from `Foundations.lean`.
-/

theorem diagonal_separation_conditions (𝒢 : GroupoidInAlgebraicSpaces S B) :
    PairwiseEquivalent
      (IsSeparated 𝒢.relation)
      (IsSeparated 𝒢.stabilizerToObj)
      (IsClosedImmersion 𝒢.stabilizerIdentity) ∧
    PairwiseEquivalent
      (IsImmersion 𝒢.relation)
      (IsImmersion 𝒢.stabilizerToObj)
      (IsImmersion 𝒢.stabilizerIdentity) ∧
    PairwiseEquivalent
      (QuasiSeparated 𝒢.relation)
      (QuasiSeparated 𝒢.stabilizerToObj)
      (QuasiCompact 𝒢.stabilizerIdentity) := by
  sorry

end Formalization.Books.SpacesGroupoids.Unit29
