import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Exercises, Chapter 16: Core objects

This file records the polynomial rings used by the statements in the Hilbert
Nullstellensatz exercise.  The spectrum of a linear operator is Mathlib's canonical
`spectrum`, so no parallel spectrum predicate is introduced here.
-/

noncomputable section

universe u

open Set

namespace Formalization.Books.Exercises.Unit16

/-- The ring denoted by `k[x₁, ..., xₙ]` in this chapter. -/
abbrev polynomialRing (k : Type u) [CommSemiring k] (n : ℕ) :=
  MvPolynomial (Fin n) k

/-- The ideal `(xᵢ - αᵢ | i < n)` in `k[x₁, ..., xₙ]`. -/
def polynomialCoordinateIdeal (k : Type u) [CommRing k] (n : ℕ)
    (α : Fin n → k) : Ideal (polynomialRing k n) :=
  Ideal.span
    (Set.range (fun i : Fin n =>
      MvPolynomial.X (R := k) (σ := Fin n) i -
        MvPolynomial.C (R := k) (σ := Fin n) (α i)) :
      Set (polynomialRing k n))

end Formalization.Books.Exercises.Unit16
