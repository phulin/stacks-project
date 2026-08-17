import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Nullstellensatz

/-!
# Exercises, Chapter 31: Regular functions

This file fixes the affine-space and locally closed-set interfaces used by the
chapter.  Affine points are functions on `Fin n`, and polynomial evaluation is
Mathlib's canonical `MvPolynomial.aeval`.
-/

namespace Formalization.Books.Exercises.Unit31

open Set

universe u

noncomputable section

/-! ## Locally closed affine sets and regular functions -/

/- A relative Zariski-open subset is written as the complement of a zero locus
   inside the ambient subset.  This is the source's usual `D(J)` notation. -/
 /-- `U` is Zariski open in the subset `Z` of affine `n`-space. -/
def IsZariskiOpenIn (k : Type u) [Field k] (n : ℕ)
    (Z U : Set (Fin n → k)) : Prop :=
  ∃ J : Ideal (MvPolynomial (Fin n) k),
    U = Z \ MvPolynomial.zeroLocus k J

 /-- A subset of affine space is Zariski locally closed. -/
def IsZariskiLocallyClosed (k : Type u) [Field k] (n : ℕ)
    (Z : Set (Fin n → k)) : Prop :=
  ∃ I J : Ideal (MvPolynomial (Fin n) k), I ≤ J ∧
    Z = MvPolynomial.zeroLocus k I \ MvPolynomial.zeroLocus k J

 /-- An affine variety is the zero locus of a prime ideal. -/
def IsAffineVariety (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (X : Set (Fin n → k)) : Prop :=
  ∃ p : Ideal (MvPolynomial (Fin n) k), p.IsPrime ∧
    X = MvPolynomial.zeroLocus k p

 /-- The source's notion of a regular function on a locally closed affine set.

 The function is defined on the subtype `Z`; at every point, a relative
 Zariski-open neighbourhood is described by a denominator zero locus and the
 function agrees there with a polynomial quotient whose denominator is
 everywhere nonzero on that neighbourhood.
 -/
def IsRegularFunction {k : Type u} [Field k] {n : ℕ}
    (Z : Set (Fin n → k)) (φ : Z → k) : Prop :=
  ∀ z : Z, ∃ U : Set (Fin n → k), z.1 ∈ U ∧
    ∃ hU : U ⊆ Z,
      IsZariskiOpenIn k n Z U ∧
        ∃ f g : MvPolynomial (Fin n) k,
          (∀ u : Fin n → k, u ∈ U → MvPolynomial.aeval u g ≠ 0) ∧
            ∀ (u : Fin n → k) (hu : u ∈ U),
              φ ⟨u, hU hu⟩ = MvPolynomial.aeval u f / MvPolynomial.aeval u g

 /-- A function on `Z` is induced by one polynomial on the ambient affine
 space. -/
def IsPolynomialRestriction {k : Type u} [Field k] {n : ℕ}
    (Z : Set (Fin n → k)) (φ : Z → k) : Prop :=
  ∃ f : MvPolynomial (Fin n) k,
    ∀ z : Z, φ z = MvPolynomial.aeval z.1 f

/-! ## Cones and homogeneous generators -/

 /-- A subset of affine space is stable under scalar multiplication. -/
def IsCone {k : Type u} [Semiring k] {n : ℕ}
    (X : Set (Fin n → k)) : Prop :=
  ∀ x : Fin n → k, x ∈ X → ∀ c : k,
    (fun i => c * x i) ∈ X

end

end Formalization.Books.Exercises.Unit31
