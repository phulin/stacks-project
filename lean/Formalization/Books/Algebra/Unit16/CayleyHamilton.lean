import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.FiniteType

/-!
# Commutative Algebra, Chapter 16: Cayley–Hamilton

The source uses the characteristic polynomial of a square matrix and the
finite-module form of the Cayley–Hamilton theorem.  These are already
available in Mathlib as `Matrix.charpoly` and the theorems in
`Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap`, so the declarations below
keep the book-facing statements while reusing those canonical interfaces.
-/

namespace Formalization.Books.Algebra.Unit16

universe u v

/-! ## Characteristic polynomials -/

/-
The source defines the characteristic polynomial as `det (t • 1 - A)`.
This is Mathlib's `Matrix.charpoly`; the source's base-change reductions are
proof narration and need no separate declarations.
-/

/-- The characteristic polynomial of a square matrix annihilates the matrix. -/
theorem cayley_hamilton {R : Type u} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    Polynomial.aeval A A.charpoly = 0 := by
  exact Matrix.aeval_self_charpoly A

/-! ## Finite modules -/

/-- A finite module endomorphism has a monic polynomial annihilator. -/
theorem exists_monic_annihilating_polynomial
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (φ : Module.End R M) :
    ∃ p : Polynomial R, p.Monic ∧ Polynomial.aeval φ p = 0 := by
  exact LinearMap.exists_monic_and_aeval_eq_zero R φ

/--
The ideal-refined finite-module Cayley–Hamilton theorem.

The coefficient condition is the canonical formulation of the source's
displayed shape `t^n + a₁ t^(n-1) + ⋯ + aₙ`, with the coefficient of degree
`k` lying in `I ^ (n - k)`.
-/
theorem exists_monic_annihilating_polynomial_with_ideal_coefficients
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (φ : Module.End R M)
    (hφ : LinearMap.range φ ≤ I • (⊤ : Submodule R M)) :
    ∃ p : Polynomial R,
      p.Monic ∧
        (∀ k : ℕ, p.coeff k ∈ I ^ (p.natDegree - k)) ∧
          Polynomial.aeval φ p = 0 := by
  obtain ⟨p, hp, _, hcoeff, hzero⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      R φ I hφ
  exact ⟨p, hp, hcoeff, hzero⟩

/-! ## Surjective endomorphisms -/

/-- A surjective endomorphism of a finite module is a module isomorphism. -/
theorem surjective_endomorphism_isomorphism
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (φ : Module.End R M) (hφ : Function.Surjective φ) :
    ∃ e : M ≃ₗ[R] M, e.toLinearMap = φ := by
  exact ⟨LinearEquiv.ofBijective φ
    (OrzechProperty.bijective_of_surjective_endomorphism φ hφ), rfl⟩

end Formalization.Books.Algebra.Unit16
