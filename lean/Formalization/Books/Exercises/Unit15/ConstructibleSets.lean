import Mathlib.RingTheory.Nullstellensatz

/-!
# Exercises, Chapter 15: Constructible sets

This file records the definitions and theorem interfaces for the first two
exercises.  Affine algebraic sets use Mathlib's multivariate-polynomial
zero-locus API, while the finite-union and disjoint-union statements retain
the source's description by basic pieces.
-/

namespace Formalization.Books.Exercises.Unit15

open Set

universe u v

noncomputable section

/-! ## Algebraic sets -/

/- The source writes `k[x₁, ..., xₙ]`; the canonical Lean presentation is
   `MvPolynomial (Fin n) k`. -/

/-- Evaluation of a polynomial at a point of affine `n`-space. -/
def polynomialEvaluation {k : Type u} [CommSemiring k] {n : ℕ}
    (f : MvPolynomial (Fin n) k) (x : Fin n → k) : k :=
  MvPolynomial.eval x f

/-- The common zero locus of a collection of polynomials in affine space. -/
def polynomialZeroSet (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (S : Set (MvPolynomial (Fin n) k)) : Set (Fin n → k) :=
  MvPolynomial.zeroLocus k (Ideal.span S)

/-- An algebraic set is the common zero locus of a collection of polynomials. -/
def IsAlgebraicSet (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (Z : Set (Fin n → k)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) k), Z = polynomialZeroSet k n S

/-! ### Exercise `finite-nr-equations` -/

/-- Every algebraic set is the zero locus of finitely many polynomials. -/
theorem exists_finite_polynomials_eq_polynomialZeroSet
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {Z : Set (Fin n → k)} (hZ : IsAlgebraicSet k n Z) :
    ∃ S : Set (MvPolynomial (Fin n) k), S.Finite ∧
      Z = polynomialZeroSet k n S := by
  sorry

/-! ## Constructible sets -/

/-- Data for one basic constructible piece `Z ∩ {f ≠ 0}`. -/
structure ConstructiblePiece (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) where
  zeroSet : Set (Fin n → k)
  polynomial : MvPolynomial (Fin n) k
  zeroSet_isAlgebraic : IsAlgebraicSet k n zeroSet

/-- The subset represented by a basic constructible piece. -/
def ConstructiblePiece.toSet {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (P : ConstructiblePiece k n) : Set (Fin n → k) :=
  P.zeroSet ∩ {x | polynomialEvaluation P.polynomial x ≠ 0}

/- A finite set of `ConstructiblePiece`s gives the source's finite union of
   sets `Z ∩ {f ≠ 0}`. -/
/-- A subset of affine space is constructible when it is a finite union of
basic constructible pieces. -/
def IsConstructible (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (E : Set (Fin n → k)) : Prop :=
  ∃ T : Set (ConstructiblePiece k n), T.Finite ∧
    E = ⋃ P ∈ T, P.toSet

/-! ### Exercise `constructible-classical` -/

/-- The complement of a constructible set is constructible. -/
theorem isConstructible_compl
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {E : Set (Fin n → k)} (hE : IsConstructible k n E) :
    IsConstructible k n Eᶜ := by
  sorry

/-- A finite union of constructible sets is constructible. -/
theorem isConstructible_finite_iUnion
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {ι : Type v} (T : Set ι) (hT : T.Finite)
    (E : ι → Set (Fin n → k))
    (hE : ∀ i ∈ T, IsConstructible k n (E i)) :
    IsConstructible k n (⋃ i ∈ T, E i) := by
  sorry

/-- A finite intersection of constructible sets is constructible. -/
theorem isConstructible_finite_iInter
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {ι : Type v} (T : Set ι) (hT : T.Finite)
    (E : ι → Set (Fin n → k))
    (hE : ∀ i ∈ T, IsConstructible k n (E i)) :
    IsConstructible k n (⋂ i ∈ T, E i) := by
  sorry

/-- Every constructible set is a finite disjoint union of basic pieces. -/
theorem exists_finite_pairwiseDisjoint_constructiblePieces
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
    {E : Set (Fin n → k)} (hE : IsConstructible k n E) :
    ∃ T : Set (ConstructiblePiece k n), T.Finite ∧
      (E = ⋃ P ∈ T, P.toSet) ∧
        T.PairwiseDisjoint (fun P : ConstructiblePiece k n => P.toSet) := by
  sorry

end

end Formalization.Books.Exercises.Unit15
