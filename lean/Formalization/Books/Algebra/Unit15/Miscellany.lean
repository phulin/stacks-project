import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Commutative Algebra, Chapter 15: Miscellany

The source section consists of elementary consequences of the basic theory of
commutative rings.  The finite lists in the source are represented by finite
types, and finite free modules are represented by functions on `Fin`.
-/

namespace Formalization.Books.Algebra.Unit15

open Set
open scoped BigOperators

universe u

/-! ## Ideals -/

/- The earlier chapter's equivalence is stronger than the one-sided source
   assertion, so this source-facing form is a direct specialization. -/
theorem product_ideals_in_prime
    {R : Type u} [CommRing R] {I J p : Ideal R} (hp : p.IsPrime)
    (hIJ : I * J ≤ p) : I ≤ p ∨ J ≤ p := by
  exact (Unit03.prime_mul_le_iff hp).mp hIJ

/- The source says that all but two of a finite list of ideals are prime.  A
   finite set of at most two exceptional indices is the uniform encoding,
   including the cases of lists of length zero or one. -/
theorem prime_avoidance
    {R : Type u} [CommRing R] {r : ℕ} (I : Fin r → Ideal R) (J : Ideal R)
    (hJ : ∀ i, ¬ J ≤ I i)
    (hprime : ∃ s : Finset (Fin r), s.card ≤ 2 ∧
      ∀ i, i ∉ s → (I i).IsPrime) :
    ∃ x : R, x ∈ J ∧ ∀ i, x ∉ I i := by
  sorry

theorem prime_coset_avoidance
    {R : Type u} [CommRing R] {r : ℕ} (x : R) (I : Ideal R)
    (p : Fin r → Ideal R)
    (hp : ∀ i, (p i).IsPrime)
    (h : ∀ i, ¬ (Set.image (fun y : R => x + y) (I : Set R) ⊆ (p i : Set R))) :
    ∃ y : R, y ∈ I ∧ ∀ i, x + y ∉ p i := by
  sorry

/-! ## Chinese remainder -/

theorem chinese_remainder
    {R ι : Type*} [CommRing R] [Fintype ι] (I : ι → Ideal R)
    (hI : Pairwise (fun i j => I i + I j = ⊤)) :
    (⨅ i, I i = ∏ i, I i) ∧
      Nonempty ((R ⧸ ∏ i, I i) ≃+* (∀ i, R ⧸ I i)) := by
  sorry

theorem chinese_remainder_of_pairwise_distinct_maximal
    {R ι : Type*} [CommRing R] [Fintype ι] (I : ι → Ideal R)
    (hmax : ∀ i, (I i).IsMaximal)
    (hdistinct : Pairwise (fun i j => I i ≠ I j)) :
    (⨅ i, I i = ∏ i, I i) ∧
      Nonempty ((R ⧸ ∏ i, I i) ≃+* (∀ i, R ⧸ I i)) := by
  sorry

/-! ## Determinantal ideals and matrix inverses -/

/- The `rowMinor` construction from the earlier basic-notions chapter is the
   determinant of every square row minor of a rectangular matrix. -/
noncomputable def maximalMinorIdeal
    {R : Type u} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) R) : Ideal R :=
  Ideal.span (Set.range (fun S : {s : Finset (Fin n) // s.card = m} =>
    Unit03.rowMinor A S))

theorem matrix_left_inverse_of_mem_maximalMinorIdeal
    {R : Type u} [CommRing R] {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    (hf : f ∈ maximalMinorIdeal A) :
    ∃ B : Matrix (Fin m) (Fin n) R,
      B * A = f • (1 : Matrix (Fin m) (Fin m) R) := by
  sorry

theorem matrix_left_inverse_power_mem_maximalMinorIdeal
    {R : Type u} [CommRing R] {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    {B : Matrix (Fin m) (Fin n) R}
    (hBA : B * A = f • (1 : Matrix (Fin m) (Fin m) R)) :
    f ^ m ∈ maximalMinorIdeal A := by
  sorry

/- The first conjunct records the upper block of the displayed product.  The
   second records that every lower entry is, up to sign, the determinant of
   the minor obtained by deleting the corresponding upper row and adjoining
   the corresponding lower row. -/
theorem matrix_right_inverse_block_form
    {R : Type u} [CommRing R] {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin n) (Fin m) R) :
    let A₁ : Matrix (Fin m) (Fin m) R :=
      A.submatrix (fun i : Fin m => i.castLE hmn) id
    let B : Matrix (Fin m) (Fin m) R := A₁.adjugate
    (∀ i j : Fin m,
        (A * B) (i.castLE hmn) j =
          (A₁.det • (1 : Matrix (Fin m) (Fin m) R)) i j) ∧
      (∀ i : Fin (n - m), ∀ j : Fin m,
        ∃ S : {s : Finset (Fin n) // s.card = m},
        S.1 =
            insert
              (Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i))
              (Finset.univ.erase (j.castLE hmn)) ∧
          ∃ ε : R, (ε = 1 ∨ ε = -1) ∧
            (A * B)
                (Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i)) j =
              ε * Unit03.rowMinor A S) := by
  sorry

/-! ## Finite free rank -/

theorem module_map_from_fin_generators_not_injective
    {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {n : ℕ} (hn : 1 ≤ n)
    (hM : ∃ k : ℕ, k < n ∧
      ∃ g : (Fin k → R) →ₗ[R] M, Function.Surjective g)
    (f : (Fin n → R) →ₗ[R] M) :
    LinearMap.ker f ≠ ⊥ := by
  sorry

theorem fin_free_module_rank_unique
    {R : Type*} [CommRing R] [Nontrivial R] {n m : ℕ}
    (e : (Fin n → R) ≃ₗ[R] (Fin m → R)) : n = m := by
  sorry

end Formalization.Books.Algebra.Unit15
