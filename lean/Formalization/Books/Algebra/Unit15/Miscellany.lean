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
  have hcop : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
    intro i j hij
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact hI hij
  have hprod : (∏ i, I i) = ⨅ i, I i := by
    simpa using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := (Finset.univ : Finset ι)) (J := I) (by
          intro i hi j hj hij
          exact hcop hij))
  refine ⟨hprod.symm, ⟨(Ideal.quotEquivOfEq hprod).trans
    (Ideal.quotientInfRingEquivPiQuotient I hcop)⟩⟩

theorem chinese_remainder_of_pairwise_distinct_maximal
    {R ι : Type*} [CommRing R] [Fintype ι] (I : ι → Ideal R)
    (hmax : ∀ i, (I i).IsMaximal)
    (hdistinct : Pairwise (fun i j => I i ≠ I j)) :
    (⨅ i, I i = ∏ i, I i) ∧
      Nonempty ((R ⧸ ∏ i, I i) ≃+* (∀ i, R ⧸ I i)) := by
  apply chinese_remainder I
  intro i j hij
  letI : (I i).IsMaximal := hmax i
  letI : (I j).IsMaximal := hmax j
  exact (Ideal.isCoprime_of_isMaximal (hdistinct hij)).sup_eq

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
  classical
  unfold maximalMinorIdeal at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, rfl⟩ := hf
      let e : Fin m ↪ Fin n := (S.1.orderEmbOfFin S.2).toEmbedding
      let A_S : Matrix (Fin m) (Fin m) R := A.submatrix e id
      refine ⟨A_S.adjugate *
          (1 : Matrix (Fin n) (Fin n) R).submatrix e (Equiv.refl (Fin n)), ?_⟩
      rw [Matrix.mul_assoc, Matrix.one_submatrix_mul e (Equiv.refl (Fin n)) A]
      simpa [A_S, e, Unit03.rowMinor, Function.comp_def] using
        (Matrix.adjugate_mul A_S)
  | zero =>
      exact ⟨0, by simp⟩
  | add f g hf hg hf' hg' =>
      obtain ⟨Bf, hBf⟩ := hf'
      obtain ⟨Bg, hBg⟩ := hg'
      refine ⟨Bf + Bg, ?_⟩
      rw [Matrix.add_mul, hBf, hBg, add_smul]
  | smul c f hf hf' =>
      obtain ⟨Bf, hBf⟩ := hf'
      refine ⟨c • Bf, ?_⟩
      rw [Matrix.smul_mul, hBf, smul_smul]
      simp [smul_eq_mul]

theorem matrix_left_inverse_power_mem_maximalMinorIdeal
    {R : Type u} [CommRing R] {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    {B : Matrix (Fin m) (Fin n) R}
    (hBA : B * A = f • (1 : Matrix (Fin m) (Fin m) R)) :
    f ^ m ∈ maximalMinorIdeal A := by
  have hdet : f ^ m =
      ∑ S : {s : Finset (Fin n) // s.card = m},
        Unit03.columnMinor B S * Unit03.rowMinor A S := by
    calc
      f ^ m = (f • (1 : Matrix (Fin m) (Fin m) R)).det := by
        simp [Matrix.det_smul]
      _ = (B * A).det := by rw [hBA]
      _ = _ := Unit03.cauchyBinet B A
  rw [maximalMinorIdeal, hdet]
  apply Ideal.sum_mem
  intro S hS
  exact Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨S, rfl⟩)

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
              ((Finset.univ.image (fun k : Fin m => k.castLE hmn)).erase
                (j.castLE hmn)) ∧
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
  rcases hM with ⟨k, hk, g, hg⟩
  intro hker
  have hf_inj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g f hg
  have hl_inj : Function.Injective l := by
    intro x y hxy
    apply hf_inj
    calc
      f x = (g.comp l) x := by rw [hl]
      _ = g (l x) := rfl
      _ = g (l y) := congrArg g hxy
      _ = (g.comp l) y := rfl
      _ = f y := by rw [hl]
  exact (Nat.not_lt_of_ge (le_of_fin_injective R l hl_inj)) hk

theorem fin_free_module_rank_unique
    {R : Type*} [CommRing R] [Nontrivial R] {n m : ℕ}
    (e : (Fin n → R) ≃ₗ[R] (Fin m → R)) : n = m := by
  exact eq_of_fin_equiv R e

end Formalization.Books.Algebra.Unit15
