import Formalization.Books.Fields.Unit11.RelativelyPrimePolynomials
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Fields, Chapter 12: Separable algebraic extensions

The source's three notions of separability are already Mathlib's canonical
`Polynomial.Separable`, `IsSeparable`, and `Algebra.IsSeparable`.  The source's
separable degree is `Polynomial.natSepDegree`; its finite-extension embedding
count is expressed using `Nat.card` of `AlgHom`s into a chosen algebraic
closure.  The finite-generator situation is packaged below with
`IntermediateField.adjoin`, and its successive root tuples are made explicit
so that the chapter's embedding-count correspondence has a usable interface.
-/

namespace Formalization.Books.Fields.Unit12

noncomputable section

open Polynomial
open scoped BigOperators

universe u v

/-! ## Irreducible polynomials and separability -/

/- `Polynomial.Separable` is exactly the source's definition of a separable
   polynomial, so no parallel predicate is introduced. -/
/-- A polynomial is separable exactly when it is coprime to its derivative. -/
theorem separable_polynomial_iff_coprime_derivative
    {F : Type u} [CommSemiring F] (P : F[X]) :
    P.Separable ↔ IsCoprime P P.derivative :=
  Polynomial.separable_def P

/- The field version gives the source's dichotomy for an irreducible
   polynomial. -/
/-- An irreducible polynomial is separable or has zero derivative. -/
theorem irreducible_polynomial_separable_or_derivative_zero
    {F : Type u} [Field F] {P : F[X]} (hP : Irreducible P) :
    P.Separable ∨ P.derivative = 0 := by
  by_cases h : P.derivative = 0
  · exact Or.inr h
  · exact Or.inl ((Polynomial.separable_iff_derivative_ne_zero hP).2 h)

/-- If an irreducible polynomial has zero derivative, it is a Frobenius power
    of a separable irreducible polynomial in positive characteristic. -/
theorem irreducible_polynomial_derivative_zero_factorization
    {F : Type u} [Field F] {P : F[X]} (hP : Irreducible P)
    (hderiv : P.derivative = 0) :
    ∃ (p n : ℕ) (Q : F[X]),
      0 < p ∧ CharP F p ∧ Q.Separable ∧ Irreducible Q ∧
        Polynomial.expand F (p ^ n) Q = P := by
  sorry

/-- Every irreducible polynomial has a separable Frobenius contraction; in
    characteristic zero this contraction can be chosen to be the polynomial
    itself. -/
theorem irreducible_polynomial_separable_contraction
    {F : Type u} [Field F] {P : F[X]} (hP : Irreducible P) :
    ∃ (q n : ℕ) (Q : F[X]),
      ExpChar F q ∧ Q.Separable ∧ Irreducible Q ∧
        Polynomial.expand F (q ^ n) Q = P := by
  sorry

/- `IsSeparable` and `Algebra.IsSeparable` are Mathlib's definitions of the
   source's separable element and separable algebraic extension. -/
/-- An element is separable exactly when its minimal polynomial is separable. -/
theorem separable_element_iff_minpoly_separable
    {F K : Type*} [CommRing F] [Ring K] [Algebra F K] (α : K) :
    IsSeparable F α ↔ (minpoly F α).Separable :=
  Iff.rfl

/-- An extension is separable exactly when all of its elements are separable. -/
theorem separable_extension_iff_all_elements_separable
    {F K : Type*} [CommRing F] [Ring K] [Algebra F K] :
    Algebra.IsSeparable F K ↔ ∀ α : K, IsSeparable F α :=
  Algebra.isSeparable_def F K

/- The characteristic-zero consequences in the source are instances and
   theorems already supplied by the separability API. -/
/-- Every irreducible polynomial over a characteristic-zero field is separable. -/
theorem irreducible_polynomial_separable_of_char_zero
    {F : Type u} [Field F] [CharZero F] {P : F[X]}
    (hP : Irreducible P) : P.Separable :=
  hP.separable

/-- Every algebraic element over a characteristic-zero field is separable. -/
theorem algebraic_element_separable_of_char_zero
    {F K : Type*} [Field F] [Field K] [Algebra F K] [CharZero F]
    {α : K} (hα : IsAlgebraic F α) : IsSeparable F α := by
  exact (minpoly.irreducible hα.isIntegral).separable

/-- Every algebraic extension in characteristic zero is separable. -/
theorem algebraic_extension_separable_of_char_zero
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] [CharZero F] :
    Algebra.IsSeparable F K := by
  infer_instance

/- The two upward statements are the canonical tower lemmas. -/
/-- Separability of an element persists after enlarging the coefficient field. -/
theorem separable_element_goes_up
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    {α : K} (hα : IsSeparable F α) : IsSeparable E α :=
  IsSeparable.tower_top E hα

/-- A separable extension remains separable over every intermediate field. -/
theorem separable_extension_goes_up
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [Algebra.IsSeparable F K] :
    Algebra.IsSeparable E K := by
  exact ⟨fun α => IsSeparable.tower_top E (Algebra.IsSeparable.isSeparable F α)⟩

/-- For an irreducible polynomial, separability is equivalent to having no
    repeated roots in an algebraic closure. -/
theorem irreducible_polynomial_separable_iff_distinct_algebraic_closure_roots
    {F : Type u} [Field F] {P : F[X]} (hP : Irreducible P) :
    P.Separable ↔
      (P.aroots (AlgebraicClosure F)).Nodup := by
  classical
  exact (Polynomial.nodup_aroots_iff_of_splits hP.ne_zero
    (IsAlgClosed.splits (P.map (algebraMap F (AlgebraicClosure F))))).symm

/- The source's Frobenius-root-count assertion is recorded with the canonical
   separable-degree invariant, which is independent of the chosen closure. -/
/-- In positive characteristic, substituting the Frobenius power preserves the
    number of distinct roots in an algebraic closure. -/
theorem separable_degree_unchanged_under_frobenius_substitution
    {F : Type u} [Field F] (p : ℕ) [CharP F p] (hp : 0 < p) (P : F[X]) :
    P.natSepDegree = (P.comp (X ^ p)).natSepDegree := by
  sorry

/-! ## Separable degree -/

/- `Polynomial.natSepDegree` is Mathlib's definition of the source's
   `deg_s(P)`. -/
/-- The separable degree is the number of distinct roots in an algebraic
    closure. -/
theorem separable_degree_eq_card_distinct_roots
    {F : Type u} [Field F] (P : F[X]) :
    P.natSepDegree = Nat.card (P.rootSet (AlgebraicClosure F)) := by
  sorry

/-- The separable degree of an irreducible polynomial divides its degree. -/
theorem irreducible_separable_degree_dvd_degree
    {F : Type u} [Field F] {P : F[X]} (hP : Irreducible P) :
    P.natSepDegree ∣ P.natDegree :=
  hP.natSepDegree_dvd_natDegree

/-- For an irreducible polynomial, the quotient of the degree by the
    separable degree is a power of the exponential characteristic. -/
theorem irreducible_degree_eq_separable_degree_mul_expChar_power
    {F : Type u} [Field F] {P : F[X]} (hP : Irreducible P) :
    ∃ (q m : ℕ), ExpChar F q ∧ P.natSepDegree * q ^ m = P.natDegree := by
  sorry

/-- In characteristic zero, the separable degree equals the polynomial degree. -/
theorem irreducible_separable_degree_eq_degree_of_char_zero
    {F : Type u} [Field F] [CharZero F] {P : F[X]}
    (hP : Irreducible P) :
    P.natSepDegree = P.natDegree :=
  hP.separable.natSepDegree_eq_natDegree

/-- A separable polynomial has separable degree equal to its degree. -/
theorem separable_polynomial_separable_degree_eq_degree
    {F : Type u} [Field F] {P : F[X]} (hP : P.Separable) :
    P.natSepDegree = P.natDegree :=
  hP.natSepDegree_eq_natDegree

/-! ## Finite-generation situation -/

/- The source's finite extension generated by a finite list is represented by
   a finite-dimensional extension together with a finite generator family. -/
/-- A finite field extension together with an ordered finite generating family. -/
structure FinitelyGeneratedFieldExtension
    (F K : Type*) [Field F] [Field K] [Algebra F K] where
  n : ℕ
  alpha : Fin n → K
  finite : FiniteDimensional F K
  generated : IntermediateField.adjoin F (Set.range alpha) = ⊤

/-- The index of a generator in the prefix ending at `i`. -/
def prefixGeneratorIndex {n : ℕ} (i : Fin (n + 1)) (j : Fin i) : Fin n :=
  ⟨j, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)⟩

/-- The intermediate field generated by the first `i` generators. -/
def generatedIntermediateField
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin (S.n + 1)) :
    IntermediateField F K :=
  IntermediateField.adjoin F
    (Set.range (fun j : Fin i => S.alpha (prefixGeneratorIndex i j)))

/-- The `i`-th generator viewed in the field generated by the first `i + 1`
    generators. -/
def generatorInNextField
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    generatedIntermediateField S i.succ :=
  ⟨S.alpha i, IntermediateField.subset_adjoin F _
    ⟨⟨i.1, Nat.lt_succ_self i.1⟩, rfl⟩⟩

/-- Prefix fields are nested. -/
theorem generatedIntermediateField_le
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K)
    {i j : Fin (S.n + 1)} (hij : i.1 ≤ j.1) :
    generatedIntermediateField S i ≤ generatedIntermediateField S j := by
  sorry

/-- The canonical inclusion from one prefix field to the next. -/
def generatedIntermediateFieldInclusion
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    generatedIntermediateField S i.castSucc →ₐ[F]
      generatedIntermediateField S i.succ :=
  IntermediateField.inclusion
    (generatedIntermediateField_le S (by simp))

/- The successive fields need the algebra structure induced by this inclusion;
   Mathlib does not infer an algebra between two intermediate fields with
   different base-field parameters automatically. -/
instance generatedIntermediateField_step_algebra
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    Algebra (generatedIntermediateField S i.castSucc)
      (generatedIntermediateField S i.succ) :=
  (generatedIntermediateFieldInclusion S i).toRingHom.toAlgebra

/-- The initial prefix field is the canonical copy of the base field. -/
theorem generatedIntermediateField_zero_eq_bot
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) :
    generatedIntermediateField S 0 = ⊥ := by
  sorry

/-- The final prefix field is the whole extension. -/
theorem generatedIntermediateField_last_eq_top
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) :
    generatedIntermediateField S (Fin.last S.n) = ⊤ := by
  sorry

/-- Every prefix field is finite over the base field. -/
theorem generatedIntermediateField_finite
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin (S.n + 1)) :
    FiniteDimensional F (generatedIntermediateField S i) := by
  sorry

/-- Each successive prefix field is finite over its predecessor. -/
theorem generatedIntermediateField_step_finite
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    FiniteDimensional (generatedIntermediateField S i.castSucc)
      (generatedIntermediateField S i.succ) := by
  sorry

/- The source's `P_i` is the canonical minimal polynomial over the preceding
   prefix field. -/
/-- The minimal polynomial of the `i`-th generator over the preceding prefix. -/
def generatedMinpoly
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    Polynomial (generatedIntermediateField S i.castSucc) :=
  minpoly (generatedIntermediateField S i.castSucc) (S.alpha i)

/-- Each successive minimal polynomial is irreducible. -/
theorem generatedMinpoly_irreducible
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    Irreducible (generatedMinpoly S i) := by
  sorry

/-- The degree of a successive minimal polynomial is the degree of the
    corresponding simple extension. -/
theorem generated_step_finrank_eq_minpoly_natDegree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    Module.finrank (generatedIntermediateField S i.castSucc)
        (generatedIntermediateField S i.succ) =
      (generatedMinpoly S i).natDegree := by
  sorry

/-- Each successive prefix field has the quotient presentation by the
    corresponding minimal polynomial. -/
theorem generatedIntermediateField_step_quotient
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    Nonempty
      (generatedIntermediateField S i.succ ≃ₐ[
        generatedIntermediateField S i.castSucc]
        AdjoinRoot (generatedMinpoly S i)) := by
  sorry

/-! ## Embeddings and successive root tuples -/

/-- The restriction of an extension embedding to a prefix field. -/
def generatedEmbedding
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (φ : K →ₐ[F] L)
    (i : Fin (S.n + 1)) :
    generatedIntermediateField S i →ₐ[F] L :=
  φ.comp (generatedIntermediateField S i).val

/-- The image of a successive minimal polynomial under a restricted
    embedding. -/
def generatedMappedPolynomial
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (φ : K →ₐ[F] L)
    (i : Fin S.n) : Polynomial L :=
  (generatedMinpoly S i).map (generatedEmbedding S φ i.castSucc).toRingHom

/-- The image of the `i`-th generator under an extension embedding. -/
def generatedEmbeddingGenerator
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (φ : K →ₐ[F] L)
    (i : Fin S.n) : L :=
  generatedEmbedding S φ i.succ (generatorInNextField S i)

/-- The image of a generator is a root of the corresponding mapped minimal
    polynomial. -/
theorem generated_embedding_generator_is_root
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (φ : K →ₐ[F] L)
    (i : Fin S.n) :
    Polynomial.aeval (generatedEmbeddingGenerator S φ i)
      (generatedMappedPolynomial S φ i) = 0 := by
  sorry

/-- A root of a mapped successive minimal polynomial extends a fixed embedding
    of the preceding prefix field. -/
theorem generated_step_extension_exists_of_root
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K)
    (i : Fin S.n)
    (φ : generatedIntermediateField S i.castSucc →ₐ[F] L) (β : L)
    (hβ : Polynomial.aeval β
      ((generatedMinpoly S i).map φ.toRingHom) = 0) :
    ∃ ψ : generatedIntermediateField S i.succ →ₐ[F] L,
      ψ.comp (generatedIntermediateFieldInclusion S i) = φ ∧
        ψ (generatorInNextField S i) = β := by
  sorry

/-- Such an extension is unique. -/
theorem generated_step_extension_unique
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K)
    (i : Fin S.n)
    (φ : generatedIntermediateField S i.castSucc →ₐ[F] L)
    (ψ₁ ψ₂ : generatedIntermediateField S i.succ →ₐ[F] L)
    (h₁ : ψ₁.comp (generatedIntermediateFieldInclusion S i) = φ)
    (h₂ : ψ₂.comp (generatedIntermediateFieldInclusion S i) = φ)
    (hβ : ψ₁ (generatorInNextField S i) = ψ₂ (generatorInNextField S i)) :
    ψ₁ = ψ₂ := by
  sorry

/- A tuple is source-faithful when it is realized by a compatible chain of
   prefix embeddings and satisfies the successive root conditions. -/
/-- The type of successive root tuples for a finite generator family. -/
def SuccessiveRootTuple
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (β : Fin S.n → L) : Prop :=
  ∃ φ : ∀ j : Fin (S.n + 1),
      generatedIntermediateField S j →ₐ[F] L,
    ∀ i : Fin S.n,
      (φ i.succ).comp (generatedIntermediateFieldInclusion S i) = φ i.castSucc ∧
        φ i.succ (generatorInNextField S i) = β i ∧
          Polynomial.aeval (β i)
            ((generatedMinpoly S i).map (φ i.castSucc).toRingHom) = 0

/-- The tuple attached to an embedding of the whole extension. -/
def generatedEmbeddingTuple
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (φ : K →ₐ[F] L) :
    Fin S.n → L :=
  fun i => generatedEmbeddingGenerator S φ i

/-- The tuple attached to a whole-extension embedding satisfies the successive
    root conditions. -/
theorem generated_embedding_tuple_is_successive_root_tuple
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (φ : K →ₐ[F] L) :
    SuccessiveRootTuple S (generatedEmbeddingTuple S φ) := by
  sorry

/-- The embedding-to-tuple map with its source-facing codomain. -/
def generatedEmbeddingTupleWithProperty
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) :
    (K →ₐ[F] L) → {β : Fin S.n → L // SuccessiveRootTuple S β} :=
  fun φ => ⟨generatedEmbeddingTuple S φ,
    generated_embedding_tuple_is_successive_root_tuple S φ⟩

/-- Embeddings of the whole extension correspond bijectively to successive
    root tuples. -/
theorem generated_embedding_tuple_bijective
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    (S : FinitelyGeneratedFieldExtension F K) :
    Function.Bijective (generatedEmbeddingTupleWithProperty (L := L) S) := by
  sorry

/-- The number of extension embeddings is the product of the successive
    separable degrees. -/
theorem count_embeddings_explicitly
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    (S : FinitelyGeneratedFieldExtension F K) :
    Nat.card (K →ₐ[F] L) =
      ∏ i : Fin S.n, (generatedMinpoly S i).natSepDegree := by
  sorry

/-! ## Finite separable extensions -/

/-- If every successive minimal polynomial is separable, the extension is
    separable and the embedding count equals its degree. -/
theorem finitely_generated_separable_of_step_separable
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    (S : FinitelyGeneratedFieldExtension F K)
    (hsep : ∀ i : Fin S.n, (generatedMinpoly S i).Separable) :
    Nat.card (K →ₐ[F] L) = Module.finrank F K ∧
      Algebra.IsSeparable F K := by
  sorry

/-- If one successive minimal polynomial is inseparable, the embedding count
    is strictly smaller than the degree. -/
theorem finitely_generated_embedding_count_lt_of_step_not_separable
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    (S : FinitelyGeneratedFieldExtension F K)
    (hnot : ∃ i : Fin S.n, ¬(generatedMinpoly S i).Separable) :
    Nat.card (K →ₐ[F] L) < Module.finrank F K := by
  sorry

/-- For a finite extension, the embedding count is bounded by the degree, with
    equality exactly in the separable case. -/
theorem finite_extension_embedding_count_le_and_eq_iff
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    [FiniteDimensional F K] :
    Nat.card (K →ₐ[F] L) ≤ Module.finrank F K ∧
      (Nat.card (K →ₐ[F] L) = Module.finrank F K ↔
        Algebra.IsSeparable F K) := by
  sorry

/-! ## Permanence and the separable-element subextension -/

/-- Separability is transitive in a tower of separable algebraic extensions. -/
theorem separable_extension_permanence
    {k E K : Type*} [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra E K] [Algebra k K] [IsScalarTower k E K]
    [Algebra.IsSeparable k E] [Algebra.IsSeparable E K] :
    Algebra.IsSeparable k K :=
  Algebra.IsSeparable.trans k E K

/- The canonical `separableClosure` is precisely the subextension formed by
   the elements separable over the base. -/
/-- The elements separable over the base field form an intermediate field. -/
theorem separable_elements_form_subextension
    {k E : Type*} [Field k] [Field E] [Algebra k E] :
    ∀ x : E, x ∈ separableClosure k E ↔ IsSeparable k x :=
  fun _ => mem_separableClosure_iff

end

end Formalization.Books.Fields.Unit12
