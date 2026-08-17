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
  rcases CharP.exists' F with hzero | ⟨p, hp, hchar⟩
  · let : CharZero F := hzero
    exact False.elim <| (separable_iff_derivative_ne_zero hP).1 hP.separable hderiv
  · let : Fact p.Prime := hp
    let : CharP F p := hchar
    rcases hP.hasSeparableContraction p with ⟨Q, hQ, n, hQP⟩
    refine ⟨p, n, Q, hp.out.pos, hchar, hQ, ?_, hQP⟩
    apply Polynomial.of_irreducible_expand_pow hp.out.ne_zero
    rwa [hQP]

/-- Every irreducible polynomial has a separable Frobenius contraction; in
    characteristic zero this contraction can be chosen to be the polynomial
    itself. -/
theorem irreducible_polynomial_separable_contraction
    {F : Type u} [Field F] {P : F[X]} (hP : Irreducible P) :
    ∃ (q n : ℕ) (Q : F[X]),
      ExpChar F q ∧ Q.Separable ∧ Irreducible Q ∧
        Polynomial.expand F (q ^ n) Q = P := by
  let q := ringExpChar F
  let : ExpChar F q := ringExpChar.expChar F
  rcases hP.hasSeparableContraction q with ⟨Q, hQ, n, hQP⟩
  refine ⟨q, n, Q, inferInstance, hQ, ?_, hQP⟩
  apply Polynomial.of_irreducible_expand_pow (expChar_ne_zero F q)
  rwa [hQP]

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
  let : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero F p).resolve_right hp.ne'⟩
  let : ExpChar F p := ExpChar.prime Fact.out
  rw [← expand_eq_comp_X_pow]
  simpa [pow_one] using (natSepDegree_expand P p (n := 1)).symm

/-! ## Separable degree -/

/- `Polynomial.natSepDegree` is Mathlib's definition of the source's
   `deg_s(P)`. -/
/-- The separable degree is the number of distinct roots in an algebraic
    closure. -/
theorem separable_degree_eq_card_distinct_roots
    {F : Type u} [Field F] (P : F[X]) :
    P.natSepDegree = Nat.card (P.rootSet (AlgebraicClosure F)) := by
  classical
  rw [rootSet_def, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F) P

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
  let q := ringExpChar F
  let : ExpChar F q := ringExpChar.expChar F
  let hcontraction := hP.hasSeparableContraction q
  obtain ⟨m, hm⟩ := hcontraction.dvd_degree'
  refine ⟨q, m, inferInstance, ?_⟩
  calc
    P.natSepDegree * q ^ m = hcontraction.degree * q ^ m := by
      rw [hcontraction.natSepDegree_eq]
    _ = P.natDegree := hm

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
  unfold generatedIntermediateField
  apply IntermediateField.adjoin.mono F
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨k.1, lt_of_lt_of_le k.2 hij⟩, ?_⟩
  rfl

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
  simp [generatedIntermediateField]

/-- The final prefix field is the whole extension. -/
theorem generatedIntermediateField_last_eq_top
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) :
    generatedIntermediateField S (Fin.last S.n) = ⊤ := by
  rw [generatedIntermediateField, ← S.generated]
  apply le_antisymm
  · apply IntermediateField.adjoin.mono F
    rintro _ ⟨j, rfl⟩
    exact ⟨prefixGeneratorIndex (Fin.last S.n) j, rfl⟩
  · apply IntermediateField.adjoin.mono F
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨j, j.isLt⟩, rfl⟩

/-- Every prefix field is finite over the base field. -/
theorem generatedIntermediateField_finite
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin (S.n + 1)) :
    FiniteDimensional F (generatedIntermediateField S i) := by
  let : FiniteDimensional F K := S.finite
  infer_instance

/-- Each successive prefix field is finite over its predecessor. -/
theorem generatedIntermediateField_step_finite
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    FiniteDimensional (generatedIntermediateField S i.castSucc)
      (generatedIntermediateField S i.succ) := by
  let : FiniteDimensional F K := S.finite
  let : FiniteDimensional F (generatedIntermediateField S i.succ) :=
    generatedIntermediateField_finite S i.succ
  let : IsScalarTower F (generatedIntermediateField S i.castSucc)
      (generatedIntermediateField S i.succ) :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  exact Module.Finite.of_restrictScalars_finite F
    (generatedIntermediateField S i.castSucc)
    (generatedIntermediateField S i.succ)

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
  let : FiniteDimensional F K := S.finite
  exact minpoly.irreducible
    (IsIntegral.of_finite (generatedIntermediateField S i.castSucc) (S.alpha i))

/-- The degree of a successive minimal polynomial is the degree of the
    corresponding simple extension. -/
theorem generated_step_finrank_eq_minpoly_natDegree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    Module.finrank (generatedIntermediateField S i.castSucc)
        (generatedIntermediateField S i.succ) =
      (generatedMinpoly S i).natDegree := by
  let A := generatedIntermediateField S i.castSucc
  let : FiniteDimensional F K := S.finite
  let : IsScalarTower F A K := IsScalarTower.of_algebraMap_eq' (by rfl)
  let : Module.Finite A K := Module.Finite.of_restrictScalars_finite F A K
  have hfunc :
      (fun j : Fin i.succ => S.alpha (prefixGeneratorIndex i.succ j)) =
        Fin.snoc
          (fun j : Fin i.castSucc => S.alpha (prefixGeneratorIndex i.castSucc j))
          (S.alpha i) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Fin.snoc, prefixGeneratorIndex]
    · simp [Fin.snoc, prefixGeneratorIndex]
  have hfield :
      (IntermediateField.adjoin A ({S.alpha i} : Set K)).restrictScalars F =
        generatedIntermediateField S i.succ := by
    unfold generatedIntermediateField
    rw [IntermediateField.restrictScalars_adjoin,
      IntermediateField.adjoin_union, IntermediateField.adjoin_self,
      hfunc, Fin.range_snoc, Set.insert_eq, IntermediateField.adjoin_union]
    exact sup_comm _ _
  let hAB : A ≤ generatedIntermediateField S i.succ :=
    generatedIntermediateField_le S (by simp)
  let B' := IntermediateField.extendScalars hAB
  have hB' : B' = IntermediateField.adjoin A ({S.alpha i} : Set K) := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.extendScalars_restrictScalars, hfield]
  have hfin : Module.finrank A B' = (generatedMinpoly S i).natDegree := by
    rw [hB']
    simpa [generatedMinpoly] using
      IntermediateField.adjoin.finrank (IsIntegral.of_finite A (S.alpha i))
  change Module.finrank A B' = (generatedMinpoly S i).natDegree
  exact hfin

/-- Each successive prefix field has the quotient presentation by the
    corresponding minimal polynomial. -/
theorem generatedIntermediateField_step_quotient
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : FinitelyGeneratedFieldExtension F K) (i : Fin S.n) :
    Nonempty
      (generatedIntermediateField S i.succ ≃ₐ[
        generatedIntermediateField S i.castSucc]
        AdjoinRoot (generatedMinpoly S i)) := by
  let A := generatedIntermediateField S i.castSucc
  let : FiniteDimensional F K := S.finite
  let : IsScalarTower F A K := IsScalarTower.of_algebraMap_eq' (by rfl)
  let : Module.Finite A K := Module.Finite.of_restrictScalars_finite F A K
  have hfunc :
      (fun j : Fin i.succ => S.alpha (prefixGeneratorIndex i.succ j)) =
        Fin.snoc
          (fun j : Fin i.castSucc => S.alpha (prefixGeneratorIndex i.castSucc j))
          (S.alpha i) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Fin.snoc, prefixGeneratorIndex]
    · simp [Fin.snoc, prefixGeneratorIndex]
  have hfield :
      (IntermediateField.adjoin A ({S.alpha i} : Set K)).restrictScalars F =
        generatedIntermediateField S i.succ := by
    unfold generatedIntermediateField
    rw [IntermediateField.restrictScalars_adjoin,
      IntermediateField.adjoin_union, IntermediateField.adjoin_self,
      hfunc, Fin.range_snoc, Set.insert_eq, IntermediateField.adjoin_union]
    exact sup_comm _ _
  let hAB : A ≤ generatedIntermediateField S i.succ :=
    generatedIntermediateField_le S (by simp)
  let B' := IntermediateField.extendScalars hAB
  have hB' : B' = IntermediateField.adjoin A ({S.alpha i} : Set K) := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.extendScalars_restrictScalars, hfield]
  let e0 :=
    ((IntermediateField.equivOfEq hB').trans
      (IntermediateField.adjoinRootEquivAdjoin A
        (IsIntegral.of_finite A (S.alpha i))).symm)
  let f :
      generatedIntermediateField S i.succ →ₐ[
        generatedIntermediateField S i.castSucc]
        AdjoinRoot (generatedMinpoly S i) :=
    { toFun := e0
      map_one' := by
        change e0 1 = 1
        exact e0.map_one
      map_mul' := by
        intro x y
        change e0 (x * y) = e0 x * e0 y
        exact e0.map_mul x y
      map_zero' := by
        change e0 0 = 0
        exact e0.map_zero
      map_add' := by
        intro x y
        change e0 (x + y) = e0 x + e0 y
        exact e0.map_add x y
      commutes' := by
        intro r
        change e0 (algebraMap A B' r) =
          (algebraMap A (AdjoinRoot (minpoly A (S.alpha i))) r)
        exact e0.commutes r }
  exact ⟨AlgEquiv.ofBijective f ⟨e0.injective, e0.surjective⟩⟩

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
  have hcomp :
      (algebraMap L L).comp
          (generatedEmbedding S φ i.castSucc).toRingHom =
        φ.toRingHom.comp
          (algebraMap (generatedIntermediateField S i.castSucc) K) := by
    ext x
    rfl
  have hmap := Polynomial.map_aeval_eq_aeval_map
    (R := generatedIntermediateField S i.castSucc)
    (φ := (generatedEmbedding S φ i.castSucc).toRingHom)
    (ψ := φ.toRingHom) hcomp (generatedMinpoly S i) (S.alpha i)
  have hroot : Polynomial.aeval (S.alpha i) (generatedMinpoly S i) = 0 :=
    minpoly.aeval _ _
  rw [hroot, map_zero] at hmap
  simpa [generatedEmbeddingGenerator, generatedMappedPolynomial,
    generatedEmbedding, generatorInNextField] using hmap.symm

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
  let A := generatedIntermediateField S i.castSucc
  let : FiniteDimensional F K := S.finite
  let : IsScalarTower F A K := IsScalarTower.of_algebraMap_eq' (by rfl)
  let : Module.Finite A K := Module.Finite.of_restrictScalars_finite F A K
  let : IsScalarTower F A (generatedIntermediateField S i.succ) :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  have hfunc :
      (fun j : Fin i.succ => S.alpha (prefixGeneratorIndex i.succ j)) =
        Fin.snoc
          (fun j : Fin i.castSucc => S.alpha (prefixGeneratorIndex i.castSucc j))
          (S.alpha i) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Fin.snoc, prefixGeneratorIndex]
    · simp [Fin.snoc, prefixGeneratorIndex]
  have hfield :
      (IntermediateField.adjoin A ({S.alpha i} : Set K)).restrictScalars F =
        generatedIntermediateField S i.succ := by
    unfold generatedIntermediateField
    rw [IntermediateField.restrictScalars_adjoin,
      IntermediateField.adjoin_union, IntermediateField.adjoin_self,
      hfunc, Fin.range_snoc, Set.insert_eq, IntermediateField.adjoin_union]
    exact sup_comm _ _
  let hAB : A ≤ generatedIntermediateField S i.succ :=
    generatedIntermediateField_le S (by simp)
  let B' := IntermediateField.extendScalars hAB
  have hB' : B' = IntermediateField.adjoin A ({S.alpha i} : Set K) := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.extendScalars_restrictScalars, hfield]
  let e0 :=
    ((IntermediateField.equivOfEq hB').trans
      (IntermediateField.adjoinRootEquivAdjoin A
        (IsIntegral.of_finite A (S.alpha i))).symm)
  let f :
      generatedIntermediateField S i.succ →ₐ[A]
        AdjoinRoot (generatedMinpoly S i) :=
    { toFun := e0
      map_one' := by
        change e0 1 = 1
        exact e0.map_one
      map_mul' := by
        intro x y
        change e0 (x * y) = e0 x * e0 y
        exact e0.map_mul x y
      map_zero' := by
        change e0 0 = 0
        exact e0.map_zero
      map_add' := by
        intro x y
        change e0 (x + y) = e0 x + e0 y
        exact e0.map_add x y
      commutes' := by
        intro r
        change e0 (algebraMap A B' r) =
          (algebraMap A (AdjoinRoot (minpoly A (S.alpha i))) r)
        exact e0.commutes r }
  let e : generatedIntermediateField S i.succ ≃ₐ[A]
      AdjoinRoot (generatedMinpoly S i) :=
    AlgEquiv.ofBijective f ⟨e0.injective, e0.surjective⟩
  have hβ' :
      (generatedMinpoly S i).eval₂
          (φ : generatedIntermediateField S i.castSucc →+* L) β = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_map] using hβ
  let ψ : generatedIntermediateField S i.succ →ₐ[F] L :=
    (AdjoinRoot.liftAlgHom (generatedMinpoly S i) φ β hβ').comp
      (e.restrictScalars F)
  refine ⟨ψ, ?_, ?_⟩
  · ext x
    change (AdjoinRoot.liftAlgHom (generatedMinpoly S i) φ β hβ')
        (e (algebraMap A (generatedIntermediateField S i.succ) x)) = φ x
    rw [e.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]
  · change (AdjoinRoot.liftAlgHom (generatedMinpoly S i) φ β hβ')
      (e (generatorInNextField S i)) = β
    have hgen :
        e (generatorInNextField S i) = AdjoinRoot.root (generatedMinpoly S i) := by
      change e0 (generatorInNextField S i) =
        AdjoinRoot.root (minpoly A (S.alpha i))
      change (IntermediateField.adjoinRootEquivAdjoin A
        (IsIntegral.of_finite A (S.alpha i))).symm
          ((IntermediateField.equivOfEq hB') (generatorInNextField S i)) =
        AdjoinRoot.root (minpoly A (S.alpha i))
      have hgen' :
          (IntermediateField.equivOfEq hB') (generatorInNextField S i) =
            IntermediateField.AdjoinSimple.gen A (S.alpha i) := by
        apply Subtype.ext
        rfl
      rw [hgen', IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
    rw [hgen]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

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
  apply IntermediateField.algHom_ext_of_eq_adjoin (hS := by
    rfl)
  intro x hx
  rcases hx with ⟨j, rfl⟩
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change ψ₁ (generatorInNextField S i) = ψ₂ (generatorInNextField S i)
    exact hβ
  · let a : generatedIntermediateField S i.castSucc :=
      ⟨S.alpha (prefixGeneratorIndex i.castSucc j),
        IntermediateField.subset_adjoin F _
          ⟨j, rfl⟩⟩
    change ψ₁ (generatedIntermediateFieldInclusion S i a) =
      ψ₂ (generatedIntermediateFieldInclusion S i a)
    calc
      ψ₁ (generatedIntermediateFieldInclusion S i a) =
          (ψ₁.comp (generatedIntermediateFieldInclusion S i)) a := rfl
      _ = φ a := congrArg (fun f => f a) h₁
      _ = (ψ₂.comp (generatedIntermediateFieldInclusion S i)) a :=
        (congrArg (fun f => f a) h₂).symm
      _ = ψ₂ (generatedIntermediateFieldInclusion S i a) := rfl

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

private theorem algHom_comp_intermediateField_inclusion
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    {A B : IntermediateField F K} (h : A ≤ B) (φ : K →ₐ[F] L) :
    (φ.comp B.val).comp (IntermediateField.inclusion h) =
      φ.comp A.val := by
  apply AlgHom.ext
  intro x
  change φ ((IntermediateField.inclusion h) x) = φ x
  rw [IntermediateField.coe_inclusion]

private theorem generated_embedding_prefix_compatible
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (φ : K →ₐ[F] L)
    (i : Fin S.n) :
    (generatedEmbedding S φ i.succ).comp
        (generatedIntermediateFieldInclusion S i) =
      generatedEmbedding S φ i.castSucc := by
  unfold generatedEmbedding generatedIntermediateFieldInclusion
  exact algHom_comp_intermediateField_inclusion _ φ

/-- The tuple attached to a whole-extension embedding satisfies the successive
    root conditions. -/
theorem generated_embedding_tuple_is_successive_root_tuple
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L]
    (S : FinitelyGeneratedFieldExtension F K) (φ : K →ₐ[F] L) :
    SuccessiveRootTuple S (generatedEmbeddingTuple S φ) := by
  refine ⟨fun j => generatedEmbedding S φ j, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · exact generated_embedding_prefix_compatible S φ i
  · rfl
  · change Polynomial.aeval (generatedEmbeddingGenerator S φ i)
      (generatedMappedPolynomial S φ i) = 0
    exact generated_embedding_generator_is_root S φ i

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
  refine ⟨?_, ?_⟩
  · intro φ ψ h
    let fφ : (⊤ : IntermediateField F K) →ₐ[F] L :=
      φ.comp IntermediateField.topEquiv.toAlgHom
    let fψ : (⊤ : IntermediateField F K) →ₐ[F] L :=
      ψ.comp IntermediateField.topEquiv.toAlgHom
    have htop : fφ = fψ := by
      apply IntermediateField.algHom_ext_of_eq_adjoin (hS := S.generated.symm)
      intro x hx
      rcases hx with ⟨i, rfl⟩
      change φ (S.alpha i) = ψ (S.alpha i)
      have hi : generatedEmbeddingTuple S φ i = generatedEmbeddingTuple S ψ i :=
        congrArg (fun q => q.1 i) h
      change φ (S.alpha i) = ψ (S.alpha i) at hi
      exact hi
    apply AlgHom.ext
    intro x
    have hx : x ∈ (⊤ : IntermediateField F K) := trivial
    exact DFunLike.congr_fun htop ⟨x, hx⟩
  · rintro ⟨β, hβ⟩
    rcases hβ with ⟨φs, hφs⟩
    let last : Fin (S.n + 1) := Fin.last S.n
    let incToLast (j : Fin (S.n + 1)) :
        generatedIntermediateField S j →ₐ[F]
          generatedIntermediateField S last :=
      IntermediateField.inclusion
        (generatedIntermediateField_le S (Nat.le_of_lt_succ j.isLt))
    let topEq : generatedIntermediateField S last ≃ₐ[F]
        (⊤ : IntermediateField F K) :=
      IntermediateField.equivOfEq (generatedIntermediateField_last_eq_top S)
    let ψ : K →ₐ[F] L :=
      (φs last).comp
        (topEq.symm.toAlgHom.comp IntermediateField.topEquiv.symm.toAlgHom)
    have hψ (j : Fin (S.n + 1)) :
        generatedEmbedding S ψ j = (φs last).comp (incToLast j) := by
      ext x
      rfl
    have hdown : ∀ j : Fin (S.n + 1),
        (φs last).comp (incToLast j) = φs j := by
      intro j
      induction j using Fin.reverseInduction with
      | last =>
          apply AlgHom.ext
          intro x
          change (φs last) (incToLast last x) = (φs last) x
          congr 1
      | cast i ih =>
          have hfactor :
              incToLast i.castSucc =
                (incToLast i.succ).comp
                  (generatedIntermediateFieldInclusion S i) := by
            have hAB :
                generatedIntermediateField S i.castSucc ≤
                  generatedIntermediateField S i.succ :=
              generatedIntermediateField_le S (by simp)
            have hBC :
                generatedIntermediateField S i.succ ≤
                  generatedIntermediateField S last :=
              generatedIntermediateField_le S
                (Nat.le_of_lt_succ i.succ.isLt)
            unfold incToLast generatedIntermediateFieldInclusion
            apply AlgHom.ext
            intro x
            exact (IntermediateField.inclusion_inclusion hAB hBC x).symm
          calc
            (φs last).comp (incToLast i.castSucc) =
                ((φs last).comp (incToLast i.succ)).comp
                  (generatedIntermediateFieldInclusion S i) := by
              rw [AlgHom.comp_assoc, hfactor]
            _ = (φs i.succ).comp
                (generatedIntermediateFieldInclusion S i) := by
              rw [ih]
            _ = φs i.castSucc := (hφs i).1
    refine ⟨ψ, ?_⟩
    apply Subtype.ext
    funext i
    change generatedEmbeddingGenerator S ψ i = β i
    rw [generatedEmbeddingGenerator, hψ i.succ]
    have hgen := DFunLike.congr_fun (hdown i.succ)
      (generatorInNextField S i)
    rw [hgen]
    exact (hφs i).2.1

/-- The number of extension embeddings is the product of the successive
    separable degrees. -/
theorem count_embeddings_explicitly
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    (S : FinitelyGeneratedFieldExtension F K) :
    Nat.card (K →ₐ[F] L) =
      ∏ i : Fin S.n, (generatedMinpoly S i).natSepDegree := by
  let : FiniteDimensional F K := S.finite
  let : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hprod :
      ∀ (m : ℕ) (hm : m ≤ S.n),
        Field.finSepDegree F
            (generatedIntermediateField S
              ⟨m, Nat.lt_succ_of_le hm⟩) =
          ∏ i : Fin m,
            (generatedMinpoly S
              ⟨i.1, lt_of_lt_of_le i.isLt hm⟩).natSepDegree := by
    intro m
    induction m with
    | zero =>
        intro hm
        change Field.finSepDegree F
            (generatedIntermediateField S (0 : Fin (S.n + 1))) = _
        rw [generatedIntermediateField_zero_eq_bot S]
        simp
    | succ m ih =>
        intro hm
        have hmle : m ≤ S.n := le_trans (Nat.le_succ m) hm
        have hmlt : m < S.n :=
          lt_of_lt_of_le (Nat.lt_succ_self m) hm
        let j : Fin S.n := ⟨m, hmlt⟩
        let A := generatedIntermediateField S j.castSucc
        let B := generatedIntermediateField S j.succ
        let : IsScalarTower F A K :=
          IsScalarTower.of_algebraMap_eq' (by rfl)
        let : Module.Finite A K :=
          Module.Finite.of_restrictScalars_finite F A K
        let : FiniteDimensional A B :=
          generatedIntermediateField_step_finite S j
        let : IsScalarTower F A B :=
          IsScalarTower.of_algebraMap_eq' (by rfl)
        let : Algebra.IsAlgebraic A B :=
          Algebra.IsAlgebraic.of_finite A B
        have hmul :
            Field.finSepDegree F A * Field.finSepDegree A B =
              Field.finSepDegree F B :=
          Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F A B
        obtain ⟨e⟩ := generatedIntermediateField_step_quotient S j
        have hstep :
            Field.finSepDegree A B =
              (generatedMinpoly S j).natSepDegree := by
          have hp : Irreducible (generatedMinpoly S j) :=
            generatedMinpoly_irreducible S j
          have hp_monic : (generatedMinpoly S j).Monic :=
            minpoly.monic (IsIntegral.of_finite A (S.alpha j))
          let : Fact (Irreducible (generatedMinpoly S j)) := ⟨hp⟩
          have htop :
              IntermediateField.adjoin A
                  ({AdjoinRoot.root (generatedMinpoly S j)} :
                    Set (AdjoinRoot (generatedMinpoly S j))) =
                (⊤ : IntermediateField A
                  (AdjoinRoot (generatedMinpoly S j))) :=
            IntermediateField.adjoin_root_eq_top (generatedMinpoly S j)
          have hmin :
              minpoly A (AdjoinRoot.root (generatedMinpoly S j)) =
                generatedMinpoly S j := by
            rw [AdjoinRoot.minpoly_root hp.ne_zero]
            simp [hp_monic]
          have hs := IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree
            (F := A) (E := AdjoinRoot (generatedMinpoly S j))
            (α := AdjoinRoot.root (generatedMinpoly S j))
            (AdjoinRoot.isAlgebraic_root hp.ne_zero)
          calc
            Field.finSepDegree A B =
                Field.finSepDegree A
                  (AdjoinRoot (generatedMinpoly S j)) :=
              Field.finSepDegree_eq_of_equiv A B
                (AdjoinRoot (generatedMinpoly S j)) e
            _ = Field.finSepDegree A
                (⊤ : IntermediateField A
                  (AdjoinRoot (generatedMinpoly S j))) := by
              rw [← IntermediateField.finSepDegree_top
                (F := A) (E := A)
                (K := AdjoinRoot (generatedMinpoly S j))]
            _ = Field.finSepDegree A
                (IntermediateField.adjoin A
                  ({AdjoinRoot.root (generatedMinpoly S j)} :
                    Set (AdjoinRoot (generatedMinpoly S j)))) := by
              exact congrArg
                (fun T : IntermediateField A
                  (AdjoinRoot (generatedMinpoly S j)) =>
                    Field.finSepDegree A T) htop.symm
            _ = (generatedMinpoly S j).natSepDegree := by
              rw [hmin] at hs
              exact hs
        have hprev := ih hmle
        have hprev' :
            Field.finSepDegree F A =
              ∏ i : Fin m,
                (generatedMinpoly S
                  ⟨i.1, lt_of_lt_of_le i.isLt hmle⟩).natSepDegree := by
          simpa [A, j] using hprev
        calc
          Field.finSepDegree F
              (generatedIntermediateField S
                ⟨m + 1, Nat.lt_succ_of_le hm⟩) =
              Field.finSepDegree F A * Field.finSepDegree A B := by
            rw [show (generatedIntermediateField S
                ⟨m + 1, Nat.lt_succ_of_le hm⟩) = B by
              rfl]
            exact hmul.symm
          _ = (∏ i : Fin m,
                (generatedMinpoly S
                  ⟨i.1, lt_of_lt_of_le i.isLt hmle⟩).natSepDegree) *
              (generatedMinpoly S j).natSepDegree := by
            rw [hprev', hstep]
          _ = ∏ i : Fin (m + 1),
                (generatedMinpoly S
                  ⟨i.1, lt_of_lt_of_le i.isLt hm⟩).natSepDegree := by
            rw [Fin.prod_univ_castSucc]
            rfl
  have hfinal :
      Field.finSepDegree F K =
        ∏ i : Fin S.n, (generatedMinpoly S i).natSepDegree := by
    rw [← IntermediateField.finSepDegree_top
      (F := F) (E := F) (K := K)]
    rw [← generatedIntermediateField_last_eq_top S]
    have hlast := hprod S.n le_rfl
    have hidx :
        (⟨S.n, Nat.lt_succ_self S.n⟩ : Fin (S.n + 1)) =
          Fin.last S.n := by
      apply Fin.ext
      rfl
    rw [hidx] at hlast
    exact hlast
  calc
    Nat.card (K →ₐ[F] L) = Field.finSepDegree F K :=
      (Field.finSepDegree_eq_of_isAlgClosed F K L).symm
    _ = ∏ i : Fin S.n, (generatedMinpoly S i).natSepDegree := hfinal

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
  let : FiniteDimensional F K := S.finite
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hprod_degree :
      ∀ (m : ℕ) (hm : m ≤ S.n),
        Module.finrank F
            (generatedIntermediateField S
              ⟨m, Nat.lt_succ_of_le hm⟩) =
          ∏ i : Fin m,
            (generatedMinpoly S
              ⟨i.1, lt_of_lt_of_le i.isLt hm⟩).natDegree := by
    intro m
    induction m with
    | zero =>
        intro hm
        change Module.finrank F
            (generatedIntermediateField S (0 : Fin (S.n + 1))) = _
        rw [generatedIntermediateField_zero_eq_bot S]
        simp
    | succ m ih =>
        intro hm
        have hmle : m ≤ S.n := le_trans (Nat.le_succ m) hm
        have hmlt : m < S.n :=
          lt_of_lt_of_le (Nat.lt_succ_self m) hm
        let j : Fin S.n := ⟨m, hmlt⟩
        let A := generatedIntermediateField S j.castSucc
        let B := generatedIntermediateField S j.succ
        let : IsScalarTower F A K :=
          IsScalarTower.of_algebraMap_eq' (by rfl)
        let : Module.Finite A K :=
          Module.Finite.of_restrictScalars_finite F A K
        let : FiniteDimensional A B :=
          generatedIntermediateField_step_finite S j
        let : IsScalarTower F A B :=
          IsScalarTower.of_algebraMap_eq' (by rfl)
        have hmul :
            Module.finrank F A * Module.finrank A B =
              Module.finrank F B :=
          Module.finrank_mul_finrank F A B
        have hstep :
            Module.finrank A B = (generatedMinpoly S j).natDegree := by
          simpa [A, B] using generated_step_finrank_eq_minpoly_natDegree S j
        have hprev := ih hmle
        have hprev' :
            Module.finrank F A =
              ∏ i : Fin m,
                (generatedMinpoly S
                  ⟨i.1, lt_of_lt_of_le i.isLt hmle⟩).natDegree := by
          simpa [A, j] using hprev
        calc
          Module.finrank F
              (generatedIntermediateField S
                ⟨m + 1, Nat.lt_succ_of_le hm⟩) =
              Module.finrank F A * Module.finrank A B := by
            rw [show (generatedIntermediateField S
                ⟨m + 1, Nat.lt_succ_of_le hm⟩) = B by
              rfl]
            exact hmul.symm
          _ = (∏ i : Fin m,
                (generatedMinpoly S
                  ⟨i.1, lt_of_lt_of_le i.isLt hmle⟩).natDegree) *
              (generatedMinpoly S j).natDegree := by
            rw [hprev', hstep]
          _ = ∏ i : Fin (m + 1),
                (generatedMinpoly S
                  ⟨i.1, lt_of_lt_of_le i.isLt hm⟩).natDegree := by
            rw [Fin.prod_univ_castSucc]
            rfl
  have hdegree :
      (∏ i : Fin S.n, (generatedMinpoly S i).natDegree) =
        Module.finrank F K := by
    have hlast := hprod_degree S.n le_rfl
    have hidx :
        (⟨S.n, Nat.lt_succ_self S.n⟩ : Fin (S.n + 1)) =
          Fin.last S.n := by
      apply Fin.ext
      rfl
    rw [hidx] at hlast
    rw [generatedIntermediateField_last_eq_top S,
      IntermediateField.finrank_top'] at hlast
    exact hlast.symm
  have hprod_eq :
      (∏ i : Fin S.n, (generatedMinpoly S i).natSepDegree) =
        ∏ i : Fin S.n, (generatedMinpoly S i).natDegree := by
    apply Finset.prod_congr rfl
    intro i hi
    exact separable_polynomial_separable_degree_eq_degree (hsep i)
  have hcard :
      Nat.card (K →ₐ[F] L) = Module.finrank F K := by
    calc
      Nat.card (K →ₐ[F] L) =
          ∏ i : Fin S.n, (generatedMinpoly S i).natSepDegree :=
        count_embeddings_explicitly S
      _ = ∏ i : Fin S.n, (generatedMinpoly S i).natDegree := hprod_eq
      _ = Module.finrank F K := hdegree
  have hfinsep :
      Field.finSepDegree F K = Module.finrank F K :=
    (Field.finSepDegree_eq_of_isAlgClosed F K L).trans hcard
  exact ⟨hcard, (Field.finSepDegree_eq_finrank_iff F K).mp hfinsep⟩

/-- If one successive minimal polynomial is inseparable, the embedding count
    is strictly smaller than the degree. -/
theorem finitely_generated_embedding_count_lt_of_step_not_separable
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    (S : FinitelyGeneratedFieldExtension F K)
    (hnot : ∃ i : Fin S.n, ¬(generatedMinpoly S i).Separable) :
    Nat.card (K →ₐ[F] L) < Module.finrank F K := by
  let : FiniteDimensional F K := S.finite
  let : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hnot_sep_ext : ¬ Algebra.IsSeparable F K := by
    intro hK
    let : Algebra.IsSeparable F K := hK
    rcases hnot with ⟨i, hi⟩
    let A := generatedIntermediateField S i.castSucc
    let : IsScalarTower F A K :=
      IsScalarTower.of_algebraMap_eq' (by rfl)
    have hαF : IsSeparable F (S.alpha i) :=
      Algebra.IsSeparable.isSeparable F (S.alpha i)
    have hαA : IsSeparable A (S.alpha i) :=
      separable_element_goes_up hαF
    apply hi
    have hminsep : (minpoly A (S.alpha i)).Separable :=
      (separable_element_iff_minpoly_separable
        (F := A) (K := K) (S.alpha i)).mp hαA
    simpa [generatedMinpoly, A] using hminsep
  have hle :
      Nat.card (K →ₐ[F] L) ≤ Module.finrank F K := by
    calc
      Nat.card (K →ₐ[F] L) = Field.finSepDegree F K :=
        (Field.finSepDegree_eq_of_isAlgClosed F K L).symm
      _ ≤ Module.finrank F K := Field.finSepDegree_le_finrank F K
  have hne :
      Nat.card (K →ₐ[F] L) ≠ Module.finrank F K := by
    intro heq
    have hfinsep :
        Field.finSepDegree F K = Module.finrank F K :=
      (Field.finSepDegree_eq_of_isAlgClosed F K L).trans heq
    have hK : Algebra.IsSeparable F K :=
      (Field.finSepDegree_eq_finrank_iff F K).mp hfinsep
    exact hnot_sep_ext hK
  exact lt_of_le_of_ne hle hne

/-- For a finite extension, the embedding count is bounded by the degree, with
    equality exactly in the separable case. -/
theorem finite_extension_embedding_count_le_and_eq_iff
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    [FiniteDimensional F K] :
    Nat.card (K →ₐ[F] L) ≤ Module.finrank F K ∧
      (Nat.card (K →ₐ[F] L) = Module.finrank F K ↔
        Algebra.IsSeparable F K) := by
  let : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hcard :
      Nat.card (K →ₐ[F] L) = Field.finSepDegree F K :=
    (Field.finSepDegree_eq_of_isAlgClosed F K L).symm
  have hle :
      Nat.card (K →ₐ[F] L) ≤ Module.finrank F K := by
    calc
      Nat.card (K →ₐ[F] L) = Field.finSepDegree F K := hcard
      _ ≤ Module.finrank F K := Field.finSepDegree_le_finrank F K
  have hiff :
      Nat.card (K →ₐ[F] L) = Module.finrank F K ↔
        Algebra.IsSeparable F K := by
    constructor
    · intro heq
      apply (Field.finSepDegree_eq_finrank_iff F K).mp
      exact (Field.finSepDegree_eq_of_isAlgClosed F K L).trans heq
    · intro hsep
      let : Algebra.IsSeparable F K := hsep
      calc
        Nat.card (K →ₐ[F] L) = Field.finSepDegree F K := hcard
        _ = Module.finrank F K :=
          Field.finSepDegree_eq_finrank_of_isSeparable F K
  exact ⟨hle, hiff⟩

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
