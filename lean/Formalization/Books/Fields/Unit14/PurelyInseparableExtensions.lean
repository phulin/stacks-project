import Formalization.Books.Fields.Unit12.SeparableAlgebraicExtensions
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Fields, Chapter 14: Purely inseparable extensions

Mathlib's `IsPurelyInseparable` is the canonical extension predicate used by
this chapter.  Its `isPurelyInseparable_iff_pow_mem` characterization records
the source's p-power definition, while `perfectClosure` is the canonical
intermediate field formed by the purely inseparable elements.  The source's
separable and inseparable degrees are `Field.sepDegree` and
`Field.insepDegree`; the finite embedding count is `Field.finSepDegree`.
-/

namespace Formalization.Books.Fields.Unit14

noncomputable section

open Polynomial
open scoped BigOperators

universe u v w

/-! ## Definitions and the p-th-root example -/

/- The source's extension predicate is Mathlib's `IsPurelyInseparable`.
   The characteristic-free convention includes the identity extension through
   Mathlib's canonical `isPurelyInseparable_self` instance. -/
/-- The identity field extension is purely inseparable. -/
theorem purely_inseparable_self_extension
    (F : Type u) [Field F] : IsPurelyInseparable F F :=
  inferInstance

/- `perfectClosure` is Mathlib's canonical intermediate field of all elements
   satisfying the source's element-level p-power condition. -/
/-- An element is purely inseparable over the base exactly when it lies in the
    relative perfect closure. -/
theorem purely_inseparable_element_iff_pow_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) (hp : p.Prime) [CharP F p] (α : E) :
    α ∈ perfectClosure F E ↔
      ∃ n : ℕ, α ^ p ^ n ∈ (algebraMap F E).range := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact mem_perfectClosure_iff_pow_mem p

/- The simple-extension form is also useful for the source's p-th-root
   example, and is already part of Mathlib's perfect-closure API. -/
/-- A simple extension is purely inseparable exactly when its generator has a
    p-power in the base field. -/
theorem purely_inseparable_simple_extension_iff_pow_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) (hp : p.Prime) [CharP F p] (α : E) :
    IsPurelyInseparable F (IntermediateField.adjoin F ({α} : Set E)) ↔
      ∃ n : ℕ, α ^ p ^ n ∈ (algebraMap F E).range := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F E p

/-- Over a field of exponential characteristic `p`, an extension is purely
    inseparable exactly when every element becomes a p-power in the base. -/
theorem purely_inseparable_extension_iff_pow_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) (hp : p.Prime) [CharP F p] :
    IsPurelyInseparable F E ↔
      ∀ x : E, ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap F E).range := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact isPurelyInseparable_iff_pow_mem F p

/- The source's observation that purely inseparable extensions are algebraic is
   already a field of the canonical Mathlib class. -/
/-- A purely inseparable field extension is algebraic. -/
theorem purely_inseparable_extension_is_algebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsPurelyInseparable F E] : Algebra.IsAlgebraic F E :=
  IsPurelyInseparable.isAlgebraic F E

/-- In characteristic zero, a purely inseparable field extension is the
    identity extension in the sense that its base-field map is surjective. -/
theorem purely_inseparable_char_zero_is_trivial
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    [IsPurelyInseparable F E] : Function.Surjective (algebraMap F E) := by
  let _ : Algebra.IsAlgebraic F E := IsPurelyInseparable.isAlgebraic F E
  let _ : Algebra.IsSeparable F E :=
    Formalization.Books.Fields.Unit12.algebraic_extension_separable_of_char_zero
  exact IsPurelyInseparable.surjective_algebraMap_of_isSeparable F E

/- The source's polynomial `x^p - t` is represented by this canonical
   polynomial interface. -/
/-- If `t` has no p-th root, then `X^p - C t` is irreducible. -/
theorem take_pth_root_polynomial_irreducible
    {F : Type u} [Field F] (p : ℕ) (hp : p.Prime) [CharP F p]
    (t : F) (ht : ∀ b : F, b ^ p ≠ t) :
    Irreducible (X ^ p - C t) :=
  X_pow_sub_C_irreducible_of_prime hp ht

/- The quotient's distinguished element is the source's `t^(1/p)`. -/
/-- The distinguished root of the p-th-root quotient has p-th power `t`. -/
theorem pth_root_extension_root_is_pth_root
    {F : Type u} [Field F] (p : ℕ) (t : F) :
    (AdjoinRoot.root (X ^ p - C t)) ^ p = AdjoinRoot.of (X ^ p - C t) t :=
  root_X_pow_sub_C_pow p t

/-- Every element of the p-th-root quotient has the source's degree-`p`
    coefficient expansion, and its p-th power is in the base field. -/
theorem pth_root_extension_element_expansion
    {F : Type u} [Field F] (p : ℕ) (hp : p.Prime) [CharP F p]
    (t : F) (z : AdjoinRoot (X ^ p - C t)) :
    ∃ a : Fin p → F,
      z = ∑ i : Fin p,
          algebraMap F (AdjoinRoot (X ^ p - C t)) (a i) *
            (AdjoinRoot.root (X ^ p - C t)) ^ (i : ℕ) ∧
        z ^ p = algebraMap F (AdjoinRoot (X ^ p - C t))
          (∑ i : Fin p, (a i) ^ p * t ^ (i : ℕ)) := by
  sorry

/-- Adjoining a p-th root of an element without a p-th root gives a field and
    a purely inseparable extension. -/
theorem pth_root_adjoinRoot_field_and_purely_inseparable
    {F : Type u} [Field F] (p : ℕ) (hp : p.Prime) [CharP F p]
    (t : F) (ht : ∀ b : F, b ^ p ≠ t) :
    IsField (AdjoinRoot (X ^ p - C t)) ∧
      IsPurelyInseparable F (AdjoinRoot (X ^ p - C t)) := by
  refine ⟨Formalization.Books.Fields.Unit06.adjoinRoot_isField_of_irreducible
    (take_pth_root_polynomial_irreducible p hp t ht), ?_⟩
  sorry

/- The rational-function sentence in the source is made explicit using
   `RatFunc.X` over the prime field `ZMod p`. -/
/-- The rational-function indeterminate is not a p-th power. -/
theorem rational_function_indeterminate_not_pth_power
    (p : ℕ) [Fact p.Prime] :
    ∀ b : RatFunc (ZMod p), b ^ p ≠ (RatFunc.X : RatFunc (ZMod p)) := by
  sorry

/-- The rational-function field supplies the source's p-th-root example. -/
theorem rational_function_pth_root_extension
    (p : ℕ) [Fact p.Prime] :
    Irreducible
        (X ^ p - C (RatFunc.X : RatFunc (ZMod p))) ∧
      IsField
        (AdjoinRoot (X ^ p - C (RatFunc.X : RatFunc (ZMod p)))) ∧
      IsPurelyInseparable
        (RatFunc (ZMod p))
        (AdjoinRoot (X ^ p - C (RatFunc.X : RatFunc (ZMod p)))) := by
  sorry

/-! ## Permanence and the purely inseparable subextension -/

/- This is Mathlib's tower theorem, with the source's field-extension
   notation made explicit through `Algebra` and `IsScalarTower`. -/
/-- Purely inseparable extensions are transitive in a field tower. -/
theorem purely_inseparable_extension_permanence
    {k E F : Type*} [Field k] [Field E] [Field F]
    [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]
    [IsPurelyInseparable k E] [IsPurelyInseparable E F] :
    IsPurelyInseparable k F :=
  IsPurelyInseparable.trans k E F

/- `perfectClosure F E` is Mathlib's canonical subextension of all elements
   satisfying the source's purely-inseparable element condition. -/
/-- The purely inseparable elements form an intermediate field. -/
theorem purely_inseparable_elements_form_subextension
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    ∃ L : IntermediateField F E, ∀ x : E,
      x ∈ L ↔
        ∃ n : ℕ, x ^ (ringExpChar F) ^ n ∈ (algebraMap F E).range := by
  refine ⟨perfectClosure F E, ?_⟩
  exact fun _ => mem_perfectClosure_iff

/-! ## Finite purely inseparable extensions -/

/- The finite tower is expressed with Unit 12's ordered generator family and
   its canonical prefix intermediate fields.  This retains the source's
   successive fields while reusing the established field-extension interface. -/
/-- A finite purely inseparable extension admits a tower whose successive steps
    adjoin p-th roots and have degree `p`. -/
theorem finite_purely_inseparable_has_pth_root_tower
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} (hp : p.Prime) [CharP F p]
    [FiniteDimensional F E] [IsPurelyInseparable F E] :
    ∃ S : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension F E,
      ∀ i : Fin S.n,
        ∃ y : Formalization.Books.Fields.Unit12.generatedIntermediateField
            S i.castSucc,
          algebraMap
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ) y =
            (Formalization.Books.Fields.Unit12.generatorInNextField S i) ^ p ∧
          (∀ z : Formalization.Books.Fields.Unit12.generatedIntermediateField
              S i.castSucc, z ^ p ≠ y) ∧
          Module.finrank
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ) = p := by
  sorry

/-! ## Separable first and degrees -/

/- `separableClosure F E` is the source's `E_sep`; Mathlib supplies both its
   separability and the purely inseparable top extension, together with the
   uniqueness criterion. -/
/-- Every algebraic field extension is uniquely separable followed by purely
    inseparable. -/
theorem separable_first_then_purely_inseparable_unique
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] :
    ∃! L : IntermediateField F E,
      Algebra.IsSeparable F L ∧ IsPurelyInseparable L E := by
  refine ⟨separableClosure F E, ⟨inferInstance, inferInstance⟩, ?_⟩
  intro L hL
  exact (eq_separableClosure_iff F E L).2 hL

/- The source's two degree definitions are exactly the following canonical
   rank definitions. -/
/-- `Field.sepDegree` and `Field.insepDegree` are the degrees of the two
    successive extensions through `separableClosure`. -/
theorem separable_and_inseparable_degree_definitions
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    Field.sepDegree F E = Module.rank F (separableClosure F E) ∧
      Field.insepDegree F E = Module.rank (separableClosure F E) E :=
  ⟨rfl, rfl⟩

/-- In characteristic zero, the separable degree is the extension degree and
    the inseparable degree is one. -/
theorem characteristic_zero_degree_consequences
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra.IsAlgebraic F E] :
    Field.sepDegree F E = Module.rank F E ∧ Field.insepDegree F E = 1 := by
  let _ : Algebra.IsSeparable F E :=
    Formalization.Books.Fields.Unit12.algebraic_extension_separable_of_char_zero
  exact ⟨Algebra.IsSeparable.sepDegree_eq F E, Algebra.IsSeparable.insepDegree_eq F E⟩

/-- The separable and inseparable degrees multiply to the full degree, also
    for infinite algebraic extensions. -/
theorem extension_degree_factorization
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    Field.sepDegree F E * Field.insepDegree F E = Module.rank F E :=
  Field.sepDegree_mul_insepDegree F E

/-- For a finite extension, the separable degree is the number of embeddings
    into any chosen algebraic closure. -/
theorem finite_extension_separable_degree_eq_embedding_card
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    [FiniteDimensional F K] :
    Field.finSepDegree F K = Nat.card (K →ₐ[F] L) := by
  let _ : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  let _ : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  exact Field.finSepDegree_eq_of_isAlgClosed F K L

/- The source's final tower law is Mathlib's canonical algebraic tower law for
   both degree notions. -/
/-- Separable and inseparable degrees are multiplicative in an algebraic tower. -/
theorem separable_and_inseparable_degree_multiplicative
    {F E K : Type u} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic F E] [Algebra.IsAlgebraic E K] :
    Field.sepDegree E K * Field.sepDegree F E = Field.sepDegree F K ∧
      Field.insepDegree E K * Field.insepDegree F E = Field.insepDegree F K := by
  constructor
  · simpa [mul_comm] using Field.sepDegree_mul_sepDegree_of_isAlgebraic F E K
  · simpa [mul_comm] using Field.insepDegree_mul_insepDegree_of_isAlgebraic F E K

end

end Formalization.Books.Fields.Unit14
