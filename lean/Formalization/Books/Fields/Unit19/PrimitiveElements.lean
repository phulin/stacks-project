import Mathlib.FieldTheory.PrimitiveElement

/-!
# Fields, Chapter 19: Primitive elements

The source's primitive-element predicate is represented by Mathlib's canonical
intermediate-field expression `F⟮α⟯ = ⊤`: no parallel predicate is needed.
For a finite extension, the intermediate fields between `F` and `E` are
represented by `IntermediateField F E`.
-/

namespace Formalization.Books.Fields.Unit19

noncomputable section

/-! ## Primitive elements -/

/- The source's definition is the equality `F⟮α⟯ = ⊤` used below.  Mathlib
   deliberately does not introduce a separate `IsPrimitiveElement` predicate
   for this statement. -/

/- The finite-extension hypothesis supplies algebraicity, so the source's
   equivalence is the finite-dimensional specialization of Mathlib's stronger
   algebraic-extension theorem. -/
/-- The finite-extension primitive element criterion. -/
theorem primitive_element_iff_finite_intermediateField
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    (∃ α : E, IntermediateField.adjoin F ({α} : Set E) = ⊤) ↔
      Finite (IntermediateField F E) := by
  have h_alg : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  constructor
  · intro h
    exact (Field.exists_primitive_element_iff_finite_intermediateField F E).mp
      ⟨h_alg, h⟩
  · intro h
    exact ((Field.exists_primitive_element_iff_finite_intermediateField F E).mpr h).2

/- Mathlib's primitive element theorem gives the source's “moreover” assertion
   (1) for a finite separable extension directly. -/
/-- A finite separable extension has a primitive element. -/
theorem exists_primitive_element_of_finite_separable
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ α : E, IntermediateField.adjoin F ({α} : Set E) = ⊤ :=
  Field.exists_primitive_element F E

/- The equivalence then gives the source's “moreover” assertion (2). -/
/-- A finite separable extension has finitely many intermediate fields. -/
theorem finite_intermediateField_of_finite_separable
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Finite (IntermediateField F E) := by
  exact (primitive_element_iff_finite_intermediateField (F := F) (E := E)).mp
    (exists_primitive_element_of_finite_separable (F := F) (E := E))

/-- Both parts of the primitive element lemma hold for a finite separable
    extension. -/
theorem primitive_element_and_finite_intermediateField_of_finite_separable
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    (∃ α : E, IntermediateField.adjoin F ({α} : Set E) = ⊤) ∧
      Finite (IntermediateField F E) :=
  ⟨exists_primitive_element_of_finite_separable (F := F) (E := E),
    finite_intermediateField_of_finite_separable (F := F) (E := E)⟩

end

end Formalization.Books.Fields.Unit19
