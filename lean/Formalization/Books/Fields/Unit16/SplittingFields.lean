import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.PiTensorProduct

/-!
# Fields, Chapter 16: Splitting fields

The source's splitting-field predicate is Mathlib's canonical
`Polynomial.IsSplittingField`, with `Polynomial.SplittingField` providing the
chosen construction.  Normal closures are represented by
`IntermediateField.normalClosure` and its predicate `IsNormalClosure`.
For the displayed tensor product, `PiTensorProduct` gives the finite indexed
tensor product of copies of a field as a `K`-algebra.
-/

namespace Formalization.Books.Fields.Unit16

noncomputable section

open Polynomial
open scoped BigOperators TensorProduct

universe u v w

/-! ## Splitting fields -/

/- The source's “smallest extension” is the universal property of
   `Polynomial.SplittingField`: it splits the polynomial, embeds into every
   field in which the polynomial splits, and is unique up to an algebra
   equivalence among splitting fields.  The normality assertion is the
   existing `Polynomial.SplittingField.instNormal` instance. -/
theorem splitting_field_spec
    {F : Type u} [Field F] {P : F[X]} (hP : P.natDegree ≠ 0) :
    P.IsSplittingField F P.SplittingField ∧
      Normal F P.SplittingField ∧
        (∀ {L : Type v} [Field L] [Algebra F L],
          (P.map (algebraMap F L)).Splits →
            Nonempty (P.SplittingField →ₐ[F] L)) ∧
          (∀ {L : Type v} [Field L] [Algebra F L]
              [hL : P.IsSplittingField F L],
            Nonempty (L ≃ₐ[F] P.SplittingField)) := by
  sorry

/- The source's definition introduces no new object: the canonical object
   `P.SplittingField`, together with the predicate above, is the Mathlib
   splitting field of `P` over `F`. -/

/-! ## Normal closures -/

/- `IntermediateField.normalClosure F E L` is the smallest intermediate field
   containing the images of all `F`-algebra embeddings of `E` into `L`.
   The theorem below records the finite, normal, and uniqueness properties in
   a normal ambient extension. -/
theorem normal_closure_spec
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [FiniteDimensional F E] [Normal F L] :
    let K := IntermediateField.normalClosure F E L
    Normal F K ∧
      FiniteDimensional F K ∧
        FiniteDimensional E K ∧
          IsNormalClosure F E K ∧
            (∀ K' : IntermediateField F L,
              K ≤ K' ↔ ∀ φ : E →ₐ[F] L, φ.fieldRange ≤ K') ∧
              (∀ {T : Type*} [Field T] [Algebra F T]
                  (hT : IsNormalClosure F E T),
                Nonempty (T ≃ₐ[F] K)) := by
  sorry

/- The algebra over `E` on the normal closure is the canonical one supplied
   by Mathlib's `normalClosure.algebra`; finiteness over `E` follows from the
   tower finiteness theorem once finiteness over `F` is known. -/
theorem normal_closure_finite_over_middle
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [FiniteDimensional F E] :
    FiniteDimensional E (IntermediateField.normalClosure F E L) := by
  exact Module.Finite.right F E (IntermediateField.normalClosure F E L)

/- Choosing an algebraic closure supplies the ambient normal extension needed
   for existence.  The `letI`s make the chosen embedding of the finite
   extension into the algebraic closure the algebra structure used on the
   normal closure. -/
theorem exists_normal_closure_of_finite_extension
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    ∃ ι : E →ₐ[F] AlgebraicClosure F,
      letI : Algebra E (AlgebraicClosure F) := ι.toRingHom.toAlgebra
      letI : IsScalarTower F E (AlgebraicClosure F) :=
        IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
      let K := IntermediateField.normalClosure F E (AlgebraicClosure F)
      Nonempty (E →ₐ[F] K) ∧
        Normal F K ∧ FiniteDimensional E K ∧ IsNormalClosure F E K := by
  sorry

/-! ## Normal closures inside a normal extension -/

/- The source's subextensions are represented by intermediate fields.  If
   `M ≤ M'`, `M'.extendScalars hM` is the same field viewed as an extension of
   `M`, so the tower and its finiteness are explicit in the conclusion. -/
theorem normal_closure_inside_normal_extension_first
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    (M : IntermediateField K L) [FiniteDimensional K M] :
    ∃ (M' : IntermediateField K L) (hM : M ≤ M'),
      FiniteDimensional K M' ∧ Normal K M' ∧
        FiniteDimensional M (IntermediateField.extendScalars hM) := by
  sorry

/- In the second part, `M/K` is normal and `M'/M` is finite.  The normal
   closure of `M'` in the ambient normal field supplies `M''`; the conclusion
   records that it contains `M'`, is normal over `K`, and is finite over `M`. -/
theorem normal_closure_inside_normal_extension_second
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    (M M' : IntermediateField K L) (hMM' : M ≤ M')
    [hM : Normal K M]
    [FiniteDimensional M (IntermediateField.extendScalars hMM')] :
    ∃ (M'' : IntermediateField K L) (hM'M'' : M' ≤ M''),
      Normal K M'' ∧
        FiniteDimensional M (IntermediateField.extendScalars (hMM'.trans hM'M'')) := by
  sorry

/-! ## The tensor-product description of a normal closure -/

/- The source's map sends a pure tensor to the product of the images under an
   enumeration of all `K`-embeddings of `L` into the normal closure.  The
   indexed tensor product is already a `K`-algebra in Mathlib, and
   `PiTensorProduct.liftAlgHom` is its universal construction. -/
noncomputable def normalClosureTensorProductMap
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (e : Fin (Field.finSepDegree K L) ≃ (L →ₐ[K] M)) :
    (⨂[K] _ : Fin (Field.finSepDegree K L), L) →ₐ[K] M :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra K (Fin (Field.finSepDegree K L)) M).compLinearMap
      (fun i => (e i).toLinearMap))
    (by simp)
    (by
      intro x y
      simp [MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, Finset.prod_mul_distrib])

theorem normalClosureTensorProductMap_tprod
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (e : Fin (Field.finSepDegree K L) ≃ (L →ₐ[K] M))
    (x : Fin (Field.finSepDegree K L) → L) :
    normalClosureTensorProductMap e (PiTensorProduct.tprod K x) =
      ∏ i, e i (x i) := by
  sorry

/- The finite-extension tensor-product assertion is stated with the canonical
   `IsNormalClosure` predicate.  Its normality is the existing
   `IsNormalClosure.normal` theorem, while the last inequality is exactly
   Mathlib's `Field.finSepDegree_le_finrank`. -/
theorem normal_closure_tensor_product_surjective
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L]
    [hM : IsNormalClosure K L M] :
    ∃ e : Fin (Field.finSepDegree K L) ≃ (L →ₐ[K] M),
      Function.Surjective (normalClosureTensorProductMap e) ∧
        Field.finSepDegree K L ≤ Module.finrank K L := by
  sorry

end

end Formalization.Books.Fields.Unit16
