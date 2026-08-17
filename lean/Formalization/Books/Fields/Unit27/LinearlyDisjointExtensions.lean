import Formalization.Books.Fields.Unit26.Transcendence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Fields, Chapter 27: Linearly disjoint extensions

The source's compositum is Mathlib's supremum of two intermediate fields.
Linear disjointness is Mathlib's canonical `IntermediateField.LinearDisjoint`,
whose underlying multiplication map is the tensor-product map in the source.
The normal-extension decomposition uses the relative separable closure and the
fixed field of the full automorphism group.  The source's tensor-product
equality is represented by the canonical multiplication map and its induced
algebra equivalence.
-/

namespace Formalization.Books.Fields.Unit27

noncomputable section

open scoped TensorProduct

/-! ## The compositum and linear disjointness -/

/- `K ⊔ L` is the canonical compositum of two subextensions in an ambient
   field.  The following definitional identity exposes its source-facing
   generated-field description. -/
theorem compositum_eq_adjoin_union
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) :
    K ⊔ L = IntermediateField.adjoin k ((K : Set Ω) ∪ (L : Set Ω)) := by
  rfl

/- The lattice universal property is exactly the source's "smallest
   subfield" clause. -/
theorem compositum_is_smallest
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L M : IntermediateField k Ω) :
    K ⊔ L ≤ M ↔ K ≤ M ∧ L ≤ M := by
  exact sup_le_iff

/- The other two generated-field descriptions in the source use the field
   generated over one intermediate field by the other.  The fields are
   compared through their underlying subsets of the common ambient field. -/
theorem compositum_eq_adjoin_over_left
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) :
    ∀ x : Ω,
      x ∈ K ⊔ L ↔ x ∈ IntermediateField.adjoin L (K : Set Ω) := by
  sorry

theorem compositum_eq_adjoin_over_right
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) :
    ∀ x : Ω,
      x ∈ K ⊔ L ↔ x ∈ IntermediateField.adjoin K (L : Set Ω) := by
  sorry

/- Mathlib's definition is source-faithful: for intermediate fields in the
   same ambient field, `K.LinearDisjoint L` is the injectivity of the natural
   multiplication map from the tensor product. -/
theorem linear_disjoint_iff_tensor_product_multiplication_injective
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) :
    K.LinearDisjoint L ↔
      Function.Injective (K.toSubalgebra.mulMap L.toSubalgebra) := by
  rw [IntermediateField.linearDisjoint_iff',
    Subalgebra.linearDisjoint_iff_injective]

@[simp]
theorem tensor_product_multiplication_map_tmul
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) (x : K) (y : L) :
    K.toSubalgebra.mulMap L.toSubalgebra (x ⊗ₜ[k] y) = (x : Ω) * (y : Ω) := by
  rfl

/-! ## The embedding-dependence example -/

def realEighthRoot : ℝ := (2 : ℝ) ^ (1 / 8 : ℝ)

def realTwelfthRoot : ℝ := (2 : ℝ) ^ (1 / 12 : ℝ)

def realTwentyFourthRoot : ℝ := (2 : ℝ) ^ (1 / 24 : ℝ)

def rotatedEighthRoot : ℂ :=
  (realEighthRoot : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8)

abbrev realEighthRootField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({realEighthRoot} : Set ℝ)

abbrev realTwelfthRootField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({realTwelfthRoot} : Set ℝ)

abbrev realTwentyFourthRootField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({realTwentyFourthRoot} : Set ℝ)

abbrev realRadicalCompositum : IntermediateField ℚ ℝ :=
  realEighthRootField ⊔ realTwelfthRootField

abbrev complexEighthRootField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({rotatedEighthRoot} : Set ℂ)

abbrev complexTwelfthRootField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({(realTwelfthRoot : ℂ)} : Set ℂ)

abbrev complexRadicalCompositum : IntermediateField ℚ ℂ :=
  complexEighthRootField ⊔ complexTwelfthRootField

/- The first embedding choice in the source gives the real compositum and its
   degree. -/
theorem real_radical_compositum_description :
    realRadicalCompositum = realTwentyFourthRootField := by
  sorry

theorem real_radical_compositum_degree :
    Module.finrank ℚ realRadicalCompositum = 24 := by
  sorry

/- The second embedding choice maps the eighth-root generator to the rotated
   root.  These declarations record the source's two precise conclusions. -/
theorem complex_radical_compositum_contains_imaginary_unit :
    Complex.I ∈ complexRadicalCompositum := by
  sorry

theorem complex_radical_compositum_degree :
    Module.finrank ℚ complexRadicalCompositum = 48 := by
  sorry

theorem real_and_complex_radical_composita_not_isomorphic :
    ¬ Nonempty (realRadicalCompositum ≃+* complexRadicalCompositum) := by
  sorry

/-! ## Normal extensions and their separable/inseparable parts -/

/- These are source-facing names for Mathlib's canonical constructions, not
   parallel definitions: the separable part is `separableClosure`, and the
   inseparable part is the fixed field of all `F`-automorphisms of `E`. -/
noncomputable abbrev normalSeparablePart
    (F E : Type*) [Field F] [Field E] [Algebra F E] : IntermediateField F E :=
  separableClosure F E

noncomputable abbrev normalInseparablePart
    (F E : Type*) [Field F] [Field E] [Algebra F E] : IntermediateField F E :=
  IntermediateField.fixedField (⊤ : Subgroup Gal(E / F))

/- The map is the canonical tensor-product multiplication map into the
   ambient field. -/
noncomputable def normalExtensionTensorProductMap
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    (normalSeparablePart F E ⊗[F] normalInseparablePart F E) →ₐ[F] E :=
  Algebra.TensorProduct.productMap
    (normalSeparablePart F E).val (normalInseparablePart F E).val

@[simp]
theorem normalExtensionTensorProductMap_tmul
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : normalSeparablePart F E) (y : normalInseparablePart F E) :
    normalExtensionTensorProductMap (F := F) (E := E) (x ⊗ₜ[F] y) =
      (x : E) * (y : E) := by
  rfl

/- The source's tensor-product equality is corrected to the natural
   `F`-algebra equivalence induced by this map. -/
theorem normal_extension_tensor_product_map_bijective
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    Function.Bijective (normalExtensionTensorProductMap (F := F) (E := E)) := by
  sorry

noncomputable def normalExtensionTensorProductAlgEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    (normalSeparablePart F E ⊗[F] normalInseparablePart F E) ≃ₐ[F] E :=
  AlgEquiv.ofBijective
    (normalExtensionTensorProductMap (F := F) (E := E))
    (normal_extension_tensor_product_map_bijective (F := F) (E := E))

/- This packages the source lemma with the canonical choices of the two
   subextensions. -/
theorem normal_extension_separable_inseparable_decomposition
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    ∃ E_sep E_insep : IntermediateField F E,
      E_sep = normalSeparablePart F E ∧
        E_insep = normalInseparablePart F E ∧
        IsGalois F E_sep ∧
        IsPurelyInseparable E_sep E ∧
        IsPurelyInseparable F E_insep ∧
        IsGalois E_insep E ∧
        Nonempty (E_sep ⊗[F] E_insep ≃ₐ[F] E) := by
  sorry

end

end Formalization.Books.Fields.Unit27
