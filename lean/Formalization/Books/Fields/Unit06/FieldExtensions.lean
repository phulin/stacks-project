import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Data.Rat.Encodable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Fields, Chapter 6: Field extensions

The source uses inclusions of fields informally.  This file uses Mathlib's
canonical `Algebra` interface for an extension, `AlgHom` for a morphism of
extensions, and `IntermediateField.adjoin` for `k(S)`.  Finite towers are
recorded as adjacent algebra structures; when a three-field compatibility is
needed, Mathlib's `IsScalarTower` is the canonical interface.  The category
of field extensions is the full subcategory of `AlgCat k` on objects whose
underlying ring satisfies Mathlib's proposition-valued `IsField` predicate.
-/

namespace Formalization.Books.Fields.Unit06

open CategoryTheory
open scoped TensorProduct

universe u v w

/-! ## Maps of fields and the category of extensions -/

/- Mathlib proves the source lemma in the stronger simple-ring interface. -/
/-- A ring homomorphism from a field to a nontrivial semiring is injective. -/
theorem field_ring_hom_injective {F R : Type*} [Field F] [NonAssocSemiring R]
    [Nontrivial R] (φ : F →+* R) : Function.Injective φ := by
  exact RingHom.injective φ

/- A field extension is represented by a field together with an `Algebra`
   instance.  The following object property makes the source's category
   precise while retaining Mathlib's canonical category of algebra maps. -/
def fieldExtensionProperty (k : Type u) [Field k] :
    ObjectProperty (AlgCat.{v} k) :=
  fun A => IsField A

/-- The category of field extensions of a fixed field. -/
abbrev FieldExtensionCat (k : Type u) [Field k] :=
  (fieldExtensionProperty.{u, v} k).FullSubcategory

/-- The object of `FieldExtensionCat k` associated to a field `E/k`. -/
def fieldExtensionObject (k : Type u) (E : Type v) [Field k] [Field E]
    [Algebra k E] : FieldExtensionCat.{u, v} k :=
  ⟨AlgCat.of k E, Field.toIsField E⟩

/-- The scalar map of a field extension is injective. -/
theorem field_extension_algebraMap_injective {k : Type u} {E : Type v} [Field k]
    [Field E] [Algebra k E] : Function.Injective (algebraMap k E) := by
  exact field_ring_hom_injective (algebraMap k E)

/- The source's `Mor_k(E, E')` is Mathlib's `AlgHom`. -/
abbrev fieldExtensionHom (k : Type u) (E : Type v) (E' : Type w) [Field k] [Field E]
    [Field E'] [Algebra k E] [Algebra k E'] := E →ₐ[k] E'

/-- A morphism of extensions commutes with the two scalar maps. -/
theorem field_extension_hom_commutes {k : Type u} {E : Type v} {E' : Type w} [Field k]
    [Field E] [Field E'] [Algebra k E] [Algebra k E']
    (f : fieldExtensionHom k E E') (x : k) :
    f (algebraMap k E x) = algebraMap k E' x := by
  exact f.commutes x

/- Any field homomorphism supplies the algebra structure used in the source's
   “slight abuse of language”. -/
@[instance_reducible]
def fieldHomToAlgebra {F E : Type*} [Field F] [Field E] (φ : F →+* E) :
    Algebra F E :=
  φ.toAlgebra

/-- A ring homomorphism of fields is injective and determines a compatible
field-algebra structure on its target. -/
theorem field_hom_gives_extension {F E : Type*} [Field F] [Field E]
    (φ : F →+* E) :
    Function.Injective φ ∧
      ∃ A : Algebra F E, @algebraMap F E _ _ A = φ := by
  refine ⟨field_ring_hom_injective φ, ⟨fieldHomToAlgebra φ, ?_⟩⟩
  exact RingHom.algebraMap_toAlgebra φ

/-- A field homomorphism can be viewed as an object of the extension category. -/
def fieldHomExtensionObject {F : Type u} {E : Type v} [Field F] [Field E] (φ : F →+* E) :
    FieldExtensionCat.{u, v} F := by
  letI : Algebra F E := fieldHomToAlgebra φ
  exact fieldExtensionObject F E

/- The category instance on `FieldExtensionCat` is inherited from the full
   subcategory.  Its morphisms are exactly the underlying `AlgHom`s, so the
   identity, composition, and commutative triangle in the source require no
   parallel category structure here. -/

/- A tower is likewise represented by adjacent `Algebra` instances.  For a
   three-field tower, `IsScalarTower` can additionally record compatibility
   of the two scalar actions. -/
/-- A finite sequence `E₀, ..., Eₙ` with an extension between each adjacent
pair. -/
structure FieldExtensionTower (n : ℕ) (E : Fin (n + 1) → Type u) where
  [fieldInst : ∀ i, Field (E i)]
  [algebraInst : ∀ i : Fin n, Algebra (E i.castSucc) (E i.succ)]

/-! ## Standard examples -/

/- `AdjoinRoot P` is Mathlib's canonical presentation of `k[t]/(P)`. -/
/-- The quotient by an irreducible polynomial over a field is a field. -/
theorem adjoinRoot_isField_of_irreducible {k : Type u} [Field k]
    {P : Polynomial k} (hP : Irreducible P) : IsField (AdjoinRoot P) := by
  let _ : Fact (Irreducible P) := ⟨hP⟩
  exact Field.toIsField _

/-- The irreducible-polynomial quotient is an object of the extension category. -/
noncomputable def irreduciblePolynomialExtension {k : Type u} [Field k]
    {P : Polynomial k} (hP : Irreducible P) :
    FieldExtensionCat.{u, u} k := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  exact fieldExtensionObject k (AdjoinRoot P)

/- Mathlib and the preceding chapter do not package a Riemann-surface
   function field.  Thus `C_X` is the supplied model of `C(X)`, recording the
   field/algebra data needed for the source's extension statement. -/
/-- The supplied meromorphic function field model `C_X` is an extension of `ℂ`. -/
noncomputable def meromorphicFunctionFieldExtension
    (_X : Type u) (C_X : Type v) [Field C_X] [Algebra ℂ C_X] :
    FieldExtensionCat.{0, v} ℂ :=
  fieldExtensionObject ℂ C_X

/-- The supplied meromorphic-function field model has an injective map of
constant functions from `ℂ`. -/
theorem meromorphic_function_field_is_extension
    (_X : Type u) (C_X : Type v) [Field C_X] [Algebra ℂ C_X] :
    Function.Injective (algebraMap ℂ C_X) :=
  field_extension_algebraMap_injective

/-! ## Generated subextensions -/

/- The source's `k(S)` is Mathlib's `IntermediateField.adjoin k S`; its
   intersection/minimality construction and finite-operation description are
   already definitionally and theorem-wise present in that API. -/

/-- The generated intermediate field contains every generator. -/
theorem subset_generated_field {k : Type u} {E : Type v} [Field k] [Field E]
    [Algebra k E] (S : Set E) : S ⊆ IntermediateField.adjoin k S := by
  exact IntermediateField.subset_adjoin k S

/-- The generated intermediate field contains the base field. -/
theorem base_field_maps_into_generated_field {k : Type u} {E : Type v} [Field k]
    [Field E] [Algebra k E] (S : Set E) (x : k) :
    algebraMap k E x ∈ IntermediateField.adjoin k S := by
  exact IntermediateField.algebraMap_mem _ x

/-- `IntermediateField.adjoin` is the smallest intermediate field containing
the chosen set. -/
theorem generated_field_is_smallest {k : Type u} {E : Type v} [Field k]
    [Field E] [Algebra k E] (S : Set E) (T : IntermediateField k E) :
    IntermediateField.adjoin k S ≤ T ↔ S ⊆ T := by
  exact IntermediateField.adjoin_le_iff

/-- Membership in `k(S)` has the source's finite rational-expression form. -/
theorem generated_field_members_are_finite_expressions {k : Type u} {E : Type v}
    [Field k] [Field E] [Algebra k E] (S : Set E) (x : E) :
    x ∈ IntermediateField.adjoin k S ↔
      ∃ r s : MvPolynomial S k,
        x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s := by
  exact IntermediateField.mem_adjoin_iff (F := k) (S := S) x

/-- The finite-generator definition of a field extension agrees with
Mathlib's `Algebra.EssFiniteType` predicate. -/
theorem finitely_generated_extension_iff {k : Type u} {E : Type v} [Field k]
    [Field E] [Algebra k E] :
    (∃ S : Set E, S.Finite ∧ IntermediateField.adjoin k S = ⊤) ↔
      Algebra.EssFiniteType k E := by
  exact
    (IntermediateField.fg_def (F := k) (E := E)
      (S := (⊤ : IntermediateField k E))).symm.trans
      (IntermediateField.fg_top_iff (F := k) (E := E))

/-! ## The examples attached to generation -/

/-- The complex numbers are generated by `I` over the reals. -/
theorem complex_generated_by_I :
    IntermediateField.adjoin ℝ ({Complex.I} : Set ℂ) = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hz]
  apply add_mem
  · exact IntermediateField.algebraMap_mem _ _
  · apply mul_mem
    · exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin _ _ (by simp)

/-- The complex numbers have no countable set of generators over `ℚ`. -/
theorem complex_not_countably_generated_over_rationals :
    ¬ ∃ S : Set ℂ, S.Countable ∧
      IntermediateField.adjoin ℚ S = (⊤ : IntermediateField ℚ ℂ) := by
  intro h
  obtain ⟨S, hS, htop⟩ := h
  have hA : Countable (IntermediateField.adjoin ℚ S) := by
    apply Cardinal.mk_le_aleph0_iff.mp
    calc
      Cardinal.mk (IntermediateField.adjoin ℚ S) ≤
          Cardinal.mk ℚ ⊔ Cardinal.mk S ⊔ Cardinal.aleph0 :=
        IntermediateField.cardinalMk_adjoin_le ℚ S
      _ ≤ Cardinal.aleph0 := by
        exact sup_le (sup_le Cardinal.mk_le_aleph0 hS.le_aleph0) le_rfl
  rw [htop] at hA
  exact not_countable_complex (Set.countable_univ_iff.mpr
    (@Countable.of_equiv ℂ (⊤ : IntermediateField ℚ ℂ) hA
      (IntermediateField.topEquiv (F := ℚ) (E := ℂ))))

/-! ## Simple extensions -/

/-- A simple field extension is either rational or a quotient by an
irreducible polynomial. -/
theorem simple_extension_classification {k : Type u} {E : Type v} [Field k]
    [Field E] [Algebra k E] (α : E)
    (hα : IntermediateField.adjoin k ({α} : Set E) = ⊤) :
    Nonempty (E ≃ₐ[k] RatFunc k) ∨
      ∃ P : Polynomial k, Irreducible P ∧
        Nonempty (E ≃ₐ[k] AdjoinRoot P) := by
  by_cases hαalg : IsAlgebraic k α
  · exact Or.inr ⟨minpoly k α, minpoly.irreducible hαalg.isIntegral, ⟨
      ((IntermediateField.adjoinRootEquivAdjoin k hαalg.isIntegral).trans
        ((IntermediateField.equivOfEq hα).trans
          (IntermediateField.topEquiv (F := k) (E := E)))).symm⟩⟩
  · exact Or.inl ⟨
      ((RatFunc.algEquivOfTranscendental α hαalg).trans
        ((IntermediateField.equivOfEq hα).trans
          (IntermediateField.topEquiv (F := k) (E := E)))).symm⟩

/-! ## Common extensions -/

/-- Two field extensions of the same field admit a common field extension. -/
theorem exists_common_field_extension {k : Type u} {E : Type v} {F : Type w}
    [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F] :
    ∃ M : FieldExtensionCat.{u, max v w} k,
      Nonempty (E →ₐ[k] M.obj) ∧ Nonempty (F →ₐ[k] M.obj) := by
  let hnt : Nontrivial (E ⊗[k] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      k E F (field_extension_algebraMap_injective (k := k) (E := E))
        (field_extension_algebraMap_injective (k := k) (E := F))
  let hmax : ∃ I : Ideal (E ⊗[k] F), I.IsMaximal :=
    @Ideal.exists_maximal (E ⊗[k] F) inferInstance hnt
  let I : Ideal (E ⊗[k] F) :=
    Classical.choose hmax
  have hI : I.IsMaximal :=
    Classical.choose_spec hmax
  let hfield : Field ((E ⊗[k] F) ⧸ I) :=
    @Ideal.Quotient.field (E ⊗[k] F) inferInstance I hI
  let M : FieldExtensionCat.{u, max v w} k :=
    @fieldExtensionObject k ((E ⊗[k] F) ⧸ I) inferInstance hfield inferInstance
  refine ⟨M, ?_, ?_⟩
  · change Nonempty (E →ₐ[k] (E ⊗[k] F) ⧸ I)
    exact ⟨(Ideal.Quotient.mkₐ k I).comp
      (Algebra.TensorProduct.includeLeft (R := k) (A := E) (B := F))⟩
  · change Nonempty (F →ₐ[k] (E ⊗[k] F) ⧸ I)
    exact ⟨(Ideal.Quotient.mkₐ k I).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := E) (B := F))⟩

end Formalization.Books.Fields.Unit06
