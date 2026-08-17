import Mathlib.Algebra.Exact.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# Fields, Chapter 21: Galois theory

The source's Galois extensions and Galois groups are Mathlib's canonical
`IsGalois` class and `Gal(E / F)` notation.  Fixed fields, the Galois
correspondence, and restriction maps likewise use Mathlib's existing
`IntermediateField` and `AlgEquiv` interfaces.
-/

namespace Formalization.Books.Fields.Unit21

noncomputable section

/-! ## Galois extensions and Galois groups -/

/- Mathlib's `IsGalois F E` is exactly the source's definition: the extension
   is separable and normal, and hence algebraic.  The source's `Aut(E/F)` and
   `Gal(E/F)` are the same canonical type, `E ≃ₐ[F] E`, exposed by the `Gal`
   notation. -/

/- The source's cardinality notation `[E : F]` is Mathlib's
   `Module.finrank F E`, while the cardinality of the automorphism group is
   `Nat.card (Gal(E / F))`. -/
/-- A finite field extension is Galois exactly when its automorphism group has
    cardinality equal to its degree. -/
theorem finite_galois_iff_card_aut_eq_finrank
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    IsGalois F E ↔ Nat.card (Gal(E / F)) = Module.finrank F E := by
  constructor
  · intro h
    exact @IsGalois.card_aut_eq_finrank F _ E _ _ _ h
  · exact IsGalois.of_card_aut_eq_finrank F E

/- The note that an infinite Galois group carries a natural topological-group
   structure is deferred to the next source section, `Infinite Galois theory`.
   No topology is introduced in this finite-section file. -/

/- `IsGalois.tower_top_of_isGalois` is the canonical tower result used for the
   source's assertion that a Galois extension remains Galois over an
   intermediate field. -/
/-- Galoisness goes up a tower of field extensions. -/
theorem galois_goes_up
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [IsGalois F K] :
    IsGalois E K :=
  IsGalois.tower_top_of_isGalois F E K

/- A normal closure is represented by Mathlib's `IsNormalClosure`.  The
   separable-extension hypothesis is retained from the source; the theorem
   below is the source-facing Galois conclusion for that canonical normal
   closure interface. -/
/-- The normal closure of a finite separable extension is Galois over its base. -/
theorem normal_closure_is_galois
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsNormalClosure K L M] :
    IsGalois K M := by
  sorry

/-! ## Fixed fields -/

/- For a group action on a field, the source's set
   `K^G = {x | ∀ σ, σ x = x}` is Mathlib's `FixedPoints.subfield G K`.
   When the base field is explicit, the corresponding intermediate-field
   interface is `FixedPoints.intermediateField`; for a subgroup of a Galois
   group it is `IntermediateField.fixedField`. -/

/- The source's fixed-field lemma is already implemented by Mathlib's fixed
   points construction.  The final equivalence is the assertion that the
   acting group is the Galois group, expressed by the canonical multiplicative
   equivalence `FixedPoints.toAlgAutMulEquiv`. -/
/-- A finite faithful field action has the acting group as the Galois group of
    its fixed field, with the expected extension degree. -/
theorem galois_over_fixed_field
    {G K : Type*} [Group G] [Field K] [MulSemiringAction G K]
    [Finite G] [FaithfulSMul G K] :
    IsGalois (FixedPoints.subfield G K) K ∧
      Module.finrank (FixedPoints.subfield G K) K = Nat.card G ∧
        Nonempty (G ≃* Gal(K / FixedPoints.subfield G K)) := by
  refine ⟨inferInstance, ?_, ⟨FixedPoints.toAlgAutMulEquiv G K⟩⟩
  calc
    Module.finrank (FixedPoints.subfield G K) K =
        Nat.card (Gal(K / FixedPoints.subfield G K)) :=
      (IsGalois.card_aut_eq_finrank _ _).symm
    _ = Nat.card G := Nat.card_congr (FixedPoints.toAlgAutMulEquiv G K).symm

/-! ## Fundamental theorem of Galois theory -/

/- The source's map from subgroups to subextensions is Mathlib's
   `IntermediateField.fixedField`, and the inverse map is
   `IntermediateField.fixingSubgroup`.  `IntermediateField.fixingSubgroupEquiv`
   identifies that subgroup with the source's `Gal(L/M)`. -/
/-- The finite Galois correspondence, including the fixed base field and the
    normal-subgroup/Galois-subextension criterion. -/
theorem fundamental_theorem_galois_correspondence
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IntermediateField.fixedField (⊤ : Subgroup Gal(L / K)) = ⊥ ∧
      Function.Bijective
        (fun H : Subgroup Gal(L / K) => IntermediateField.fixedField H) ∧
      (∀ H : Subgroup Gal(L / K),
        IntermediateField.fixingSubgroup (IntermediateField.fixedField H) = H) ∧
      (∀ M : IntermediateField K L,
        IntermediateField.fixedField M.fixingSubgroup = M) ∧
      (∀ M : IntermediateField K L,
        Nonempty (M.fixingSubgroup ≃* Gal(L / M))) ∧
      (∀ H : Subgroup Gal(L / K),
        Subgroup.Normal H ↔ IsGalois K (IntermediateField.fixedField H)) ∧
      (∀ M : IntermediateField K L,
        M.fixingSubgroup.Normal ↔ IsGalois K M) := by
  sorry

/-! ## The restriction exact sequence -/

/- The left arrow in the source's sequence is
   `AlgEquiv.restrictScalarsHom K`, and the right arrow is
   `AlgEquiv.restrictNormalHom M`.  `Function.MulExact` is Mathlib's
   multiplicative exactness predicate, so the declaration records exactness,
   injectivity, surjectivity, and finiteness of all three groups. -/
/-- Restriction gives the short exact sequence of finite Galois groups in a
    finite Galois tower. -/
theorem galois_short_exact
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional K M] [FiniteDimensional K L]
    [IsGalois K M] [IsGalois K L] :
    let i : Gal(L / M) →* Gal(L / K) :=
      AlgEquiv.restrictScalarsHom (R := K) (S := M) (A := L)
    let p : Gal(L / K) →* Gal(M / K) :=
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
    Finite (Gal(L / M)) ∧ Finite (Gal(L / K)) ∧ Finite (Gal(M / K)) ∧
      Function.Injective i ∧ Function.MulExact i p ∧ Function.Surjective p := by
  sorry

end

end Formalization.Books.Fields.Unit21
