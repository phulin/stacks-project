import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SeparableDegree

/-!
# Fields, Chapter 15: Normal extensions

The source's “splits completely” predicate is Mathlib's canonical
`Polynomial.Splits`.  Normality is likewise Mathlib's `Normal` class, which
packages algebraicity with splitting of every minimal polynomial.  A
`K`-algebra embedding is an `AlgHom`, an automorphism group is `Gal(L / K)`,
and the source's separable degree is `Field.finSepDegree`.
-/

namespace Formalization.Books.Fields.Unit15

noncomputable section

open Polynomial

/-! ## Splitting and normality -/

/- `Polynomial.Splits` is the existing definition of splitting into a scalar
   and monic linear factors.  The source's scalar is the leading coefficient
   in this factorization, and the definition itself needs no parallel
   predicate.  The theorem below records the nonconstant case from the
   displayed factorization, using a finite multiset for the list of roots. -/
theorem polynomial_splits_completely_iff
    {F : Type*} [Field F] {P : F[X]} (hP : P.natDegree ≠ 0) :
    P.Splits ↔
      ∃ (c : F) (roots : Multiset F),
        c ≠ 0 ∧ 0 < roots.card ∧
          P = C c * (roots.map (X - C ·)).prod := by
  sorry

/- `Normal F E` is the existing definition of an algebraic normal extension;
   its `normal_iff` theorem already exposes the pointwise minimal-polynomial
   splitting condition. -/

/-! ## Basic properties -/

/- The source assumes an algebraic tower.  `Normal F K` already supplies the
   needed algebraicity of the top extension, and Mathlib's tower theorem
   derives the algebraicity over the middle field. -/
theorem normal_goes_up
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [Normal F K] :
    Normal E K :=
  Normal.tower_top_of_normal F E K

/- The source's index type is required to be nonempty: for an empty family,
   the intersection is the ambient algebraic extension, which need not be
   normal. -/
theorem normal_intersection
    {F M ι : Type*} [Field F] [Field M] [Algebra F M]
    [Algebra.IsAlgebraic F M] [Nonempty ι]
    (E : ι → IntermediateField F M)
    [hE : ∀ i, Normal F (E i)] :
    Normal F (⨅ i, E i : IntermediateField F M) := by
  infer_instance

/- The separable subextension in the source is Mathlib's canonical
   `separableClosure`. -/
theorem separable_closure_normal
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E] :
    Normal F (separableClosure F E) := by
  sorry

/-! ## Embeddings and generators -/

/- The source's algebraic closure is represented by `IsAlgClosure`, and its
   extension maps by `AlgHom`.  `fieldRange` is the bundled image
   intermediate field. -/
theorem normal_iff_algebraic_closure_embedding_ranges
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [IsAlgClosure F L]
    [Algebra.IsAlgebraic F E] :
    Normal F E ↔
      ∀ σ σ' : E →ₐ[F] L, σ.fieldRange = σ'.fieldRange := by
  sorry

/- The source's indexed family of generators is represented by a set. -/
theorem normal_of_generated_by_splits
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] (S : Set E)
    (hS : IntermediateField.adjoin F S = ⊤)
    (hsplits : ∀ α ∈ S,
      ((minpoly F α).map (algebraMap F E)).Splits) :
    Normal F E := by
  sorry

/-! ## Lifting maps and automorphisms -/

/- Part (1) of the source's lifting lemma: the restriction is an
   automorphism of the normal middle field, expressed by the commutative
   equation from the displayed diagram. -/
theorem automorphism_restricts_to_normal_subextension
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [Algebra.IsAlgebraic M L] [Normal K M]
    (τ : L ≃ₐ[K] L) :
    ∃ σ : M ≃ₐ[K] M,
      ∀ x : M, algebraMap M L (σ x) = τ (algebraMap M L x) := by
  sorry

/- Part (2) is already supplied by the canonical `AlgHom.liftNormal` together
   with `AlgHom.normal_bijective`.
   The source-facing theorem below states its extension property without
   introducing a parallel wrapper definition. -/
theorem normal_extension_lifts_algebra_map
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [Algebra.IsAlgebraic K M] [Algebra.IsAlgebraic M L] [Normal K L]
    (σ : M →ₐ[K] L) :
    ∃ τ : L ≃ₐ[K] L,
      ∀ x : M, τ (algebraMap M L x) = σ x := by
  sorry

/- The source's `Aut(E/F)` is Mathlib's existing `Gal(E / F)` notation for
   the group `E ≃ₐ[F] E`; no new automorphism-group definition is needed. -/

/-! ## Automorphism counts -/

/- `Field.finSepDegree` is Mathlib's natural-number version of the source's
   separable degree. -/
theorem finite_extension_automorphism_card_le_finSepDegree
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    Nat.card (Gal(E / F)) ≤ Field.finSepDegree F E := by
  sorry

theorem finite_extension_automorphism_card_eq_finSepDegree_iff_normal
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    Nat.card (Gal(E / F)) = Field.finSepDegree F E ↔ Normal F E := by
  sorry

/-! ## Embeddings into an extension -/

/- For a normal algebraic extension, all embeddings into a fixed target form
   either the empty set or one orbit under the source automorphism group. -/
theorem normal_embeddings_empty_or_differ_by_automorphism
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Normal K L] :
    (¬ Nonempty (L →ₐ[K] E)) ∨
      ∃ τ : L →ₐ[K] E,
        ∀ φ : L →ₐ[K] E,
          ∃ σ : Gal(L / K), φ = τ.comp σ.toAlgHom := by
  sorry

end

end Formalization.Books.Fields.Unit15
