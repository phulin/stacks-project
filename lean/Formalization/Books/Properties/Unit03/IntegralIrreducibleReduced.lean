import Mathlib.AlgebraicGeometry.Properties

/-!
# Properties of Schemes, Chapter 3: Integral, irreducible, and reduced schemes

The source section is `books/properties.tex:186--293`.  Scheme integrality and
reducedness reuse Mathlib's canonical `AlgebraicGeometry.IsIntegral` and
`AlgebraicGeometry.IsReduced` properties.  The source's definition of
integrality is exactly the canonical `AlgebraicGeometry.IsIntegral` property;
the characterization results use the canonical topological and ring
properties.
-/

namespace Formalization.Books.Properties.Unit03

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/-! ## Definition `definition-integral` -/

/- The source's definition is represented directly by Mathlib's
`AlgebraicGeometry.IsIntegral`, whose API uses nonemptiness and integral-domain
sections on nonempty affine opens. -/

/-! ## Lemma `lemma-characterize-reduced` -/

/-- The four equivalent reducedness criteria in the source. -/
theorem lemma_characterize_reduced (X : Scheme.{u}) :
    List.TFAE [
      AlgebraicGeometry.IsReduced X,
      ∃ (I : Type v) (U : I → X.Opens),
        TopologicalSpace.IsOpenCover U ∧
          ∀ i, IsAffineOpen (U i) ∧ _root_.IsReduced Γ(X, U i),
      ∀ U : X.Opens, IsAffineOpen U → _root_.IsReduced Γ(X, U),
      ∀ U : X.Opens, _root_.IsReduced Γ(X, U)] := by
  sorry

/-! ## Lemma `lemma-characterize-irreducible` -/

/-- The three equivalent irreducibility criteria in the source.  Irreducible
open subsets are represented by Mathlib's canonical `IsIrreducible` predicate
on subsets, and the scheme-wide condition by `IrreducibleSpace`. -/
theorem lemma_characterize_irreducible (X : Scheme.{u}) :
    List.TFAE [
      IrreducibleSpace X,
      ∃ (I : Type v) (U : I → X.Opens),
        Nonempty I ∧
          TopologicalSpace.IsOpenCover U ∧
          (∀ i, IsIrreducible (U i : Set X)) ∧
          (∀ i j, (U i : Set X) ∩ (U j : Set X) ≠ ∅),
      Nonempty X ∧
        ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          IsIrreducible (U : Set X)] := by
  sorry

/-! ## Lemma `lemma-characterize-integral` -/

/-- A scheme is integral exactly when it is reduced and irreducible. -/
theorem lemma_characterize_integral (X : Scheme.{u}) :
    AlgebraicGeometry.IsIntegral X ↔
      AlgebraicGeometry.IsReduced X ∧ IrreducibleSpace X := by
  simpa [and_comm] using
    (AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced X)

/-! ## The connected locally-integral non-integral example -/

/- The source defers the construction to the Examples book.  The existence
claim is recorded here without a forward import of that construction. -/
theorem exists_connected_affine_locally_integral_not_integral :
    ∃ X : Scheme.{u},
      ConnectedSpace X ∧ IsAffine X ∧
        (∀ x : X, IsDomain (X.presheaf.stalk x)) ∧
          ¬ AlgebraicGeometry.IsIntegral X := by
  sorry

end Formalization.Books.Properties.Unit03
