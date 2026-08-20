import Mathlib.AlgebraicGeometry.Properties

/-!
# Properties of Schemes, Chapter 3: Integral, irreducible, and reduced schemes

The source section is `books/properties.tex:186--293`.  Scheme integrality and
reducedness reuse Mathlib's canonical `AlgebraicGeometry.IsIntegral` and
`AlgebraicGeometry.IsReduced` properties.  The affine-open formulation of the
definition of integrality is retained as a source-facing interface, while the
three characterization results use the canonical topological and ring
properties.
-/

namespace Formalization.Books.Properties.Unit03

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/-! ## Definition `definition-integral` -/

/-- The source's affine-open formulation of integrality.  The ring of
sections `Γ(X, U)` is the coordinate ring of an affine open `U`. -/
def IsIntegralOnAffineOpens (X : Scheme.{u}) : Prop :=
  Nonempty X ∧
    ∀ (U : X.Opens), IsAffineOpen U → Nonempty U → IsDomain Γ(X, U)

/-- Mathlib's canonical scheme-integrality property is equivalent to the
source's affine-open formulation. -/
theorem isIntegral_iff_isIntegralOnAffineOpens (X : Scheme.{u}) :
    AlgebraicGeometry.IsIntegral X ↔ IsIntegralOnAffineOpens X := by
  sorry

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

/-- Every local ring of a scheme is an integral domain. -/
def AllLocalRingsAreDomains (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x)

/-- The source records the existence of a connected affine scheme with domain
local rings that is not integral; its construction is deferred to the
Examples book. -/
theorem exists_connected_affine_locally_integral_not_integral :
    ∃ X : Scheme.{u},
      ConnectedSpace X ∧ IsAffine X ∧
        AllLocalRingsAreDomains X ∧ ¬ AlgebraicGeometry.IsIntegral X := by
  sorry

end Formalization.Books.Properties.Unit03
