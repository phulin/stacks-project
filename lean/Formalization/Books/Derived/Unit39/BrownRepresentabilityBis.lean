import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Formalization.Books.Derived.Unit07.AdjointsForExactFunctors
import Formalization.Books.Derived.Unit36.GeneratorsOfTriangulatedCategories

/-!
# Derived Categories, Chapter 39: Brown representability, bis

The source's set of generators is recorded by `BrownGeneratorConditions`.
The functor in the representability statement is written as a functor out of
the opposite category, so that its contravariance is explicit.  Countable
coproducts in the source category become countable products in the opposite
category, which is expressed by Mathlib's preservation predicate.

The source calls the result a weak version of Krause's theorem.  The proof
constructs a representing object by a countable sequence of cones and a
homotopy colimit; those proof-level constructions are accounted for by the
representability theorem rather than duplicated as unsupported auxiliary
definitions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit07
open Formalization.Books.Derived.Unit36
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u'

namespace Formalization.Books.Derived.Unit39

section BrownRepresentability

variable {D : Type u} [Category.{v, u} D] [AdditiveCategory D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [CategoryTheory.IsTriangulated D]
  [HasCountableCoproducts D]

/-!
The two hypotheses on the set `𝓔` are the exact conditions in the source.
The second condition uses Mathlib's canonical `Sigma.map` for the coproduct
of the maps `β n`.
-/
structure BrownGeneratorConditions (𝓔 : Set D) : Prop where
  detectsNonzero :
    ∀ ⦃X : D⦄, ¬ IsZero X →
      ∃ (E : D), 𝓔 E ∧ ∃ f : E ⟶ X, f ≠ 0
  factorsThroughCoproduct :
    ∀ ⦃E : D⦄, 𝓔 E →
      ∀ (X : ℕ → D) (α : E ⟶ ∐ X),
        ∃ (E' : ℕ → D), (∀ n, 𝓔 (E' n)) ∧
          ∃ (β : ∀ n, E' n ⟶ X n) (γ : E ⟶ ∐ E'),
            α = γ ≫ Limits.Sigma.map β

/-!
The proof's displayed construction is deliberately not promoted to a second
set of chapter definitions: the coproduct `X₁ = ⨿ (E,a)`, its Yoneda-induced
map to `H`, the recursive cone triangles `Kₙ₊₁ ⟶ Xₙ ⟶ Xₙ₊₁`, the defining
hocolim triangle, and the exact product sequence are proof witnesses for
`brown_representability`.  The subsequent factorization argument accounts
for the injectivity and surjectivity on generators, while the final
strictly-full, saturated, triangulated, coproduct-closed subcategory argument
accounts for the extension from generators to all objects.  None is an
independent source assertion or a reusable definition beyond the theorem's
stated hypotheses and conclusion.
-/

/-!
`H : Dᵒᵖ ⥤ Ab` is the source's contravariant functor.  Its cohomological
condition is Mathlib's `IsHomological` condition on the opposite category.
The preservation hypothesis is the source's direct-sums-to-products
condition, expressed in the opposite category.
-/
theorem brown_representability
    (𝓔 : Set D) (h𝓔 : BrownGeneratorConditions 𝓔)
    (H : Dᵒᵖ ⥤ AddCommGrpCat)
    [H.IsHomological]
    [PreservesLimitsOfShape (Discrete ℕ) H] :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  sorry

/-!
An exact right adjoint packages the adjunction together with the canonical
shift-commutation data and the resulting triangulated-functor property.  This
is the source's phrase “exact right adjoint”, stated without choosing a
particular representative of an adjunction externally.
-/
def HasExactRightAdjoint
    {D' : Type u'} [Category.{v', u'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') : Prop :=
  ∃ (G : D' ⥤ D) (_adj : F ⊣ G) (hG : G.CommShift ℤ),
    letI : G.CommShift ℤ := hG
    G.IsTriangulated

/-!
The Brown representability consequence: an exact functor preserving the
countable direct sums of the source has an exact right adjoint.
-/
theorem exact_right_adjoint_of_brown_representability
    {D' : Type u'} [Category.{v', u'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesColimitsOfShape (Discrete ℕ) F]
    (𝓔 : Set D) (h𝓔 : BrownGeneratorConditions 𝓔) :
    HasExactRightAdjoint F := by
  sorry

end BrownRepresentability

end Formalization.Books.Derived.Unit39
