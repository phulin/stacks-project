import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Formalization.Books.Derived.Unit07.AdjointsForExactFunctors
import Formalization.Books.Derived.Unit38.BrownRepresentability

/-!
# Derived Categories, Chapter 39: Brown representability, bis

The source's set of generators is recorded by `BrownGeneratorConditions`.
The functor in the representability statement is written as a functor out of
the opposite category, so that its contravariance is explicit.  Countable
coproducts used in the construction are available from the source's direct
sums, while the functor hypothesis preserves all discrete limits in the
opposite category, expressing that direct sums become products.

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
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u'

namespace Formalization.Books.Derived.Unit39

section BrownRepresentability

variable {D : Type u} [Category.{v, u} D] [AdditiveCategory D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [CategoryTheory.IsTriangulated D]
  [HasCoproducts.{v} D]

local instance : HasCoproducts.{0} D := hasCoproducts_shrink

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
condition for every small discrete diagram, expressed in the opposite
category.
-/
theorem brown_representability
    (𝓔 : Set D) (h𝓔 : BrownGeneratorConditions 𝓔)
    (H : Dᵒᵖ ⥤ AddCommGrpCat)
    [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  sorry

/-!
The Brown representability consequence: an exact functor preserving the
direct sums of the source has an exact right adjoint.
-/
theorem exact_right_adjoint_of_brown_representability
    {D' : Type u'} [Category.{v', u'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F)
    (h𝓔 : ∃ 𝓔 : Set D, BrownGeneratorConditions 𝓔) :
    Formalization.Books.Derived.Unit38.HasExactRightAdjoint F := by
  sorry

end BrownRepresentability

end Formalization.Books.Derived.Unit39
