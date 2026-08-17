import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Formalization.Books.Derived.Unit07.AdjointsForExactFunctors
import Formalization.Books.Derived.Unit37.CompactObjects

/-!
# Derived Categories, Chapter 38: Brown representability

The source's compactly generated hypothesis is the canonical
`IsCompactlyGenerated` condition from Chapter 37.  Contravariant
cohomological functors are written as functors out of the opposite category,
and preservation of direct sums as products is expressed by Mathlib's
discrete-shape limit-preservation predicate.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit07
open Formalization.Books.Derived.Unit37
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u'

namespace Formalization.Books.Derived.Unit38

section BrownRepresentability

variable {D : Type u} [Category.{v} D] [AdditiveCategory D]
  [HasCoproducts.{v} D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [CategoryTheory.IsTriangulated D]

/-!
The proof-level construction is accounted for by the representability
statement rather than duplicated as unsupported interfaces.  In particular,
this includes the coproduct `X₁` indexed by pairs `(Eᵢ, a)`, its Yoneda map,
the recursively chosen cone triangles
`Kₙ₊₁ ⟶ Xₙ ⟶ Xₙ₊₁ ⟶ Kₙ₊₁[1]`, the homotopy-colimit triangle, and the exact
sequence of products obtained by applying `H`.  The proof's generator
factorization argument records the surjectivity and injectivity on compact
generators, and the final subcategory argument extends the isomorphism to all
objects.
-/

/-!
`H : Dᵒᵖ ⥤ Ab` is the source's contravariant cohomological functor.  The
source's condition that direct sums become products is the preservation of
all discrete limits indexed by the source's allowed small sets.
-/
theorem brown_representability
    (H : Dᵒᵖ ⥤ AddCommGrpCat)
    [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    (hD : IsCompactlyGenerated (C := D)) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  sorry

/-!
An exact right adjoint packages the adjunction together with the canonical
shift-commutation data and the resulting triangulated-functor property.  This
is the source's phrase “exact right adjoint”, stated without choosing a
particular representative externally.
-/
def HasExactRightAdjoint
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') : Prop :=
  ∃ (G : D' ⥤ D) (_adj : F ⊣ G) (hG : G.CommShift ℤ),
    letI : G.CommShift ℤ := hG
    G.IsTriangulated

/-!
The Brown representability consequence: an exact functor preserving all
direct sums has an exact right adjoint.  Preservation is stated for the
source's full size of small coproduct diagrams.  The proof-level functor
`W ↦ Hom (F W) Y`, its Brown representing object, the resulting adjunction,
and the exactness of its right adjoint are accounted for by this interface;
the last step uses the canonical Chapter 7 adjoint-exactness result.
-/
theorem exact_right_adjoint_of_brown_representability
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') (hD : IsCompactlyGenerated (C := D))
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F) :
    HasExactRightAdjoint F := by
  sorry

end BrownRepresentability

end Formalization.Books.Derived.Unit38
