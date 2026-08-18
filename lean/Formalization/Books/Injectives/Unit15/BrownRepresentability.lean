import Formalization.Books.Injectives.Unit14.GabrielPopescu
import Formalization.Books.Derived.Unit38.BrownRepresentability

/-!
# Injectives, Chapter 15: Brown representability and Grothendieck abelian categories

The source's contravariant cohomological functors are functors out of the
opposite derived category.  Their preservation of direct sums as products is
the canonical preservation of discrete limits, and representability is stated
through the preadditive Yoneda functor.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite

universe u v u' v'

namespace Formalization.Books.Injectives.Unit15

section BrownRepresentability

variable {C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{max u v} C] [HasDerivedCategory.{u} C]

/-!
`H : D(𝒜)ᵒᵖ ⥤ Ab` is the source's contravariant cohomological functor.
Mathlib's `Functor.IsHomological` on the opposite derived category is the
canonical cohomological condition.
-/
abbrev ContravariantCohomologicalFunctor : Type _ :=
  (DerivedCategory C)ᵒᵖ ⥤ AddCommGrpCat

/-!
The source's phrase “transforms direct sums into products” is expressed by
preservation of limits of every discrete diagram in the opposite category.
-/
def PreservesDirectSumsAsProducts
    (H : ContravariantCohomologicalFunctor (C := C)) : Prop :=
  ∀ I : Type (max u v), PreservesLimitsOfShape (Discrete I) H

/-- Brown representability for the derived category of a Grothendieck
abelian category. -/
theorem brown_representability
    (H : ContravariantCohomologicalFunctor (C := C))
    [H.IsHomological]
    (hH : PreservesDirectSumsAsProducts H) :
    ∃ X : DerivedCategory C, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  sorry

/-!
The target of the adjoint statement is an arbitrary triangulated category.
The canonical `HasExactRightAdjoint` package records the adjunction, shift
compatibility, and triangulated exactness of the right adjoint.
-/
theorem exact_right_adjoint
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : DerivedCategory C ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type (max u v),
      PreservesColimitsOfShape (Discrete I) F) :
    Formalization.Books.Derived.Unit38.HasExactRightAdjoint F := by
  sorry

end BrownRepresentability

end Formalization.Books.Injectives.Unit15
