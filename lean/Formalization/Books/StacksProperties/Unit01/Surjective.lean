import Formalization.Books.StacksProperties.Unit01.Points

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 5

Surjectivity is recorded on the topological point maps introduced in the
preceding section.  The base-change notation uses the fibre products from the
chapter's conventions.
-/

noncomputable section

universe u

open AlgebraicGeometry

namespace Formalization.Books.StacksProperties.Unit01

def IsSurjective {S : Scheme.{u}} {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) : Prop :=
  Function.Surjective (inducedPointMap f)

theorem comp_surjective {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) :
    IsSurjective f → IsSurjective g →
      IsSurjective (StackMorphism.comp f g) := by
  sorry

theorem base_change_surjective {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) :
    IsSurjective f → IsSurjective (fibreProductSnd f g) := by
  sorry

theorem descent_surjective {S : Scheme.{u}}
    {X Y Y' : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y' Y) :
    IsSurjective g →
      IsSurjective (fibreProductFst g f) →
        IsSurjective f := by
  sorry

theorem surjective_permanence {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) :
    IsSurjective (StackMorphism.comp f g) → IsSurjective g := by
  sorry

end Formalization.Books.StacksProperties.Unit01
