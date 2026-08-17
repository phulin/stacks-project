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
  intro hf hg
  simpa [IsSurjective, inducedPointMap_comp, Function.Surjective] using
    Function.Surjective.comp hg hf

theorem base_change_surjective {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) :
    IsSurjective f → IsSurjective (fibreProductSnd f g) := by
  intro hf z
  induction z using Quotient.inductionOn with
  | _ q =>
    rcases hf (inducedPointMap g (Quotient.mk Z.points.setoid q)) with ⟨x, hx⟩
    induction x using Quotient.inductionOn with
    | _ p =>
      refine ⟨Quotient.mk _ ⟨⟨p, q⟩, Quotient.exact hx⟩, ?_⟩
      rfl

theorem descent_surjective {S : Scheme.{u}}
    {X Y Y' : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y' Y) :
    IsSurjective g →
      IsSurjective (fibreProductFst g f) →
        IsSurjective f := by
  intro hg hpb y
  rcases hg y with ⟨y', hy'⟩
  rcases hpb y' with ⟨p, hp⟩
  induction p using Quotient.inductionOn with
  | _ p =>
    refine ⟨Quotient.mk X.points.setoid p.1.2, ?_⟩
    calc
      inducedPointMap f (Quotient.mk X.points.setoid p.1.2) =
          inducedPointMap g (Quotient.mk Y'.points.setoid p.1.1) :=
        (Quotient.sound p.2).symm
      _ = inducedPointMap g y' := congrArg (inducedPointMap g) hp
      _ = y := hy'

theorem surjective_permanence {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) :
    IsSurjective (StackMorphism.comp f g) → IsSurjective g := by
  intro hcomp y
  rcases hcomp y with ⟨x, hx⟩
  refine ⟨inducedPointMap f x, ?_⟩
  simpa [IsSurjective, inducedPointMap_comp, Function.comp_def] using hx

end Formalization.Books.StacksProperties.Unit01
