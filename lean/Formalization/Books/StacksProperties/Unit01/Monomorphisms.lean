import Formalization.Books.StacksProperties.Unit01.TypesProperties
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 8

The chapter defines monomorphisms by representability by algebraic spaces and
the ordinary monomorphism property after every test base change.  The
diagonal and pullback interfaces below make the corresponding source
statements available without introducing a second stack formalism.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

def SpaceMorphismMonomorphism {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y) : Prop :=
  MorphismProperty.monomorphisms (AlgebraicSpace S) f

def RelativeMonomorphismProperty (S : Scheme.{u}) : RelativeSpaceProperty S where
  property := fun _ _ f => SpaceMorphismMonomorphism f
  fppfLocalOnTarget := True
  stableUnderArbitraryBaseChange := True
  localOnSource := fun _ => True
  preservedUnderComposition := True

def IsMonomorphism {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  HasRelativeProperty (RelativeMonomorphismProperty S) f

def StackFullyFaithful {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  RepresentableByAlgebraicSpaces f ∧
    ∀ p q : RawPoint X,
      X.points.equivalent p q ↔
        Y.points.equivalent (f.rawMap p) (f.rawMap q)

def stackDiagonal {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) :
    StackMorphism X (fibreProduct f f) where
  rawMap := fun p =>
    ⟨⟨p, p⟩, Y.points.isEquivalence.refl (f.rawMap p)⟩
  map_respects := by
    intro p q h
    exact ⟨h, h⟩

def DiagonalIsEquivalence {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  RepresentableByAlgebraicSpaces f ∧ IsStackEquivalence (stackDiagonal f)

def HasLocalMonomorphismTest {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  RepresentableByAlgebraicSpaces f ∧
    ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      Function.Surjective w.map ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
        ∃ bc : BaseChangeData f W w, SpaceMorphismMonomorphism bc.projection

theorem base_change_monomorphism {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hg : IsMonomorphism g) :
    IsMonomorphism (fibreProductSnd g f) := by
  sorry

theorem comp_monomorphism {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (hf : IsMonomorphism f)
    (hg : IsMonomorphism g) :
    IsMonomorphism (StackMorphism.comp f g) := by
  sorry

theorem monomorphism_iff_fully_faithful {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) :
    IsMonomorphism f ↔ StackFullyFaithful f := by
  sorry

theorem monomorphism_iff_diagonal_equivalence {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) :
    IsMonomorphism f ↔ DiagonalIsEquivalence f := by
  sorry

theorem monomorphism_iff_local_test {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) :
    IsMonomorphism f ↔ HasLocalMonomorphismTest f := by
  sorry

theorem monomorphism_injective_on_points {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : IsMonomorphism f) :
    Function.Injective (inducedPointMap f) := by
  sorry

def IsStackPullbackSquare {S : Scheme.{u}}
    {A B C D : AlgebraicStack S}
    (top : StackMorphism A B) (left : StackMorphism A C)
    (right : StackMorphism B D) (bottom : StackMorphism C D) : Prop :=
  StackTwoMorphism (StackMorphism.comp top right)
      (StackMorphism.comp left bottom) ∧
    ∀ (T : AlgebraicStack S) (u : StackMorphism T B)
      (v : StackMorphism T C),
      StackTwoMorphism (StackMorphism.comp u right)
        (StackMorphism.comp v bottom) →
      ∃ h : StackMorphism T A,
        StackTwoMorphism (StackMorphism.comp h top) u ∧
          StackTwoMorphism (StackMorphism.comp h left) v ∧
            ∀ h' : StackMorphism T A,
              StackTwoMorphism (StackMorphism.comp h' top) u →
              StackTwoMorphism (StackMorphism.comp h' left) v →
              StackTwoMorphism h h'

structure StackPullbackSquare {S : Scheme.{u}}
    {A B C D : AlgebraicStack S}
    (top : StackMorphism A B) (left : StackMorphism A C)
    (right : StackMorphism B D) (bottom : StackMorphism C D) : Prop where
  commutes : StackTwoMorphism
    (StackMorphism.comp top right) (StackMorphism.comp left bottom)
  isPullback : IsStackPullbackSquare top left right bottom

theorem monomorphism_diagonal_pullback {S : Scheme.{u}}
    {X X' Y : AlgebraicStack S} (i : StackMorphism X X')
    (g : StackMorphism X' Y) (hi : IsMonomorphism i) :
    StackPullbackSquare (stackDiagonal (StackMorphism.comp i g))
      i (fibreProductMap i g) (stackDiagonal g) := by
  sorry

end Formalization.Books.StacksProperties.Unit01
