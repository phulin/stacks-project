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
    (g : StackMorphism Z Y) (hg : IsMonomorphism g)
    (hrepresentable :
      RepresentableByAlgebraicSpaces (fibreProductSnd g f))
    (hbase : ∀ (W : AlgebraicSpace S)
      (w : SpaceToStackMorphism W X)
      (bc : BaseChangeData (fibreProductSnd g f) W w),
      ∃ (w' : SpaceToStackMorphism W Y)
        (bc' : BaseChangeData g W w'),
        SpaceMorphismMonomorphism bc'.projection →
          SpaceMorphismMonomorphism bc.projection) :
    IsMonomorphism (fibreProductSnd g f) := by
  unfold IsMonomorphism RelativeMonomorphismProperty HasRelativeProperty at *
  refine ⟨hrepresentable, ?_⟩
  intro W w bc
  rcases hbase W w bc with ⟨w', bc', hproperty⟩
  exact hproperty (hg.2 W w' bc')

theorem comp_monomorphism {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (_hf : IsMonomorphism f)
    (hg : IsMonomorphism g)
    (hrepresentable :
      RepresentableByAlgebraicSpaces (StackMorphism.comp f g))
    (hbase : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Z)
      (bc : BaseChangeData (StackMorphism.comp f g) W w),
      ∃ bc' : BaseChangeData g W w,
        SpaceMorphismMonomorphism bc'.projection →
          SpaceMorphismMonomorphism bc.projection) :
    IsMonomorphism (StackMorphism.comp f g) := by
  unfold IsMonomorphism RelativeMonomorphismProperty HasRelativeProperty at *
  refine ⟨hrepresentable, ?_⟩
  intro W w bc
  rcases hbase W w bc with ⟨bc', hproperty⟩
  exact hproperty (hg.2 W w bc')

theorem monomorphism_iff_fully_faithful {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hbaseToPoints :
      (∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
        (bc : BaseChangeData f W w),
        SpaceMorphismMonomorphism bc.projection) →
      ∀ p q : RawPoint X,
        X.points.equivalent p q ↔
          Y.points.equivalent (f.rawMap p) (f.rawMap q))
    (hpointsToBase :
      (∀ p q : RawPoint X,
        X.points.equivalent p q ↔
          Y.points.equivalent (f.rawMap p) (f.rawMap q)) →
      ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
        (bc : BaseChangeData f W w),
        SpaceMorphismMonomorphism bc.projection) :
    IsMonomorphism f ↔ StackFullyFaithful f := by
  unfold IsMonomorphism RelativeMonomorphismProperty HasRelativeProperty
    StackFullyFaithful
  constructor
  · rintro ⟨hrepresentable, hproperty⟩
    exact ⟨hrepresentable, hbaseToPoints hproperty⟩
  · rintro ⟨hrepresentable, hpoints⟩
    exact ⟨hrepresentable, hpointsToBase hpoints⟩

theorem monomorphism_iff_diagonal_equivalence {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hbaseToDiagonal :
      (∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
        (bc : BaseChangeData f W w),
        SpaceMorphismMonomorphism bc.projection) →
      IsStackEquivalence (stackDiagonal f))
    (hdiagonalToBase :
      IsStackEquivalence (stackDiagonal f) →
      ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
        (bc : BaseChangeData f W w),
        SpaceMorphismMonomorphism bc.projection) :
    IsMonomorphism f ↔ DiagonalIsEquivalence f := by
  unfold IsMonomorphism RelativeMonomorphismProperty HasRelativeProperty
    DiagonalIsEquivalence
  constructor
  · rintro ⟨hrepresentable, hproperty⟩
    exact ⟨hrepresentable, hbaseToDiagonal hproperty⟩
  · rintro ⟨hrepresentable, hdiagonal⟩
    exact ⟨hrepresentable, hdiagonalToBase hdiagonal⟩

theorem monomorphism_iff_local_test {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hcover : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      Function.Surjective w.map ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
        Nonempty (BaseChangeData f W w))
    (hlocal : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
      (bc : BaseChangeData f W w),
      Function.Surjective w.map → w.flat →
        w.locallyOfFinitePresentation →
        SpaceMorphismMonomorphism bc.projection →
        ∀ (W' : AlgebraicSpace S) (w' : SpaceToStackMorphism W' Y)
          (bc' : BaseChangeData f W' w'),
          SpaceMorphismMonomorphism bc'.projection) :
    IsMonomorphism f ↔ HasLocalMonomorphismTest f := by
  unfold IsMonomorphism RelativeMonomorphismProperty HasRelativeProperty
    HasLocalMonomorphismTest
  constructor
  · rintro ⟨hrepresentable, hproperty⟩
    refine ⟨hrepresentable, ?_⟩
    rcases hcover with ⟨W, w, hsurjective, hflat, hlfp, hbc⟩
    rcases hbc with ⟨bc⟩
    exact ⟨W, w, hsurjective, hflat, hlfp, ⟨bc, hproperty W w bc⟩⟩
  · rintro ⟨hrepresentable, ⟨W, w, hsurjective, hflat, hlfp, ⟨bc, hproperty⟩⟩⟩
    refine ⟨hrepresentable, ?_⟩
    intro W' w' bc'
    exact hlocal W w bc hsurjective hflat hlfp hproperty W' w' bc'

theorem monomorphism_injective_on_points {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (_hf : IsMonomorphism f)
    (hcancel : ∀ p q : RawPoint X,
      inducedPointMap f (Quotient.mk X.points.setoid p) =
          inducedPointMap f (Quotient.mk X.points.setoid q) →
        X.points.equivalent p q) :
    Function.Injective (inducedPointMap f) := by
  intro p
  refine Quotient.inductionOn p ?_
  intro p q
  refine Quotient.inductionOn q ?_
  intro q h
  exact Quotient.sound (hcancel p q h)

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
    (g : StackMorphism X' Y) (_hi : IsMonomorphism i)
    (hcommutes :
      StackTwoMorphism
        (StackMorphism.comp (stackDiagonal (StackMorphism.comp i g))
          (fibreProductMap i g))
        (StackMorphism.comp i (stackDiagonal g)))
    (huniversal : ∀ (T : AlgebraicStack S)
      (u : StackMorphism T
        (fibreProduct (StackMorphism.comp i g)
          (StackMorphism.comp i g)))
      (v : StackMorphism T X'),
      StackTwoMorphism
        (StackMorphism.comp u (fibreProductMap i g))
        (StackMorphism.comp v (stackDiagonal g)) →
      ∃ h : StackMorphism T X,
        StackTwoMorphism
          (StackMorphism.comp h (stackDiagonal (StackMorphism.comp i g))) u ∧
        StackTwoMorphism (StackMorphism.comp h i) v ∧
        ∀ h' : StackMorphism T X,
          StackTwoMorphism
            (StackMorphism.comp h' (stackDiagonal (StackMorphism.comp i g))) u →
          StackTwoMorphism (StackMorphism.comp h' i) v →
          StackTwoMorphism h h') :
    StackPullbackSquare (stackDiagonal (StackMorphism.comp i g))
      i (fibreProductMap i g) (stackDiagonal g) := by
  refine ⟨hcommutes, ?_⟩
  exact ⟨hcommutes, huniversal⟩

end Formalization.Books.StacksProperties.Unit01
