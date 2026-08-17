import Formalization.Books.StacksProperties.Unit01.Introduction
import Formalization.Books.Stacks.Unit01.Groupoids
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Properties of Algebraic Stacks, Chapter 1: common interfaces

Mathlib has the scheme and fibred-category APIs used by this chapter, but it
does not provide a native object for an algebraic stack.  The declarations
below keep the stack-theoretic data needed by the source explicit.  An
algebraic space over `S` is represented by an object of `Over S`, following
the representable model used by the earlier formalizations.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace Formalization.Books.StacksProperties.Unit01

/-! ## The fixed relative site and the stack point interface -/

abbrev RelativeSite (S : Scheme.{u}) := CategoryTheory.Over S

abbrev RelativeFppfTopology (S : Scheme.{u}) :
    GrothendieckTopology (RelativeSite S) :=
  Scheme.fppfTopology.over S

structure Convention where
  base : Scheme.{u}

structure FieldPointComparison (α : Type u) (p q : α) where
  extension : Type u
  extensionField : Field extension
  leftExtension : Prop
  rightExtension : Prop
  twoCommutative : Prop

structure PointData where
  raw : Type u
  fieldValued : raw → Prop
  equivalent : raw → raw → Prop
  isEquivalence : Equivalence equivalent

namespace PointData

def setoid (P : PointData.{u}) : Setoid P.raw where
  r := P.equivalent
  iseqv := P.isEquivalence

abbrev Points (P : PointData.{u}) := Quotient P.setoid

end PointData

structure AlgebraicStack (S : Scheme.{u}) where
  points : PointData.{u}
  reduced : Prop
  locallyNoetherian : Prop
  regular : Prop
  quasiCompact : Prop
  finiteTypeOverBase : Prop
  empty : Prop
  representableByAlgebraicSpace : Prop
  representableByScheme : Prop

abbrev RawPoint (X : AlgebraicStack S) := X.points.raw
abbrev StackPoint (X : AlgebraicStack S) := X.points.Points

def IsReduced (X : AlgebraicStack S) : Prop := X.reduced

def IsLocallyNoetherian (X : AlgebraicStack S) : Prop := X.locallyNoetherian

def IsRegular (X : AlgebraicStack S) : Prop := X.regular

def IsEmpty (X : AlgebraicStack S) : Prop := X.empty

structure StackMorphism {S : Scheme.{u}}
    (X Y : AlgebraicStack S) where
  rawMap : RawPoint X → RawPoint Y
  map_respects : ∀ p q, X.points.equivalent p q →
    Y.points.equivalent (rawMap p) (rawMap q)

namespace StackMorphism

def id (X : AlgebraicStack S) : StackMorphism X X where
  rawMap := fun p => p
  map_respects := by
    intro p q h
    exact h

def comp {X Y Z : AlgebraicStack S}
    (f : StackMorphism X Y) (g : StackMorphism Y Z) : StackMorphism X Z where
  rawMap := g.rawMap ∘ f.rawMap
  map_respects := by
    intro p q h
    exact g.map_respects _ _ (f.map_respects _ _ h)

end StackMorphism

def StackTwoMorphism {X Y : AlgebraicStack S}
    (f g : StackMorphism X Y) : Prop :=
  ∀ p, Y.points.equivalent (f.rawMap p) (g.rawMap p)

/-! A chosen fibre product at the level of the field-valued point interface. -/

def fibreProductPointData {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) : PointData.{u} where
  raw := {p : RawPoint X × RawPoint Z //
    Y.points.equivalent (f.rawMap p.1) (g.rawMap p.2)}
  fieldValued := fun p => X.points.fieldValued p.1.1 ∧ Z.points.fieldValued p.1.2
  equivalent := fun p q =>
    X.points.equivalent p.1.1 q.1.1 ∧ Z.points.equivalent p.1.2 q.1.2
  isEquivalence := by
    constructor
    · intro p
      exact ⟨X.points.isEquivalence.refl _, Z.points.isEquivalence.refl _⟩
    · intro p q h
      exact ⟨X.points.isEquivalence.symm h.1,
        Z.points.isEquivalence.symm h.2⟩
    · intro p q r hpq hqr
      exact ⟨X.points.isEquivalence.trans hpq.1 hqr.1,
        Z.points.isEquivalence.trans hpq.2 hqr.2⟩

def fibreProduct {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) : AlgebraicStack S where
  points := fibreProductPointData f g
  reduced := X.reduced ∧ Z.reduced
  locallyNoetherian := X.locallyNoetherian ∧ Z.locallyNoetherian
  regular := X.regular ∧ Z.regular
  quasiCompact := X.quasiCompact ∧ Z.quasiCompact
  finiteTypeOverBase := X.finiteTypeOverBase ∧ Z.finiteTypeOverBase
  empty := X.empty ∨ Z.empty
  representableByAlgebraicSpace :=
    X.representableByAlgebraicSpace ∧ Z.representableByAlgebraicSpace
  representableByScheme := X.representableByScheme ∧ Z.representableByScheme

def fibreProductFst {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) : StackMorphism (fibreProduct f g) X where
  rawMap := fun p => p.1.1
  map_respects := by
    intro p q h
    exact h.1

def fibreProductSnd {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) : StackMorphism (fibreProduct f g) Z where
  rawMap := fun p => p.1.2
  map_respects := by
    intro p q h
    exact h.2

/-! ## Algebraic spaces, morphism properties, and test base changes -/

abbrev AlgebraicSpace (S : Scheme.{u}) := RelativeSite S

abbrev SpaceMorphism {S : Scheme.{u}} (X Y : AlgebraicSpace S) := X ⟶ Y

abbrev SpaceMorphismProperty (S : Scheme.{u}) :=
  MorphismProperty (AlgebraicSpace S)

def underlyingSpaceMorphism {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y) :
    X.left ⟶ Y.left := f.left

structure SpaceToStackMorphism {S : Scheme.{u}}
    (W : AlgebraicSpace S) (X : AlgebraicStack S) where
  map : W.left → StackPoint X
  surjective : Prop
  flat : Prop
  locallyOfFinitePresentation : Prop
  smooth : Prop
  etale : Prop
  syntomic : Prop

structure BaseChangeData {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y) where
  source : AlgebraicSpace S
  projection : SpaceMorphism source W
  sourcePoint : source.left → StackPoint X
  cartesian : Prop
  compatible : Prop

def RepresentableByAlgebraicSpaces {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
    Nonempty (BaseChangeData f W w)

structure RelativeSpaceProperty (S : Scheme.{u}) where
  property : SpaceMorphismProperty S
  fppfLocalOnTarget : Prop
  stableUnderArbitraryBaseChange : Prop
  localOnSource : Prop
  preservedUnderComposition : Prop

def HasRelativeProperty {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) : Prop :=
  RepresentableByAlgebraicSpaces f ∧
    ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
      (bc : BaseChangeData f W w), P.property bc.projection

def HasRelativePropertyOnSpace {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) : Prop :=
  ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
    (bc : BaseChangeData f W w), P.property bc.projection

def IsEmptySpace {S : Scheme.{u}} (_ : AlgebraicSpace S) : Prop := False

/-! Presentations and charts used by later sections. -/

structure StackChart {S : Scheme.{u}} (X : AlgebraicStack S) where
  source : Scheme.{u}
  map : source → StackPoint X
  surjective : Prop
  flat : Prop
  locallyOfFinitePresentation : Prop
  smooth : Prop
  affineSource : Prop
  quasiCompactSchemeSource : Prop
  quasiCompactAlgebraicSpaceSource : Prop

structure StackPresentation {S : Scheme.{u}} (X : AlgebraicStack S)
    extends StackChart X where
  relation : Scheme.{u}
  sourceMap : relation ⟶ source
  targetMap : relation ⟶ source
  identityMap : source ⟶ relation
  groupoidAxioms : Prop

structure LocalPropertyOfGerms where
  property : Scheme → (X : Scheme) → X → Prop
  smoothLocal : Prop

end Formalization.Books.StacksProperties.Unit01
