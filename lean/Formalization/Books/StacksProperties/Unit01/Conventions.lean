import Formalization.Books.StacksProperties.Unit01.Introduction
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Sites.Over

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

structure PointData where
  raw : Type u
  fieldValued : raw → Prop
  allFieldValued : ∀ p, fieldValued p
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
  representableByAlgebraicSpace : Prop
  representableByScheme : Prop

abbrev RawPoint (X : AlgebraicStack S) := X.points.raw
abbrev StackPoint (X : AlgebraicStack S) := X.points.Points

structure FieldValuedMorphism {S : Scheme.{u}}
    (X : AlgebraicStack S) where
  field : Type u
  fieldStructure : Field field
  point : RawPoint X
  fieldValued : X.points.fieldValued point
  flat : Prop
  locallyOfFiniteType : Prop
  locallyOfFinitePresentation : Prop
  quasiCompact : Prop

def IsSurjectiveFieldValuedMorphism {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : FieldValuedMorphism X) : Prop :=
  ∀ x : StackPoint X, x = Quotient.mk X.points.setoid p.point

def stackPointOfFieldValuedMorphism {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : FieldValuedMorphism X) : StackPoint X :=
  Quotient.mk X.points.setoid p.point

def IsReduced (X : AlgebraicStack S) : Prop := X.reduced

def IsLocallyNoetherian (X : AlgebraicStack S) : Prop := X.locallyNoetherian

def IsRegular (X : AlgebraicStack S) : Prop := X.regular

def IsEmpty (X : AlgebraicStack S) : Prop :=
  ∀ _x : StackPoint X, False

def IsRepresentableByAlgebraicSpace (X : AlgebraicStack S) : Prop :=
  X.representableByAlgebraicSpace

def IsRepresentableByScheme (X : AlgebraicStack S) : Prop :=
  X.representableByScheme

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

def inducedPointMap {S : Scheme.{u}} {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) : StackPoint X → StackPoint Y :=
  Quotient.map f.rawMap f.map_respects

def StackTwoMorphism {X Y : AlgebraicStack S}
    (f g : StackMorphism X Y) : Prop :=
  ∀ p, Y.points.equivalent (f.rawMap p) (g.rawMap p)

/-! An equivalence of the explicit stack interface used in this chapter. -/

structure StackEquivalence {S : Scheme.{u}}
    (X Y : AlgebraicStack S) where
  forward : StackMorphism X Y
  inverse : StackMorphism Y X
  leftInverse : StackTwoMorphism
    (StackMorphism.comp forward inverse) (StackMorphism.id X)
  rightInverse : StackTwoMorphism
    (StackMorphism.comp inverse forward) (StackMorphism.id Y)

def IsStackEquivalence {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  ∃ e : StackEquivalence X Y, e.forward = f

/-! A chosen fibre product at the level of the field-valued point interface. -/

def fibreProductPointData {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) : PointData.{u} where
  raw := {p : RawPoint X × RawPoint Z //
    Y.points.equivalent (f.rawMap p.1) (g.rawMap p.2)}
  fieldValued := fun p => X.points.fieldValued p.1.1 ∧ Z.points.fieldValued p.1.2
  allFieldValued := fun p =>
    ⟨X.points.allFieldValued p.1.1, Z.points.allFieldValued p.1.2⟩
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

def fibreProductMap {S : Scheme.{u}}
    {X X' Y : AlgebraicStack S} (i : StackMorphism X X')
    (f : StackMorphism X' Y) :
    StackMorphism
      (fibreProduct (StackMorphism.comp i f) (StackMorphism.comp i f))
      (fibreProduct f f) where
  rawMap := fun p =>
    ⟨⟨i.rawMap p.1.1, i.rawMap p.1.2⟩,
      by simpa [StackMorphism.comp] using p.2⟩
  map_respects := by
    intro p q h
    exact ⟨i.map_respects _ _ h.1, i.map_respects _ _ h.2⟩

def stackProductPointData {S : Scheme.{u}}
    (X Y : AlgebraicStack S) : PointData.{u} where
  raw := RawPoint X × RawPoint Y
  fieldValued := fun p =>
    X.points.fieldValued p.1 ∧ Y.points.fieldValued p.2
  allFieldValued := fun p =>
    ⟨X.points.allFieldValued p.1, Y.points.allFieldValued p.2⟩
  equivalent := fun p q =>
    X.points.equivalent p.1 q.1 ∧ Y.points.equivalent p.2 q.2
  isEquivalence := by
    constructor
    · intro p
      exact ⟨X.points.isEquivalence.refl _, Y.points.isEquivalence.refl _⟩
    · intro p q h
      exact ⟨X.points.isEquivalence.symm h.1,
        Y.points.isEquivalence.symm h.2⟩
    · intro p q r hpq hqr
      exact ⟨X.points.isEquivalence.trans hpq.1 hqr.1,
        Y.points.isEquivalence.trans hpq.2 hqr.2⟩

def stackProduct {S : Scheme.{u}}
    (X Y : AlgebraicStack S) : AlgebraicStack S where
  points := stackProductPointData X Y
  reduced := X.reduced ∧ Y.reduced
  locallyNoetherian := X.locallyNoetherian ∧ Y.locallyNoetherian
  regular := X.regular ∧ Y.regular
  quasiCompact := X.quasiCompact ∧ Y.quasiCompact
  finiteTypeOverBase := X.finiteTypeOverBase ∧ Y.finiteTypeOverBase
  representableByAlgebraicSpace :=
    X.representableByAlgebraicSpace ∧ Y.representableByAlgebraicSpace
  representableByScheme := X.representableByScheme ∧ Y.representableByScheme

def stackProductMorphism {S : Scheme.{u}}
    {X₁ Y₁ X₂ Y₂ : AlgebraicStack S}
    (f : StackMorphism X₁ X₂) (g : StackMorphism Y₁ Y₂) :
    StackMorphism (stackProduct X₁ Y₁) (stackProduct X₂ Y₂) where
  rawMap := fun p => ⟨f.rawMap p.1, g.rawMap p.2⟩
  map_respects := by
    intro p q h
    exact ⟨f.map_respects _ _ h.1, g.map_respects _ _ h.2⟩

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
  compatible : ∀ p : source.left,
    inducedPointMap f (sourcePoint p) = w.map (projection.left p)
  cartesian : Function.Bijective
    (fun p : source.left =>
      (⟨(sourcePoint p, projection.left p), compatible p⟩ :
        {q : StackPoint X × W.left //
          inducedPointMap f q.1 = w.map q.2}))

def RepresentableByAlgebraicSpaces {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
    Nonempty (BaseChangeData f W w)

def IsEmptySpace {S : Scheme.{u}} (W : AlgebraicSpace S) : Prop :=
  ∀ _x : W.left, False

/-! Presentations and charts used by later sections. -/

structure StackChart {S : Scheme.{u}} (X : AlgebraicStack S) where
  source : Scheme.{u}
  map : source → StackPoint X
  surjective : Function.Surjective map
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
  relationIsEquivalence :
    Equivalence (fun u v =>
      ∃ r : relation, sourceMap r = u ∧ targetMap r = v)
  mapRelation :
    ∀ u v,
      (∃ r : relation, sourceMap r = u ∧ targetMap r = v) ↔
        toStackChart.map u = toStackChart.map v

structure LocalPropertyOfGerms where
  property : (X : Scheme.{u}) → X → Prop
  smoothLocal : Prop

end Formalization.Books.StacksProperties.Unit01
