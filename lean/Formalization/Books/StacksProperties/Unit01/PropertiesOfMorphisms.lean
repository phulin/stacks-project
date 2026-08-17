import Formalization.Books.StacksProperties.Unit01.Conventions

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 3

The section transfers properties of morphisms of algebraic spaces to
representable morphisms of algebraic stacks.  The locality and base-change
conditions are retained as explicit fields of `RelativeSpaceProperty`.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

inductive CoveringTopology
  | etale
  | smooth
  | syntomic
  | fppf
  deriving DecidableEq, Repr

structure RelativeSpaceProperty (S : Scheme.{u}) where
  property : SpaceMorphismProperty S
  fppfLocalOnTarget : Prop
  stableUnderArbitraryBaseChange : Prop
  localOnSource : CoveringTopology → Prop
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

/-! ## The list of standard relative properties -/

inductive StandardPropertyName
  | quasiCompact
  | quasiSeparated
  | universallyClosed
  | universallyOpen
  | universallySubmersive
  | universalHomeomorphism
  | surjective
  | universallyInjective
  | locallyOfFiniteType
  | locallyOfFinitePresentation
  | finiteType
  | finitePresentation
  | flat
  | openImmersion
  | isomorphism
  | affine
  | closedImmersion
  | separated
  | proper
  | quasiAffine
  | integral
  | finite
  | quasiFinite
  | syntomic
  | smooth
  | unramified
  | etale
  | finiteLocallyFree
  | monomorphism
  | immersion
  | locallySeparated
  deriving DecidableEq, Repr

def standardPropertyNames : List StandardPropertyName :=
  [.quasiCompact, .quasiSeparated, .universallyClosed, .universallyOpen,
   .universallySubmersive, .universalHomeomorphism, .surjective,
   .universallyInjective, .locallyOfFiniteType, .locallyOfFinitePresentation,
   .finiteType, .finitePresentation, .flat, .openImmersion, .isomorphism,
   .affine, .closedImmersion, .separated, .proper, .quasiAffine, .integral,
   .finite, .quasiFinite, .syntomic, .smooth, .unramified, .etale,
   .finiteLocallyFree, .monomorphism, .immersion, .locallySeparated]

structure StandardPropertyData (S : Scheme.{u}) where
  property : StandardPropertyName → SpaceMorphismProperty S
  fppfLocalOnTarget : ∀ _n : StandardPropertyName, Prop
  stableUnderArbitraryBaseChange : ∀ _n : StandardPropertyName, Prop
  localOnSource : ∀ _n : StandardPropertyName, CoveringTopology → Prop
  preservedUnderComposition : ∀ _n : StandardPropertyName, Prop

def standardRelativeProperty (D : StandardPropertyData S)
    (n : StandardPropertyName) : RelativeSpaceProperty S where
  property := D.property n
  fppfLocalOnTarget := D.fppfLocalOnTarget n
  stableUnderArbitraryBaseChange := D.stableUnderArbitraryBaseChange n
  localOnSource := D.localOnSource n
  preservedUnderComposition := D.preservedUnderComposition n

def RelativePropertyImplies {S : Scheme.{u}}
    (P Q : RelativeSpaceProperty S) : Prop :=
  ∀ {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y),
    P.property f → Q.property f

/-! The general permanence assertions stated immediately after the
definition of a relative property. -/

theorem relative_property_base_change {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y Z : AlgebraicStack S}
    (f : StackMorphism X Y) (g : StackMorphism Z Y)
    (hP : P.stableUnderArbitraryBaseChange)
    (hf : HasRelativeProperty P f) :
    HasRelativeProperty P (fibreProductSnd f g) := by
  sorry

theorem relative_property_comp {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y Z : AlgebraicStack S}
    (f : StackMorphism X Y) (g : StackMorphism Y Z)
    (hP : P.preservedUnderComposition)
    (hf : HasRelativeProperty P f) (hg : HasRelativeProperty P g) :
    HasRelativeProperty P (StackMorphism.comp f g) := by
  sorry

theorem relative_property_product {S : Scheme.{u}}
    (P : RelativeSpaceProperty S)
    {X₁ Y₁ X₂ Y₂ : AlgebraicStack S}
    (f : StackMorphism X₁ X₂) (g : StackMorphism Y₁ Y₂)
    (hbase : P.stableUnderArbitraryBaseChange)
    (hcomp : P.preservedUnderComposition)
    (hf : HasRelativeProperty P f) (hg : HasRelativeProperty P g) :
    HasRelativeProperty P (stackProductMorphism f g) := by
  sorry

theorem relative_property_implication {S : Scheme.{u}}
    (P Q : RelativeSpaceProperty S) (hPQ : RelativePropertyImplies P Q)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : HasRelativeProperty P f) :
    HasRelativeProperty Q f := by
  exact ⟨hf.1, fun W w bc => hPQ bc.projection (hf.2 W w bc)⟩

def baseChangeIsAlgebraicSpace {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y) : Prop :=
  Nonempty (BaseChangeData f W w)

theorem check_representable_covering {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
    (hcover : Function.Surjective w.map ∧ w.flat ∧
      w.locallyOfFinitePresentation) :
    RepresentableByAlgebraicSpaces f ↔
      baseChangeIsAlgebraicSpace f W w := by
  sorry

def HasRelativePropertyOnAllSpaces {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) : Prop :=
  HasRelativePropertyOnSpace P f

theorem property_spacelike_tests {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) (hf : RepresentableByAlgebraicSpaces f) :
    HasRelativeProperty P f ↔ HasRelativePropertyOnAllSpaces P f := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hf, h⟩

theorem check_property_covering {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) (W : AlgebraicSpace S)
    (w : SpaceToStackMorphism W Y)
    (hP : P.fppfLocalOnTarget ∧ P.stableUnderArbitraryBaseChange)
    (hcover : Function.Surjective w.map ∧ w.flat ∧
      w.locallyOfFinitePresentation) :
    HasRelativeProperty P f ↔
      (RepresentableByAlgebraicSpaces f ∧
        ∀ (bc : BaseChangeData f W w), P.property bc.projection) := by
  sorry

structure StackCoveringMorphism {S : Scheme.{u}}
    {Z Y : AlgebraicStack S} where
  map : StackMorphism Z Y
  representableByAlgebraicSpaces : RepresentableByAlgebraicSpaces map
  surjective : Function.Surjective (inducedPointMap map)
  flat : Prop
  locallyOfFinitePresentation : Prop

structure StackBaseChangeData {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (z : StackCoveringMorphism (Z := Z) (Y := Y)) where
  target : AlgebraicSpace S
  source : AlgebraicSpace S
  projection : SpaceMorphism source target
  cartesian : Prop

def HasRelativePropertyAfterStackBaseChange {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y Z : AlgebraicStack S}
    (f : StackMorphism X Y)
    (z : StackCoveringMorphism (Z := Z) (Y := Y)) : Prop :=
  ∀ (bc : StackBaseChangeData f z), P.property bc.projection

theorem check_property_weak_covering {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y Z : AlgebraicStack S}
    (f : StackMorphism X Y)
    (z : StackCoveringMorphism (Z := Z) (Y := Y))
    (hP : P.fppfLocalOnTarget ∧ P.stableUnderArbitraryBaseChange)
    (hz : RepresentableByAlgebraicSpaces z.map ∧
      Function.Surjective (inducedPointMap z.map) ∧ z.flat ∧
      z.locallyOfFinitePresentation) :
    HasRelativeProperty P f ↔ HasRelativePropertyAfterStackBaseChange P f z := by
  sorry

structure PrecompositionCoverData {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) where
  surjective : Function.Surjective (inducedPointMap f)
  etale : Prop
  smooth : Prop
  syntomic : Prop
  flat : Prop
  locallyOfFinitePresentation : Prop

def CoveringKindCondition {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} {f : StackMorphism X Y}
    {g : StackMorphism Y Z} (τ : CoveringTopology)
    (c : PrecompositionCoverData f g) : Prop :=
  match τ with
  | .etale => c.etale
  | .smooth => c.smooth
  | .syntomic => c.syntomic
  | .fppf => c.flat ∧ c.locallyOfFinitePresentation

def HasPrecompositionCover {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (τ : CoveringTopology) : Prop :=
  RepresentableByAlgebraicSpaces f ∧
    RepresentableByAlgebraicSpaces g ∧
      ∃ c : PrecompositionCoverData f g,
        Function.Surjective (inducedPointMap f) ∧ CoveringKindCondition τ c

def IsLocalOnSourceIn (P : RelativeSpaceProperty S)
    (τ : CoveringTopology) : Prop := P.localOnSource τ

theorem property_after_precomposing {S : Scheme.{u}}
    (P : RelativeSpaceProperty S) {X Y Z : AlgebraicStack S}
    (f : StackMorphism X Y) (g : StackMorphism Y Z)
    (τ : CoveringTopology) (hcover : HasPrecompositionCover f g τ)
    (hcomp : HasRelativeProperty P (StackMorphism.comp f g))
    (hlocal : IsLocalOnSourceIn P τ) :
    HasRelativeProperty P g := by
  sorry

structure PresentationMorphismData {S : Scheme.{u}}
    {X' X : AlgebraicStack S} (g : StackMorphism X' X)
    (p : StackPresentation X) where
  presentation : StackPresentation X'
  projectionOnObjects : Prop
  projectionOnRelations : Prop
  twoCommutative : Prop

theorem representable_in_terms_presentations {S : Scheme.{u}}
    {X' X : AlgebraicStack S} (g : StackMorphism X' X)
    (p : StackPresentation X)
    (hg : RepresentableByAlgebraicSpaces g) :
    Nonempty (PresentationMorphismData g p) := by
  sorry

/-! ## The relative 2-category in the final remark of the section -/

structure RelativeSpaceObject {S : Scheme.{u}}
    (Y : AlgebraicStack S) where
  source : AlgebraicStack S
  map : StackMorphism source Y
  representable : RepresentableByAlgebraicSpaces map

structure RelativeSpaceOneMorphism {S : Scheme.{u}}
    {Y : AlgebraicStack S} (F G : RelativeSpaceObject Y) where
  map : StackMorphism F.source G.source
  beta : StackTwoMorphism F.map (StackMorphism.comp map G.map)

structure RelativeSpaceTwoMorphism {S : Scheme.{u}}
    {Y : AlgebraicStack S} {F G : RelativeSpaceObject Y}
    (a b : RelativeSpaceOneMorphism F G) where
  component : StackTwoMorphism a.map b.map
  compatibility : Prop

def RelativeSpaceOneMorphismEquivalent {S : Scheme.{u}}
    {Y : AlgebraicStack S} {F G : RelativeSpaceObject Y}
    (a b : RelativeSpaceOneMorphism F G) : Prop :=
  Nonempty (RelativeSpaceTwoMorphism a b)

theorem relativeSpaceOneMorphism_equivalence {S : Scheme.{u}}
    {Y : AlgebraicStack S} (F G : RelativeSpaceObject Y) :
    Equivalence (@RelativeSpaceOneMorphismEquivalent S Y F G) := by
  refine { refl := ?_, symm := ?_, trans := ?_ }
  · intro a
    exact ⟨{ component := fun p => G.source.points.isEquivalence.refl _, compatibility := True }⟩
  · intro a b hab
    rcases hab with ⟨h⟩
    exact ⟨{ component := fun p => G.source.points.isEquivalence.symm (h.component p), compatibility := True }⟩
  · intro a b c hab hbc
    rcases hab with ⟨hab⟩
    rcases hbc with ⟨hbc⟩
    exact ⟨{ component := fun p => G.source.points.isEquivalence.trans (hab.component p) (hbc.component p), compatibility := True }⟩

def relativeSpaceMorphismSetoid {S : Scheme.{u}}
    {Y : AlgebraicStack S} (F G : RelativeSpaceObject Y) :
    Setoid (RelativeSpaceOneMorphism F G) where
  r := RelativeSpaceOneMorphismEquivalent
  iseqv := relativeSpaceOneMorphism_equivalence F G

theorem relative_space_over_is_setoid {S : Scheme.{u}}
    {Y : AlgebraicStack S} (F G : RelativeSpaceObject Y) :
    Nonempty (Setoid (RelativeSpaceOneMorphism F G)) := by
  exact ⟨relativeSpaceMorphismSetoid F G⟩

end Formalization.Books.StacksProperties.Unit01
