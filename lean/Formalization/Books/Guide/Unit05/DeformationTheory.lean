import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 1: deformation theory and algebraic stacks

This file records the precise theorem interfaces in the papers summarized in
the first subsection.  The scheme category and the deformation functors are
kept as parameters; this preserves the quantifiers in the source without
pretending that the project already has a native category of algebraic
stacks.
-/

noncomputable section

open CategoryTheory
open Opposite
open Formalization.Books.StacksMorphisms.Unit07

universe u v

namespace Formalization.Books.Guide.Unit05

abbrev ContravariantSetFunctor (C : Type u) [Category.{v} C] :=
  Cᵒᵖ ⥤ Type u

structure FormalDeformationSituation (C : Type u) [Category.{v} C] where
  base : C
  functor : ContravariantSetFunctor C
  locallyOfFinitePresentation : Prop
  baseFiniteTypeOverFieldOrExcellentDvr : Prop
  markedPoint : Prop
  formalObject : C
  formalObjectIsCompletionAtMarkedPoint : Prop
  truncation : ℕ → C
  truncationIsInfinitesimalNeighborhood : ∀ _n : ℕ, Prop
  formalElement : functor.obj (op formalObject)
  restriction : ∀ n, functor.obj (op formalObject) → functor.obj (op (truncation n))
  effective : Prop

def AgreesUpToOrder {C : Type u} [Category.{v} C]
    (D : FormalDeformationSituation C) (n : ℕ)
    (ξ : D.functor.obj (op D.formalObject))
    (η : D.functor.obj (op (D.truncation n))) : Prop :=
  D.restriction n ξ = η

structure FormalApproximationWitness {C : Type u} [Category.{v} C]
    (D : FormalDeformationSituation C) (n : ℕ) where
  neighborhood : C
  map : neighborhood ⟶ D.base
  etale : Prop
  residuallyTrivial : Prop
  markedPointCompatibility : Prop
  element : D.functor.obj (op neighborhood)
  restrictionToTruncation : D.truncation n ⟶ neighborhood
  agrees :
    D.functor.map (op restrictionToTruncation) element =
      D.restriction n D.formalElement

theorem algebraic_approximation_of_effective_formal_deformation
    {C : Type u} [Category.{v} C] (D : FormalDeformationSituation C)
    (n : ℕ) (hn : 0 < n) (heffective : D.effective) :
    Nonempty (FormalApproximationWitness D n) := by
  sorry

structure FormalVersalSituation (C : Type u) [Category.{v} C] where
  deformation : FormalDeformationSituation C
  locallyClosedMarkedPoint : Prop
  completeNoetherianLocalAlgebra : Prop
  residueField : Type u
  finiteResidueFieldExtension : Prop
  residueElement : Prop
  formalVersal : Prop
  universal : Prop

structure AlgebraizationWitness {C : Type u} [Category.{v} C]
    [StackCategory C]
    (D : FormalVersalSituation C) where
  scheme : C
  schemeStructure : IsScheme scheme
  finiteTypeOverBase : Prop
  closedPoint : Prop
  residueFieldIdentified : Prop
  formalCompletion : C
  formalCompletionIso : formalCompletion ≅ D.deformation.formalObject
  element : D.deformation.functor.obj (op scheme)
  elementMatchesFormalDeformation : Prop
  agreesAtEveryOrder : ℕ → Prop

structure AlgebraizationComparison {C : Type u} [Category.{v} C]
    [StackCategory C] {D : FormalVersalSituation C}
    (W₁ W₂ : AlgebraizationWitness D) where
  completionIso : W₁.formalCompletion ≅ W₂.formalCompletion
  identifiesFormalElements : Prop

theorem algebraization_of_effective_formal_versal_deformation
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : FormalVersalSituation C)
    (heffective : D.deformation.effective) (hversal : D.formalVersal) :
    ∃ W : AlgebraizationWitness D, ∀ n : ℕ, W.agreesAtEveryOrder n := by
  sorry

theorem algebraization_unique_for_universal_deformation
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : FormalVersalSituation C)
    (huniversal : D.universal) (W₁ W₂ : AlgebraizationWitness D) :
    Nonempty (AlgebraizationComparison W₁ W₂) := by
  sorry

structure FormalContractionSituation (C : Type u) [Category.{v} C]
    [StackCategory C] where
  source : C
  closedSubspace : C
  closedEmbedding : closedSubspace ⟶ source
  closedSubset : Prop
  formallyLocallyContractible : Prop

structure GlobalContractionWitness {C : Type u} [Category.{v} C]
    [StackCategory C]
    (D : FormalContractionSituation C) where
  target : C
  morphism : D.source ⟶ target
  targetIsAlgebraicSpace : IsAlgebraicSpace target
  contractsClosedSubset : Prop

theorem global_contraction_from_formal_contraction
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : FormalContractionSituation C)
    (hformal : D.formallyLocallyContractible) :
    ∃ W : GlobalContractionWitness D, W.contractsClosedSubset := by
  sorry

structure DeformationObstructionTheory where
  compatibleWithEtaleLocalization : Prop
  compatibleWithCompletion : Prop
  constructible : Prop

structure ArtinCriterionInput (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stack : C
  limitPreserving : Prop
  schlessingerCriterion : Prop
  formalVersalDeformation : Prop
  formalDeformationsEffective : Prop
  obstructionTheory : DeformationObstructionTheory

structure ArtinCriterionConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] (D : ArtinCriterionInput C) where
  completeLocalRing : Prop
  effectiveFormalVersal : Prop
  scheme : C
  schemeStructure : IsScheme scheme
  finiteType : Prop
  markedPoint : Prop
  formallyVersalMap : scheme ⟶ D.stack
  formallyVersalAtMarkedPoint : Prop
  smoothAfterShrinking : Prop

theorem artin_criterion
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ArtinCriterionInput C) :
    ∃ W : ArtinCriterionConclusion D, W.smoothAfterShrinking := by
  sorry

structure FppfPresentation {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  source : C
  map : source ⟶ X
  sourceIsScheme : IsScheme source
  isFppfPresentation : IsFppfMorphism map

structure SmoothPresentation {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  source : C
  map : source ⟶ X
  sourceIsScheme : IsScheme source
  isSmooth : IsSmoothMorphism map

theorem smooth_presentation_of_fppf_presentation
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (P : FppfPresentation X) :
    ∃ Q : SmoothPresentation X, IsSmoothMorphism Q.map := by
  sorry

structure FlatSeparatedFinitelyPresentedGroupScheme (C : Type u)
    [Category.{v} C] [StackCategory C] (S : C) where
  carrier : Type u
  [group : Group carrier]
  overBase : Prop
  flat : Prop
  separated : Prop
  finitelyPresented : Prop

attribute [instance] FlatSeparatedFinitelyPresentedGroupScheme.group

structure QuotientStackByGroupData {C : Type u} [Category.{v} C]
    [StackCategory C] (X S : C) where
  groupScheme : FlatSeparatedFinitelyPresentedGroupScheme C S
  quotient : C
  quotientMap : X ⟶ quotient
  quotientIsArtinStack : IsArtinStack quotient
  action : groupScheme.carrier → (X ⟶ X)
  one_action : action 1 = 𝟙 X
  mul_action : ∀ g h,
    action (g * h) = action h ≫ action g
  presents : Prop

theorem fppf_presentation_gives_quotients_by_flat_groups
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (P : FppfPresentation X) :
    ∃ (S : C) (D : QuotientStackByGroupData X S), D.presents := by
  sorry

structure PopescuSituation where
  A : Type u
  B : Type u
  [commRingA : CommRing A]
  [commRingB : CommRing B]
  [algebraAB : Algebra A B]
  map : A →+* B
  algebraMapAgrees : algebraMap A B = map
  noetherianA : Prop
  noetherianB : Prop
  regularMorphism : Prop
  filteredColimitOfSmoothAlgebras : Prop

def IsRegularMorphism (D : PopescuSituation) : Prop := D.regularMorphism

def IsFilteredColimitOfSmoothAlgebras (D : PopescuSituation) : Prop :=
  D.filteredColimitOfSmoothAlgebras

theorem popescu_characterization (D : PopescuSituation) :
    IsRegularMorphism D ↔ IsFilteredColimitOfSmoothAlgebras D := by
  sorry

structure ExcellentApproximationSituation (C : Type u) [Category.{v} C]
    [StackCategory C] where
  base : C
  excellent : Prop
  groupoidGeneralization : Prop
  arbitraryPoint : Prop
  etaleLocalUniqueness : Prop
  automorphismActionOnHenselization : Prop

theorem excellent_base_artin_approximation
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ExcellentApproximationSituation C) (hex : D.excellent) :
    D.groupoidGeneralization ∧ D.etaleLocalUniqueness ∧ D.arbitraryPoint := by
  sorry

structure ArtinAxiomForMorphism {C : Type u} [Category.{v} C]
    [StackCategory C] {X Y : C} (f : X ⟶ Y) where
  algebraizationAxiom : Prop
  approximationAxiom : Prop

theorem artin_axioms_are_stable_under_composition
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ArtinAxiomForMorphism f) (hg : ArtinAxiomForMorphism g) :
    Nonempty (ArtinAxiomForMorphism (f ≫ g)) := by
  sorry

structure RepresentableMorphismDeformationData
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) where
  representable : RepresentableByAlgebraicSpace f
  cotangentComplex : Type u
  controlsDeformations : Prop
  tangentSpace : Type u
  obstructionSpace : Type u

theorem representable_morphism_deformation_theory
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) (D : RepresentableMorphismDeformationData f)
    (hrepresentable : RepresentableByAlgebraicSpace f) :
    D.controlsDeformations := by
  sorry

end Formalization.Books.Guide.Unit05
