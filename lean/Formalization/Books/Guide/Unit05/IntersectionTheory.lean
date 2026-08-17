import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 3: intersection theory
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

class ChowTheory (C : Type u) [Category.{v} C] where
  chowGroup : C → ℤ → Type u
  chowGroupAddCommGroup : ∀ (X : C) (k : ℤ), AddCommGroup (chowGroup X k)
  chowGroupRationalModule : ∀ (X : C) (k : ℤ), Module ℚ (chowGroup X k)

abbrev ChowGroup {C : Type u} [Category.{v} C] [ChowTheory C]
    (X : C) (k : ℤ) := ChowTheory.chowGroup X k

instance chowGroupAddCommGroupInstance {C : Type u} [Category.{v} C]
    [ChowTheory C] (X : C) (k : ℤ) : AddCommGroup (ChowGroup X k) :=
  ChowTheory.chowGroupAddCommGroup X k

instance chowGroupRationalModuleInstance {C : Type u} [Category.{v} C]
    [ChowTheory C] (X : C) (k : ℤ) : Module ℚ (ChowGroup X k) :=
  ChowTheory.chowGroupRationalModule X k

structure IntegralClosedSubstack {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  substack : C
  inclusion : substack ⟶ X
  closed : Prop
  integral : Prop
  dimension : ℤ

structure RationalCycleConstruction {C : Type u} [Category.{v} C]
    [StackCategory C] [ChowTheory C] (X : C) (k : ℤ) where
  cycles : Type u
  cycle : cycles → IntegralClosedSubstack X
  dimensionCorrect : ∀ z, (cycle z).dimension = k
  rationalEquivalence : cycles → cycles → Prop
  freeAbelianQuotient : Prop
  quotientMap : cycles → ChowGroup X k

structure IntersectionOperations {C : Type u} [Category.{v} C]
    [StackCategory C] [ChowTheory C] {X Y : C} (f : X ⟶ Y) where
  flatPullback : Prop
  properPushforward : Prop
  regularLocalEmbedding : Prop
  generalizedGysinHomomorphism : Prop

structure ModuliSpaceChowData {C : Type u} [Category.{v} C]
    [StackCategory C] [ChowTheory C] (X Y : C) where
  map : X ⟶ Y
  proper : IsProperMorphism map
  geometricPointBijection : Prop
  pushforward : ∀ k : ℤ, ChowGroup X k →+ ChowGroup Y k
  pushforwardIsomorphism : ∀ k : ℤ, Nonempty (ChowGroup X k ≃+ ChowGroup Y k)

theorem moduli_space_chow_pushforward_isomorphism
    {C : Type u} [Category.{v} C] [StackCategory C] [ChowTheory C]
    {X Y : C} (D : ModuliSpaceChowData X Y) (k : ℤ) :
    Nonempty (ChowGroup X k ≃+ ChowGroup Y k) := by
  sorry

structure EquivariantChowApproximation (G X : Type u) [Group G]
    [MulAction G X] where
  dimensionX : ℤ
  dimensionG : ℤ
  representation : Type u
  representationDimension : ℤ
  openFreeLocus : Set representation
  freeOnOpenLocus : Prop
  complementCodimension : ℤ
  codimensionBound : Prop
  mixedQuotient : Type u
  mixedQuotientIsAlgebraicSpace : Prop
  mixedQuotientCanBeScheme : Prop
  equivariantChowGroups : ℤ → Type u
  quotientStackChowGroups : ℤ → Type u

def EquivariantChowGroup {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) (i : ℤ) : Type u :=
  D.equivariantChowGroups i

def QuotientStackChowGroup {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) (i : ℤ) : Type u :=
  D.quotientStackChowGroups i

structure EquivariantChowIndexing {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) where
  equivariantFormula : ∀ i : ℤ,
    EquivariantChowGroup D i = D.equivariantChowGroups i
  quotientFormula : ∀ i : ℤ,
    QuotientStackChowGroup D i = D.quotientStackChowGroups i
  equivariantDimensionShift : ℤ
  quotientDimensionShift : ℤ

theorem equivariant_chow_group_formula
    {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) (I : EquivariantChowIndexing D)
    (i : ℤ) :
    EquivariantChowGroup D i = D.equivariantChowGroups i := by
  sorry

theorem quotient_stack_chow_group_formula
    {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) (I : EquivariantChowIndexing D)
    (i : ℤ) :
    QuotientStackChowGroup D i = D.quotientStackChowGroups i := by
  sorry

structure QuotientStackChowVanishingStatement
    {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) where
  quotientDimension : ℤ
  vanishesAboveDimension : ∀ i : ℤ, i > quotientDimension →
    Subsingleton (QuotientStackChowGroup D i)
  canBeNonzeroInNegativeDegrees : Prop

structure BGmChowStatement where
  chowGroup : ℤ → Type u
  chowGroupAddCommGroup : ∀ i, AddCommGroup (chowGroup i)
  nonpositiveIntegral : ∀ i : ℤ, i ≤ 0 → Prop

theorem classifying_multiplicative_group_chow_groups
    (D : BGmChowStatement) (i : ℤ) (hi : i ≤ 0) :
    D.nonpositiveIntegral i hi := by
  sorry

structure QuotientStackPresentationChowData (C : Type u) [Category.{v} C]
    [StackCategory C] [ChowTheory C] where
  stack : C
  group : Type u
  groupStructure : Group group
  quotientPresentationProperty : Prop
  presentationChowGroup : ℤ → Type u
  presentationComparison : ℤ → Prop

theorem quotient_stack_chow_is_independent_of_presentation
    {C : Type u} [Category.{v} C] [StackCategory C] [ChowTheory C]
    (D₁ D₂ : QuotientStackPresentationChowData C)
    (i : ℤ) :
    D₁.stack = D₂.stack →
      D₁.presentationComparison i ∧ D₂.presentationComparison i := by
  sorry

structure ArtinStackChowData (C : Type u) [Category.{v} C]
    [StackCategory C] [ChowTheory C] where
  stack : C
  artin : IsArtinStack stack
  affineStabilizers : Prop
  chowGroups : ℤ → Type u
  agreesWithQuotientStackDefinition : Prop
  usualFunctorialProperties : Prop

theorem Kresch_chow_groups_for_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] [ChowTheory C]
    (D : ArtinStackChowData C) :
    D.agreesWithQuotientStackDefinition ∧ D.usualFunctorialProperties := by
  sorry

structure VirtualFundamentalClassData (C : Type u) [Category.{v} C]
    [StackCategory C] [ChowTheory C] where
  stack : C
  deligneMumford : IsDeligneMumfordStack stack
  intrinsicNormalCone : Type u
  virtualFundamentalClass : Type u
  classInChowGroup : ∀ k : ℤ, virtualFundamentalClass → ChowGroup stack k

theorem intrinsic_normal_cone_gives_virtual_fundamental_class
    {C : Type u} [Category.{v} C] [StackCategory C] [ChowTheory C]
    (D : VirtualFundamentalClassData C) :
    Nonempty D.virtualFundamentalClass := by
  sorry

end Formalization.Books.Guide.Unit05
