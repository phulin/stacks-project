import Mathlib.Algebra.Module.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
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
  rationalEquivalence : Setoid (FreeAbelianGroup cycles)
  [quotientAddCommGroup : AddCommGroup (Quotient rationalEquivalence)]
  quotientIdentifiesWithChow :
    Nonempty (Quotient rationalEquivalence ≃+ ChowGroup X k)

structure IntersectionOperations {C : Type u} [Category.{v} C]
    [StackCategory C] [ChowTheory C] {X Y : C} (f : X ⟶ Y) where
  flatPullback : ∀ k : ℤ, ChowGroup Y k →+ ChowGroup X k
  properPushforward : ∀ k : ℤ, ChowGroup X k →+ ChowGroup Y k
  regularLocalEmbedding : Prop
  generalizedGysinHomomorphism : ∀ k : ℤ, ChowGroup X k →+ ChowGroup Y k

structure ModuliSpaceChowData {C : Type u} [Category.{v} C]
    [StackCategory C] [ChowTheory C] (X Y : C) where
  map : X ⟶ Y
  proper : IsProperMorphism map
  geometricPointBijection : Prop
  pushforward : ∀ k : ℤ, ChowGroup X k →+ ChowGroup Y k

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
  mixedChowGroups : ℤ → Type u
  equivariantChowGroups : ℤ → Type u
  quotientStackChowGroups : ℤ → Type u

def EquivariantChowGroup {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) (i : ℤ) : Type u :=
  D.equivariantChowGroups i

def QuotientStackChowGroup {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) (i : ℤ) : Type u :=
  D.quotientStackChowGroups i

theorem equivariant_chow_group_formula
    {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) (i : ℤ) :
    EquivariantChowGroup D i =
      D.mixedChowGroups (i + D.representationDimension - D.dimensionG) := by
  sorry

theorem quotient_stack_chow_group_formula
    {G X : Type u} [Group G] [MulAction G X]
    (D : EquivariantChowApproximation G X) (i : ℤ) :
    QuotientStackChowGroup D i =
      D.mixedChowGroups (i + D.representationDimension) := by
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
  chowGroupIsIntegers : ∀ i : ℤ, i ≤ 0 → Nonempty (chowGroup i ≃ ℤ)

theorem classifying_multiplicative_group_chow_groups
    (D : BGmChowStatement) (i : ℤ) (hi : i ≤ 0) :
    Nonempty (D.chowGroup i ≃ ℤ) := by
  sorry

structure QuotientStackPresentationChowData (C : Type u) [Category.{v} C]
    [StackCategory C] [ChowTheory C] where
  stack : C
  group : Type u
  groupStructure : Group group
  quotientPresentationProperty : Prop
  presentationChowGroup : ℤ → Type u
  presentationComparison : ∀ i : ℤ,
    Nonempty (ChowGroup stack i ≃ presentationChowGroup i)

theorem quotient_stack_chow_is_independent_of_presentation
    {C : Type u} [Category.{v} C] [StackCategory C] [ChowTheory C]
    (D₁ D₂ : QuotientStackPresentationChowData C)
    (i : ℤ) :
    D₁.stack = D₂.stack →
      Nonempty (D₁.presentationChowGroup i ≃ D₂.presentationChowGroup i) := by
  sorry

structure ArtinStackChowData (C : Type u) [Category.{v} C]
    [StackCategory C] [ChowTheory C] where
  stack : C
  artin : IsArtinStack stack
  affineStabilizers : Prop
  chowGroups : ℤ → Type u

structure ArtinStackChowConclusion where
  agreesWithQuotientStackDefinition : Prop
  usualFunctorialProperties : Prop

theorem Kresch_chow_groups_for_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] [ChowTheory C]
    (D : ArtinStackChowData C) :
    Nonempty ArtinStackChowConclusion := by
  sorry

structure VirtualFundamentalClassData (C : Type u) [Category.{v} C]
    [StackCategory C] [ChowTheory C] where
  stack : C
  deligneMumford : IsDeligneMumfordStack stack
  intrinsicNormalCone : Type u
  virtualDimension : ℤ

theorem intrinsic_normal_cone_gives_virtual_fundamental_class
    {C : Type u} [Category.{v} C] [StackCategory C] [ChowTheory C]
    (D : VirtualFundamentalClassData C) :
    Nonempty (ChowGroup D.stack D.virtualDimension) := by
  sorry

end Formalization.Books.Guide.Unit05
