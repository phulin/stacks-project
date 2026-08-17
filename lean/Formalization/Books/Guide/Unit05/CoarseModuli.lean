import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 2: coarse moduli spaces
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

structure KeelMoriHypotheses {C : Type u} [Category.{v} C]
    [StackCategory C] where
  stack : C
  base : C
  structureMap : stack ⟶ base
  artin : IsArtinStack stack
  baseScheme : IsScheme base
  locallyFiniteType : IsLocallyFiniteTypeMorphism structureMap
  baseNoetherian : Prop
  finiteInertia : HasFiniteInertia stack

theorem keel_mori_coarse_moduli_space
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : KeelMoriHypotheses (C := C)) :
    HasSeparatedCoarseModuliSpace D.stack := by
  sorry

theorem separated_coarse_moduli_space_iff_finite_inertia
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hartin : IsArtinStack X) (hfiniteType : IsFiniteTypeStack X)
    (hnoetherianBase : Prop) :
    HasSeparatedCoarseModuliSpace X ↔ HasFiniteInertia X := by
  sorry

structure ConradCoarseModuliHypotheses {C : Type u} [Category.{v} C]
    [StackCategory C] where
  stack : C
  base : C
  structureMap : stack ⟶ base
  artin : IsArtinStack stack
  finiteInertia : HasFiniteInertia stack
  locallyOfFiniteType : IsLocallyFiniteTypeMorphism structureMap

theorem conrad_coarse_moduli_space_without_noetherian_hypothesis
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ConradCoarseModuliHypotheses (C := C)) :
    HasCoarseModuliSpace D.stack := by
  sorry

structure RydhCoarseModuliHypotheses {C : Type u} [Category.{v} C]
    [StackCategory C] where
  stack : C
  base : C
  structureMap : stack ⟶ base
  artin : IsArtinStack stack
  finiteInertia : HasFiniteInertia stack
  quasiCompact : IsQuasiCompactMorphism structureMap

theorem rydh_coarse_moduli_space_without_finite_presentation
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : RydhCoarseModuliHypotheses (C := C)) :
    HasCoarseModuliSpace D.stack := by
  sorry

theorem tame_iff_linearly_reductive_stabilizers
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hartin : IsArtinStack X) (hfiniteInertia : HasFiniteInertia X) :
    IsTameArtinStack X ↔ HasLinearlyReductiveStabilizers X := by
  sorry

theorem tame_iff_etale_local_linearly_reductive_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hartin : IsArtinStack X) (hfiniteInertia : HasFiniteInertia X) :
    IsTameArtinStack X ↔
      (IsEtaleLocalQuotient X ∧ HasLinearlyReductiveStabilizers X) := by
  sorry

structure TameCoarseBaseChangeData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  coarse : CoarseModuliSpaceData X
  commutesWithArbitraryBaseChange : Prop

structure FiniteInertiaCoarseBaseChangeData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  coarse : CoarseModuliSpaceData X
  commutesWithFlatBaseChange : Prop

theorem tame_coarse_moduli_commutes_with_arbitrary_base_change
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X : C} (h : IsTameArtinStack X) :
    ∃ D : TameCoarseBaseChangeData X, D.commutesWithArbitraryBaseChange := by
  rcases h with ⟨_, _, Y, q, hcoarse, hexact⟩
  exact ⟨⟨⟨Y, q, hcoarse⟩, TameByExactPushforward q⟩, ⟨hcoarse, hexact⟩⟩

theorem general_finite_inertia_coarse_moduli_commutes_with_flat_base_change
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X : C} (h : IsArtinStack X ∧ HasFiniteInertia X) :
    ∃ D : FiniteInertiaCoarseBaseChangeData X, D.commutesWithFlatBaseChange := by
  sorry

structure GoodModuliSpaceExample {C : Type u} [Category.{v} C]
    [StackCategory C] where
  stack : C
  stackIsArtin : IsArtinStack stack
  coarseCandidate : C
  map : stack ⟶ coarseCandidate
  quasiCompact : IsQuasiCompactMorphism map
  structureSheafIsomorphism : StructureSheafPushforwardIsIso map
  exactPushforward : ExactOnQuasiCoherent map

def IsGoodModuliSpaceExample {C : Type u} [Category.{v} C]
    [StackCategory C] (D : GoodModuliSpaceExample (C := C)) : Prop :=
  IsGoodModuliSpace D.map

theorem good_moduli_space_properties
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (q : X ⟶ Y) (hgood : IsGoodModuliSpace q) :
    Nonempty (GoodModuliSpaceProperties q) := by
  sorry

structure AffineLineByMultiplicativeGroupExample
    {C : Type u} [Category.{v} C] [StackCategory C] where
  stack : C
  affineLine : Type u
  affineLineIsAffineLine : Prop
  multiplicativeGroup : Type u
  [groupStructure : Group multiplicativeGroup]
  affineLineAction : GroupActionData multiplicativeGroup affineLine
  quotientStackPresentation : Prop
  stackIsArtin : IsArtinStack stack

theorem affine_line_by_multiplicative_group_has_no_coarse_moduli_space
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : AffineLineByMultiplicativeGroupExample (C := C)) :
    ¬ HasCoarseModuliSpace D.stack := by
  sorry

structure GITGoodModuliSpaceData {C : Type u} [Category.{v} C]
    [StackCategory C] where
  group : Type u
  groupStructure : Group group
  semistableLocus : C
  quotientStack : C
  quotientStackIsArtin : IsArtinStack quotientStack
  gitQuotient : C
  quotientMap : quotientStack ⟶ gitQuotient
  quotientStackIsTheSemistableQuotient : Prop
  reductive : Prop
  linearAction : Prop

theorem git_quotient_is_a_good_moduli_space
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : GITGoodModuliSpaceData (C := C))
    (hquotient : D.quotientStackIsTheSemistableQuotient)
    (hlinear : D.linearAction) (hreductive : D.reductive) :
    IsGoodModuliSpace D.quotientMap := by
  sorry

end Formalization.Books.Guide.Unit05
