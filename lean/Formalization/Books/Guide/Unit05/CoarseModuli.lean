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

class KeelMoriLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  coarseModuli : ∀ (D : KeelMoriHypotheses (C := C)), D.baseNoetherian →
    HasSeparatedCoarseModuliSpace D.stack

theorem keel_mori_coarse_moduli_space
    {C : Type u} [Category.{v} C] [StackCategory C]
    [KeelMoriLaws (C := C)] (D : KeelMoriHypotheses (C := C))
    (hbaseNoetherian : D.baseNoetherian) :
    HasSeparatedCoarseModuliSpace D.stack :=
  KeelMoriLaws.coarseModuli D hbaseNoetherian

class SeparatedCoarseModuliLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  finiteInertiaIff : ∀ (X : C) (_hartin : IsArtinStack X)
    (_hfiniteType : IsFiniteTypeStack X) (hnoetherianBase : Prop)
    (_hbaseNoetherian : hnoetherianBase),
      HasSeparatedCoarseModuliSpace X ↔ HasFiniteInertia X

theorem separated_coarse_moduli_space_iff_finite_inertia
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [SeparatedCoarseModuliLaws (C := C)]
    (hartin : IsArtinStack X) (hfiniteType : IsFiniteTypeStack X)
    (hnoetherianBase : Prop) (hbaseNoetherian : hnoetherianBase) :
    HasSeparatedCoarseModuliSpace X ↔ HasFiniteInertia X :=
  SeparatedCoarseModuliLaws.finiteInertiaIff X hartin hfiniteType
    hnoetherianBase hbaseNoetherian

structure ConradCoarseModuliHypotheses {C : Type u} [Category.{v} C]
    [StackCategory C] where
  stack : C
  base : C
  structureMap : stack ⟶ base
  artin : IsArtinStack stack
  finiteInertia : HasFiniteInertia stack
  locallyOfFiniteType : IsLocallyFiniteTypeMorphism structureMap

class ConradCoarseModuliLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  coarseModuli : ∀ (D : ConradCoarseModuliHypotheses (C := C)),
    HasCoarseModuliSpace D.stack

theorem conrad_coarse_moduli_space_without_noetherian_hypothesis
    {C : Type u} [Category.{v} C] [StackCategory C]
    [ConradCoarseModuliLaws (C := C)]
    (D : ConradCoarseModuliHypotheses (C := C)) :
    HasCoarseModuliSpace D.stack :=
  ConradCoarseModuliLaws.coarseModuli D

structure RydhCoarseModuliHypotheses {C : Type u} [Category.{v} C]
    [StackCategory C] where
  stack : C
  base : C
  structureMap : stack ⟶ base
  artin : IsArtinStack stack
  finiteInertia : HasFiniteInertia stack
  quasiCompact : IsQuasiCompactMorphism structureMap

class RydhCoarseModuliLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  coarseModuli : ∀ (D : RydhCoarseModuliHypotheses (C := C)),
    HasCoarseModuliSpace D.stack

theorem rydh_coarse_moduli_space_without_finite_presentation
    {C : Type u} [Category.{v} C] [StackCategory C]
    [RydhCoarseModuliLaws (C := C)]
    (D : RydhCoarseModuliHypotheses (C := C)) :
    HasCoarseModuliSpace D.stack :=
  RydhCoarseModuliLaws.coarseModuli D

class TameStabilizerLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  tameIff : ∀ (X : C) (_hartin : IsArtinStack X)
    (_hfiniteInertia : HasFiniteInertia X),
    IsTameArtinStack X ↔ HasLinearlyReductiveStabilizers X

theorem tame_iff_linearly_reductive_stabilizers
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [TameStabilizerLaws (C := C)]
    (hartin : IsArtinStack X) (hfiniteInertia : HasFiniteInertia X) :
    IsTameArtinStack X ↔ HasLinearlyReductiveStabilizers X :=
  TameStabilizerLaws.tameIff X hartin hfiniteInertia

class TameEtaleLocalQuotientLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  tameIffEtaleLocal : ∀ (X : C) (_hartin : IsArtinStack X)
    (_hfiniteInertia : HasFiniteInertia X),
    IsTameArtinStack X ↔
      (IsEtaleLocalQuotient X ∧ HasLinearlyReductiveStabilizers X)

theorem tame_iff_etale_local_linearly_reductive_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [TameEtaleLocalQuotientLaws (C := C)]
    (hartin : IsArtinStack X) (hfiniteInertia : HasFiniteInertia X) :
    IsTameArtinStack X ↔
      (IsEtaleLocalQuotient X ∧ HasLinearlyReductiveStabilizers X) :=
  TameEtaleLocalQuotientLaws.tameIffEtaleLocal X hartin hfiniteInertia

structure TameCoarseBaseChangeData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  coarse : CoarseModuliSpaceData X
  commutesWithArbitraryBaseChange : Prop

structure FiniteInertiaCoarseBaseChangeData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  coarse : CoarseModuliSpaceData X
  commutesWithFlatBaseChange : Prop

class FiniteInertiaCoarseBaseChangeLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  flatBaseChange : ∀ {X : C},
    IsArtinStack X ∧ HasFiniteInertia X →
      ∃ D : FiniteInertiaCoarseBaseChangeData X, D.commutesWithFlatBaseChange

theorem tame_coarse_moduli_commutes_with_arbitrary_base_change
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X : C} (h : IsTameArtinStack X) :
    ∃ D : TameCoarseBaseChangeData X, D.commutesWithArbitraryBaseChange := by
  rcases h with ⟨_, _, Y, q, hcoarse, hexact⟩
  exact ⟨⟨⟨Y, q, hcoarse⟩, TameByExactPushforward q⟩, ⟨hcoarse, hexact⟩⟩

theorem general_finite_inertia_coarse_moduli_commutes_with_flat_base_change
    {C : Type u} [Category.{v} C] [StackCategory C]
    [FiniteInertiaCoarseBaseChangeLaws (C := C)]
    {X : C} (h : IsArtinStack X ∧ HasFiniteInertia X) :
    ∃ D : FiniteInertiaCoarseBaseChangeData X, D.commutesWithFlatBaseChange :=
  FiniteInertiaCoarseBaseChangeLaws.flatBaseChange h

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

class GoodModuliSpaceLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  properties : ∀ {X Y : C} (q : X ⟶ Y), IsGoodModuliSpace q →
    Nonempty (GoodModuliSpaceProperties q)

theorem good_moduli_space_properties
    {C : Type u} [Category.{v} C] [StackCategory C]
    [GoodModuliSpaceLaws (C := C)]
    {X Y : C} (q : X ⟶ Y) (hgood : IsGoodModuliSpace q) :
    Nonempty (GoodModuliSpaceProperties q) :=
  GoodModuliSpaceLaws.properties q hgood

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

class AffineLineMultiplicativeGroupLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  noCoarseModuli : ∀ (D : AffineLineByMultiplicativeGroupExample (C := C)),
    ¬ HasCoarseModuliSpace D.stack

theorem affine_line_by_multiplicative_group_has_no_coarse_moduli_space
    {C : Type u} [Category.{v} C] [StackCategory C]
    [AffineLineMultiplicativeGroupLaws (C := C)]
    (D : AffineLineByMultiplicativeGroupExample (C := C)) :
    ¬ HasCoarseModuliSpace D.stack :=
  AffineLineMultiplicativeGroupLaws.noCoarseModuli D

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

class GITGoodModuliSpaceLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  goodModuliSpace : ∀ (D : GITGoodModuliSpaceData (C := C)),
    D.quotientStackIsTheSemistableQuotient → D.linearAction → D.reductive →
      IsGoodModuliSpace D.quotientMap

theorem git_quotient_is_a_good_moduli_space
    {C : Type u} [Category.{v} C] [StackCategory C]
    [GITGoodModuliSpaceLaws (C := C)]
    (D : GITGoodModuliSpaceData (C := C))
    (hquotient : D.quotientStackIsTheSemistableQuotient)
    (hlinear : D.linearAction) (hreductive : D.reductive) :
    IsGoodModuliSpace D.quotientMap :=
  GITGoodModuliSpaceLaws.goodModuliSpace D hquotient hlinear hreductive

end Formalization.Books.Guide.Unit05
