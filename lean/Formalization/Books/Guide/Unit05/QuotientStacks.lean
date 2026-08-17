import Formalization.Books.Guide.Unit05.Core
import Formalization.Books.SpacesGroupoids.Unit20.Core
import Formalization.Books.SpacesGroupoids.Unit27.Gerbes

/-!
# Chapter 5, Section 4: quotient stacks
-/

noncomputable section

open CategoryTheory
open Formalization.Books.StacksMorphisms.Unit07

universe u v

namespace Formalization.Books.Guide.Unit05

def HasFiniteEtaleCoverByScheme {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ Y : C, IsScheme Y ∧ ∃ e : Y ⟶ X,
    IsFiniteMorphism e ∧ IsEtaleMorphism e ∧ Surjective e

structure FiniteGroupQuotientData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  group : Type u
  groupStructure : Group group
  finiteGroup : Prop
  quotientSpace : C
  quotientMap : quotientSpace ⟶ X
  quotientSpaceIsScheme : IsScheme quotientSpace
  quotientSpaceIsAlgebraicSpace : IsAlgebraicSpace quotientSpace

theorem finite_group_quotient_iff_finite_etale_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C) :
    IsGlobalQuotient X ↔ HasFiniteEtaleCoverByScheme X := by
  sorry

structure EtaleSeparatedFiniteGroupChart {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  point : Point X
  residueField : Type u
  group : Type u
  groupStructure : Group group
  finiteGroup : Prop
  affineScheme : C
  affineSchemeIsAffine : Prop
  quotientChart : C
  chartMap : quotientChart ⟶ X
  representable : Prop
  etale : IsEtaleMorphism chartMap
  separated : IsSeparatedMorphism chartMap
  fiberIsTheSpecifiedPoint : Prop

theorem deligne_mumford_local_finite_group_chart
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (hDM : IsDeligneMumfordStack X) (x : Point X) :
    Nonempty (EtaleSeparatedFiniteGroupChart X) := by
  sorry

structure FaithfulVectorBundleCriterion {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  vectorBundle : VectorBundle X
  stabilizersActFaithfully : Prop
  locallyClosedRepresentableLocus : Prop
  locusSurjects : Prop

def HasFaithfulVectorBundle {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  Nonempty (FaithfulVectorBundleCriterion X)

def HasRepresentableSurjectiveVectorBundleLocus {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : FaithfulVectorBundleCriterion X,
    D.locallyClosedRepresentableLocus ∧ D.locusSurjects

theorem quotient_stack_iff_faithful_vector_bundle
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C) :
    IsGlobalQuotient X ↔ HasFaithfulVectorBundle X := by
  sorry

theorem quotient_stack_iff_representable_vector_bundle_locus
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C) :
    IsGlobalQuotient X ↔ HasRepresentableSurjectiveVectorBundleLocus X := by
  sorry

def HasFiniteFlatCoverByAlgebraicSpace {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ Y : C, IsAlgebraicSpace Y ∧ ∃ f : Y ⟶ X,
    IsFiniteMorphism f ∧ Flat f ∧ Surjective f

theorem finite_flat_cover_implies_quotient_stack
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (h : HasFiniteFlatCoverByAlgebraicSpace X) :
    IsGlobalQuotient X := by
  sorry

theorem smooth_deligne_mumford_generically_trivial_is_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hsmooth : IsSmoothStack X) (hDM : IsDeligneMumfordStack X)
    (hgeneric : HasGenericallyTrivialStabilizer X) :
    IsGlobalQuotient X := by
  sorry

structure GmGerbeBrauerData {C : Type u} [Category.{v} C]
    [StackCategory C] where
  base : C
  gerbe : C
  cohomologicalBrauerClass : Type u
  isGmGerbe : Prop
  brauerMapImage : Prop

theorem gm_gerbe_is_quotient_iff_brauer_class_is_azumaya
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : GmGerbeBrauerData (C := C)) :
    IsGlobalQuotient D.gerbe ↔ D.brauerMapImage := by
  sorry

theorem exists_nonseparated_deligne_mumford_stack_not_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] :
    ∃ X : C, IsDeligneMumfordStack X ∧
      ¬ IsSeparatedStack X ∧ ¬ IsGlobalQuotient X := by
  sorry

def HasResolutionPropertyViaGLnQuasiAffineQuotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  ∃ Y : C, IsQuasiProjectiveStack Y ∧ ∃ f : Y ⟶ X,
    f ≫ 𝟙 X = f ∧ IsGlobalQuotient X

def HasAffineFiniteTypeGroupQuotient {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ G : Type u, Nonempty (Group G) ∧ IsGlobalQuotient X

theorem totaro_resolution_property_iff_gl_n_quasi_affine_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hnormal : IsNormalStack X) (hnoetherian : Prop)
    (haffineStabilizers : Prop) :
    HasResolutionProperty X ↔ HasResolutionPropertyViaGLnQuasiAffineQuotient X := by
  sorry

theorem finite_type_field_resolution_property_iff_affine_group_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hfiniteTypeOverField : Prop) :
    HasResolutionProperty X ↔ HasAffineFiniteTypeGroupQuotient X := by
  sorry

theorem quotient_stacks_have_resolution_property
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hquotient : IsGlobalQuotient X) :
    HasResolutionProperty X := by
  sorry

theorem smooth_deligne_mumford_resolution_property
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hsmooth : IsSmoothStack X) (hDM : IsDeligneMumfordStack X)
    (hfiniteStabilizer : HasFiniteStabilizer X)
    (hgeneric : HasGenericallyTrivialStabilizer X)
    (hcoarseScheme : CoarseSpaceIsScheme X)
    (haffineDiagonal : HasAffineDiagonal X) :
    HasResolutionProperty X := by
  sorry

structure ClosedPointStabilizerData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  affineAtEveryClosedPoint : Prop

def ClosedPointsHaveAffineStabilizer {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : ClosedPointStabilizerData X, D.affineAtEveryClosedPoint

theorem affine_diagonal_iff_affine_closed_stabilizers
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hnoetherian : Prop) (hresolution : HasResolutionProperty X) :
    HasAffineDiagonal X ↔ ClosedPointsHaveAffineStabilizer X := by
  sorry

theorem smooth_separated_generically_tame_quasi_projective_is_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hsmooth : IsSmoothStack X) (hseparated : IsSeparatedStack X)
    (hgenericallyTame : Prop) (hDM : IsDeligneMumfordStack X)
    (hcoarseQuasiProjective : Prop) :
    IsGlobalQuotient X := by
  sorry

def HasOpenCoverByFiniteGroupSchemeQuotients {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ n : ℕ, ∃ U : Fin n → C,
    ∀ i, ∃ f : U i ⟶ X, f ≫ 𝟙 X = f ∧ IsGlobalQuotient (U i)

theorem zariski_local_quotient_iff_open_finite_group_quotient_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hcoarseScheme : CoarseSpaceIsScheme X) :
    IsZariskiLocalQuotient X ↔ HasOpenCoverByFiniteGroupSchemeQuotients X := by
  sorry

structure SmoothProperProjectiveEmbedding {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  ambient : C
  smooth : IsSmoothStack ambient
  proper : IsProperStack ambient
  projectiveCoarse : CoarseSpaceIsProjective ambient
  embedding : X ⟶ ambient
  isClosedEmbedding : Prop

def IsProjectiveDMStackByEmbedding {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (SmoothProperProjectiveEmbedding X)

def ProperCharacteristicZeroDMQuotientCriterion
    {C : Type u} [Category.{v} C] [StackCategory C] (X Y : C) : Prop :=
  CoarseSpaceIsProjective Y ∧
    (IsGlobalQuotient X ↔ HasGeneratingSheaf X) ∧
    (HasGeneratingSheaf X ↔ IsProjectiveDMStackByEmbedding X)

theorem proper_dm_projective_quotient_criterion
    {C : Type u} [Category.{v} C] [StackCategory C] (X Y : C)
    (hproper : IsProperStack X) (hDM : IsDeligneMumfordStack X)
    (hcharZero : Prop) (hcoarse : CoarseSpaceIsProjective Y) :
    ProperCharacteristicZeroDMQuotientCriterion X Y := by
  sorry

theorem projective_dm_stack_definition
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C) :
    IsProjectiveStack X ↔ IsProjectiveDMStackByEmbedding X := by
  sorry

def EverySmoothDMStackOfDimensionIsQuotient {C : Type u} [Category.{v} C]
    [StackCategory C] (n : ℕ) : Prop :=
  ∀ X : C, IsSmoothStack X → IsDeligneMumfordStack X →
    StackDimension X = n → IsGlobalQuotient X

structure AzumayaCohomologicalBrauerComparison (C : Type u)
    [Category.{v} C] [StackCategory C] (n : ℕ) where
  comparison : Prop

def AzumayaEqualsCohomologicalBrauerInDimension {C : Type u}
    [Category.{v} C] [StackCategory C] (n : ℕ) : Prop :=
  ∃ D : AzumayaCohomologicalBrauerComparison C n, D.comparison

theorem Kresch_Vistoli_dimension_equivalence
    {C : Type u} [Category.{v} C] [StackCategory C] (n : ℕ)
    (hcharZero : Prop) :
    hcharZero → (EverySmoothDMStackOfDimensionIsQuotient (C := C) n ↔
      AzumayaEqualsCohomologicalBrauerInDimension (C := C) n) := by
  sorry

def StratifiedByQuotientStacks {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ n : ℕ, ∃ strata : Fin n → C,
    ∀ i, ∃ f : strata i ⟶ X, f ≫ 𝟙 X = f ∧ IsGlobalQuotient (strata i)

theorem reduced_artin_stack_stratified_by_quotients
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hartin : IsArtinStack X) (hfiniteType : IsFiniteTypeStack X)
    (hreduced : Prop) (haffineStabilizers : Prop) :
    StratifiedByQuotientStacks X := by
  sorry

structure EtaleLocallyAffineFiniteStabilizerQuotientData
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C) where
  chart : C
  chartMap : chart ⟶ X
  affine : Prop
  finiteStabilizerGroup : Prop
  etale : IsEtaleMorphism chartMap

def EtaleLocallyAffineFiniteStabilizerQuotient {C : Type u}
    [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  IsEtaleLocalQuotient X ∧ Nonempty (EtaleLocallyAffineFiniteStabilizerQuotientData X)

theorem separated_dm_stack_etale_locally_affine_finite_group_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hseparated : IsSeparatedStack X) (hDM : IsDeligneMumfordStack X) :
    EtaleLocallyAffineFiniteStabilizerQuotient X := by
  sorry

theorem tame_stack_etale_locally_affine_stabilizer_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (htame : IsTameArtinStack X) :
    EtaleLocallyAffineFiniteStabilizerQuotient X := by
  sorry

structure LocalQuotientSliceData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  closedPoint : Point X
  stabilizer : Type u
  stabilizerGroup : Group stabilizer
  linearlyReductive : Prop
  algebraicSpace : C
  chart : C
  chartMap : chart ⟶ X
  etale : IsEtaleMorphism chartMap
  formallyLocal : Prop

theorem local_quotient_slice_formal_statement
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (x : Point X) (hlinearlyReductive : Prop) :
    ∃ D : LocalQuotientSliceData X, D.closedPoint = x ∧ D.formallyLocal := by
  sorry

theorem luna_slice_for_linearly_reductive_quotient_stack
    {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) (hquotient : IsGlobalQuotient X)
    (hlinearlyReductive : Prop) :
    IsEtaleLocalQuotient X := by
  sorry

end Formalization.Books.Guide.Unit05
