import Formalization.Books.Guide.Unit05.Core

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
    IsFiniteMorphism e ∧ IsEtaleMorphism e ∧
      RepresentableByAlgebraicSpace e ∧ Surjective e

structure FiniteGroupQuotientData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  group : Type u
  groupStructure : Group group
  finiteGroup : Finite group
  cover : C
  coverMap : cover ⟶ X
  coverIsScheme : IsScheme cover
  coverIsAlgebraicSpace : IsAlgebraicSpace cover
  coverMapFinite : IsFiniteMorphism coverMap
  coverMapEtale : IsEtaleMorphism coverMap
  coverMapRepresentable : RepresentableByAlgebraicSpace coverMap
  coverMapSurjective : Surjective coverMap
  groupActionOnCover : Prop
  quotientPresentation : Prop

def HasFiniteGroupQuotient {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (FiniteGroupQuotientData X)

class FiniteGroupQuotientLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  quotientOfCover : ∀ {X : C}, HasFiniteEtaleCoverByScheme X →
    Nonempty (FiniteGroupQuotientData X)

theorem finite_group_quotient_iff_finite_etale_cover
    {C : Type u} [Category.{v} C] [StackCategory C]
    [FiniteGroupQuotientLaws (C := C)] (X : C) :
    HasFiniteGroupQuotient X ↔ HasFiniteEtaleCoverByScheme X := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.cover, D.coverIsScheme, D.coverMap, D.coverMapFinite,
      D.coverMapEtale, D.coverMapRepresentable, D.coverMapSurjective⟩
  · intro h
    exact FiniteGroupQuotientLaws.quotientOfCover h

structure EtaleSeparatedFiniteGroupChart {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  point : Point X
  residueField : Type u
  group : Type u
  groupStructure : Group group
  finiteGroup : Finite group
  quotientChart : C
  affineScheme : C
  affineSchemeIsScheme : IsScheme affineScheme
  affineSchemeIsAffine : Prop
  affineSchemeToChart : affineScheme ⟶ quotientChart
  chartMap : quotientChart ⟶ X
  representable : RepresentableByAlgebraicSpace chartMap
  etale : IsEtaleMorphism chartMap
  separated : IsSeparatedMorphism chartMap
  chartIsFiniteGroupQuotient : Prop
  fiberIsTheSpecifiedPoint : Prop

class DeligneMumfordChartLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  localFiniteGroupChart : ∀ {X : C}, IsDeligneMumfordStack X → Point X →
    Nonempty (EtaleSeparatedFiniteGroupChart X)

theorem deligne_mumford_local_finite_group_chart
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    [DeligneMumfordChartLaws (C := C)]
    (hDM : IsDeligneMumfordStack X) (x : Point X) :
    Nonempty (EtaleSeparatedFiniteGroupChart X) :=
  DeligneMumfordChartLaws.localFiniteGroupChart hDM x

structure FaithfulVectorBundleCriterion {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  vectorBundle : VectorBundle X
  stabilizersActFaithfully : Prop

structure RepresentableVectorBundleLocusData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  vectorBundle : VectorBundle X
  locallyClosedRepresentableLocus : Prop
  locusSurjects : Prop

def HasFaithfulVectorBundle {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  Nonempty (FaithfulVectorBundleCriterion X)

def HasRepresentableSurjectiveVectorBundleLocus {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (RepresentableVectorBundleLocusData X)

class FaithfulVectorBundleLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  faithfulIff : ∀ (X : C) (hfiniteType : Prop) (_hfiniteTypeProof : hfiniteType)
    (hnoetherian : Prop) (_hnoetherianProof : hnoetherian),
    IsGlobalQuotient X ↔ HasFaithfulVectorBundle X

class RepresentableVectorBundleLocusLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  locusIff : ∀ (X : C) (hfiniteType : Prop) (_hfiniteTypeProof : hfiniteType)
    (hnoetherian : Prop) (_hnoetherianProof : hnoetherian),
    IsGlobalQuotient X ↔ HasRepresentableSurjectiveVectorBundleLocus X

theorem quotient_stack_iff_faithful_vector_bundle
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [FaithfulVectorBundleLaws (C := C)]
    (hfiniteType : Prop) (hfiniteTypeProof : hfiniteType)
    (hnoetherian : Prop) (hnoetherianProof : hnoetherian) :
    IsGlobalQuotient X ↔ HasFaithfulVectorBundle X :=
  FaithfulVectorBundleLaws.faithfulIff X hfiniteType hfiniteTypeProof
    hnoetherian hnoetherianProof

theorem quotient_stack_iff_representable_vector_bundle_locus
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [RepresentableVectorBundleLocusLaws (C := C)]
    (hfiniteType : Prop) (hfiniteTypeProof : hfiniteType)
    (hnoetherian : Prop) (hnoetherianProof : hnoetherian) :
    IsGlobalQuotient X ↔ HasRepresentableSurjectiveVectorBundleLocus X :=
  RepresentableVectorBundleLocusLaws.locusIff X hfiniteType hfiniteTypeProof
    hnoetherian hnoetherianProof

def HasFiniteFlatCoverByAlgebraicSpace {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ Y : C, IsAlgebraicSpace Y ∧ ∃ f : Y ⟶ X,
    IsFiniteMorphism f ∧ Flat f ∧ Surjective f

class FiniteFlatCoverQuotientLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  quotientOfCover : ∀ {X : C}, HasFiniteFlatCoverByAlgebraicSpace X →
    IsGlobalQuotient X

theorem finite_flat_cover_implies_quotient_stack
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    [FiniteFlatCoverQuotientLaws (C := C)]
    (h : HasFiniteFlatCoverByAlgebraicSpace X) :
    IsGlobalQuotient X :=
  FiniteFlatCoverQuotientLaws.quotientOfCover h

class SmoothDMQuotientLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  quotient : ∀ (X : C), IsSmoothStack X → IsDeligneMumfordStack X →
    HasGenericallyTrivialStabilizer X → IsGlobalQuotient X

theorem smooth_deligne_mumford_generically_trivial_is_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [SmoothDMQuotientLaws (C := C)]
    (hsmooth : IsSmoothStack X) (hDM : IsDeligneMumfordStack X)
    (hgeneric : HasGenericallyTrivialStabilizer X) :
    IsGlobalQuotient X :=
  SmoothDMQuotientLaws.quotient X hsmooth hDM hgeneric

structure GmGerbeBrauerData {C : Type u} [Category.{v} C]
    [StackCategory C] where
  base : C
  baseIsScheme : IsScheme base
  baseNoetherian : Prop
  gerbe : C
  gerbeToBase : gerbe ⟶ base
  cohomologicalBrauerClass : Type u
  isGmGerbe : Prop
  brauerMapImage : Prop

class GmGerbeBrauerLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  quotientIffBrauerImage : ∀ (D : GmGerbeBrauerData (C := C))
    (_hbaseNoetherian : D.baseNoetherian) (_hgerbe : D.isGmGerbe),
      IsGlobalQuotient D.gerbe ↔ D.brauerMapImage

theorem gm_gerbe_is_quotient_iff_brauer_class_is_azumaya
    {C : Type u} [Category.{v} C] [StackCategory C]
    [GmGerbeBrauerLaws (C := C)]
    (D : GmGerbeBrauerData (C := C))
    (hbaseNoetherian : D.baseNoetherian) (hgerbe : D.isGmGerbe) :
    IsGlobalQuotient D.gerbe ↔ D.brauerMapImage :=
  GmGerbeBrauerLaws.quotientIffBrauerImage D hbaseNoetherian hgerbe

class NonSeparatedDMNonQuotientLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  counterexample : ∃ X : C, IsDeligneMumfordStack X ∧
    ¬ IsSeparatedStack X ∧ ¬ IsGlobalQuotient X

theorem exists_nonseparated_deligne_mumford_stack_not_quotient
    {C : Type u} [Category.{v} C] [StackCategory C]
    [NonSeparatedDMNonQuotientLaws (C := C)] :
    ∃ X : C, IsDeligneMumfordStack X ∧
      ¬ IsSeparatedStack X ∧ ¬ IsGlobalQuotient X :=
  NonSeparatedDMNonQuotientLaws.counterexample

structure GLnQuasiAffineQuotientData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  quotientSpace : C
  quotientSpaceIsQuasiAffine : IsQuasiAffineStack quotientSpace
  rank : ℕ
  gln : Type u
  glnGroup : Group gln
  glnIsGeneralLinearGroup : Prop
  quotientMap : quotientSpace ⟶ X
  glnAction : Prop
  isTheGLnQuotient : Prop

def HasResolutionPropertyViaGLnQuasiAffineQuotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  Nonempty (GLnQuasiAffineQuotientData X)

class TotaroResolutionLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  resolutionIffGLn : ∀ (X : C) (_hnormal : IsNormalStack X)
    (hnoetherian : Prop) (_hnoetherianProof : hnoetherian)
    (haffineStabilizers : Prop) (_haffineStabilizersProof : haffineStabilizers),
    HasResolutionProperty X ↔ HasResolutionPropertyViaGLnQuasiAffineQuotient X

structure AffineFiniteTypeGroupQuotientData {C : Type u}
    [Category.{v} C] [StackCategory C] (X : C) where
  group : Type u
  groupStructure : Group group
  groupIsAffineFiniteType : Prop
  affineScheme : C
  affineSchemeIsScheme : IsScheme affineScheme
  quotientMap : affineScheme ⟶ X
  groupAction : Prop
  isTheGroupQuotient : Prop

def HasAffineFiniteTypeGroupQuotient {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (AffineFiniteTypeGroupQuotientData X)

class AffineFiniteTypeGroupQuotientLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  resolutionIffAffineGroup : ∀ (X : C) (hfiniteTypeOverField : Prop)
    (_hfiniteTypeOverFieldProof : hfiniteTypeOverField),
      HasResolutionProperty X ↔ HasAffineFiniteTypeGroupQuotient X

theorem totaro_resolution_property_iff_gl_n_quasi_affine_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [TotaroResolutionLaws (C := C)]
    (hnormal : IsNormalStack X) (hnoetherian : Prop)
    (hnoetherianProof : hnoetherian) (haffineStabilizers : Prop)
    (haffineStabilizersProof : haffineStabilizers) :
    HasResolutionProperty X ↔ HasResolutionPropertyViaGLnQuasiAffineQuotient X :=
  TotaroResolutionLaws.resolutionIffGLn X hnormal hnoetherian hnoetherianProof
    haffineStabilizers haffineStabilizersProof

theorem finite_type_field_resolution_property_iff_affine_group_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [AffineFiniteTypeGroupQuotientLaws (C := C)]
    (hfiniteTypeOverField : Prop) (hfiniteTypeOverFieldProof : hfiniteTypeOverField) :
    HasResolutionProperty X ↔ HasAffineFiniteTypeGroupQuotient X :=
  AffineFiniteTypeGroupQuotientLaws.resolutionIffAffineGroup X
    hfiniteTypeOverField hfiniteTypeOverFieldProof

class QuotientResolutionLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  resolution : ∀ (X : C), IsGlobalQuotient X → HasResolutionProperty X

theorem quotient_stacks_have_resolution_property
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [QuotientResolutionLaws (C := C)]
    (hquotient : IsGlobalQuotient X) :
    HasResolutionProperty X :=
  QuotientResolutionLaws.resolution X hquotient

class SmoothDMResolutionLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  resolution : ∀ (X : C), IsSmoothStack X → IsDeligneMumfordStack X →
    HasFiniteStabilizer X → HasGenericallyTrivialStabilizer X →
    CoarseSpaceIsScheme X → HasAffineDiagonal X → HasResolutionProperty X

theorem smooth_deligne_mumford_resolution_property
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [SmoothDMResolutionLaws (C := C)]
    (hsmooth : IsSmoothStack X) (hDM : IsDeligneMumfordStack X)
    (hfiniteStabilizer : HasFiniteStabilizer X)
    (hgeneric : HasGenericallyTrivialStabilizer X)
    (hcoarseScheme : CoarseSpaceIsScheme X)
    (haffineDiagonal : HasAffineDiagonal X) :
    HasResolutionProperty X :=
  SmoothDMResolutionLaws.resolution X hsmooth hDM hfiniteStabilizer hgeneric
    hcoarseScheme haffineDiagonal

structure ClosedPointStabilizerData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  affineAtEveryClosedPoint : ∀ _x : Point X, IsClosedPoint _x → Prop

def ClosedPointsHaveAffineStabilizer {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : ClosedPointStabilizerData X,
    ∀ x : Point X, ∀ hx : IsClosedPoint x,
      D.affineAtEveryClosedPoint x hx

class AffineDiagonalStabilizerLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  affineIffStabilizers : ∀ (X : C) (hnoetherian : Prop)
    (_hnoetherianProof : hnoetherian) (_hresolution : HasResolutionProperty X),
      HasAffineDiagonal X ↔ ClosedPointsHaveAffineStabilizer X

theorem affine_diagonal_iff_affine_closed_stabilizers
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [AffineDiagonalStabilizerLaws (C := C)]
    (hnoetherian : Prop) (hnoetherianProof : hnoetherian)
    (hresolution : HasResolutionProperty X) :
    HasAffineDiagonal X ↔ ClosedPointsHaveAffineStabilizer X :=
  AffineDiagonalStabilizerLaws.affineIffStabilizers X hnoetherian
    hnoetherianProof hresolution

class SmoothSeparatedDMQuotientLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  quotient : ∀ (X : C) (_hsmooth : IsSmoothStack X)
    (_hseparated : IsSeparatedStack X) (hgenericallyTame : Prop)
    (_hgenericallyTameProof : hgenericallyTame)
    (_hDM : IsDeligneMumfordStack X) (hcoarseQuasiProjective : Prop)
    (_hcoarseQuasiProjectiveProof : hcoarseQuasiProjective),
    IsGlobalQuotient X

theorem smooth_separated_generically_tame_quasi_projective_is_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [SmoothSeparatedDMQuotientLaws (C := C)]
    (hsmooth : IsSmoothStack X) (hseparated : IsSeparatedStack X)
    (hgenericallyTame : Prop) (hgenericallyTameProof : hgenericallyTame)
    (hDM : IsDeligneMumfordStack X) (hcoarseQuasiProjective : Prop)
    (hcoarseQuasiProjectiveProof : hcoarseQuasiProjective) :
    IsGlobalQuotient X :=
  SmoothSeparatedDMQuotientLaws.quotient X hsmooth hseparated
    hgenericallyTame hgenericallyTameProof hDM hcoarseQuasiProjective
    hcoarseQuasiProjectiveProof

structure OpenFiniteGroupQuotientChart {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  openSubstack : C
  inclusion : openSubstack ⟶ X
  openImmersion : Prop
  affineScheme : C
  affineSchemeIsScheme : IsScheme affineScheme
  finiteGroup : Type u
  groupStructure : Group finiteGroup
  finiteGroupStructure : Finite finiteGroup
  quotientMap : affineScheme ⟶ openSubstack
  quotientByFiniteGroup : Prop
  covers : Prop

def HasOpenCoverByFiniteGroupSchemeQuotients {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
    ∃ ι : Type u, Nonempty ι ∧ ∃ U : ι → OpenFiniteGroupQuotientChart X,
    ∀ i, (U i).covers

class ZariskiLocalQuotientLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  localIffCover : ∀ (X : C) (_hcoarseScheme : CoarseSpaceIsScheme X),
    IsZariskiLocalQuotient X ↔ HasOpenCoverByFiniteGroupSchemeQuotients X

theorem zariski_local_quotient_iff_open_finite_group_quotient_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [ZariskiLocalQuotientLaws (C := C)]
    (hcoarseScheme : CoarseSpaceIsScheme X) :
    IsZariskiLocalQuotient X ↔ HasOpenCoverByFiniteGroupSchemeQuotients X :=
  ZariskiLocalQuotientLaws.localIffCover X hcoarseScheme

structure SmoothProperProjectiveEmbedding {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  ambient : C
  smooth : IsSmoothStack ambient
  ambientDeligneMumford : IsDeligneMumfordStack ambient
  proper : IsProperStack ambient
  projectiveCoarse : CoarseSpaceIsProjective ambient
  embedding : X ⟶ ambient
  isClosedEmbedding : Prop

def IsProjectiveDMStackByEmbedding {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (SmoothProperProjectiveEmbedding X)

def ProperCharacteristicZeroDMQuotientCriterion
    {C : Type u} [Category.{v} C] [StackCategory C] (X Y : C) : Prop :=
  (∃ q : X ⟶ Y, IsCoarseModuliSpaceMap q) ∧ CoarseSpaceIsProjective Y ∧
    (IsGlobalQuotient X ↔ HasGeneratingSheaf X) ∧
    (HasGeneratingSheaf X ↔ IsProjectiveDMStackByEmbedding X)

class ProperDMQuotientCriterionLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  criterion : ∀ (X Y : C) (_hproper : IsProperStack X)
    (_hDM : IsDeligneMumfordStack X) (hcharZero : Prop)
    (_hcharZeroProof : hcharZero) (q : X ⟶ Y)
    (_hcoarseMap : IsCoarseModuliSpaceMap q) (_hcoarse : CoarseSpaceIsProjective Y),
    ProperCharacteristicZeroDMQuotientCriterion X Y

theorem proper_dm_projective_quotient_criterion
    {C : Type u} [Category.{v} C] [StackCategory C] (X Y : C)
    [ProperDMQuotientCriterionLaws (C := C)]
    (hproper : IsProperStack X) (hDM : IsDeligneMumfordStack X)
    (hcharZero : Prop) (hcharZeroProof : hcharZero)
    (q : X ⟶ Y) (hcoarseMap : IsCoarseModuliSpaceMap q)
    (hcoarse : CoarseSpaceIsProjective Y) :
    ProperCharacteristicZeroDMQuotientCriterion X Y :=
  ProperDMQuotientCriterionLaws.criterion X Y hproper hDM hcharZero
    hcharZeroProof q hcoarseMap hcoarse

class ProjectiveDMStackDefinitionLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  projectiveIffEmbedding : ∀ (X : C), IsDeligneMumfordStack X →
    (IsProjectiveStack X ↔ IsProjectiveDMStackByEmbedding X)

theorem projective_dm_stack_definition
    {C : Type u} [Category.{v} C] [StackCategory C]
    [ProjectiveDMStackDefinitionLaws (C := C)] (X : C) :
    IsDeligneMumfordStack X →
      (IsProjectiveStack X ↔ IsProjectiveDMStackByEmbedding X) := by
  intro hDM
  exact ProjectiveDMStackDefinitionLaws.projectiveIffEmbedding (X := X) hDM

def EverySmoothDMStackOfDimensionIsQuotient {C : Type u} [Category.{v} C]
    [StackCategory C] (n : ℕ) (hcharZero : Prop) : Prop :=
  hcharZero ∧ ∀ X : C, IsSmoothStack X → IsDeligneMumfordStack X →
    StackDimension X = n → IsGlobalQuotient X

structure QuotientStratum {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  stratum : C
  inclusion : stratum ⟶ X
  locallyClosed : Prop
  quotient : IsGlobalQuotient stratum

structure QuotientStratification {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  length : ℕ
  positiveLength : 0 < length
  strata : Fin length → QuotientStratum X
  strataAreLocallyClosedQuotients : ∀ i,
    (strata i).locallyClosed ∧ IsGlobalQuotient (strata i).stratum
  covers : Prop

structure AzumayaCohomologicalBrauerComparison (C : Type u)
    [Category.{v} C] [StackCategory C] (n : ℕ) where
  azumayaBrauerGroup : Type u
  [azumayaGroupStructure : AddCommGroup azumayaBrauerGroup]
  cohomologicalBrauerGroup : Type u
  [cohomologicalGroupStructure : AddCommGroup cohomologicalBrauerGroup]
  comparison : azumayaBrauerGroup ≃+ cohomologicalBrauerGroup

attribute [instance] AzumayaCohomologicalBrauerComparison.azumayaGroupStructure
  AzumayaCohomologicalBrauerComparison.cohomologicalGroupStructure

def AzumayaEqualsCohomologicalBrauerInDimension {C : Type u}
    [Category.{v} C] [StackCategory C] (n : ℕ) : Prop :=
  ∃ D : AzumayaCohomologicalBrauerComparison C n,
    Nonempty (D.azumayaBrauerGroup ≃+ D.cohomologicalBrauerGroup)

class KreschVistoliDimensionLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  dimensionIffBrauer : ∀ (n : ℕ) (hcharZero : Prop)
    (_hcharZeroProof : hcharZero),
    EverySmoothDMStackOfDimensionIsQuotient (C := C) n hcharZero ↔
      AzumayaEqualsCohomologicalBrauerInDimension (C := C) n

theorem Kresch_Vistoli_dimension_equivalence
    {C : Type u} [Category.{v} C] [StackCategory C] (n : ℕ)
    [KreschVistoliDimensionLaws (C := C)]
    (hcharZero : Prop) (hcharZeroProof : hcharZero) :
    EverySmoothDMStackOfDimensionIsQuotient (C := C) n hcharZero ↔
      AzumayaEqualsCohomologicalBrauerInDimension (C := C) n :=
  KreschVistoliDimensionLaws.dimensionIffBrauer n hcharZero hcharZeroProof

def StratifiedByQuotientStacks {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (QuotientStratification X)

class QuotientStratificationLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  stratified : ∀ (X : C) (_hartin : IsArtinStack X)
    (_hfiniteType : IsFiniteTypeStack X) (hreduced : Prop)
    (_hreducedProof : hreduced) (haffineStabilizers : Prop)
    (_haffineStabilizersProof : haffineStabilizers),
    StratifiedByQuotientStacks X

theorem reduced_artin_stack_stratified_by_quotients
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [QuotientStratificationLaws (C := C)]
    (hartin : IsArtinStack X) (hfiniteType : IsFiniteTypeStack X)
    (hreduced : Prop) (hreducedProof : hreduced)
    (haffineStabilizers : Prop) (haffineStabilizersProof : haffineStabilizers) :
    StratifiedByQuotientStacks X :=
  QuotientStratificationLaws.stratified X hartin hfiniteType hreduced
    hreducedProof haffineStabilizers haffineStabilizersProof

structure EtaleLocallyAffineFiniteStabilizerQuotientData
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C) where
  chartForPoint : ∀ _x : Point X, C
  chartMapForPoint : ∀ (_x : Point X), chartForPoint _x ⟶ X
  chartIsAlgebraicSpace : ∀ _x : Point X, IsAlgebraicSpace (chartForPoint _x)
  affineForPoint : ∀ _x : Point X, Prop
  finiteStabilizerGroupForPoint : ∀ _x : Point X, Prop
  quotientByFiniteStabilizerForPoint : ∀ _x : Point X, Prop
  etaleForPoint : ∀ _x : Point X,
    IsEtaleMorphism (chartMapForPoint _x)

def EtaleLocallyAffineFiniteStabilizerQuotient {C : Type u}
    [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  IsEtaleLocalQuotient X ∧ Nonempty (EtaleLocallyAffineFiniteStabilizerQuotientData X)

class SeparatedDMEtaleLocalQuotientLaws {C : Type u}
    [Category.{v} C] [StackCategory C] where
  quotient : ∀ (X : C), IsSeparatedStack X → IsDeligneMumfordStack X →
    EtaleLocallyAffineFiniteStabilizerQuotient X

class TameEtaleLocalQuotientLaws' {C : Type u}
    [Category.{v} C] [StackCategory C] where
  quotient : ∀ (X : C), IsTameArtinStack X →
    EtaleLocallyAffineFiniteStabilizerQuotient X

theorem separated_dm_stack_etale_locally_affine_finite_group_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [SeparatedDMEtaleLocalQuotientLaws (C := C)]
    (hseparated : IsSeparatedStack X) (hDM : IsDeligneMumfordStack X) :
    EtaleLocallyAffineFiniteStabilizerQuotient X :=
  SeparatedDMEtaleLocalQuotientLaws.quotient X hseparated hDM

theorem tame_stack_etale_locally_affine_stabilizer_quotient
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [TameEtaleLocalQuotientLaws' (C := C)]
    (htame : IsTameArtinStack X) :
    EtaleLocallyAffineFiniteStabilizerQuotient X :=
  TameEtaleLocalQuotientLaws'.quotient X htame

structure LocalQuotientSliceData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  closedPoint : Point X
  stabilizer : Type u
  stabilizerGroup : Group stabilizer
  linearlyReductive : Prop
  algebraicSpace : C
  algebraicSpaceIsAlgebraicSpace : IsAlgebraicSpace algebraicSpace
  chart : C
  chartMap : chart ⟶ X
  etale : IsEtaleMorphism chartMap
  quotientByStabilizer : Prop
  formallyLocal : Prop

class LocalQuotientSliceLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  slice : ∀ {X : C} (x : Point X) (_hclosed : IsClosedPoint x)
    (hlinearlyReductive : Prop) (_hlinearlyReductiveProof : hlinearlyReductive),
    ∃ D : LocalQuotientSliceData X, D.closedPoint = x ∧ D.formallyLocal

theorem local_quotient_slice_formal_statement
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    [LocalQuotientSliceLaws (C := C)]
    (x : Point X) (hclosed : IsClosedPoint x) (hlinearlyReductive : Prop)
    (hlinearlyReductiveProof : hlinearlyReductive) :
    ∃ D : LocalQuotientSliceData X, D.closedPoint = x ∧ D.formallyLocal :=
  LocalQuotientSliceLaws.slice x hclosed hlinearlyReductive
    hlinearlyReductiveProof

class LunaSliceLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  etaleLocal : ∀ (X : C) (_hquotient : IsGlobalQuotient X)
    (hlinearlyReductive : Prop) (_hlinearlyReductiveProof : hlinearlyReductive),
    IsEtaleLocalQuotient X

theorem luna_slice_for_linearly_reductive_quotient_stack
    {C : Type u} [Category.{v} C] [StackCategory C]
    [LunaSliceLaws (C := C)] (X : C) (hquotient : IsGlobalQuotient X)
    (hlinearlyReductive : Prop)
    (hlinearlyReductiveProof : hlinearlyReductive) :
    IsEtaleLocalQuotient X :=
  LunaSliceLaws.etaleLocal X hquotient hlinearlyReductive
    hlinearlyReductiveProof

end Formalization.Books.Guide.Unit05
