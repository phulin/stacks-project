import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 9: Hilbert, Quot, Hom, and branchvariety stacks
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

structure HilbertStackData {C : Type u} [Category.{v} C]
    [StackCategory C] (X S : C) where
  sheaf : Type u
  structureMap : X ⟶ S
  separated : IsSeparatedStack X
  locallyFiniteType : IsFiniteTypeStack X
  baseLocallyNoetherian : Prop
  baseLocallySeparated : Prop
  parameterizesFiniteUnramifiedProperSchemes : Prop
  hilbertStack : C

theorem hilbert_stack_is_algebraic
    {C : Type u} [Category.{v} C] [StackCategory C] {X S : C}
    (D : HilbertStackData X S) :
    IsArtinStack D.hilbertStack := by
  sorry

structure HomStackData {C : Type u} [Category.{v} C]
    [StackCategory C] (T X S : C) where
  sourceProper : IsProperStack T
  sourceToBase : T ⟶ S
  sourceFlatOverBase : Prop
  targetSeparated : IsSeparatedStack X
  targetLocallyFiniteType : IsFiniteTypeStack X
  baseLocallyNoetherian : Prop
  homStack : C

theorem hom_stack_from_proper_flat_source_is_algebraic
    {C : Type u} [Category.{v} C] [StackCategory C] {T X S : C}
    (D : HomStackData T X S) :
    IsArtinStack D.homStack := by
  sorry

structure QuotFunctorData {C : Type u} [Category.{v} C]
    [StackCategory C] (X S : C) where
  deligneMumford : IsDeligneMumfordStack X
  separated : IsSeparatedStack X
  locallyFinitePresentationOverBase : Prop
  module : Type u
  moduleLocallyFinitelyPresented : Prop
  quotSpace : C
  quotMap : quotSpace ⟶ S

structure QuotFunctorConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] {X S : C} (D : QuotFunctorData X S) where
  quotSpaceIsAlgebraicSpace : IsAlgebraicSpace D.quotSpace
  quotSpaceSeparated : IsSeparatedMorphism D.quotMap
  quotSpaceLocallyFinitePresentation : Prop

theorem quot_functor_is_a_separated_algebraic_space
    {C : Type u} [Category.{v} C] [StackCategory C] {X S : C}
    (D : QuotFunctorData X S) :
    Nonempty (QuotFunctorConclusion D) := by
  sorry

structure GeneratingSheafData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  tame : IsTameArtinStack X
  separated : IsSeparatedStack X
  globalFiniteGroupQuotient : IsGlobalQuotient X

structure GeneratingSheafConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} where
  generatingSheaf : VectorBundle X
  generates : HasGeneratingSheaf X

theorem tame_separated_finite_group_quotient_has_generating_sheaf
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : GeneratingSheafData X) :
    Nonempty (GeneratingSheafConclusion (X := X)) := by
  sorry

structure HomStackFiniteDiagonalData {C : Type u} [Category.{v} C]
    [StackCategory C] (X Y S : C) where
  sourceArtin : IsArtinStack X
  targetArtin : IsArtinStack Y
  locallyFinitePresentation : Prop
  finiteDiagonal : Prop
  sourceProper : IsProperStack X
  sourceFlat : Prop
  fppfLocallyFiniteFlatCover : Prop
  homStack : C

structure HomStackArtinConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] {X Y S : C} (D : HomStackFiniteDiagonalData X Y S) where
  homStackArtin : IsArtinStack D.homStack
  homStackLocallyFinitePresentation : Prop

theorem hom_stack_artin_for_finite_diagonal_targets
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y S : C} (D : HomStackFiniteDiagonalData X Y S) :
    Nonempty (HomStackArtinConclusion D) := by
  sorry

structure Branchvariety {C : Type u} [Category.{v} C]
    [StackCategory C] where
  projectiveSpace : C
  projectiveSpaceIsScheme : IsScheme projectiveSpace
  projectiveSpaceIsProjective : Prop
  source : C
  sourceIsScheme : IsScheme source
  sourceReduced : Prop
  finiteMap : source ⟶ projectiveSpace
  finite : IsFiniteMorphism finiteMap

structure BranchvarietyModuliData {C : Type u} [Category.{v} C]
    [StackCategory C] where
  projectiveSpace : C
  hilbertPolynomial : Type u
  componentDegrees : ℕ → ℕ
  fixedHilbertPolynomial : Prop
  fixedTotalComponentDegrees : Prop
  moduliStack : C
  parameterizesBranchvarieties : Prop

structure BranchvarietyModuliConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] (D : BranchvarietyModuliData (C := C)) where
  proper : IsProperStack D.moduliStack
  artin : IsArtinStack D.moduliStack
  finiteStabilizer : HasFiniteStabilizer D.moduliStack
  comparesWithHilbertChowStableMap : Prop

theorem branchvariety_moduli_stack_is_proper_artin_with_finite_stabilizer
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : BranchvarietyModuliData (C := C)) :
    Nonempty (BranchvarietyModuliConclusion D) := by
  sorry

structure CoherentAlgebraStackData {C : Type u} [Category.{v} C]
    [StackCategory C] (Y : C) where
  algebraObject : Type u
  algebraOverStructureSheaf : Prop
  stack : C
  builtAsStackOfAlgebras : Prop

structure CoherentAlgebraStackConclusion where
  quotAndHomExistence : Prop

theorem coherent_algebra_stack_generalizes_branchvarieties
    {C : Type u} [Category.{v} C] [StackCategory C] {Y : C}
    (D : CoherentAlgebraStackData Y) :
    Nonempty CoherentAlgebraStackConclusion := by
  sorry

structure GAmpleLineBundleData {C : Type u} [Category.{v} C]
    [StackCategory C] (T S : C) where
  properAlgebraicSpace : IsAlgebraicSpace T
  proper : IsProperStack T
  lineBundle : LineBundleData (Point T)
  ample : Prop
  groupActionCompatible : Prop

structure StarrMappingStackData {C : Type u} [Category.{v} C]
    [StackCategory C] (X S : C) where
  stackLocallyFiniteTypeOverExcellentBase : Prop
  finiteDiagonal : Prop
  source : C
  sourceProperAlgebraicSpace : IsProperStack source
  ampleLineBundle : GAmpleLineBundleData source S
  mappingStack : C

structure StarrMappingStackConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] {X S : C} (D : StarrMappingStackData X S) where
  mappingStackArtin : IsArtinStack D.mappingStack
  mappingStackLocallyFiniteType : Prop

theorem artin_axioms_mapping_stack_theorem
    {C : Type u} [Category.{v} C] [StackCategory C] {X S : C}
    (D : StarrMappingStackData X S) :
    Nonempty (StarrMappingStackConclusion D) := by
  sorry

structure NonEffectiveHilbertDeformationExample {C : Type u}
    [Category.{v} C] [StackCategory C] where
  nonSeparatedScheme : C
  nonSeparated : ¬ IsSeparatedStack nonSeparatedScheme
  hilbertFunctor : Type u
  nonEffectiveDeformation : Prop

structure NonEffectiveHilbertConclusion where
  notRepresented : Prop

theorem hilbert_functor_nonseparated_scheme_not_represented
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : NonEffectiveHilbertDeformationExample (C := C)) :
    Nonempty NonEffectiveHilbertConclusion := by
  sorry

structure GeneralMappingStackData {C : Type u} [Category.{v} C]
    [StackCategory C] (X Y S : C) where
  sourceHypotheses : Prop
  targetHypotheses : Prop
  categoricalProperness : Prop
  mappingStack : C

structure GeneralMappingStackConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] {X Y S : C} (D : GeneralMappingStackData X Y S) where
  mappingStackAlgebraic : IsArtinStack D.mappingStack
  locallyFinitePresentation : Prop

theorem mapping_stack_algebraicity_under_categorical_properness
    {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y S : C} (D : GeneralMappingStackData X Y S) :
    Nonempty (GeneralMappingStackConclusion D) := by
  sorry

end Formalization.Books.Guide.Unit05
