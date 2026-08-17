import Mathlib.Data.Set.Lattice
import Formalization.Books.StacksMorphisms.Unit07.QuasiCompactMorphisms

/-!
# A Guide to the Literature, Chapter 5: shared interfaces

The project does not yet contain a native category of algebraic stacks.  The
earlier morphisms chapter supplies the canonical category-level interface, so
the declarations below use that interface and add only the properties which
are needed by the papers surveyed in this chapter.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.StacksMorphisms.Unit07

universe u v

namespace Formalization.Books.Guide.Unit05

/-! ## Algebraic-stack properties used throughout the chapter -/

class StackCategory (C : Type u) [Category.{v} C]
    extends Formalization.Books.StacksMorphisms.Unit07.AlgebraicStackCategory C where
  isScheme : C → Prop
  isArtin : C → Prop
  isDeligneMumford : C → Prop
  isNormal : C → Prop
  isSmooth : C → Prop
  isProper : C → Prop
  isSeparated : C → Prop
  isFiniteType : C → Prop
  isQuasiAffine : C → Prop
  isQuasiProjective : C → Prop
  hasQuasiFiniteDiagonal : C → Prop
  isProjective : C → Prop
  finiteInertia : C → Prop
  finiteStabilizer : C → Prop
  genericallyTrivialStabilizer : C → Prop
  linearlyReductiveStabilizers : C → Prop
  hasAffineDiagonal : C → Prop
  hasResolutionProperty : C → Prop
  hasGeneratingSheaf : C → Prop
  coarseSpaceIsScheme : C → Prop
  coarseSpaceIsProjective : C → Prop
  isGlobalQuotient : C → Prop
  isZariskiLocalQuotient : C → Prop
  isEtaleLocalQuotient : C → Prop
  isStackQuotientByFiniteGroup : C → Prop
  isToric : C → Prop
  dimension : C → ℕ
  isFiniteMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isProperMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isSeparatedMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isQuasiFiniteMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isFiniteTypeMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isLocallyFiniteTypeMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isEtaleMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isSmoothMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isUniversallyClosedMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isUniversallySubmersiveMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isFppfMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  isGenericallyEtaleMorphism : ∀ {X Y : C}, (X ⟶ Y) → Prop
  exactOnQuasiCoherent : ∀ {X Y : C}, (X ⟶ Y) → Prop
  structureSheafPushforwardIsIso : ∀ {X Y : C}, (X ⟶ Y) → Prop
  vectorBundle : C → Type u
  vectorBundleDescends : ∀ {X Y : C}, (X ⟶ Y) → vectorBundle X → Prop
  vectorBundleHasTrivialClosedPointRepresentations :
    ∀ {X : C}, vectorBundle X → Prop

/-!
TODO(proof agents): the fields of `StackCategory` deliberately record only
predicates and data; they do not imply the comparison theorems surveyed in
this chapter. Add a separate `StackCategoryLaws`/`Unit05Results` typeclass for
the required implications and constructions instead of enlarging this data
interface. Keep those law bundles small (for example, coarse-moduli,
quotient, or approximation laws), and make each theorem request only the
narrow bundle that supplies its mathematical input.
-/

abbrev StackObject (C : Type u) := C

abbrev StackMorphism {C : Type u} [Category.{v} C]
    [StackCategory C] (X Y : C) := X ⟶ Y

def IsScheme {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isScheme X

def IsAlgebraicSpace {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  Formalization.Books.StacksMorphisms.Unit07.IsAlgebraicSpace X

def IsArtinStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isArtin X

def IsDeligneMumfordStack {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.isDeligneMumford X

def IsNormalStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isNormal X

def IsSmoothStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isSmooth X

def IsProperStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isProper X

def IsSeparatedStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isSeparated X

def IsFiniteTypeStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isFiniteType X

def IsQuasiAffineStack {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.isQuasiAffine X

def HasQuasiFiniteDiagonal {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.hasQuasiFiniteDiagonal X

def IsQuasiProjectiveStack {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.isQuasiProjective X

def IsProjectiveStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isProjective X

def HasFiniteInertia {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.finiteInertia X

def HasFiniteStabilizer {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.finiteStabilizer X

def HasGenericallyTrivialStabilizer {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.genericallyTrivialStabilizer X

def HasLinearlyReductiveStabilizers {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.linearlyReductiveStabilizers X

def HasAffineDiagonal {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.hasAffineDiagonal X

def HasResolutionProperty {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.hasResolutionProperty X

def HasGeneratingSheaf {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.hasGeneratingSheaf X

def CoarseSpaceIsScheme {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.coarseSpaceIsScheme X

def CoarseSpaceIsProjective {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.coarseSpaceIsProjective X

def IsGlobalQuotient {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isGlobalQuotient X

def IsZariskiLocalQuotient {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.isZariskiLocalQuotient X

def IsEtaleLocalQuotient {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.isEtaleLocalQuotient X

def IsStackQuotientByFiniteGroup {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  StackCategory.isStackQuotientByFiniteGroup X

def IsToricStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  StackCategory.isToric X

def StackDimension {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : ℕ :=
  StackCategory.dimension X

def IsFiniteMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isFiniteMorphism f

def IsProperMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isProperMorphism f

def IsSeparatedMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isSeparatedMorphism f

def IsQuasiFiniteMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isQuasiFiniteMorphism f

def IsFiniteTypeMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isFiniteTypeMorphism f

def IsLocallyFiniteTypeMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isLocallyFiniteTypeMorphism f

def IsEtaleMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isEtaleMorphism f

def IsSmoothMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isSmoothMorphism f

def IsUniversallyClosedMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isUniversallyClosedMorphism f

def IsUniversallySubmersiveMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isUniversallySubmersiveMorphism f

def IsFppfMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isFppfMorphism f

def IsGenericallyEtaleMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.isGenericallyEtaleMorphism f

def IsQuasiCompactMorphism {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  ExistingQuasiCompact f

def ExactOnQuasiCoherent {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.exactOnQuasiCoherent f

def StructureSheafPushforwardIsIso {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  StackCategory.structureSheafPushforwardIsIso f

abbrev VectorBundle {C : Type u} [Category.{v} C] [StackCategory C] (X : C) :=
  StackCategory.vectorBundle X

def VectorBundleDescends {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) (V : VectorBundle X) : Prop :=
  StackCategory.vectorBundleDescends f V

def TrivialClosedPointRepresentations {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (V : VectorBundle X) : Prop :=
  StackCategory.vectorBundleHasTrivialClosedPointRepresentations V

/-! ## Points, closure equivalence, and coarse spaces -/

abbrev Point {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Type u :=
  Formalization.Books.StacksMorphisms.Unit07.Point X

def stackPointMap {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Point X → Point Y :=
  Formalization.Books.StacksMorphisms.Unit07.pointMap f

def IsClosedPoint {C : Type u} [Category.{v} C] [StackCategory C]
    {X : C} (x : Point X) : Prop :=
  IsClosed ({x} : Set (Point X))

def ClosureEquivalent {α : Type u} [TopologicalSpace α] (x y : α) : Prop :=
  closure ({x} : Set α) = closure ({y} : Set α)

def FibresAreClosureEquivalence {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (q : X ⟶ Y) : Prop :=
  ∀ x₁ x₂ : Point X, stackPointMap q x₁ = stackPointMap q x₂ ↔
    ClosureEquivalent x₁ x₂

def IsCoarseModuliSpaceMap {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (q : X ⟶ Y) : Prop :=
  IsAlgebraicSpace Y ∧
    Function.Bijective (stackPointMap q) ∧
    (∀ (Z : C), IsAlgebraicSpace Z → ∀ (f : X ⟶ Z),
      ∃! g : Y ⟶ Z, q ≫ g = f)

def IsModuliSpaceMap {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  IsAlgebraicSpace Y ∧ IsProperMorphism f ∧
    Function.Bijective (stackPointMap f)

structure CoarseModuliSpaceData {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) where
  space : C
  map : X ⟶ space
  isCoarse : IsCoarseModuliSpaceMap map

def HasCoarseModuliSpace {C : Type u} [Category.{v} C] [StackCategory C]
    (X : C) : Prop :=
  Nonempty (CoarseModuliSpaceData X)

def HasSeparatedCoarseModuliSpace {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ (Y : C) (q : X ⟶ Y), IsCoarseModuliSpaceMap q ∧ IsSeparatedMorphism q

def TameByExactPushforward {C : Type u} [Category.{v} C]
    [StackCategory C] {X Y : C} (q : X ⟶ Y) : Prop :=
  IsCoarseModuliSpaceMap q ∧ ExactOnQuasiCoherent q

/-! ## Tame and good moduli spaces -/

def IsTameArtinStack {C : Type u} [Category.{v} C] [StackCategory C] (X : C) : Prop :=
  IsArtinStack X ∧ HasFiniteInertia X ∧
    ∃ (Y : C) (q : X ⟶ Y), TameByExactPushforward q

def IsGoodModuliSpace {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (q : X ⟶ Y) : Prop :=
  IsArtinStack X ∧ IsAlgebraicSpace Y ∧ IsQuasiCompactMorphism q ∧
    StructureSheafPushforwardIsIso q ∧ ExactOnQuasiCoherent q

structure GoodModuliSpaceProperties {C : Type u} [Category.{v} C]
    [StackCategory C] {X Y : C} (q : X ⟶ Y) where
  surjective : Surjective q
  universallyClosed : IsUniversallyClosedMorphism q
  universallySubmersive : IsUniversallySubmersiveMorphism q
  closureIdentification : FibresAreClosureEquivalence q
  universalForAlgebraicSpaces :
    ∀ (Z : C), IsAlgebraicSpace Z → ∀ (f : X ⟶ Z),
      ∃! g : Y ⟶ Z, q ≫ g = f
  stableUnderArbitraryBaseChange : ∀ (Z : C) (_g : Z ⟶ Y), Prop
  vectorBundleDescent : ∀ (V : VectorBundle X),
    VectorBundleDescends q V ↔ TrivialClosedPointRepresentations V

/-! ## Small, reusable geometric data structures -/

structure EffectiveCartierDivisor {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  carrier : Set (Point X)
  effective : Prop
  effectiveProof : effective
  Cartier : Prop
  CartierProof : Cartier

structure GroupActionData (G X : Type u) [Group G] where
  action : G → X → X
  one_action : ∀ x, action 1 x = x
  mul_action : ∀ g h x, action (g * h) x = action g (action h x)

structure LineBundleData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  underlying : Type u
  invertible : Prop
  invertibleProof : invertible
  totalSpace : Point X → underlying → Prop

structure GerbeData where
  band : Type u
  locallyNonempty : Prop
  locallyConnected : Prop

structure FinitePresentationData where
  finite : Prop
  finitelyPresented : Prop

end Formalization.Books.Guide.Unit05
