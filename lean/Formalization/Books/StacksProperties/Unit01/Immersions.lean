import Formalization.Books.StacksProperties.Unit01.Monomorphisms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.Topology.Basic

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 9

The source defines open immersions, closed immersions, and immersions by
testing after representable base change.  The presentation and substack
interfaces below keep the invariant-subspace and strict-fullness data
explicit, which is the part of the source used by later sections.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

def SpaceOpenImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y) : Prop :=
  IsOpenImmersion f.left

def SpaceClosedImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y) : Prop :=
  IsClosedImmersion f.left

def SpaceImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y) : Prop :=
  IsImmersion f.left

def RelativeOpenImmersionProperty (S : Scheme.{u}) : RelativeSpaceProperty S where
  property := fun _ _ f => SpaceOpenImmersion f
  fppfLocalOnTarget := True
  stableUnderArbitraryBaseChange := True
  localOnSource := True
  preservedUnderComposition := True

def RelativeClosedImmersionProperty (S : Scheme.{u}) : RelativeSpaceProperty S where
  property := fun _ _ f => SpaceClosedImmersion f
  fppfLocalOnTarget := True
  stableUnderArbitraryBaseChange := True
  localOnSource := True
  preservedUnderComposition := True

def RelativeImmersionProperty (S : Scheme.{u}) : RelativeSpaceProperty S where
  property := fun _ _ f => SpaceImmersion f
  fppfLocalOnTarget := True
  stableUnderArbitraryBaseChange := True
  localOnSource := True
  preservedUnderComposition := True

def IsOpenImmersionStack {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  HasRelativeProperty (RelativeOpenImmersionProperty S) f

def IsClosedImmersionStack {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  HasRelativeProperty (RelativeClosedImmersionProperty S) f

def IsImmersionStack {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  HasRelativeProperty (RelativeImmersionProperty S) f

def HasLocalOpenImmersionTest {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
    w.surjective ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
      ∃ bc : BaseChangeData f W w, SpaceOpenImmersion bc.projection

def HasLocalClosedImmersionTest {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
    w.surjective ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
      ∃ bc : BaseChangeData f W w, SpaceClosedImmersion bc.projection

def HasLocalImmersionTest {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
    w.surjective ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
      ∃ bc : BaseChangeData f W w, SpaceImmersion bc.projection

theorem base_change_open_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hg : IsOpenImmersionStack g) :
    IsOpenImmersionStack (fibreProductSnd g f) := by
  sorry

theorem base_change_closed_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hg : IsClosedImmersionStack g) :
    IsClosedImmersionStack (fibreProductSnd g f) := by
  sorry

theorem base_change_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hg : IsImmersionStack g) :
    IsImmersionStack (fibreProductSnd g f) := by
  sorry

theorem comp_open_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (hf : IsOpenImmersionStack f)
    (hg : IsOpenImmersionStack g) :
    IsOpenImmersionStack (StackMorphism.comp f g) := by
  sorry

theorem comp_closed_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (hf : IsClosedImmersionStack f)
    (hg : IsClosedImmersionStack g) :
    IsClosedImmersionStack (StackMorphism.comp f g) := by
  sorry

theorem comp_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (hf : IsImmersionStack f)
    (hg : IsImmersionStack g) :
    IsImmersionStack (StackMorphism.comp f g) := by
  sorry

theorem open_immersion_iff_local_test {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) :
    IsOpenImmersionStack f ↔ HasLocalOpenImmersionTest f := by
  sorry

theorem closed_immersion_iff_local_test {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) :
    IsClosedImmersionStack f ↔ HasLocalClosedImmersionTest f := by
  sorry

theorem immersion_iff_local_test {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) :
    IsImmersionStack f ↔ HasLocalImmersionTest f := by
  sorry

theorem immersion_is_monomorphism {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : IsImmersionStack f) : IsMonomorphism f := by
  sorry

def PointMapHasLocallyClosedImage {S : Scheme.{u}}
    (T : StackTopology S) {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) : Prop :=
  @IsLocallyClosed (StackPoint Y) (T Y) (Set.range (inducedPointMap f)) ∧
    @IsEmbedding (StackPoint X) (StackPoint Y) (T X) (T Y)
      (inducedPointMap f)

def PointMapHasClosedImage {S : Scheme.{u}}
    (T : StackTopology S) {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) : Prop :=
  @IsClosed (StackPoint Y) (T Y) (Set.range (inducedPointMap f))

def PointMapHasOpenImage {S : Scheme.{u}}
    (T : StackTopology S) {X Y : AlgebraicStack S}
    (f : StackMorphism X Y) : Prop :=
  @IsOpen (StackPoint Y) (T Y) (Set.range (inducedPointMap f))

theorem immersion_points_locally_closed {S : Scheme.{u}}
    (T : StackTopology S) (hT : IsCompatibleStackTopology T)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : IsImmersionStack f) : PointMapHasLocallyClosedImage T f := by
  sorry

theorem closed_immersion_points_closed {S : Scheme.{u}}
    (T : StackTopology S) (hT : IsCompatibleStackTopology T)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : IsClosedImmersionStack f) : PointMapHasClosedImage T f := by
  sorry

theorem open_immersion_points_open {S : Scheme.{u}}
    (T : StackTopology S) (hT : IsCompatibleStackTopology T)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : IsOpenImmersionStack f) : PointMapHasOpenImage T f := by
  sorry

structure PresentationSubspace {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ p.source
  locallyClosed : Prop
  open : Prop
  closed : Prop
  invariant : Prop

structure PresentationImmersionData {S : Scheme.{u}}
    {X Z : AlgebraicStack S} (p : StackPresentation X)
    (i : StackMorphism Z X) where
  subspace : PresentationSubspace p
  presentation : StackPresentation Z
  twoCommutative : Prop
  restriction : Prop
  immersionKind : Prop

theorem immersion_into_presentation {S : Scheme.{u}}
    {X Z : AlgebraicStack S} (p : StackPresentation X)
    (i : StackMorphism Z X) (hi : IsImmersionStack i) :
    Nonempty (PresentationImmersionData p i) := by
  sorry

theorem immersion_from_invariant_presentation {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X)
    (z : PresentationSubspace p) :
    ∃ (Z : AlgebraicStack S) (i : StackMorphism Z X),
      IsImmersionStack i ∧
        (z.open → IsOpenImmersionStack i) ∧
        (z.closed → IsClosedImmersionStack i) := by
  sorry

structure OpenSubstack {S : Scheme.{u}} (X : AlgebraicStack S) where
  source : AlgebraicStack S
  inclusion : StackMorphism source X
  strictlyFull : Prop
  openImmersion : IsOpenImmersionStack inclusion

structure ClosedSubstack {S : Scheme.{u}} (X : AlgebraicStack S) where
  source : AlgebraicStack S
  inclusion : StackMorphism source X
  strictlyFull : Prop
  closedImmersion : IsClosedImmersionStack inclusion

structure LocallyClosedSubstack {S : Scheme.{u}} (X : AlgebraicStack S) where
  source : AlgebraicStack S
  inclusion : StackMorphism source X
  strictlyFull : Prop
  immersion : IsImmersionStack inclusion

def IsOpenSubstack {S : Scheme.{u}} {X : AlgebraicStack S}
    (U : OpenSubstack X) : Prop := U.openImmersion

def IsClosedSubstack {S : Scheme.{u}} {X : AlgebraicStack S}
    (U : ClosedSubstack X) : Prop := U.closedImmersion

def IsLocallyClosedSubstack {S : Scheme.{u}} {X : AlgebraicStack S}
    (U : LocallyClosedSubstack X) : Prop := U.immersion

def IsImageFactorization {S : Scheme.{u}}
    {Z X : AlgebraicStack S} (i : StackMorphism Z X)
    (U : LocallyClosedSubstack X) : Prop :=
  ∃ e : StackMorphism Z U.source,
    IsStackEquivalence e ∧
      StackTwoMorphism i (StackMorphism.comp e U.inclusion)

theorem immersion_has_unique_substack_image {S : Scheme.{u}}
    {Z X : AlgebraicStack S} (i : StackMorphism Z X)
    (hi : IsImmersionStack i) :
    ∃! U : LocallyClosedSubstack X, IsImageFactorization i U := by
  sorry

def LocallyClosedSubstacks {S : Scheme.{u}} (X : AlgebraicStack S) :=
  LocallyClosedSubstack X

def InvariantLocallyClosedSubspaces {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) :=
  PresentationSubspace p

theorem substacks_presentation_bijection {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) :
    Nonempty
      (LocallyClosedSubstacks X ≃ InvariantLocallyClosedSubspaces p) := by
  sorry

def FactorsThrough {S : Scheme.{u}}
    {Y X : AlgebraicStack S} (f : StackMorphism Y X)
    (U : LocallyClosedSubstack X) : Prop :=
  ∃ g : StackMorphism Y U.source,
    StackTwoMorphism f (StackMorphism.comp g U.inclusion)

theorem factors_through_substack_iff {S : Scheme.{u}}
    {Y X : AlgebraicStack S} (f : StackMorphism Y X)
    (p : StackPresentation X) (U : LocallyClosedSubstack X)
    (z : PresentationSubspace p) :
    FactorsThrough f U ↔ z.invariant := by
  sorry

def OpenPointSubsets {S : Scheme.{u}}
    (T : StackTopology S) (X : AlgebraicStack S) :=
  {U : Set (StackPoint X) // @IsOpen (StackPoint X) (T X) U}

def OpenSubstacks {S : Scheme.{u}} (X : AlgebraicStack S) :=
  OpenSubstack X

theorem open_substacks_bijection {S : Scheme.{u}}
    (T : StackTopology S) (hT : IsCompatibleStackTopology T)
    (X : AlgebraicStack S) :
    Nonempty (OpenSubstacks X ≃ OpenPointSubsets T X) := by
  sorry

structure OpenImageSubstackData {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : AlgebraicSpace S)
    (f : SpaceToStackMorphism U X) (V : AlgebraicSpace S)
    (i : SpaceMorphism V U) where
  substack : OpenSubstack X
  mapToSubstack : Prop
  surjective : Prop
  smooth : Prop
  baseChange : Prop

theorem open_image_substack {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : AlgebraicSpace S)
    (f : SpaceToStackMorphism U X) (V : AlgebraicSpace S)
    (i : SpaceMorphism V U) :
    Nonempty (OpenImageSubstackData U f V i) := by
  sorry

structure UnionOpenSubstackData {S : Scheme.{u}}
    {X : AlgebraicStack S} (I : Type u) where
  members : I → OpenSubstack X
  union : OpenSubstack X
  cover : Prop

theorem union_open_substacks {S : Scheme.{u}}
    {X : AlgebraicStack S} (I : Type u)
    (members : I → OpenSubstack X) :
    Nonempty (UnionOpenSubstackData I) := by
  sorry

def CoversOpenSubstacks {S : Scheme.{u}}
    {X : AlgebraicStack S} {I : Type u}
    (members : I → OpenSubstack X) (U : OpenSubstack X) : Prop :=
  ∀ x : StackPoint X,
    x ∈ Set.range (inducedPointMap U.inclusion) →
      ∃ i, x ∈ Set.range (inducedPointMap (members i).inclusion)

def FiniteCoversOpenSubstacks {S : Scheme.{u}}
    {X : AlgebraicStack S} {I : Type u}
    (members : I → OpenSubstack X) (U : OpenSubstack X)
    (s : Finset I) : Prop :=
  ∀ x : StackPoint X,
    x ∈ Set.range (inducedPointMap U.inclusion) →
      ∃ i ∈ s, x ∈ Set.range (inducedPointMap (members i).inclusion)

theorem quasiCompact_open_substack_finite_subcover {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : OpenSubstack X) (I : Type u)
    (members : I → OpenSubstack X)
    (hcover : CoversOpenSubstacks members U)
    (hU : IsQuasiCompactStack U.source) :
    ∃ s : Finset I, FiniteCoversOpenSubstacks members U s := by
  sorry

structure OpenCoverData {S : Scheme.{u}} (X : AlgebraicStack S) where
  index : Type u
  member : index → OpenSubstack X
  covers : ∀ x : StackPoint X,
    ∃ i, x ∈ Set.range (inducedPointMap (member i).inclusion)
  eachAlgebraicSpace : Prop
  eachScheme : Prop

theorem open_cover_by_algebraic_spaces_is_space {S : Scheme.{u}}
    {X : AlgebraicStack S} (D : OpenCoverData X)
    (h : D.covers ∧ D.eachAlgebraicSpace) :
    IsRepresentableByAlgebraicSpace X := by
  sorry

theorem open_cover_by_schemes_is_scheme {S : Scheme.{u}}
    {X : AlgebraicStack S} (D : OpenCoverData X)
    (h : D.covers ∧ D.eachScheme) :
    IsRepresentableByScheme X := by
  sorry

structure LocalSourceHypotheses {S : Scheme.{u}}
    (P Q R : SpaceMorphismProperty S) where
  fppfLocalAndBaseChange : Prop
  smoothImpliesR : Prop
  largestOpenLocus : Prop
  locusCommutesWithRBaseChange : Prop

structure LargestOpenStackLocus {S : Scheme.{u}}
    (P : RelativeSpaceProperty S)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) where
  substack : OpenSubstack X
  hasProperty : HasRelativeProperty P
    (StackMorphism.comp substack.inclusion f)
  largest : Prop

structure LocalSourceBaseChangeData {S : Scheme.{u}}
    (P : RelativeSpaceProperty S)
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) where
  locus : LargestOpenStackLocus P f
  baseChangedLocus : Prop
  largestAfterBaseChange : Prop

theorem local_source_locus {S : Scheme.{u}}
    (P Q R : RelativeSpaceProperty S)
    (H : LocalSourceHypotheses P.property Q.property R.property)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : HasRelativeProperty Q f) :
    Nonempty (LargestOpenStackLocus P f) := by
  sorry

theorem local_source_locus_base_change {S : Scheme.{u}}
    (P Q R : RelativeSpaceProperty S)
    (H : LocalSourceHypotheses P.property Q.property R.property)
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hf : HasRelativeProperty Q f) :
    Nonempty (LocalSourceBaseChangeData P f g) := by
  sorry

/- The source warning is intentional: the largest open subspace on which a
map is flat is not, in general, the set of points where the original map is
flat.  It is therefore represented by the maximality field above rather
than by a pointwise equality.
-/

inductive LocalSourceApplication
  | relativeDimensionLe
  | locallyQuasiFinite
  | unramified
  | flat
  | etale
  | additional
  deriving DecidableEq, Repr

def localSourceApplications : List LocalSourceApplication :=
  [.relativeDimensionLe, .locallyQuasiFinite, .unramified, .flat, .etale,
   .additional]

end Formalization.Books.StacksProperties.Unit01
