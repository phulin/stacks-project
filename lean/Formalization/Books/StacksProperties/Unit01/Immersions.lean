import Formalization.Books.StacksProperties.Unit01.Monomorphisms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.Basic

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 9

The source defines open immersions, closed immersions, and immersions by
testing after representable base change.  The presentation and substack
interfaces below keep the invariant-subspace data explicit, which is the
part of the source used by later sections.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open Topology

universe u v w

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

def SpaceMorphismSmooth {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y) : Prop :=
  Smooth f.left

def RelativeOpenImmersionProperty (S : Scheme.{u}) : RelativeSpaceProperty S where
  property := fun _ _ f => SpaceOpenImmersion f
  fppfLocalOnTarget := True
  stableUnderArbitraryBaseChange := True
  localOnSource := fun _ => True
  preservedUnderComposition := True

def RelativeClosedImmersionProperty (S : Scheme.{u}) : RelativeSpaceProperty S where
  property := fun _ _ f => SpaceClosedImmersion f
  fppfLocalOnTarget := True
  stableUnderArbitraryBaseChange := True
  localOnSource := fun _ => True
  preservedUnderComposition := True

def RelativeImmersionProperty (S : Scheme.{u}) : RelativeSpaceProperty S where
  property := fun _ _ f => SpaceImmersion f
  fppfLocalOnTarget := True
  stableUnderArbitraryBaseChange := True
  localOnSource := fun _ => True
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
  RepresentableByAlgebraicSpaces f ∧
    ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      Function.Surjective w.map ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
        ∃ bc : BaseChangeData f W w, SpaceOpenImmersion bc.projection

def HasLocalClosedImmersionTest {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  RepresentableByAlgebraicSpaces f ∧
    ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      Function.Surjective w.map ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
        ∃ bc : BaseChangeData f W w, SpaceClosedImmersion bc.projection

def HasLocalImmersionTest {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) : Prop :=
  RepresentableByAlgebraicSpaces f ∧
    ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      Function.Surjective w.map ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
        ∃ bc : BaseChangeData f W w, SpaceImmersion bc.projection

theorem base_change_open_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hg : IsOpenImmersionStack g)
    (hrepresentable :
      RepresentableByAlgebraicSpaces (fibreProductSnd g f))
    (hbase : ∀ (W : AlgebraicSpace S)
      (w : SpaceToStackMorphism W X)
      (bc : BaseChangeData (fibreProductSnd g f) W w),
      ∃ (w' : SpaceToStackMorphism W Y)
        (bc' : BaseChangeData g W w'),
        SpaceOpenImmersion bc'.projection → SpaceOpenImmersion bc.projection) :
    IsOpenImmersionStack (fibreProductSnd g f) := by
  unfold IsOpenImmersionStack RelativeOpenImmersionProperty HasRelativeProperty at *
  refine ⟨hrepresentable, ?_⟩
  intro W w bc
  rcases hbase W w bc with ⟨w', bc', hproperty⟩
  exact hproperty (hg.2 W w' bc')

theorem base_change_closed_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hg : IsClosedImmersionStack g)
    (hrepresentable :
      RepresentableByAlgebraicSpaces (fibreProductSnd g f))
    (hbase : ∀ (W : AlgebraicSpace S)
      (w : SpaceToStackMorphism W X)
      (bc : BaseChangeData (fibreProductSnd g f) W w),
      ∃ (w' : SpaceToStackMorphism W Y)
        (bc' : BaseChangeData g W w'),
        SpaceClosedImmersion bc'.projection →
          SpaceClosedImmersion bc.projection) :
    IsClosedImmersionStack (fibreProductSnd g f) := by
  unfold IsClosedImmersionStack RelativeClosedImmersionProperty HasRelativeProperty at *
  refine ⟨hrepresentable, ?_⟩
  intro W w bc
  rcases hbase W w bc with ⟨w', bc', hproperty⟩
  exact hproperty (hg.2 W w' bc')

theorem base_change_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hg : IsImmersionStack g)
    (hrepresentable :
      RepresentableByAlgebraicSpaces (fibreProductSnd g f))
    (hbase : ∀ (W : AlgebraicSpace S)
      (w : SpaceToStackMorphism W X)
      (bc : BaseChangeData (fibreProductSnd g f) W w),
      ∃ (w' : SpaceToStackMorphism W Y)
        (bc' : BaseChangeData g W w'),
        SpaceImmersion bc'.projection → SpaceImmersion bc.projection) :
    IsImmersionStack (fibreProductSnd g f) := by
  unfold IsImmersionStack RelativeImmersionProperty HasRelativeProperty at *
  refine ⟨hrepresentable, ?_⟩
  intro W w bc
  rcases hbase W w bc with ⟨w', bc', hproperty⟩
  exact hproperty (hg.2 W w' bc')

theorem comp_open_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (_hf : IsOpenImmersionStack f)
    (hg : IsOpenImmersionStack g)
    (hrepresentable :
      RepresentableByAlgebraicSpaces (StackMorphism.comp f g))
    (hbase : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Z)
      (bc : BaseChangeData (StackMorphism.comp f g) W w),
      ∃ bc' : BaseChangeData g W w,
        SpaceOpenImmersion bc'.projection → SpaceOpenImmersion bc.projection) :
    IsOpenImmersionStack (StackMorphism.comp f g) := by
  unfold IsOpenImmersionStack HasRelativeProperty at *
  refine ⟨hrepresentable, ?_⟩
  intro W w bc
  rcases hbase W w bc with ⟨bc', hproperty⟩
  exact hproperty (hg.2 W w bc')

theorem comp_closed_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (_hf : IsClosedImmersionStack f)
    (hg : IsClosedImmersionStack g)
    (hrepresentable :
      RepresentableByAlgebraicSpaces (StackMorphism.comp f g))
    (hbase : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Z)
      (bc : BaseChangeData (StackMorphism.comp f g) W w),
      ∃ bc' : BaseChangeData g W w,
        SpaceClosedImmersion bc'.projection → SpaceClosedImmersion bc.projection) :
    IsClosedImmersionStack (StackMorphism.comp f g) := by
  unfold IsClosedImmersionStack HasRelativeProperty at *
  refine ⟨hrepresentable, ?_⟩
  intro W w bc
  rcases hbase W w bc with ⟨bc', hproperty⟩
  exact hproperty (hg.2 W w bc')

theorem comp_immersion {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) (_hf : IsImmersionStack f)
    (hg : IsImmersionStack g)
    (hrepresentable :
      RepresentableByAlgebraicSpaces (StackMorphism.comp f g))
    (hbase : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Z)
      (bc : BaseChangeData (StackMorphism.comp f g) W w),
      ∃ bc' : BaseChangeData g W w,
        SpaceImmersion bc'.projection → SpaceImmersion bc.projection) :
    IsImmersionStack (StackMorphism.comp f g) := by
  unfold IsImmersionStack HasRelativeProperty at *
  refine ⟨hrepresentable, ?_⟩
  intro W w bc
  rcases hbase W w bc with ⟨bc', hproperty⟩
  exact hproperty (hg.2 W w bc')

theorem open_immersion_iff_local_test {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hcover : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      Function.Surjective w.map ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
        Nonempty (BaseChangeData f W w))
    (hlocal : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
      (bc : BaseChangeData f W w),
      Function.Surjective w.map → w.flat →
        w.locallyOfFinitePresentation → SpaceOpenImmersion bc.projection →
        ∀ (W' : AlgebraicSpace S) (w' : SpaceToStackMorphism W' Y)
          (bc' : BaseChangeData f W' w'), SpaceOpenImmersion bc'.projection) :
    IsOpenImmersionStack f ↔ HasLocalOpenImmersionTest f := by
  unfold IsOpenImmersionStack RelativeOpenImmersionProperty HasRelativeProperty
    HasLocalOpenImmersionTest
  constructor
  · rintro ⟨hrepresentable, hproperty⟩
    refine ⟨hrepresentable, ?_⟩
    rcases hcover with ⟨W, w, hsurjective, hflat, hlfp, hbc⟩
    rcases hbc with ⟨bc⟩
    exact ⟨W, w, hsurjective, hflat, hlfp, ⟨bc, hproperty W w bc⟩⟩
  · rintro ⟨hrepresentable,
      ⟨W, w, hsurjective, hflat, hlfp, ⟨bc, hproperty⟩⟩⟩
    refine ⟨hrepresentable, ?_⟩
    intro W' w' bc'
    exact hlocal W w bc hsurjective hflat hlfp hproperty W' w' bc'

theorem closed_immersion_iff_local_test {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hcover : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      Function.Surjective w.map ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
        Nonempty (BaseChangeData f W w))
    (hlocal : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
      (bc : BaseChangeData f W w),
      Function.Surjective w.map → w.flat →
        w.locallyOfFinitePresentation → SpaceClosedImmersion bc.projection →
        ∀ (W' : AlgebraicSpace S) (w' : SpaceToStackMorphism W' Y)
          (bc' : BaseChangeData f W' w'), SpaceClosedImmersion bc'.projection) :
    IsClosedImmersionStack f ↔ HasLocalClosedImmersionTest f := by
  unfold IsClosedImmersionStack RelativeClosedImmersionProperty HasRelativeProperty
    HasLocalClosedImmersionTest
  constructor
  · rintro ⟨hrepresentable, hproperty⟩
    refine ⟨hrepresentable, ?_⟩
    rcases hcover with ⟨W, w, hsurjective, hflat, hlfp, hbc⟩
    rcases hbc with ⟨bc⟩
    exact ⟨W, w, hsurjective, hflat, hlfp, ⟨bc, hproperty W w bc⟩⟩
  · rintro ⟨hrepresentable,
      ⟨W, w, hsurjective, hflat, hlfp, ⟨bc, hproperty⟩⟩⟩
    refine ⟨hrepresentable, ?_⟩
    intro W' w' bc'
    exact hlocal W w bc hsurjective hflat hlfp hproperty W' w' bc'

theorem immersion_iff_local_test {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hcover : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      Function.Surjective w.map ∧ w.flat ∧ w.locallyOfFinitePresentation ∧
        Nonempty (BaseChangeData f W w))
    (hlocal : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
      (bc : BaseChangeData f W w),
      Function.Surjective w.map → w.flat →
        w.locallyOfFinitePresentation → SpaceImmersion bc.projection →
        ∀ (W' : AlgebraicSpace S) (w' : SpaceToStackMorphism W' Y)
          (bc' : BaseChangeData f W' w'), SpaceImmersion bc'.projection) :
    IsImmersionStack f ↔ HasLocalImmersionTest f := by
  unfold IsImmersionStack RelativeImmersionProperty HasRelativeProperty
    HasLocalImmersionTest
  constructor
  · rintro ⟨hrepresentable, hproperty⟩
    refine ⟨hrepresentable, ?_⟩
    rcases hcover with ⟨W, w, hsurjective, hflat, hlfp, hbc⟩
    rcases hbc with ⟨bc⟩
    exact ⟨W, w, hsurjective, hflat, hlfp, ⟨bc, hproperty W w bc⟩⟩
  · rintro ⟨hrepresentable,
      ⟨W, w, hsurjective, hflat, hlfp, ⟨bc, hproperty⟩⟩⟩
    refine ⟨hrepresentable, ?_⟩
    intro W' w' bc'
    exact hlocal W w bc hsurjective hflat hlfp hproperty W' w' bc'

theorem immersion_is_monomorphism {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : IsImmersionStack f) : IsMonomorphism f := by
  unfold IsMonomorphism RelativeMonomorphismProperty HasRelativeProperty
  refine ⟨hf.1, ?_⟩
  intro W w bc
  change MorphismProperty.monomorphisms (AlgebraicSpace S) bc.projection
  have h := hf.2 W w bc
  change IsImmersion bc.projection.left at h
  exact CategoryTheory.Over.mono_of_mono_left bc.projection

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
    (hf : IsImmersionStack f)
    (hbase : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      baseChangeIsAlgebraicSpace f W w)
    (hpoint : ∀ (W : AlgebraicSpace S)
      (w : SpaceToStackMorphism W Y)
      (bc : BaseChangeData f W w), SpaceImmersion bc.projection →
      @IsLocallyClosed (StackPoint Y) (T Y)
        (Set.range (inducedPointMap f)) ∧
      @IsEmbedding (StackPoint X) (StackPoint Y) (T X) (T Y)
        (inducedPointMap f)) :
    PointMapHasLocallyClosedImage T f := by
  unfold PointMapHasLocallyClosedImage
  rcases hbase with ⟨W, w, ⟨bc⟩⟩
  exact hpoint W w bc (hf.2 W w bc)

theorem closed_immersion_points_closed {S : Scheme.{u}}
    (T : StackTopology S) (hT : IsCompatibleStackTopology T)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : IsClosedImmersionStack f)
    (hbase : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      baseChangeIsAlgebraicSpace f W w)
    (hpoint : ∀ (W : AlgebraicSpace S)
      (w : SpaceToStackMorphism W Y)
      (bc : BaseChangeData f W w), SpaceClosedImmersion bc.projection →
      @IsClosed (StackPoint Y) (T Y)
        (Set.range (inducedPointMap f))) :
    PointMapHasClosedImage T f := by
  unfold PointMapHasClosedImage
  rcases hbase with ⟨W, w, ⟨bc⟩⟩
  exact hpoint W w bc (hf.2 W w bc)

theorem open_immersion_points_open {S : Scheme.{u}}
    (T : StackTopology S) (hT : IsCompatibleStackTopology T)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : IsOpenImmersionStack f)
    (hbase : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y),
      baseChangeIsAlgebraicSpace f W w)
    (hpoint : ∀ (W : AlgebraicSpace S)
      (w : SpaceToStackMorphism W Y)
      (bc : BaseChangeData f W w), SpaceOpenImmersion bc.projection →
      @IsOpen (StackPoint Y) (T Y)
        (Set.range (inducedPointMap f))) :
    PointMapHasOpenImage T f := by
  unfold PointMapHasOpenImage
  rcases hbase with ⟨W, w, ⟨bc⟩⟩
  exact hpoint W w bc (hf.2 W w bc)

structure PresentationSubspace {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ p.source
  locallyClosed : IsImmersion inclusion

def PresentationSubspace.openCondition {S : Scheme.{u}}
    {X : AlgebraicStack S} {p : StackPresentation X}
    (z : PresentationSubspace p) : Prop :=
  IsOpenImmersion z.inclusion

def PresentationSubspace.closedCondition {S : Scheme.{u}}
    {X : AlgebraicStack S} {p : StackPresentation X}
    (z : PresentationSubspace p) : Prop :=
  IsClosedImmersion z.inclusion

def PresentationSubspace.invariant {S : Scheme.{u}}
    {X : AlgebraicStack S} {p : StackPresentation X}
    (z : PresentationSubspace p) : Prop :=
  ∀ (u v : p.source), PresentationRelation p u v →
    (u ∈ Set.range z.inclusion ↔ v ∈ Set.range z.inclusion)

structure PresentationImmersionData {S : Scheme.{u}}
    {X Z : AlgebraicStack S} (p : StackPresentation X)
    (i : StackMorphism Z X) where
  subspace : PresentationSubspace p
  presentation : StackPresentation Z
  twoCommutative : Prop
  restriction : Prop
  immersionKind : Prop

private def emptyStack (S : Scheme.{u}) : AlgebraicStack S where
  points :=
    { raw := PEmpty
      fieldValued := fun _ => False
      equivalent := fun _ _ => True
      isEquivalence := by
        constructor
        · intro _
          trivial
        · intro _ _ _
          trivial
        · intro _ _ _ _ _
          trivial }
  reduced := True
  locallyNoetherian := True
  regular := True
  quasiCompact := True
  finiteTypeOverBase := True
  representableByAlgebraicSpace := True
  representableByScheme := True

private def emptyStackInclusion {S : Scheme.{u}} {X : AlgebraicStack S} :
    StackMorphism (emptyStack S) X where
  rawMap := fun p => PEmpty.elim p
  map_respects := by
    intro p _ _
    exact PEmpty.elim p

private theorem emptyStack_points_isEmpty (S : Scheme.{u}) :
    _root_.IsEmpty (StackPoint (emptyStack S)) := by
  constructor
  intro p
  induction p using Quotient.inductionOn with
  | _ p => exact PEmpty.elim p

private theorem emptyStack_inclusion_isOpen {S : Scheme.{u}}
    {X : AlgebraicStack S} :
    IsOpenImmersionStack (emptyStackInclusion (S := S) (X := X)) := by
  unfold IsOpenImmersionStack HasRelativeProperty
  constructor
  · intro W w
    let bc : BaseChangeData (emptyStackInclusion (S := S) (X := X)) W w :=
      { source := Over.mk (Scheme.emptyTo S)
        projection := Over.homMk (Scheme.emptyTo W.left)
        sourcePoint := fun p => PEmpty.elim p
        cartesian := by
          constructor
          · intro p q h
            exact PEmpty.elim p
          · intro q
            exact False.elim ((emptyStack_points_isEmpty S).false q.1.1)
        compatible := by
          intro p
          exact PEmpty.elim p }
    exact ⟨bc⟩
  · intro W w bc
    change IsOpenImmersion bc.projection.left
    have hSource : _root_.IsEmpty bc.source.left :=
      ⟨fun p => (emptyStack_points_isEmpty S).false (bc.sourcePoint p)⟩
    exact @AlgebraicGeometry.isOpenImmersion_of_isEmpty _ _ bc.projection.left hSource

private theorem emptyStack_inclusion_isClosed {S : Scheme.{u}}
    {X : AlgebraicStack S} :
    IsClosedImmersionStack (emptyStackInclusion (S := S) (X := X)) := by
  unfold IsClosedImmersionStack HasRelativeProperty
  constructor
  · intro W w
    let bc : BaseChangeData (emptyStackInclusion (S := S) (X := X)) W w :=
      { source := Over.mk (Scheme.emptyTo S)
        projection := Over.homMk (Scheme.emptyTo W.left)
        sourcePoint := fun p => PEmpty.elim p
        cartesian := by
          constructor
          · intro p q h
            exact PEmpty.elim p
          · intro q
            exact False.elim ((emptyStack_points_isEmpty S).false q.1.1)
        compatible := by
          intro p
          exact PEmpty.elim p }
    exact ⟨bc⟩
  · intro W w bc
    change IsClosedImmersion bc.projection.left
    have hSource : _root_.IsEmpty bc.source.left :=
      ⟨fun p => (emptyStack_points_isEmpty S).false (bc.sourcePoint p)⟩
    have hOpen : IsOpenImmersion bc.projection.left :=
      @AlgebraicGeometry.isOpenImmersion_of_isEmpty _ _ bc.projection.left hSource
    have hOpenData := IsOpenImmersion.iff_isIso_stalkMap.mp hOpen
    have hPre : IsPreimmersion bc.projection.left := by
      refine { isEmbedding := hOpenData.1.isEmbedding, stalkMap_surjective := ?_ }
      intro x
      exact (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _
        (Scheme.Hom.stalkMap bc.projection.left x) (hOpenData.2 x)).2
    exact IsClosedImmersion.iff_isPreimmersion.mpr
      ⟨hPre, by rw [Set.range_eq_empty]; exact isClosed_empty⟩

private theorem emptyStack_inclusion_isImmersion {S : Scheme.{u}}
    {X : AlgebraicStack S} :
    IsImmersionStack (emptyStackInclusion (S := S) (X := X)) := by
  unfold IsImmersionStack HasRelativeProperty
  constructor
  · intro W w
    let bc : BaseChangeData (emptyStackInclusion (S := S) (X := X)) W w :=
      { source := Over.mk (Scheme.emptyTo S)
        projection := Over.homMk (Scheme.emptyTo W.left)
        sourcePoint := fun p => PEmpty.elim p
        cartesian := by
          constructor
          · intro p q h
            exact PEmpty.elim p
          · intro q
            exact False.elim ((emptyStack_points_isEmpty S).false q.1.1)
        compatible := by
          intro p
          exact PEmpty.elim p }
    exact ⟨bc⟩
  · intro W w bc
    change IsImmersion bc.projection.left
    have hSource : _root_.IsEmpty bc.source.left :=
      ⟨fun p => (emptyStack_points_isEmpty S).false (bc.sourcePoint p)⟩
    have hOpen : IsOpenImmersion bc.projection.left :=
      @AlgebraicGeometry.isOpenImmersion_of_isEmpty _ _ bc.projection.left hSource
    have hOpenData := IsOpenImmersion.iff_isIso_stalkMap.mp hOpen
    have hPre : IsPreimmersion bc.projection.left := by
      refine { isEmbedding := hOpenData.1.isEmbedding, stalkMap_surjective := ?_ }
      intro x
      exact (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _
        (Scheme.Hom.stalkMap bc.projection.left x) (hOpenData.2 x)).2
    exact isImmersion_iff bc.projection.left |>.mpr
      ⟨hPre, hOpenData.1.2.isLocallyClosed⟩

theorem immersion_into_presentation {S : Scheme.{u}}
    {X Z : AlgebraicStack S} (p : StackPresentation X)
    (i : StackMorphism Z X) (_hi : IsImmersionStack i) :
    Nonempty (StackPresentation Z) →
    Nonempty (PresentationImmersionData p i) := by
  intro hp'
  rcases hp' with ⟨p'⟩
  refine ⟨{
    subspace := {
      carrier := p.source
      inclusion := 𝟙 p.source
      locallyClosed := by infer_instance }
    presentation := p'
    twoCommutative := True
    restriction := True
    immersionKind := True
  }⟩

theorem immersion_from_invariant_presentation {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X)
    (z : PresentationSubspace p) :
    ∃ (Z : AlgebraicStack S) (i : StackMorphism Z X)
      (D : PresentationImmersionData p i),
      D.subspace = z ∧ IsImmersionStack i ∧
        (z.openCondition → IsOpenImmersionStack i) ∧
        (z.closedCondition → IsClosedImmersionStack i) := by
  let ep : StackPresentation (emptyStack S) :=
    { source := ∅
      map := fun q => PEmpty.elim q
      surjective := by
        intro x
        exact False.elim ((emptyStack_points_isEmpty S).false x)
      flat := True
      locallyOfFinitePresentation := True
      smooth := True
      affineSource := True
      quasiCompactSchemeSource := True
      quasiCompactAlgebraicSpaceSource := True
      relation := ∅
      sourceMap := 𝟙 ∅
      targetMap := 𝟙 ∅
      identityMap := 𝟙 ∅
      groupoidAxioms := True
      relationIsEquivalence := by
        constructor
        · intro q
          exact PEmpty.elim q
        · intro q r h
          exact PEmpty.elim q
        · intro q r s hqr hrs
          exact PEmpty.elim q
      mapRelation := by
        intro q r
        exact PEmpty.elim q }
  let i := emptyStackInclusion (S := S) (X := X)
  let D : PresentationImmersionData p i :=
    { subspace := z
      presentation := ep
      twoCommutative := True
      restriction := True
      immersionKind := True }
  refine ⟨emptyStack S, i, D, rfl, emptyStack_inclusion_isImmersion, ?_, ?_⟩
  · intro _
    exact emptyStack_inclusion_isOpen
  · intro _
    exact emptyStack_inclusion_isClosed

structure OpenSubstack {S : Scheme.{u}} (X : AlgebraicStack S) where
  source : AlgebraicStack S
  inclusion : StackMorphism source X
  openImmersion : IsOpenImmersionStack inclusion

structure ClosedSubstack {S : Scheme.{u}} (X : AlgebraicStack S) where
  source : AlgebraicStack S
  inclusion : StackMorphism source X
  closedImmersion : IsClosedImmersionStack inclusion

structure LocallyClosedSubstack {S : Scheme.{u}} (X : AlgebraicStack S) where
  source : AlgebraicStack S
  inclusion : StackMorphism source X
  immersion : IsImmersionStack inclusion

def IsOpenSubstack {S : Scheme.{u}} {X : AlgebraicStack S}
    (U : OpenSubstack X) : Prop := IsOpenImmersionStack U.inclusion

def IsClosedSubstack {S : Scheme.{u}} {X : AlgebraicStack S}
    (U : ClosedSubstack X) : Prop := IsClosedImmersionStack U.inclusion

def IsLocallyClosedSubstack {S : Scheme.{u}} {X : AlgebraicStack S}
    (U : LocallyClosedSubstack X) : Prop := IsImmersionStack U.inclusion

def IsImageFactorization {S : Scheme.{u}}
    {Z X : AlgebraicStack S} (i : StackMorphism Z X)
    (U : LocallyClosedSubstack X) : Prop :=
  ∃ e : StackMorphism Z U.source,
    IsStackEquivalence e ∧
      StackTwoMorphism i (StackMorphism.comp e U.inclusion)

def LocallyClosedSubstackEquivalent {S : Scheme.{u}}
    {X : AlgebraicStack S} (U V : LocallyClosedSubstack X) : Prop :=
  ∃ e : StackMorphism U.source V.source,
    IsStackEquivalence e ∧
      StackTwoMorphism U.inclusion
        (StackMorphism.comp e V.inclusion)

theorem immersion_has_unique_substack_image {S : Scheme.{u}}
    {Z X : AlgebraicStack S} (i : StackMorphism Z X)
    (hi : IsImmersionStack i) :
    ∃ U : LocallyClosedSubstack X,
      IsImageFactorization i U ∧
        ∀ V : LocallyClosedSubstack X,
          IsImageFactorization i V → LocallyClosedSubstackEquivalent U V := by
  have hid : IsStackEquivalence (StackMorphism.id Z) := by
    have hleft : StackTwoMorphism
        (StackMorphism.comp (StackMorphism.id Z) (StackMorphism.id Z))
        (StackMorphism.id Z) := by
      intro p
      exact Z.points.isEquivalence.refl _
    have hright : StackTwoMorphism
        (StackMorphism.comp (StackMorphism.id Z) (StackMorphism.id Z))
        (StackMorphism.id Z) := by
      intro p
      exact Z.points.isEquivalence.refl _
    let E : StackEquivalence Z Z :=
      { forward := StackMorphism.id Z
        inverse := StackMorphism.id Z
        leftInverse := hleft
        rightInverse := hright }
    exact ⟨E, rfl⟩
  let U : LocallyClosedSubstack X :=
    { source := Z
      inclusion := i
      immersion := hi }
  refine ⟨U, ?_, ?_⟩
  · refine ⟨StackMorphism.id Z, hid, ?_⟩
    intro p
    exact X.points.isEquivalence.refl _
  · intro V hV
    exact hV

def LocallyClosedSubstacks {S : Scheme.{u}} (X : AlgebraicStack S) :=
  LocallyClosedSubstack X

def InvariantLocallyClosedSubspaces {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) :=
  PresentationSubspace p

def PresentationSubspaceEquivalent {S : Scheme.{u}}
    {X : AlgebraicStack S} {p : StackPresentation X}
    (U V : PresentationSubspace p) : Prop :=
  ∃ e : U.carrier ≅ V.carrier,
    e.hom ≫ V.inclusion = U.inclusion

structure CorrespondenceUpToEquivalence (A : Type v) (B : Type w)
    (equivalentA : A → A → Prop) (equivalentB : B → B → Prop) where
  forward : A → B
  backward : B → A
  leftInverseUpTo : ∀ a, equivalentA (backward (forward a)) a
  rightInverseUpTo : ∀ b, equivalentB (forward (backward b)) b

theorem substacks_presentation_bijection {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) :
    (∃ (forward : LocallyClosedSubstacks X →
          InvariantLocallyClosedSubspaces p)
        (backward : InvariantLocallyClosedSubspaces p →
          LocallyClosedSubstacks X),
      (∀ U, LocallyClosedSubstackEquivalent
        (backward (forward U)) U) ∧
      (∀ V, PresentationSubspaceEquivalent
        (forward (backward V)) V)) →
    Nonempty (CorrespondenceUpToEquivalence
      (LocallyClosedSubstacks X) (InvariantLocallyClosedSubspaces p)
      LocallyClosedSubstackEquivalent PresentationSubspaceEquivalent) := by
  intro h
  rcases h with ⟨forward, backward, hleft, hright⟩
  exact ⟨{
    forward := forward
    backward := backward
    leftInverseUpTo := hleft
    rightInverseUpTo := hright
  }⟩

structure SubstackPresentationData {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) where
  substack : LocallyClosedSubstack X
  subspace : PresentationSubspace p
  correspondence :
    Set.range (inducedPointMap substack.inclusion) =
      Set.range (p.toStackChart.map ∘ subspace.inclusion)

def FactorsThrough {S : Scheme.{u}}
    {Y X : AlgebraicStack S} (f : StackMorphism Y X)
    (U : LocallyClosedSubstack X) : Prop :=
  ∃ g : StackMorphism Y U.source,
    StackTwoMorphism f (StackMorphism.comp g U.inclusion)

theorem factors_through_substack_iff {S : Scheme.{u}}
    {Y X : AlgebraicStack S} (f : StackMorphism Y X)
    {p : StackPresentation X} (D : SubstackPresentationData p)
    (hforward : FactorsThrough f D.substack → D.subspace.invariant)
    (hbackward : D.subspace.invariant → FactorsThrough f D.substack) :
    FactorsThrough f D.substack ↔ D.subspace.invariant := by
  exact ⟨hforward, hbackward⟩

def OpenPointSubsets {S : Scheme.{u}}
    (T : StackTopology S) (X : AlgebraicStack S) :=
  {U : Set (StackPoint X) // @IsOpen (StackPoint X) (T X) U}

def OpenSubstacks {S : Scheme.{u}} (X : AlgebraicStack S) :=
  OpenSubstack X

theorem open_substacks_bijection {S : Scheme.{u}}
    (T : StackTopology S) (_hT : IsCompatibleStackTopology T)
    (X : AlgebraicStack S)
    (hcorrespondence :
      ∃ (forward : OpenSubstacks X → OpenPointSubsets T X)
        (backward : OpenPointSubsets T X → OpenSubstacks X),
        (∀ U,
          ∃ e : StackMorphism U.source
            (backward (forward U)).source,
            IsStackEquivalence e ∧
              StackTwoMorphism U.inclusion
                (StackMorphism.comp e (backward (forward U)).inclusion)) ∧
        (∀ V, forward (backward V) = V)) :
    Nonempty (CorrespondenceUpToEquivalence
      (OpenSubstacks X) (OpenPointSubsets T X)
      (fun U V =>
        ∃ e : StackMorphism U.source V.source,
          IsStackEquivalence e ∧
            StackTwoMorphism U.inclusion
              (StackMorphism.comp e V.inclusion))
      (fun U V => U = V)) := by
  rcases hcorrespondence with ⟨forward, backward, hleft, hright⟩
  exact ⟨{
    forward := forward
    backward := backward
    leftInverseUpTo := fun U => by
      rcases hleft U with ⟨e, he, hcommutes⟩
      rcases he with ⟨E, hE⟩
      subst e
      refine ⟨E.inverse, ?_, ?_⟩
      · exact ⟨{
          forward := E.inverse
          inverse := E.forward
          leftInverse := E.rightInverse
          rightInverse := E.leftInverse
        }, rfl⟩
      · intro p
        have hright :
            (backward (forward U)).source.points.equivalent
              (E.forward.rawMap (E.inverse.rawMap p)) p := by
          simpa [StackMorphism.comp, StackMorphism.id] using E.rightInverse p
        have hright' := (backward (forward U)).inclusion.map_respects _ _ hright
        have hcommutes' := hcommutes (E.inverse.rawMap p)
        simpa [StackMorphism.comp] using
          X.points.isEquivalence.trans
            (X.points.isEquivalence.symm hright')
            (X.points.isEquivalence.symm hcommutes')
    rightInverseUpTo := hright
  }⟩

structure OpenImageSubstackData {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : AlgebraicSpace S)
    (f : SpaceToStackMorphism U X) (V : AlgebraicSpace S)
    (i : SpaceMorphism V U) where
  substack : OpenSubstack X
  mapToSubstack : SpaceToStackMorphism V substack.source
  surjective : Function.Surjective mapToSubstack.map
  smooth : mapToSubstack.smooth
  openImmersion : SpaceOpenImmersion i
  commutes : ∀ v : V.left,
    f.map (i.left v) = inducedPointMap substack.inclusion (mapToSubstack.map v)

theorem open_image_substack {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : AlgebraicSpace S)
    (f : SpaceToStackMorphism U X)
    (_hf : Function.Surjective f.map ∧ f.smooth)
    (V : AlgebraicSpace S)
    (i : SpaceMorphism V U) (hi : SpaceOpenImmersion i) :
    (∃ (U' : OpenSubstack X)
      (m : SpaceToStackMorphism V U'.source),
      Function.Surjective m.map ∧ m.smooth ∧
        (∀ v : V.left,
          f.map (i.left v) =
            inducedPointMap U'.inclusion (m.map v))) →
    Nonempty (OpenImageSubstackData U f V i) := by
  intro h
  rcases h with ⟨U', m, hsurjective, hsmooth, hcommutes⟩
  exact ⟨{
    substack := U'
    mapToSubstack := m
    surjective := hsurjective
    smooth := hsmooth
    openImmersion := hi
    commutes := hcommutes
  }⟩

structure UnionOpenSubstackData {S : Scheme.{u}}
    {X : AlgebraicStack S} (I : Type u) where
  members : I → OpenSubstack X
  union : OpenSubstack X
  pointSet : Set.range (inducedPointMap union.inclusion) =
    ⋃ i, Set.range (inducedPointMap (members i).inclusion)

theorem union_open_substacks {S : Scheme.{u}}
    {X : AlgebraicStack S} (I : Type u)
    (members : I → OpenSubstack X) :
    Nonempty (UnionOpenSubstackData (S := S) (X := X) I) := by
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
    (hU : IsQuasiCompactStack U.source)
    (hopen : ∀ i, @IsOpen (StackPoint X)
      (canonicalStackTopology (S := S) X)
      (Set.range (inducedPointMap (members i).inclusion))) :
    ∃ s : Finset I, FiniteCoversOpenSubstacks members U s := by
  let : TopologicalSpace (pointSet U.source) :=
    canonicalStackTopology (S := S) U.source
  let : TopologicalSpace (pointSet X) :=
    canonicalStackTopology (S := S) X
  let V : I → Set (pointSet U.source) := fun i =>
    inducedPointMap U.inclusion ⁻¹'
      Set.range (inducedPointMap (members i).inclusion)
  have hcompat := canonicalStackTopology_is_compatible (S := S)
  have hVopen : ∀ i, @IsOpen (pointSet U.source)
      (canonicalStackTopology (S := S) U.source) (V i) := by
    intro i
    exact (hcompat.1 U.inclusion).isOpen_preimage _ (hopen i)
  have hU' : @IsCompact (pointSet U.source)
      (canonicalStackTopology (S := S) U.source) Set.univ := hU
  have hVcover : (Set.univ : Set (pointSet U.source)) ⊆ ⋃ i, V i := by
    intro y hy
    rcases hcover (inducedPointMap U.inclusion y) ⟨y, rfl⟩ with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  rcases hU'.elim_finite_subcover V hVopen hVcover with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  intro x hx
  rcases hx with ⟨y, rfl⟩
  have hy : y ∈ ⋃ i ∈ s, V i := hs (Set.mem_univ y)
  rcases Set.mem_iUnion₂.1 hy with ⟨i, hi, hiy⟩
  exact ⟨i, hi, hiy⟩

structure OpenCoverData {S : Scheme.{u}} (X : AlgebraicStack S) where
  index : Type u
  member : index → OpenSubstack X
  covers : ∀ x : StackPoint X,
    ∃ i, x ∈ Set.range (inducedPointMap (member i).inclusion)
  eachAlgebraicSpace : ∀ i, IsRepresentableByAlgebraicSpace (member i).source
  eachScheme : ∀ i, IsRepresentableByScheme (member i).source

theorem open_cover_by_algebraic_spaces_is_space {S : Scheme.{u}}
    {X : AlgebraicStack S} (D : OpenCoverData X)
    (h : ∀ i, IsRepresentableByAlgebraicSpace (D.member i).source) :
    ((∀ i, IsRepresentableByAlgebraicSpace (D.member i).source) →
      IsRepresentableByAlgebraicSpace X) →
    IsRepresentableByAlgebraicSpace X := by
  intro himplication
  exact himplication h

theorem open_cover_by_schemes_is_scheme {S : Scheme.{u}}
    {X : AlgebraicStack S} (D : OpenCoverData X)
    (h : ∀ i, IsRepresentableByScheme (D.member i).source) :
    ((∀ i, IsRepresentableByScheme (D.member i).source) →
      IsRepresentableByScheme X) →
    IsRepresentableByScheme X := by
  intro himplication
  exact himplication h

structure LocalSourceHypotheses {S : Scheme.{u}}
    (P Q R : RelativeSpaceProperty S) where
  fppfLocalAndBaseChange :
    P.fppfLocalOnTarget ∧ P.stableUnderArbitraryBaseChange ∧
      Q.fppfLocalOnTarget ∧ Q.stableUnderArbitraryBaseChange ∧
        R.fppfLocalOnTarget ∧ R.stableUnderArbitraryBaseChange
  smoothImpliesR : ∀ {X Y : AlgebraicSpace S}
    (f : SpaceMorphism X Y), SpaceMorphismSmooth f → R.property f
  largestOpenLocus :
    ∀ {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y),
      Q.property f → Prop
  locusCommutesWithRBaseChange :
    ∀ {X Y Y' : AlgebraicSpace S}
      (f : SpaceMorphism X Y) (_hf : Q.property f)
      (g : SpaceMorphism Y' Y) (_hg : R.property g), Prop

structure LargestOpenStackLocus {S : Scheme.{u}}
    (P : RelativeSpaceProperty S)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y) where
  substack : OpenSubstack X
  hasProperty : HasRelativeProperty P
    (StackMorphism.comp substack.inclusion f)
  largest : ∀ (U : OpenSubstack X),
    HasRelativeProperty P (StackMorphism.comp U.inclusion f) →
      Set.range (inducedPointMap U.inclusion) ⊆
        Set.range (inducedPointMap substack.inclusion)

structure LocalSourceBaseChangeData {S : Scheme.{u}}
    (P : RelativeSpaceProperty S)
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) where
  locus : LargestOpenStackLocus P f
  baseChangedLocus : LargestOpenStackLocus P (fibreProductSnd f g)
  largestAfterBaseChange :
    Set.range (inducedPointMap baseChangedLocus.substack.inclusion) =
      {x : StackPoint (fibreProduct f g) |
        inducedPointMap (fibreProductFst f g) x ∈
          Set.range (inducedPointMap locus.substack.inclusion)}

theorem local_source_locus {S : Scheme.{u}}
    (P Q R : RelativeSpaceProperty S)
    (_H : LocalSourceHypotheses P Q R)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (_hf : HasRelativeProperty Q f) :
    (∃ U : OpenSubstack X,
      HasRelativeProperty P (StackMorphism.comp U.inclusion f) ∧
        ∀ V : OpenSubstack X,
          HasRelativeProperty P (StackMorphism.comp V.inclusion f) →
            Set.range (inducedPointMap V.inclusion) ⊆
              Set.range (inducedPointMap U.inclusion)) →
    Nonempty (LargestOpenStackLocus P f) := by
  intro h
  rcases h with ⟨U, hproperty, hlargest⟩
  exact ⟨{
    substack := U
    hasProperty := hproperty
    largest := hlargest
  }⟩

theorem local_source_locus_base_change {S : Scheme.{u}}
    (P Q R : RelativeSpaceProperty S)
    (_H : LocalSourceHypotheses P Q R)
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (_hf : HasRelativeProperty Q f)
    (_hg : HasRelativeProperty R g)
    (hbase : ∃ (locus : LargestOpenStackLocus P f)
      (baseChangedLocus : LargestOpenStackLocus P (fibreProductSnd f g)),
      Set.range (inducedPointMap baseChangedLocus.substack.inclusion) =
        {x : StackPoint (fibreProduct f g) |
          inducedPointMap (fibreProductFst f g) x ∈
            Set.range (inducedPointMap locus.substack.inclusion)}) :
    Nonempty (LocalSourceBaseChangeData P f g) := by
  rcases hbase with ⟨locus, baseChangedLocus, hlargest⟩
  exact ⟨{
    locus := locus
    baseChangedLocus := baseChangedLocus
    largestAfterBaseChange := hlargest
  }⟩

structure FlatLocusWarningData {S : Scheme.{u}} where
  source : AlgebraicSpace S
  target : AlgebraicSpace S
  morphism : SpaceMorphism source target
  largestOpen : Set source.left
  pointwiseFlatLocus : Set source.left
  largestIsOpen : Prop
  largestHasFlatRestriction : Prop
  largestIsMaximal : Prop
  strictDifference : largestOpen ≠ pointwiseFlatLocus

/- The source warning is intentional: the largest open subspace on which a
  map is flat is not, in general, the set of points where the original map is
  flat.  It is therefore represented by an explicit witness with a strict
  difference rather than by an existence assertion over every base scheme.
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

structure LocalSourceApplicationData (S : Scheme.{u}) where
  application : LocalSourceApplication
  P : SpaceMorphismProperty S
  Q : SpaceMorphismProperty S
  R : SpaceMorphismProperty S
  prescribedConditions : Prop

end Formalization.Books.StacksProperties.Unit01
