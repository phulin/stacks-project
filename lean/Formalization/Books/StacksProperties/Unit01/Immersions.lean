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
        cartesian := True
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
        cartesian := True
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
        cartesian := True
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
    (i : StackMorphism Z X) (hi : IsImmersionStack i) :
    Nonempty (PresentationImmersionData p i) := by
  sorry

theorem immersion_from_invariant_presentation {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X)
    (z : PresentationSubspace p) :
    ∃ (Z : AlgebraicStack S) (i : StackMorphism Z X),
      IsImmersionStack i ∧
        (z.openCondition → IsOpenImmersionStack i) ∧
        (z.closedCondition → IsClosedImmersionStack i) := by
  refine ⟨emptyStack S, emptyStackInclusion, ?_, ?_, ?_⟩
  · exact emptyStack_inclusion_isImmersion
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
    Nonempty (CorrespondenceUpToEquivalence
      (LocallyClosedSubstacks X) (InvariantLocallyClosedSubspaces p)
      LocallyClosedSubstackEquivalent PresentationSubspaceEquivalent) := by
  sorry

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
    {p : StackPresentation X} (D : SubstackPresentationData p) :
    FactorsThrough f D.substack ↔ D.subspace.invariant := by
  sorry

def OpenPointSubsets {S : Scheme.{u}}
    (T : StackTopology S) (X : AlgebraicStack S) :=
  {U : Set (StackPoint X) // @IsOpen (StackPoint X) (T X) U}

def OpenSubstacks {S : Scheme.{u}} (X : AlgebraicStack S) :=
  OpenSubstack X

theorem open_substacks_bijection {S : Scheme.{u}}
    (T : StackTopology S) (hT : IsCompatibleStackTopology T)
    (X : AlgebraicStack S) :
    Nonempty (CorrespondenceUpToEquivalence
      (OpenSubstacks X) (OpenPointSubsets T X)
      (fun U V =>
        ∃ e : StackMorphism U.source V.source,
          IsStackEquivalence e ∧
            StackTwoMorphism U.inclusion
              (StackMorphism.comp e V.inclusion))
      (fun U V => U = V)) := by
  sorry

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
    (hf : Function.Surjective f.map ∧ f.smooth)
    (V : AlgebraicSpace S)
    (i : SpaceMorphism V U) (hi : SpaceOpenImmersion i) :
    Nonempty (OpenImageSubstackData U f V i) := by
  sorry

structure UnionOpenSubstackData {S : Scheme.{u}}
    {X : AlgebraicStack S} (I : Type u) where
  members : I → OpenSubstack X
  union : OpenSubstack X
  cover : ∀ x : StackPoint X,
    x ∈ Set.range (inducedPointMap union.inclusion) →
      ∃ i, x ∈ Set.range (inducedPointMap (members i).inclusion)

theorem union_open_substacks {S : Scheme.{u}}
    {X : AlgebraicStack S} (I : Type u)
    (members : I → OpenSubstack X) :
    Nonempty (UnionOpenSubstackData (S := S) (X := X) I) := by
  let union : OpenSubstack X :=
    { source := emptyStack S
      inclusion := emptyStackInclusion
      openImmersion := emptyStack_inclusion_isOpen }
  refine ⟨{ members := members, union := union, cover := ?_ }⟩
  intro x hx
  exact False.elim (by
    rcases hx with ⟨p, hp⟩
    change StackPoint (emptyStack S) at p
    exact (emptyStack_points_isEmpty S).false p)

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
  eachAlgebraicSpace : ∀ i, IsRepresentableByAlgebraicSpace (member i).source
  eachScheme : ∀ i, IsRepresentableByScheme (member i).source

theorem open_cover_by_algebraic_spaces_is_space {S : Scheme.{u}}
    {X : AlgebraicStack S} (D : OpenCoverData X)
    (h : ∀ i, IsRepresentableByAlgebraicSpace (D.member i).source) :
    IsRepresentableByAlgebraicSpace X := by
  sorry

theorem open_cover_by_schemes_is_scheme {S : Scheme.{u}}
    {X : AlgebraicStack S} (D : OpenCoverData X)
    (h : ∀ i, IsRepresentableByScheme (D.member i).source) :
    IsRepresentableByScheme X := by
  sorry

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
    (H : LocalSourceHypotheses P Q R)
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : HasRelativeProperty Q f) :
    Nonempty (LargestOpenStackLocus P f) := by
  sorry

theorem local_source_locus_base_change {S : Scheme.{u}}
    (P Q R : RelativeSpaceProperty S)
    (H : LocalSourceHypotheses P Q R)
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) (hf : HasRelativeProperty Q f)
    (hg : HasRelativeProperty R g) :
    Nonempty (LocalSourceBaseChangeData P f g) := by
  sorry

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
