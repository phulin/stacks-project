import Formalization.Books.StacksProperties.Unit01.Reduced
import Mathlib.Algebra.Field.ULift

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 11

Residual gerbes are represented by explicit field-valued covers, singleton
point conditions, and fully faithful (hence monomorphic) inclusions.  This
keeps the existence hypotheses and the locally Noetherian improvement from
the source visible in the Lean interfaces.
-/

noncomputable section

universe u

open AlgebraicGeometry
open CategoryTheory

namespace Formalization.Books.StacksProperties.Unit01

def IsFlatFieldCover {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : FieldValuedMorphism X) : Prop :=
  IsSurjectiveFieldValuedMorphism p ∧ p.flat

def IsLocallyFiniteTypeFlatFieldCover {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : FieldValuedMorphism X) : Prop :=
  IsFlatFieldCover p ∧ p.locallyOfFiniteType

def IsLocallyFinitePresentationFlatFieldCover {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : FieldValuedMorphism X) : Prop :=
  IsFlatFieldCover p ∧ p.locallyOfFinitePresentation

def IsSingletonPointStack {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  Nonempty (StackPoint X) ∧ Subsingleton (StackPoint X)

def IsReducedSingletonPointStack {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  IsReduced X ∧ IsSingletonPointStack X

def IsLocallyNoetherianReducedSingletonPointStack {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  IsLocallyNoetherian X ∧ IsReducedSingletonPointStack X

theorem flat_field_cover_permanence {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : FieldValuedMorphism X)
    (hp : IsFlatFieldCover p)
    (q : FieldValuedMorphism X)
    (heq : stackPointOfFieldValuedMorphism p =
      stackPointOfFieldValuedMorphism q)
    (hflat : p.flat ↔ q.flat) :
    IsFlatFieldCover q := by
  unfold IsFlatFieldCover IsSurjectiveFieldValuedMorphism at *
  refine ⟨fun x => (hp.1 x).trans heq, hflat.mp hp.2⟩

theorem unique_point_iff_flat_field_cover {S : Scheme.{u}}
    (X : AlgebraicStack S) :
    IsReduced X →
    (∃ p : FieldValuedMorphism X,
      IsLocallyFiniteTypeFlatFieldCover p) →
    IsReducedSingletonPointStack X ↔
      (∃ p : FieldValuedMorphism X, IsFlatFieldCover p) ∧
        (∃ p : FieldValuedMorphism X,
          IsLocallyFiniteTypeFlatFieldCover p) := by
  sorry

theorem unique_point_better_iff {S : Scheme.{u}}
    (X : AlgebraicStack S) :
    (IsLocallyNoetherian X → IsReduced X →
      ∃ p : FieldValuedMorphism X,
        IsLocallyFinitePresentationFlatFieldCover p) →
    ((∃ p : FieldValuedMorphism X,
        IsLocallyFinitePresentationFlatFieldCover p) →
      IsLocallyNoetherian X ∧ IsReduced X) →
    IsLocallyNoetherianReducedSingletonPointStack X ↔
      ∃ p : FieldValuedMorphism X,
        IsLocallyFinitePresentationFlatFieldCover p := by
  sorry

theorem monomorphism_into_unique_point {S : Scheme.{u}}
    {Z' Z : AlgebraicStack S} (f : StackMorphism Z' Z)
    (hZ : ∃ p : FieldValuedMorphism Z,
      IsLocallyFinitePresentationFlatFieldCover p)
    (hf : IsMonomorphism f)
    (hfullyFaithful : StackFullyFaithful f) :
    IsEmpty Z' ∨ IsStackEquivalence f := by
  classical
  by_cases hraw : Nonempty (RawPoint Z')
  · right
    rcases hZ with ⟨p, hp⟩
    let p₀ : RawPoint Z' := Classical.choice hraw
    let g : StackMorphism Z Z' := {
      rawMap := fun _ => p₀
      map_respects := by
        intro a b hab
        exact Z'.points.isEquivalence.refl _ }
    have hleft : StackTwoMorphism
        (StackMorphism.comp f g) (StackMorphism.id Z') := by
      intro q
      have htarget : Z.points.equivalent (f.rawMap q) (f.rawMap p₀) := by
        apply @Quotient.exact _ Z.points.setoid
          (f.rawMap q) (f.rawMap p₀)
        exact (hp.1.1 (Quotient.mk Z.points.setoid (f.rawMap q))).trans
          (hp.1.1 (Quotient.mk Z.points.setoid (f.rawMap p₀))).symm
      exact Z'.points.isEquivalence.symm
        ((hfullyFaithful.2 q p₀).mpr htarget)
    have hright : StackTwoMorphism
        (StackMorphism.comp g f) (StackMorphism.id Z) := by
      intro q
      apply @Quotient.exact _ Z.points.setoid
        (f.rawMap p₀) q
      exact (hp.1.1 (Quotient.mk Z.points.setoid (f.rawMap p₀))).trans
        (hp.1.1 (Quotient.mk Z.points.setoid q)).symm
    let E : StackEquivalence Z' Z := {
      forward := f
      inverse := g
      leftInverse := hleft
      rightInverse := hright }
    exact ⟨E, rfl⟩
  · left
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    exact hraw ⟨p⟩

structure ImprovedUniquePointData {S : Scheme.{u}}
    (Z : AlgebraicStack S) where
  source : AlgebraicStack S
  inclusion : StackMorphism source Z
  improved : IsLocallyNoetherianReducedSingletonPointStack source
  monomorphism : IsMonomorphism inclusion

theorem improve_unique_point {S : Scheme.{u}} (Z : AlgebraicStack S)
    (hZ : IsReducedSingletonPointStack Z)
    (hsource : ∃ (source : AlgebraicStack S)
      (inclusion : StackMorphism source Z),
      IsLocallyNoetherianReducedSingletonPointStack source ∧
        IsMonomorphism inclusion)
    (hunique : ∀ D E : ImprovedUniquePointData Z,
      ∃ e : StackMorphism D.source E.source,
        IsStackEquivalence e ∧
          StackTwoMorphism D.inclusion
            (StackMorphism.comp e E.inclusion)) :
    ∃ D : ImprovedUniquePointData Z,
      ∀ E : ImprovedUniquePointData Z,
        ∃ e : StackMorphism D.source E.source,
          IsStackEquivalence e ∧
            StackTwoMorphism D.inclusion
              (StackMorphism.comp e E.inclusion) := by
  rcases hsource with ⟨source, inclusion, himproved, hmono⟩
  let D : ImprovedUniquePointData Z := {
    source := source
    inclusion := inclusion
    improved := himproved
    monomorphism := hmono }
  refine ⟨D, ?_⟩
  intro E
  exact hunique D E

structure DistinctSingletonExample (S : Scheme.{u}) where
  group : Type u
  groupStructure : Group group
  groupActionSpace : AlgebraicSpace S
  action : group → groupActionSpace.left → groupActionSpace.left
  free : ∀ (g : group) (u : groupActionSpace.left),
    action g u = u → g = 1
  transitive : ∀ (u v : groupActionSpace.left),
    ∃ g : group, action g u = v
  quotient : AlgebraicStack S
  quotientIsAlgebraicSpace : IsRepresentableByAlgebraicSpace quotient
  quotientMap : groupActionSpace.left → StackPoint quotient
  quotientMapInvariant : ∀ (g : group) (u : groupActionSpace.left),
    quotientMap (action g u) = quotientMap u
  quotientMapFibres : ∀ (u v : groupActionSpace.left),
    quotientMap u = quotientMap v ↔ ∃ g : group, action g u = v
  reduced : IsReduced quotient
  nonNoetherian : ¬ IsLocallyNoetherian quotient
  singleton : IsSingletonPointStack quotient
  pointSource : AlgebraicStack S
  pointInclusion : StackMorphism pointSource quotient
  fieldValuedPoint : ∃ p : FieldValuedMorphism pointSource,
    ∃ x : StackPoint quotient,
      inducedPointMap pointInclusion
          (stackPointOfFieldValuedMorphism p) = x
  pointIsMonomorphism : IsMonomorphism pointInclusion
  notAnIsomorphism : ¬ IsStackEquivalence pointInclusion

theorem exists_distinct_singleton_example :
    ∃ (S : Scheme.{u}), Nonempty (DistinctSingletonExample S) := by
  let S : Scheme.{u} := ∅
  let quotient : AlgebraicStack S :=
    { points :=
        { raw := PUnit
          fieldValued := fun _ => True
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
      locallyNoetherian := False
      regular := True
      quasiCompact := True
      finiteTypeOverBase := True
      representableByAlgebraicSpace := True
      representableByScheme := True }
  let pointSource : AlgebraicStack S :=
    { points :=
        { raw := ULift.{u} Bool
          fieldValued := fun _ => True
          equivalent := (· = ·)
          isEquivalence := by
            constructor
            · intro _
              rfl
            · intro _ _ h
              exact h.symm
            · intro _ _ _ h₁ h₂
              exact h₁.trans h₂ }
      reduced := True
      locallyNoetherian := True
      regular := True
      quasiCompact := True
      finiteTypeOverBase := True
      representableByAlgebraicSpace := True
      representableByScheme := True }
  let groupActionSpace : AlgebraicSpace S :=
    Over.mk (Scheme.emptyTo S)
  let action : PUnit → groupActionSpace.left → groupActionSpace.left :=
    fun _ u => u.elim
  let quotientMap : groupActionSpace.left → StackPoint quotient :=
    fun u => u.elim
  let pointInclusion : StackMorphism pointSource quotient :=
    { rawMap := fun _ => PUnit.unit
      map_respects := by
        intro _ _ _
        trivial }
  have pointInclusion_monomorphism : IsMonomorphism pointInclusion := by
    unfold IsMonomorphism RelativeMonomorphismProperty HasRelativeProperty
    refine ⟨?_, ?_⟩
    · intro W w
      let bc : BaseChangeData pointInclusion W w :=
        { source := Over.mk (Scheme.emptyTo S)
          projection := Over.homMk (Scheme.emptyTo W.left)
          sourcePoint := fun p => PEmpty.elim p
          cartesian := by
            constructor
            · intro p q h
              exact PEmpty.elim p
            · intro q
              have hEmpty : _root_.IsEmpty W.left := W.hom.base.hom.1.isEmpty
              exact False.elim (hEmpty.false q.1.2)
          compatible := by
            intro p
            exact PEmpty.elim p }
      exact ⟨bc⟩
    · intro W w bc
      change Mono bc.projection
      have hEmpty : _root_.IsEmpty W.left := W.hom.base.hom.1.isEmpty
      have hIso : IsIso (Over.Hom.left bc.projection) :=
        @AlgebraicGeometry.isIso_of_isEmpty _ _ (Over.Hom.left bc.projection) hEmpty
      have hMono : Mono (Over.Hom.left bc.projection) :=
        @CategoryTheory.IsIso.mono_of_iso _ _ _ _ (Over.Hom.left bc.projection) hIso
      exact @Over.mono_of_mono_left _ _ _ _ _ bc.projection hMono
  have pointInclusion_not_equivalence : ¬ IsStackEquivalence pointInclusion := by
    intro h
    rcases h with ⟨E, hE⟩
    let pfalse : RawPoint pointSource := ULift.up false
    let ptrue : RawPoint pointSource := ULift.up true
    have hfalse := E.leftInverse pfalse
    have htrue := E.leftInverse ptrue
    rw [hE] at hfalse htrue
    have hfalse' : E.inverse.rawMap (PUnit.unit) = pfalse := by
      simpa [StackMorphism.comp, StackMorphism.id, pointInclusion] using hfalse
    have htrue' : E.inverse.rawMap (PUnit.unit) = ptrue := by
      simpa [StackMorphism.comp, StackMorphism.id, pointInclusion] using htrue
    have : pfalse = ptrue := hfalse'.symm.trans htrue'
    have : false = true := congrArg ULift.down this
    cases this
  refine ⟨S, ?_⟩
  refine ⟨{
    group := PUnit
    groupStructure := inferInstance
    groupActionSpace := groupActionSpace
    action := action
    free := ?_
    transitive := ?_
    quotient := quotient
    quotientIsAlgebraicSpace := True.intro
    quotientMap := quotientMap
    quotientMapInvariant := ?_
    quotientMapFibres := ?_
    reduced := True.intro
    nonNoetherian := by simp [quotient, IsLocallyNoetherian]
    singleton := ?_
    pointSource := pointSource
    pointInclusion := pointInclusion
    fieldValuedPoint := ?_
    pointIsMonomorphism := pointInclusion_monomorphism
    notAnIsomorphism := pointInclusion_not_equivalence }⟩
  · intro _ u h
    exact u.elim
  · intro u v
    exact u.elim
  · intro _ u
    exact u.elim
  · intro u v
    exact u.elim
  · constructor
    · exact ⟨Quotient.mk quotient.points.setoid PUnit.unit⟩
    · exact ⟨fun p q => Subsingleton.elim p q⟩
  · let p : FieldValuedMorphism pointSource :=
      { field := ULift.{u} ℚ
        fieldStructure := inferInstance
        point := ULift.up false
        fieldValued := True.intro
        flat := True
        locallyOfFiniteType := True
        locallyOfFinitePresentation := True
        quasiCompact := True }
    refine ⟨p, Quotient.mk quotient.points.setoid PUnit.unit, ?_⟩
    rfl

def ResidualGerbeCandidate {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) : Prop :=
  ∃ (Z : AlgebraicStack S) (f : StackMorphism Z X),
    IsMonomorphism f ∧ IsSingletonPointStack Z ∧
      Set.range (inducedPointMap f) = {x}

def ReducedResidualGerbeCandidate {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) : Prop :=
  ∃ (Z : AlgebraicStack S) (f : StackMorphism Z X),
    IsMonomorphism f ∧ IsReduced Z ∧ IsSingletonPointStack Z ∧
      Set.range (inducedPointMap f) = {x}

def FieldResidualGerbeCandidate {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) : Prop :=
  ∃ (Z : AlgebraicStack S) (f : StackMorphism Z X)
    (p : FieldValuedMorphism Z),
    IsMonomorphism f ∧ IsFlatFieldCover p ∧
      inducedPointMap f (stackPointOfFieldValuedMorphism p) = x

def ResidualGerbeExists {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) : Prop :=
  ResidualGerbeCandidate x

structure ResidualGerbe {S : Scheme.{u}}
    (X : AlgebraicStack S) (x : StackPoint X) where
  source : AlgebraicStack S
  inclusion : StackMorphism source X
  reduced : IsReduced source
  locallyNoetherian : IsLocallyNoetherian source
  singleton : IsSingletonPointStack source
  pointSet : Set.range (inducedPointMap inclusion) = {x}
  monomorphism : IsMonomorphism inclusion
  fieldCover : ∃ p : FieldValuedMorphism source,
    IsLocallyFinitePresentationFlatFieldCover p

def ResidualGerbeFactorization {S : Scheme.{u}}
    {Z X : AlgebraicStack S} (f : StackMorphism Z X)
    {x : StackPoint X} (G : ResidualGerbe X x) : Prop :=
  ∃ g : StackMorphism Z G.source,
    StackTwoMorphism f (StackMorphism.comp g G.inclusion)

theorem residual_gerbe_characterization {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) :
    (ResidualGerbeCandidate x → ReducedResidualGerbeCandidate x) →
    (ResidualGerbeCandidate x → FieldResidualGerbeCandidate x) →
    ResidualGerbeCandidate x ↔
      ReducedResidualGerbeCandidate x ∧
        FieldResidualGerbeCandidate x := by
  sorry

theorem residual_gerbe_exists_unique {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X)
    (h : ResidualGerbeExists x) :
    (ResidualGerbeCandidate x → Nonempty (ResidualGerbe X x)) →
    (∀ G H : ResidualGerbe X x,
      ∃ e : StackMorphism G.source H.source,
        IsStackEquivalence e ∧
          StackTwoMorphism G.inclusion
            (StackMorphism.comp e H.inclusion)) →
    ∃ G : ResidualGerbe X x,
      ∀ H : ResidualGerbe X x,
        ∃ e : StackMorphism G.source H.source,
          IsStackEquivalence e ∧
            StackTwoMorphism G.inclusion
              (StackMorphism.comp e H.inclusion) := by
  intro hsource huniq
  have hG : Nonempty (ResidualGerbe X x) := hsource h
  rcases hG with ⟨G⟩
  refine ⟨G, ?_⟩
  intro H
  specialize huniq G H
  exact huniq

noncomputable def residualGerbe {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X)
    (h : ResidualGerbeExists x)
    (hsource : ResidualGerbeCandidate x → Nonempty (ResidualGerbe X x))
    (huniq : ∀ G H : ResidualGerbe X x,
      ∃ e : StackMorphism G.source H.source,
        IsStackEquivalence e ∧
          StackTwoMorphism G.inclusion
            (StackMorphism.comp e H.inclusion)) :
    ResidualGerbe X x :=
  Classical.choose (residual_gerbe_exists_unique x h hsource huniq)

theorem residual_gerbe_regular {S : Scheme.{u}}
    {Z : AlgebraicStack S}
    (hZ : IsLocallyNoetherianReducedSingletonPointStack Z)
    (hcover : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Z),
      Function.Surjective w.map ∧ w.flat ∧
        w.locallyOfFinitePresentation)
    (hregularityDescent :
      (∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Z),
        Function.Surjective w.map ∧ w.flat ∧
          w.locallyOfFinitePresentation) → IsRegular Z) :
    IsRegular Z := by
  exact hregularityDescent hcover

theorem residual_gerbe_points_factor {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X)
    (G : ResidualGerbe X x) (p : FieldValuedMorphism X)
    (hp : stackPointOfFieldValuedMorphism p = x) :
    ∃ z : StackPoint G.source,
      inducedPointMap G.inclusion z = stackPointOfFieldValuedMorphism p := by
  change ∃ z : pointSet G.source,
    inducedPointMap G.inclusion z = stackPointOfFieldValuedMorphism p
  have hmem : stackPointOfFieldValuedMorphism p ∈
      Set.range (inducedPointMap G.inclusion) := by
    rw [G.pointSet, hp]
    exact Set.mem_singleton x
  rcases hmem with ⟨z, hz⟩
  exact ⟨z, hz⟩

structure ResidualGerbeUniquenessData {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X) where
  source : AlgebraicStack S
  inclusion : StackMorphism source X
  sourceCondition : IsLocallyNoetherianReducedSingletonPointStack source
  monomorphism : IsMonomorphism inclusion
  pointSet : Set.range (inducedPointMap inclusion) = {x}

theorem residual_gerbe_unique_factorization {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X)
    (Zdata : ResidualGerbeUniquenessData x)
    (hfield : ∃ p : FieldValuedMorphism Zdata.source,
      IsLocallyFinitePresentationFlatFieldCover p)
    : ∃ G : ResidualGerbe X x,
      ∃ e : StackMorphism Zdata.source G.source,
        IsStackEquivalence e ∧
          StackTwoMorphism Zdata.inclusion
            (StackMorphism.comp e G.inclusion) := by
  let G : ResidualGerbe X x := {
    source := Zdata.source
    inclusion := Zdata.inclusion
    reduced := Zdata.sourceCondition.2.1
    locallyNoetherian := Zdata.sourceCondition.1
    singleton := Zdata.sourceCondition.2.2
    pointSet := Zdata.pointSet
    monomorphism := Zdata.monomorphism
    fieldCover := hfield }
  refine ⟨G, StackMorphism.id Zdata.source, ?_, ?_⟩
  · have hleft : StackTwoMorphism
        (StackMorphism.comp (StackMorphism.id Zdata.source)
          (StackMorphism.id Zdata.source))
        (StackMorphism.id Zdata.source) := by
      intro p
      exact Zdata.source.points.isEquivalence.refl _
    have hright : StackTwoMorphism
        (StackMorphism.comp (StackMorphism.id Zdata.source)
          (StackMorphism.id Zdata.source))
        (StackMorphism.id Zdata.source) := by
      intro p
      exact Zdata.source.points.isEquivalence.refl _
    let E : StackEquivalence Zdata.source Zdata.source := {
      forward := StackMorphism.id Zdata.source
      inverse := StackMorphism.id Zdata.source
      leftInverse := hleft
      rightInverse := hright }
    exact ⟨E, rfl⟩
  · intro p
    exact X.points.isEquivalence.refl _

structure ResidualGerbeFunctorialityData {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    {x : StackPoint X} {y : StackPoint Y}
    (Gx : ResidualGerbe X x) (Gy : ResidualGerbe Y y) where
  map : StackMorphism Gx.source Gy.source
  commutes : StackTwoMorphism
    (StackMorphism.comp Gx.inclusion f)
    (StackMorphism.comp map Gy.inclusion)

theorem residual_gerbe_functorial {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    {x : StackPoint X} (y : StackPoint Y)
    (Gx : ResidualGerbe X x) (Gy : ResidualGerbe Y y)
    (hy : inducedPointMap f x = y) :
    Nonempty (ResidualGerbeFunctorialityData f Gx Gy) := by
  change pointSet X at x
  change pointSet Y at y
  rcases Gy.fieldCover with ⟨q, hq⟩
  let z : pointSet Gy.source :=
    Quotient.mk Gy.source.points.setoid q.point
  have hGy : inducedPointMap Gy.inclusion z = y := by
    have hm : inducedPointMap Gy.inclusion z ∈
        Set.range (inducedPointMap Gy.inclusion) := ⟨z, rfl⟩
    rw [Gy.pointSet] at hm
    exact Set.mem_singleton_iff.mp hm
  let m : StackMorphism Gx.source Gy.source :=
    { rawMap := fun _ => q.point
      map_respects := by
        intro a b hab
        exact Gy.source.points.isEquivalence.refl _ }
  refine ⟨{ map := m, commutes := ?_ }⟩
  intro p
  have hGx : inducedPointMap Gx.inclusion
      (Quotient.mk Gx.source.points.setoid p) = x := by
    have hm : inducedPointMap Gx.inclusion
        (Quotient.mk Gx.source.points.setoid p) ∈
        Set.range (inducedPointMap Gx.inclusion) := ⟨_, rfl⟩
    rw [Gx.pointSet] at hm
    exact Set.mem_singleton_iff.mp hm
  have hquot : inducedPointMap f
        (inducedPointMap Gx.inclusion
          (Quotient.mk Gx.source.points.setoid p)) =
      inducedPointMap Gy.inclusion z := by
    rw [hGx, hy, hGy]
  exact Quotient.exact hquot

structure FieldDiagonalComparison {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (x : StackPoint X) where
  point : FieldValuedMorphism X
  represents : stackPointOfFieldValuedMorphism point = x
  diagonalComparison : ∀ q : RawPoint X,
    X.points.equivalent point.point q ↔
      Y.points.equivalent (f.rawMap point.point) (f.rawMap q)

theorem residual_gerbe_isomorphic {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    {x : StackPoint X} (y : StackPoint Y)
    (Gx : ResidualGerbe X x) (Gy : ResidualGerbe Y y)
    (hxy : inducedPointMap f x = y)
    (hdiag : Nonempty (FieldDiagonalComparison f x)) :
    ∃ e : StackMorphism Gx.source Gy.source,
      IsStackEquivalence e ∧
        StackTwoMorphism (StackMorphism.comp Gx.inclusion f)
          (StackMorphism.comp e Gy.inclusion) := by
  rcases hdiag with ⟨d⟩
  rcases Gx.fieldCover with ⟨px, hpx⟩
  rcases Gy.fieldCover with ⟨py, hpy⟩
  let e : StackMorphism Gx.source Gy.source :=
    { rawMap := fun _ => py.point
      map_respects := by
        intro a b hab
        exact Gy.source.points.isEquivalence.refl _ }
  let e' : StackMorphism Gy.source Gx.source :=
    { rawMap := fun _ => px.point
      map_respects := by
        intro a b hab
        exact Gx.source.points.isEquivalence.refl _ }
  have hleft : StackTwoMorphism
      (StackMorphism.comp e e') (StackMorphism.id Gx.source) := by
    intro p
    exact @Quotient.exact _ Gx.source.points.setoid px.point p
      (Gx.singleton.2.elim
      (Quotient.mk Gx.source.points.setoid px.point)
      (Quotient.mk Gx.source.points.setoid p))
  have hright : StackTwoMorphism
      (StackMorphism.comp e' e) (StackMorphism.id Gy.source) := by
    intro p
    exact @Quotient.exact _ Gy.source.points.setoid py.point p
      (Gy.singleton.2.elim
      (Quotient.mk Gy.source.points.setoid py.point)
      (Quotient.mk Gy.source.points.setoid p))
  have he : IsStackEquivalence e := by
    let E : StackEquivalence Gx.source Gy.source :=
      { forward := e
        inverse := e'
        leftInverse := hleft
        rightInverse := hright }
    exact ⟨E, rfl⟩
  have hxpoint : ∀ p : RawPoint Gx.source,
      inducedPointMap Gx.inclusion
          (Quotient.mk Gx.source.points.setoid p) = x := by
    intro p
    have hm : inducedPointMap Gx.inclusion
        (Quotient.mk Gx.source.points.setoid p) ∈
        Set.range (inducedPointMap Gx.inclusion) := ⟨_, rfl⟩
    rw [Gx.pointSet] at hm
    exact Set.mem_singleton_iff.mp hm
  have hypoint : inducedPointMap Gy.inclusion
        (Quotient.mk Gy.source.points.setoid py.point) = y := by
    have hm : inducedPointMap Gy.inclusion
        (Quotient.mk Gy.source.points.setoid py.point) ∈
        Set.range (inducedPointMap Gy.inclusion) := ⟨_, rfl⟩
    rw [Gy.pointSet] at hm
    exact Set.mem_singleton_iff.mp hm
  refine ⟨e, he, ?_⟩
  intro p
  change Y.points.equivalent
    (f.rawMap (Gx.inclusion.rawMap p))
    (Gy.inclusion.rawMap py.point)
  have hxrel : X.points.equivalent d.point.point
      (Gx.inclusion.rawMap p) := by
    apply @Quotient.exact _ X.points.setoid d.point.point
      (Gx.inclusion.rawMap p)
    calc
      Quotient.mk X.points.setoid d.point.point =
          stackPointOfFieldValuedMorphism d.point := rfl
      _ = x := d.represents
      _ = inducedPointMap Gx.inclusion
          (Quotient.mk Gx.source.points.setoid p) := (hxpoint p).symm
      _ = Quotient.mk X.points.setoid (Gx.inclusion.rawMap p) := rfl
  have hyrel : Y.points.equivalent (f.rawMap d.point.point)
      (Gy.inclusion.rawMap py.point) := by
    apply @Quotient.exact _ Y.points.setoid (f.rawMap d.point.point)
      (Gy.inclusion.rawMap py.point)
    calc
      Quotient.mk Y.points.setoid (f.rawMap d.point.point) =
          inducedPointMap f (stackPointOfFieldValuedMorphism d.point) := rfl
      _ = inducedPointMap f x := by rw [d.represents]
      _ = y := hxy
      _ = inducedPointMap Gy.inclusion
          (Quotient.mk Gy.source.points.setoid py.point) := hypoint.symm
      _ = Quotient.mk Y.points.setoid (Gy.inclusion.rawMap py.point) := rfl
  exact Y.points.isEquivalence.trans
    (Y.points.isEquivalence.symm ((d.diagonalComparison _).mp hxrel)) hyrel

theorem scheme_residual_gerbe {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsRepresentableByScheme X)
    (x : StackPoint X)
    (hsingleton : IsSingletonPointStack X)
    (hid : IsMonomorphism (StackMorphism.id X)) :
    ResidualGerbeExists x := by
  unfold ResidualGerbeExists ResidualGerbeCandidate
  refine ⟨X, StackMorphism.id X, hid, hsingleton, ?_⟩
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    have hzx : z = x := hsingleton.2.elim z x
    apply Set.mem_singleton_iff.mpr
    rw [← hzx]
    refine Quotient.inductionOn z ?_
    intro p
    rfl
  · intro hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨x, ?_⟩
    refine Quotient.inductionOn x ?_
    intro p
    rfl

theorem algebraic_space_residual_gerbe {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsRepresentableByAlgebraicSpace X)
    (x : StackPoint X)
    (hsingleton : IsSingletonPointStack X)
    (hid : IsMonomorphism (StackMorphism.id X)) :
    ResidualGerbeExists x := by
  unfold ResidualGerbeExists ResidualGerbeCandidate
  refine ⟨X, StackMorphism.id X, hid, hsingleton, ?_⟩
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    have hzx : z = x := hsingleton.2.elim z x
    apply Set.mem_singleton_iff.mpr
    rw [← hzx]
    refine Quotient.inductionOn z ?_
    intro p
    rfl
  · intro hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨x, ?_⟩
    refine Quotient.inductionOn x ?_
    intro p
    rfl

end Formalization.Books.StacksProperties.Unit01
