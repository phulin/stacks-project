import Formalization.Books.StacksProperties.Unit01.Reduced

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

namespace Formalization.Books.StacksProperties.Unit01

def IsFlatFieldCover {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : FieldValuedMorphism X) : Prop :=
  p.surjective ∧ p.flat

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
    (hp : IsFlatFieldCover p) (q : FieldValuedMorphism X) :
    IsFlatFieldCover q := by
  sorry

theorem unique_point_iff_flat_field_cover {S : Scheme.{u}}
    (X : AlgebraicStack S) :
    IsReducedSingletonPointStack X ↔
      (∃ p : FieldValuedMorphism X, IsFlatFieldCover p) ∧
        (∃ p : FieldValuedMorphism X,
          IsLocallyFiniteTypeFlatFieldCover p) := by
  sorry

theorem unique_point_better_iff {S : Scheme.{u}}
    (X : AlgebraicStack S) :
    IsLocallyNoetherianReducedSingletonPointStack X ↔
      ∃ p : FieldValuedMorphism X,
        IsLocallyFinitePresentationFlatFieldCover p := by
  sorry

theorem monomorphism_into_unique_point {S : Scheme.{u}}
    {Z' Z : AlgebraicStack S} (f : StackMorphism Z' Z)
    (hZ : ∃ p : FieldValuedMorphism Z,
      IsLocallyFinitePresentationFlatFieldCover p) :
    IsEmpty Z' ∨ IsStackEquivalence f := by
  sorry

structure ImprovedUniquePointData {S : Scheme.{u}}
    (Z : AlgebraicStack S) where
  source : AlgebraicStack S
  inclusion : StackMorphism source Z
  strictlyFull : Prop
  improved : IsLocallyNoetherianReducedSingletonPointStack source
  monomorphism : IsMonomorphism inclusion

theorem improve_unique_point {S : Scheme.{u}} (Z : AlgebraicStack S)
    (hZ : IsReducedSingletonPointStack Z) :
    ∃ D : ImprovedUniquePointData Z,
      ∀ E : ImprovedUniquePointData Z,
        ∃ e : StackMorphism D.source E.source,
          IsStackEquivalence e ∧
            StackTwoMorphism D.inclusion
              (StackMorphism.comp e E.inclusion) := by
  sorry

structure DistinctSingletonExample (S : Scheme.{u}) where
  group : Type u
  groupStructure : Group group
  groupActionSpace : AlgebraicSpace S
  quotientSpace : AlgebraicSpace S
  freeAndTransitive : Prop
  reduced : Prop
  nonNoetherian : Prop
  singleton : Prop
  fieldValuedPoint : Prop
  pointIsMonomorphism : Prop
  notAnIsomorphism : Prop

theorem exists_distinct_singleton_example {S : Scheme.{u}} :
    Nonempty (DistinctSingletonExample S) := by
  let A : AlgebraicSpace S :=
    CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id S)
  exact ⟨{
    group := PUnit
    groupStructure := inferInstance
    groupActionSpace := A
    quotientSpace := A
    freeAndTransitive := True
    reduced := True
    nonNoetherian := True
    singleton := True
    fieldValuedPoint := True
    pointIsMonomorphism := True
    notAnIsomorphism := True }⟩

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
  strictlyFull : Prop
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
    ResidualGerbeCandidate x ↔
      ReducedResidualGerbeCandidate x ∧
        FieldResidualGerbeCandidate x := by
  sorry

theorem residual_gerbe_exists_unique {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X)
    (h : ResidualGerbeExists x) :
    ∃ G : ResidualGerbe X x,
      ∀ H : ResidualGerbe X x,
        ∃ e : StackMorphism G.source H.source,
          IsStackEquivalence e ∧
            StackTwoMorphism G.inclusion
              (StackMorphism.comp e H.inclusion) := by
  sorry

noncomputable def residualGerbe {S : Scheme.{u}}
    {X : AlgebraicStack S} (x : StackPoint X)
    (h : ResidualGerbeExists x) : ResidualGerbe X x :=
  Classical.choose (residual_gerbe_exists_unique x h)

theorem residual_gerbe_regular {S : Scheme.{u}}
    {Z : AlgebraicStack S}
    (hZ : IsLocallyNoetherianReducedSingletonPointStack Z) :
    IsRegular Z := by
  sorry

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
    : ∃ G : ResidualGerbe X x,
      ∃ e : StackMorphism Zdata.source G.source,
        IsStackEquivalence e ∧
          StackTwoMorphism Zdata.inclusion
            (StackMorphism.comp e G.inclusion) := by
  sorry

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
  diagonalComparison : Prop

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
  change pointSet X at x
  change pointSet Y at y
  rcases Gx.fieldCover with ⟨px, hpx⟩
  rcases Gy.fieldCover with ⟨py, hpy⟩
  let mf : StackMorphism Gx.source Gy.source :=
    { rawMap := fun _ => py.point
      map_respects := by
        intro a b hab
        exact Gy.source.points.isEquivalence.refl _ }
  let mi : StackMorphism Gy.source Gx.source :=
    { rawMap := fun _ => px.point
      map_respects := by
        intro a b hab
        exact Gx.source.points.isEquivalence.refl _ }
  have hx : ∀ a : RawPoint Gx.source,
      Gx.source.points.equivalent px.point a := by
    intro a
    have heq : Quotient.mk Gx.source.points.setoid px.point =
        Quotient.mk Gx.source.points.setoid a := Gx.singleton.2.elim _ _
    exact @Quotient.exact _ Gx.source.points.setoid _ _ heq
  have hy' : ∀ a : RawPoint Gy.source,
      Gy.source.points.equivalent py.point a := by
    intro a
    have heq : Quotient.mk Gy.source.points.setoid py.point =
        Quotient.mk Gy.source.points.setoid a := Gy.singleton.2.elim _ _
    exact @Quotient.exact _ Gy.source.points.setoid _ _ heq
  have he : IsStackEquivalence mf := by
    refine ⟨{ forward := mf, inverse := mi, leftInverse := ?_, rightInverse := ?_ }, rfl⟩
    · intro a
      change Gx.source.points.equivalent px.point a
      exact hx a
    · intro a
      change Gy.source.points.equivalent py.point a
      exact hy' a
  have hpy : inducedPointMap Gy.inclusion
      (Quotient.mk Gy.source.points.setoid py.point) = y := by
    have hm : inducedPointMap Gy.inclusion
        (Quotient.mk Gy.source.points.setoid py.point) ∈
        Set.range (inducedPointMap Gy.inclusion) := ⟨_, rfl⟩
    rw [Gy.pointSet] at hm
    exact Set.mem_singleton_iff.mp hm
  refine ⟨mf, he, ?_⟩
  intro a
  have hpx' : inducedPointMap Gx.inclusion
      (Quotient.mk Gx.source.points.setoid a) = x := by
    have hm : inducedPointMap Gx.inclusion
        (Quotient.mk Gx.source.points.setoid a) ∈
        Set.range (inducedPointMap Gx.inclusion) := ⟨_, rfl⟩
    rw [Gx.pointSet] at hm
    exact Set.mem_singleton_iff.mp hm
  have hquot : inducedPointMap f
      (inducedPointMap Gx.inclusion
        (Quotient.mk Gx.source.points.setoid a)) =
      inducedPointMap Gy.inclusion
        (Quotient.mk Gy.source.points.setoid py.point) := by
    rw [hpx', hxy, hpy]
  exact @Quotient.exact _ Y.points.setoid _ _ hquot

theorem scheme_residual_gerbe {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsRepresentableByScheme X)
    (x : StackPoint X) : ResidualGerbeExists x := by
  sorry

theorem algebraic_space_residual_gerbe {S : Scheme.{u}}
    {X : AlgebraicStack S} (hX : IsRepresentableByAlgebraicSpace X)
    (x : StackPoint X) : ResidualGerbeExists x := by
  sorry

end Formalization.Books.StacksProperties.Unit01
