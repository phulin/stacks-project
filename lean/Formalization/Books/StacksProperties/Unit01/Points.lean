import Formalization.Books.StacksProperties.Unit01.PropertiesOfMorphisms
import Mathlib.Topology.Basic

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 4

Points are the quotient of the field-valued representatives recorded by the
chapter-local `PointData`.  The maps and topology are stated at the quotient
level, so later sections can use them without choosing representatives.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

def PointEquivalent {S : Scheme.{u}} {X : AlgebraicStack S}
    (p q : RawPoint X) : Prop := X.points.equivalent p q

theorem point_equivalence_is_equivalence {S : Scheme.{u}}
    (X : AlgebraicStack S) : Equivalence (@PointEquivalent S X) := by
  exact X.points.isEquivalence

def pointSet {S : Scheme.{u}} (X : AlgebraicStack S) : Type u :=
  StackPoint X

theorem inducedPointMap_id {S : Scheme.{u}} (X : AlgebraicStack S) :
    inducedPointMap (StackMorphism.id X) = id := by
  funext p
  exact Quotient.inductionOn p (fun p => rfl)

theorem inducedPointMap_comp {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Y Z) :
    inducedPointMap (StackMorphism.comp f g) =
      inducedPointMap g ∘ inducedPointMap f := by
  funext p
  exact Quotient.inductionOn p (fun p => rfl)

def PointSquareCommutes {S : Scheme.{u}}
    {X Y Z W : AlgebraicStack S}
    (f : StackMorphism X Y) (g : StackMorphism X W)
    (h : StackMorphism Y Z) (k : StackMorphism W Z) : Prop :=
  StackTwoMorphism (StackMorphism.comp f h) (StackMorphism.comp g k)

theorem point_square_commutes {S : Scheme.{u}}
    {X Y Z W : AlgebraicStack S}
    (f : StackMorphism X Y) (g : StackMorphism X W)
    (h : StackMorphism Y Z) (k : StackMorphism W Z)
    (hsquare : PointSquareCommutes f g h k) :
    inducedPointMap h ∘ inducedPointMap f =
      inducedPointMap k ∘ inducedPointMap g := by
  funext p
  exact Quotient.inductionOn p (fun p => Quotient.sound (hsquare p))

theorem equivalence_bijective_on_points {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (e : StackEquivalence X Y) :
    Function.Bijective (inducedPointMap e.forward) := by
  let F := inducedPointMap e.forward
  let G := inducedPointMap e.inverse
  have hleft : G ∘ F = id := by
    funext p
    exact Quotient.inductionOn p (fun p => Quotient.sound (e.leftInverse p))
  have hright : F ∘ G = id := by
    funext p
    exact Quotient.inductionOn p (fun p => Quotient.sound (e.rightInverse p))
  constructor
  · intro p q h
    calc
      p = (G ∘ F) p := (congrFun hleft p).symm
      _ = G (F p) := rfl
      _ = G (F q) := congrArg G h
      _ = (G ∘ F) q := rfl
      _ = q := congrFun hleft q
  · intro p
    exact ⟨G p, congrFun hright p⟩

def SpaceMorphismSurjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : SpaceMorphism X Y) : Prop :=
  Function.Surjective f.left

def RelativeSurjectiveProperty (S : Scheme.{u}) : RelativeSpaceProperty S where
  property := fun _ _ f => SpaceMorphismSurjective f
  fppfLocalOnTarget := True
  stableUnderArbitraryBaseChange := True
  localOnSource := fun _ => True
  preservedUnderComposition := True

def PointFiberProduct {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) : Type u :=
  {p : pointSet X × pointSet Z //
    inducedPointMap f p.1 = inducedPointMap g p.2}

def fibreProductPointsMap {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) :
    pointSet (fibreProduct f g) → PointFiberProduct f g :=
  Quotient.lift
    (fun p =>
      ⟨(Quotient.mk X.points.setoid p.1.1,
          Quotient.mk Z.points.setoid p.1.2),
        @Quotient.sound _ Y.points.setoid _ _ p.2⟩)
    (by
      intro p q h
      apply Subtype.ext
      apply Prod.ext
      · exact @Quotient.sound _ X.points.setoid _ _ h.1
      · exact @Quotient.sound _ Z.points.setoid _ _ h.2)

theorem points_cartesian_surjective {S : Scheme.{u}}
    {X Y Z : AlgebraicStack S} (f : StackMorphism X Y)
    (g : StackMorphism Z Y) :
    Function.Surjective (fibreProductPointsMap f g) := by
  intro y
  rcases y with ⟨⟨px, pz⟩, h⟩
  induction px using Quotient.inductionOn with
  | _ p =>
    induction pz using Quotient.inductionOn with
    | _ q =>
      refine ⟨Quotient.mk _ ⟨⟨p, q⟩, Quotient.exact h⟩, ?_⟩
      rfl

theorem characterize_surjective {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (f : StackMorphism X Y)
    (hf : RepresentableByAlgebraicSpaces f) :
    (Function.Surjective (inducedPointMap f) →
      ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
        (bc : BaseChangeData f W w),
        Function.Surjective bc.projection.left) →
    ((∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W Y)
        (bc : BaseChangeData f W w),
        Function.Surjective bc.projection.left) →
      Function.Surjective (inducedPointMap f)) →
    Function.Surjective (inducedPointMap f) ↔
      HasRelativeProperty (RelativeSurjectiveProperty S) f := by
  sorry

def PresentationRelation {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X)
    (u v : p.source) : Prop :=
  ∃ r : p.relation, p.sourceMap r = u ∧ p.targetMap r = v

theorem presentation_relation_is_equivalence {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) :
    Equivalence (PresentationRelation p) := by
  exact p.relationIsEquivalence

def presentationRelationSetoid {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) : Setoid p.source where
  r := PresentationRelation p
  iseqv := presentation_relation_is_equivalence p

def presentationPointsQuotient {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) : Type u :=
  Quotient (presentationRelationSetoid p)

theorem points_presentation_quotient {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : StackPresentation X) :
    Nonempty (presentationPointsQuotient p ≃ pointSet X) := by
  let qmap : presentationPointsQuotient p → pointSet X :=
    Quotient.lift p.map (by
      intro u v huv
      exact (p.mapRelation u v).mp huv)
  let qinv : pointSet X → presentationPointsQuotient p :=
    fun x => Quotient.mk _ (Classical.choose (p.surjective x))
  have hqinv_qmap : ∀ q, qinv (qmap q) = q := by
    intro q
    refine Quotient.inductionOn q ?_
    intro u
    dsimp [qinv, qmap]
    apply Quotient.sound
    exact (p.mapRelation _ _).mpr
      (Classical.choose_spec (p.surjective (p.map u)))
  have hqmap_qinv : ∀ x, qmap (qinv x) = x := by
    intro x
    dsimp [qinv, qmap]
    exact Classical.choose_spec (p.surjective x)
  exact ⟨Equiv.mk qmap qinv hqinv_qmap hqmap_qinv⟩

structure GeneralPresentationData {S : Scheme.{u}}
    (X : AlgebraicStack S) where
  source : Scheme.{u}
  map : source → pointSet X
  relation : Scheme.{u}
  sourceMap : relation ⟶ source
  targetMap : relation ⟶ source
  surjective : Function.Surjective map
  groupoidAxioms : Prop
  relationIsEquivalence :
    Equivalence (fun u v =>
      ∃ r : relation, sourceMap r = u ∧ targetMap r = v)
  mapRelation :
    ∀ u v,
      (∃ r : relation, sourceMap r = u ∧ targetMap r = v) ↔
        map u = map v

def GeneralPresentationRelation {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : GeneralPresentationData X)
    (u v : p.source) : Prop :=
  ∃ r : p.relation, p.sourceMap r = u ∧ p.targetMap r = v

theorem general_presentation_quotient {S : Scheme.{u}}
    {X : AlgebraicStack S} (p : GeneralPresentationData X)
    (hrel : Equivalence (GeneralPresentationRelation p)) :
    Nonempty
      (Quotient ⟨GeneralPresentationRelation p, hrel⟩ ≃ pointSet X) := by
  let qmap : Quotient ⟨GeneralPresentationRelation p, hrel⟩ → pointSet X :=
    Quotient.lift p.map (by
      intro u v huv
      exact (p.mapRelation u v).mp huv)
  let qinv : pointSet X → Quotient ⟨GeneralPresentationRelation p, hrel⟩ :=
    fun x => Quotient.mk _ (Classical.choose (p.surjective x))
  have hqinv_qmap : ∀ q, qinv (qmap q) = q := by
    intro q
    refine Quotient.inductionOn q ?_
    intro u
    dsimp [qinv, qmap]
    apply Quotient.sound
    exact (p.mapRelation _ _).mpr
      (Classical.choose_spec (p.surjective (p.map u)))
  have hqmap_qinv : ∀ x, qmap (qinv x) = x := by
    intro x
    dsimp [qinv, qmap]
    exact Classical.choose_spec (p.surjective x)
  exact ⟨Equiv.mk qmap qinv hqinv_qmap hqmap_qinv⟩

abbrev StackTopology (S : Scheme.{u}) :=
  ∀ X : AlgebraicStack S, TopologicalSpace (pointSet X)

def IsCompatibleStackTopology {S : Scheme.{u}}
    (T : StackTopology S) : Prop :=
  (∀ {X Y : AlgebraicStack S} (f : StackMorphism X Y),
      @Continuous (pointSet X) (pointSet Y) (T X) (T Y) (inducedPointMap f)) ∧
    (∀ {X : AlgebraicStack S} (W : AlgebraicSpace S)
      (w : SpaceToStackMorphism W X),
      w.flat → w.locallyOfFinitePresentation →
        @IsOpenMap W.left (pointSet X) inferInstance (T X) w.map)

theorem exists_stack_topology {S : Scheme.{u}} :
    ∃ T : StackTopology S, IsCompatibleStackTopology T := by
  let T : StackTopology S := fun X => (⊥ : TopologicalSpace (pointSet X))
  refine ⟨T, ?_⟩
  constructor
  · intro X Y f
    letI : TopologicalSpace (StackPoint X) := ⊥
    letI : TopologicalSpace (StackPoint Y) := ⊥
    letI : DiscreteTopology (StackPoint X) := discreteTopology_bot _
    change @Continuous (StackPoint X) (StackPoint Y)
      (⊥ : TopologicalSpace (StackPoint X))
      (⊥ : TopologicalSpace (StackPoint Y)) (inducedPointMap f)
    exact continuous_of_discreteTopology
  · intro X W w _ _
    letI : TopologicalSpace (pointSet X) := ⊥
    letI : DiscreteTopology (pointSet X) := discreteTopology_bot _
    intro U _
    exact isOpen_discrete _

theorem exists_unique_stack_topology {S : Scheme.{u}}
    (hunique : ∀ T U : StackTopology S,
      IsCompatibleStackTopology T → IsCompatibleStackTopology U → T = U) :
    ∃! T : StackTopology S, IsCompatibleStackTopology T := by
  rcases exists_stack_topology (S := S) with ⟨T, hT⟩
  refine ⟨T, hT, ?_⟩
  intro U hU
  exact hunique U T hU hT

@[instance_reducible]
noncomputable def canonicalStackTopology {S : Scheme.{u}} : StackTopology S :=
  Classical.choose (exists_stack_topology (S := S))

theorem canonicalStackTopology_is_compatible {S : Scheme.{u}} :
    IsCompatibleStackTopology (canonicalStackTopology (S := S)) := by
  exact (exists_stack_topology (S := S)).choose_spec

abbrev underlyingTopologicalSpace {S : Scheme.{u}}
    (T : StackTopology S) (X : AlgebraicStack S) : TopologicalSpace (pointSet X) :=
  T X

def HasQuasiCompactOpenNeighbourhoodBasis {α : Type u}
    (τ : TopologicalSpace α) : Prop :=
  ∀ x : α, ∀ U : Set α, @IsOpen α τ U → x ∈ U →
    ∃ V : Set α, @IsOpen α τ V ∧ @IsCompact α τ V ∧ x ∈ V ∧ V ⊆ U

theorem points_locally_quasi_compact {S : Scheme.{u}}
    {X : AlgebraicStack S} (T : StackTopology S)
    (hT : IsCompatibleStackTopology T) :
    (∀ (x : StackPoint X) (U : Set (StackPoint X)),
      @IsOpen (StackPoint X) (T X) U → x ∈ U →
      ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X)
        (u : W.left) (V : Set W.left),
        w.flat ∧ w.locallyOfFinitePresentation ∧ w.smooth ∧
          w.map u = x ∧
          @Continuous W.left (StackPoint X) inferInstance (T X) w.map ∧
          @IsOpen W.left inferInstance V ∧
          @IsCompact W.left inferInstance V ∧
          u ∈ V ∧ ∀ y, y ∈ V → w.map y ∈ U) →
    HasQuasiCompactOpenNeighbourhoodBasis (T X) := by
  unfold HasQuasiCompactOpenNeighbourhoodBasis pointSet
  intro hexists x U hU hx
  letI : TopologicalSpace (StackPoint X) := T X
  rcases hexists x U hU hx with
    ⟨W, w, u, V, hflat, hlfp, hsmooth, hmap, hcontinuous, hopen, hcompact, hu, hsubset⟩
  refine ⟨w.map '' V, ?_, ?_, ?_, ?_⟩
  · exact (hT.2 W w hflat hlfp) V hopen
  · exact hcompact.image hcontinuous
  · exact ⟨u, hu, hmap⟩
  · intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact hsubset v hv

end Formalization.Books.StacksProperties.Unit01
