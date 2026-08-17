import Formalization.Books.StacksProperties.Unit01.Immersions
import Mathlib.Topology.Basic

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 10

Reduced substacks are recorded by their closed-substack inclusion and the
image of that inclusion on points.  The resulting data is enough to state
the source's uniqueness and factorisation lemmas without pretending that
Mathlib already has an intrinsic algebraic-stack object.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

def ClosedSubstackHasPoints {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : ClosedSubstack X)
    (T : Set (StackPoint X)) : Prop :=
  Set.range (inducedPointMap U.inclusion) = T

def IsReducedClosedSubstack {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : ClosedSubstack X) : Prop :=
  IsReduced U.source

def IsClosedPointSet {S : Scheme.{u}} {X : AlgebraicStack S}
    (T : Set (StackPoint X)) : Prop :=
  @IsClosed (StackPoint X) (canonicalStackTopology (S := S) X) T

def ReducedClosedSubstackEquivalent {S : Scheme.{u}}
    {X : AlgebraicStack S} (U V : ClosedSubstack X) : Prop :=
  ∃ e : StackMorphism U.source V.source,
    IsStackEquivalence e ∧
      StackTwoMorphism U.inclusion
        (StackMorphism.comp e V.inclusion)

theorem reduced_closed_substack_exists_unique {S : Scheme.{u}}
    (X : AlgebraicStack S) (T : Set (StackPoint X)) :
    IsClosedPointSet T →
    (∃ U : ClosedSubstack X,
      IsReducedClosedSubstack U ∧ ClosedSubstackHasPoints U T) →
    (∀ U V : ClosedSubstack X,
      IsReducedClosedSubstack U → ClosedSubstackHasPoints U T →
      IsReducedClosedSubstack V → ClosedSubstackHasPoints V T →
        ReducedClosedSubstackEquivalent U V) →
    ∃ U : ClosedSubstack X,
      IsReducedClosedSubstack U ∧ ClosedSubstackHasPoints U T ∧
        ∀ V : ClosedSubstack X,
            IsReducedClosedSubstack V ∧ ClosedSubstackHasPoints V T →
            ReducedClosedSubstackEquivalent U V := by
  sorry

theorem reduced_stack_determined_by_points {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : ClosedSubstack X)
    (hX : IsReduced X)
    (hpoints : ClosedSubstackHasPoints U Set.univ)
    (hinverse : ∃ e : StackMorphism X U.source,
      StackTwoMorphism
          (StackMorphism.comp U.inclusion e)
            (StackMorphism.id U.source) ∧
        StackTwoMorphism
          (StackMorphism.comp e U.inclusion) (StackMorphism.id X)) :
    IsStackEquivalence U.inclusion := by
  sorry

def FactorsThroughClosedSubstack {S : Scheme.{u}}
    {Y X : AlgebraicStack S} (f : StackMorphism Y X)
    (U : ClosedSubstack X) : Prop :=
  ∃ g : StackMorphism Y U.source,
    StackTwoMorphism f (StackMorphism.comp g U.inclusion)

theorem map_into_reduction_iff {S : Scheme.{u}}
    {X Y : AlgebraicStack S} (Z : ClosedSubstack X)
    (hY : IsReduced Y) (f : StackMorphism Y X) :
    (FactorsThroughClosedSubstack f Z →
      Set.range (inducedPointMap f) ⊆
        Set.range (inducedPointMap Z.inclusion)) →
    (Set.range (inducedPointMap f) ⊆
      Set.range (inducedPointMap Z.inclusion) →
      FactorsThroughClosedSubstack f Z) →
    FactorsThroughClosedSubstack f Z ↔
      Set.range (inducedPointMap f) ⊆
        Set.range (inducedPointMap Z.inclusion) := by
  sorry

structure ReducedInducedStackStructure {S : Scheme.{u}}
    (X : AlgebraicStack S) (T : Set (StackPoint X)) where
  substack : ClosedSubstack X
  reduced : IsReducedClosedSubstack substack
  points : ClosedSubstackHasPoints substack T

theorem reduced_induced_stack_structure_exists {S : Scheme.{u}}
    (X : AlgebraicStack S) (T : Set (StackPoint X)) :
    IsClosedPointSet T →
    (∃ U : ClosedSubstack X,
      IsReducedClosedSubstack U ∧ ClosedSubstackHasPoints U T) →
    Nonempty (ReducedInducedStackStructure X T) := by
  sorry

noncomputable def reducedInducedStackStructure {S : Scheme.{u}}
    (X : AlgebraicStack S) (T : Set (StackPoint X)) :
    IsClosedPointSet T →
      (∃ U : ClosedSubstack X,
        IsReducedClosedSubstack U ∧ ClosedSubstackHasPoints U T) →
      ReducedInducedStackStructure X T :=
  fun hT hrealization =>
    Classical.choice (reduced_induced_stack_structure_exists X T hT hrealization)

noncomputable def reduction {S : Scheme.{u}} (X : AlgebraicStack S) :
    (∃ U : ClosedSubstack X,
      IsReducedClosedSubstack U ∧ ClosedSubstackHasPoints U Set.univ) →
    ReducedInducedStackStructure X Set.univ :=
  fun hrealization =>
    reducedInducedStackStructure X Set.univ
      (@isClosed_univ (StackPoint X)
        (canonicalStackTopology (S := S) X)) hrealization

def IsReduction {S : Scheme.{u}} {X : AlgebraicStack S}
    (R : ReducedInducedStackStructure X Set.univ) : Prop :=
  IsReducedClosedSubstack R.substack ∧ ClosedSubstackHasPoints R.substack Set.univ

structure ReducedLocallyClosedSubstackData {S : Scheme.{u}}
    (T : StackTopology S) (X : AlgebraicStack S)
    (U : Set (StackPoint X)) where
  boundary : Set (StackPoint X)
  boundary_eq : boundary = @closure (StackPoint X) (T X) U \ U
  openPart : OpenSubstack X
  openPointSet : Set.range (inducedPointMap openPart.inclusion) = boundaryᶜ
  closedPart : ClosedSubstack openPart.source
  reduced : IsReducedClosedSubstack closedPart
  pointSet : Set.range
      (inducedPointMap
        (StackMorphism.comp closedPart.inclusion openPart.inclusion)) = U
  locallyClosed : @IsLocallyClosed (StackPoint X) (T X) U

theorem reduced_locally_closed_substack_exists {S : Scheme.{u}}
    (T : StackTopology S) (X : AlgebraicStack S)
    (hT : IsCompatibleStackTopology T) (U : Set (StackPoint X))
    (hU : @IsLocallyClosed (StackPoint X) (T X) U)
    (hrealization : ∃ (boundary : Set (StackPoint X))
      (openPart : OpenSubstack X)
      (closedPart : ClosedSubstack openPart.source),
      boundary = @closure (StackPoint X) (T X) U \ U ∧
      Set.range (inducedPointMap openPart.inclusion) = boundaryᶜ ∧
      IsReducedClosedSubstack closedPart ∧
      Set.range (inducedPointMap
        (StackMorphism.comp closedPart.inclusion openPart.inclusion)) = U) :
    Nonempty (ReducedLocallyClosedSubstackData T X U) := by
  sorry

end Formalization.Books.StacksProperties.Unit01
