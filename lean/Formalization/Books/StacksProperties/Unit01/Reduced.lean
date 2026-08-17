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

theorem reduced_closed_substack_exists_unique {S : Scheme.{u}}
    (X : AlgebraicStack S) (T : Set (StackPoint X)) :
    ∃! U : ClosedSubstack X,
      IsReducedClosedSubstack U ∧ ClosedSubstackHasPoints U T := by
  sorry

theorem reduced_stack_determined_by_points {S : Scheme.{u}}
    {X : AlgebraicStack S} (U : ClosedSubstack X)
    (hX : IsReduced X)
    (hpoints : ClosedSubstackHasPoints U Set.univ) :
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
    Nonempty (ReducedInducedStackStructure X T) := by
  sorry

noncomputable def reducedInducedStackStructure {S : Scheme.{u}}
    (X : AlgebraicStack S) (T : Set (StackPoint X)) :
    ReducedInducedStackStructure X T :=
  Classical.choice (reduced_induced_stack_structure_exists X T)

noncomputable def reduction {S : Scheme.{u}} (X : AlgebraicStack S) :
    ReducedInducedStackStructure X Set.univ :=
  reducedInducedStackStructure X Set.univ

def IsReduction {S : Scheme.{u}} {X : AlgebraicStack S}
    (R : ReducedInducedStackStructure X Set.univ) : Prop :=
  R.reduced ∧ ClosedSubstackHasPoints R.substack Set.univ

structure ReducedLocallyClosedSubstackData {S : Scheme.{u}}
    (T : StackTopology S) (X : AlgebraicStack S)
    (U : Set (StackPoint X)) where
  boundary : Set (StackPoint X)
  openPart : OpenSubstack X
  closedPart : ClosedSubstack openPart.source
  reduced : IsReducedClosedSubstack closedPart
  pointSet : Prop
  locallyClosed : @IsLocallyClosed (StackPoint X) (T X) U

theorem reduced_locally_closed_substack_exists {S : Scheme.{u}}
    (T : StackTopology S) (X : AlgebraicStack S)
    (hT : IsCompatibleStackTopology T) (U : Set (StackPoint X))
    (hU : @IsLocallyClosed (StackPoint X) (T X) U) :
    Nonempty (ReducedLocallyClosedSubstackData T X U) := by
  sorry

end Formalization.Books.StacksProperties.Unit01
