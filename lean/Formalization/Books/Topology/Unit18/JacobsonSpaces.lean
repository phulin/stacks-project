import Formalization.Books.Topology.Unit10.KrullDimension
import Formalization.Books.Topology.Unit15.ConstructibleSets
import Mathlib.Topology.Constructible
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Spectral.Prespectral
import Mathlib.Topology.Sets.OpenCover

/-!
# Topology, Chapter 18: Jacobson spaces

The source's Jacobson-space definition and its locally closed criterion are
Mathlib's canonical `JacobsonSpace` and `jacobsonSpace_iff_locallyClosed`.
Closed points are represented by `closedPoints`, and the closed-point
subspace has the induced subtype topology.  The source's constructible and
locally constructible subsets use Mathlib's `IsConstructible` and
`IsLocallyConstructible`; Chapter 15 records the finite-locally-closed normal
form for constructible sets.
-/

namespace Formalization.Books.Topology.Unit18

open Set Function _root_.Topology TopologicalSpace

universe u v

section JacobsonSpaces

variable {X : Type u} [TopologicalSpace X]

/-! ### Source-facing set predicates and traces -/

/-
Mathlib has no separate predicate for an arbitrary union of locally closed
subsets.  These two predicates are the literal source interfaces needed for
the inherited-subspace lemma and its finite-union correspondence.
-/

/-- A subset which is a finite union of locally closed subsets. -/
def IsFiniteUnionLocallyClosed (E : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧
    (∀ T ∈ S, IsLocallyClosed T) ∧ E = ⋃₀ S

/-- A subset which is a union of locally closed subsets. -/
def IsUnionOfLocallyClosed (E : Set X) : Prop :=
  ∃ S : Set (Set X), (∀ T ∈ S, IsLocallyClosed T) ∧ E = ⋃₀ S

/-- The intersection of a subset with the closed-point subspace. -/
def closedPointTrace (E : Set X) : Set (closedPoints X) :=
  (Subtype.val : closedPoints X → X) ⁻¹' E

/-- The induced map on closed subsets, written as a map of subtype lattices. -/
def closedSubsetsTrace (Z : {Z : Set X // IsClosed Z}) :
    {Z : Set (closedPoints X) // IsClosed Z} :=
  ⟨closedPointTrace (Z : Set X), Z.property.preimage continuous_subtype_val⟩

/-!
The definition and the equivalence with nonempty locally closed subsets are
already provided by Mathlib's `JacobsonSpace` and
`jacobsonSpace_iff_locallyClosed`; no parallel Jacobson predicate is
introduced here.
-/

/-! ### Closed points and the first lemmas -/

theorem closedSubsetsTrace_bijective [JacobsonSpace X] :
    Function.Bijective (closedSubsetsTrace (X := X)) := by
  sorry

theorem topologicalKrullDim_closedPoints [JacobsonSpace X] :
    topologicalKrullDim (closedPoints X) = topologicalKrullDim X := by
  sorry

theorem jacobsonSpace_of_closedPoints_dense_in_point_closures
    (h : ∀ x : X,
      closure (closedPoints X ∩ closure ({x} : Set X)) = closure ({x} : Set X)) :
    JacobsonSpace X := by
  sorry

theorem exists_nonclosed_point_of_not_jacobson
    [T0Space X] [PrespectralSpace X] (hX : ¬ JacobsonSpace X) :
    ∃ x : X, ¬ IsClosed ({x} : Set X) ∧ IsLocallyClosed ({x} : Set X) := by
  sorry

/-! ### Open covers -/

/-
`TopologicalSpace.IsOpenCover.jacobsonSpace_iff` is the canonical
open-cover form of the source's local Jacobson lemma.
-/

theorem jacobsonSpace_iff_isOpenCover {ι : Type v} (U : ι → Opens X)
    (hU : IsOpenCover U) :
    JacobsonSpace X ↔ ∀ i, JacobsonSpace (U i) :=
  TopologicalSpace.IsOpenCover.jacobsonSpace_iff hU

theorem closedPoints_eq_iUnion_image_closedPoints_of_isOpenCover
    {ι : Type v} (U : ι → Opens X) (hU : IsOpenCover U)
    [JacobsonSpace X] :
    closedPoints X =
      ⋃ i, (Subtype.val : U i → X) '' closedPoints (U i) := by
  sorry

/-! ### Jacobson subspaces -/

/-
The last case below uses Mathlib's `IsLocallyConstructible`, which is the
canonical pointwise/open-cover formulation of being locally a union of
constructible (hence finite locally closed) pieces from Chapter 15.
-/

theorem jacobsonSpace_of_isOpen [JacobsonSpace X] {T : Set X}
    (hT : IsOpen T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  sorry

theorem jacobsonSpace_of_isClosed [JacobsonSpace X] {T : Set X}
    (hT : IsClosed T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  sorry

theorem jacobsonSpace_of_isLocallyClosed [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyClosed T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  sorry

theorem jacobsonSpace_of_isUnionOfLocallyClosed [JacobsonSpace X] {T : Set X}
    (hT : IsUnionOfLocallyClosed T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  sorry

theorem jacobsonSpace_of_isConstructible [JacobsonSpace X] {T : Set X}
    (hT : IsConstructible T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  sorry

theorem jacobsonSpace_of_isLocallyConstructible [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyConstructible T) :
    JacobsonSpace T ∧
      ∀ x : T, x ∈ closedPoints T → IsClosed ({(x : X)} : Set X) := by
  sorry

/-! ### Finite Jacobson spaces -/

theorem discreteTopology_of_finite_jacobson [Finite X] [JacobsonSpace X] :
    DiscreteTopology X := by
  infer_instance

theorem discreteTopology_of_finite_closedPoints [JacobsonSpace X]
    (hX₀ : (closedPoints X).Finite) :
    DiscreteTopology X :=
  JacobsonSpace.discreteTopology hX₀

/-! ### Correspondence for finite unions of locally closed subsets -/

theorem exists_finiteUnionLocallyClosed_closedPoint_correspondence
    [JacobsonSpace X] :
    ∃ e :
        {E : Set X // IsFiniteUnionLocallyClosed E} ≃
          {E : Set (closedPoints X) // IsFiniteUnionLocallyClosed E},
      (∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
        (e E : Set (closedPoints X)) = closedPointTrace (E : Set X)) ∧
      (∀ E F : {E : Set X // IsFiniteUnionLocallyClosed E},
        ((E : Set X) ⊆ (F : Set X)) ↔
          ((e E : Set (closedPoints X)) ⊆ (e F : Set (closedPoints X)))) ∧
      (∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
        IsLocallyClosed (E : Set X) ↔
          IsLocallyClosed (e E : Set (closedPoints X))) ∧
      (∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
        IsOpen (E : Set X) ↔ IsOpen (e E : Set (closedPoints X))) ∧
      (∀ E : {E : Set X // IsFiniteUnionLocallyClosed E},
        IsClosed (E : Set X) ↔ IsClosed (e E : Set (closedPoints X))) := by
  sorry

/-! ### Correspondence for constructible subsets -/

theorem exists_constructible_closedPoint_correspondence [JacobsonSpace X] :
    ∃ e :
        {E : Set X // IsConstructible E} ≃
          {E : Set (closedPoints X) // IsConstructible E},
      (∀ E : {E : Set X // IsConstructible E},
        (e E : Set (closedPoints X)) = closedPointTrace (E : Set X)) ∧
      (∀ E F : {E : Set X // IsConstructible E},
        ((E : Set X) ⊆ (F : Set X)) ↔
          ((e E : Set (closedPoints X)) ⊆ (e F : Set (closedPoints X)))) ∧
      (∀ E : {E : Set X // IsConstructible E},
        (IsOpen (E : Set X) ∧ IsRetrocompact (E : Set X)) ↔
          (IsOpen (e E : Set (closedPoints X)) ∧
            IsRetrocompact (e E : Set (closedPoints X)))) ∧
      (∀ E : {E : Set X // IsConstructible E},
        IsOpen (E : Set X) ∧ IsRetrocompact (E : Set X) →
          e ⟨(E : Set X)ᶜ, E.property.compl⟩ =
            ⟨(e E : Set (closedPoints X))ᶜ, (e E).property.compl⟩) := by
  sorry

end JacobsonSpaces

end Formalization.Books.Topology.Unit18
