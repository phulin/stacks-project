import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sets.OpenCover

/-!
# Topology, Chapter 2: Basic notions

The source section is a catalogue of standard topological notions.  The
canonical Mathlib interfaces are used directly for topological spaces,
points, locally closed and dense subsets, continuity, semicontinuity, open
and closed maps, neighborhoods, induced and product topologies, Hausdorff
spaces, fibre products, and discrete or indiscrete spaces.

The source's open coverings are coverings of an arbitrary subset by open
subsets of its ambient space.  Mathlib's `TopologicalSpace.IsOpenCover` is
the corresponding predicate for a cover of the whole ambient space, so the
relative version is recorded below.  A fundamental system of neighborhoods
is represented by the existing `Filter.HasBasis` interface for `𝓝 x`.
-/

namespace Formalization.Books.Topology.Unit02

open Set

universe u

section BasicNotions

variable {X : Type u} [TopologicalSpace X]

/-!
Items 1--6 of the source use the existing declarations
`TopologicalSpace`, `IsLocallyClosed`, `IsClosed`, `Dense`, and `Continuous`.
In particular, a closed point `x` is expressed by `IsClosed ({x} : Set X)`.
-/

/-!
For an extended-real-valued function, Mathlib's `EReal` is the canonical
model of `ℝ ∪ {−∞, +∞}` and `UpperSemicontinuous`/`LowerSemicontinuous`
provide the corresponding semicontinuity predicates.  The source uses only
real thresholds; the following source-facing equivalences record that
formulation without introducing a parallel semicontinuity predicate.
-/

theorem upperSemicontinuous_iff_real_thresholds {f : X → EReal} :
    UpperSemicontinuous f ↔
      ∀ a : ℝ, IsOpen {x | f x < (a : EReal)} := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  constructor
  · intro h a
    exact h (a : EReal)
  · intro h y
    refine EReal.rec ?_ (fun a => h a) ?_ y
    · have hbot : f ⁻¹' Iio (⊥ : EReal) = ∅ := by
        simp
      rw [hbot]
      exact isOpen_empty
    · have htop : f ⁻¹' Iio (⊤ : EReal) = ⋃ a : ℝ, f ⁻¹' Iio (a : EReal) := by
        ext x
        constructor
        · intro hx
          change f x < (⊤ : EReal) at hx
          rcases EReal.exists_between_coe_real hx with ⟨a, hxa, _⟩
          exact mem_iUnion.2 ⟨a, hxa⟩
        · intro hx
          rcases mem_iUnion.1 hx with ⟨a, hfa⟩
          change f x < (a : EReal) at hfa
          change f x < (⊤ : EReal)
          exact hfa.trans (EReal.coe_lt_top a)
      rw [htop]
      exact isOpen_iUnion fun a => h a

theorem lowerSemicontinuous_iff_real_thresholds {f : X → EReal} :
    LowerSemicontinuous f ↔
      ∀ a : ℝ, IsOpen {x | (a : EReal) < f x} := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  constructor
  · intro h a
    exact h (a : EReal)
  · intro h y
    refine EReal.rec ?_ (fun a => h a) ?_ y
    · have hbot : f ⁻¹' Ioi (⊥ : EReal) = ⋃ a : ℝ, f ⁻¹' Ioi (a : EReal) := by
        ext x
        constructor
        · intro hx
          change (⊥ : EReal) < f x at hx
          rcases EReal.exists_between_coe_real hx with ⟨a, _, hax⟩
          exact mem_iUnion.2 ⟨a, hax⟩
        · intro hx
          rcases mem_iUnion.1 hx with ⟨a, hax⟩
          change (a : EReal) < f x at hax
          change (⊥ : EReal) < f x
          exact (EReal.bot_lt_coe a).trans hax
      rw [hbot]
      exact isOpen_iUnion fun a => h a
    · have htop : f ⁻¹' Ioi (⊤ : EReal) = ∅ := by
        simp
      rw [htop]
      exact isOpen_empty

/-!
`IsOpenMap` and `IsClosedMap` are the canonical predicates for items 9 and
10.  As in the source, continuity is a contextual hypothesis; Mathlib keeps
it separate because an open or closed map need not be continuous.

For item 11, the source's statement that `E` is a neighborhood of `x` is
exactly the existing filter-membership proposition `E ∈ 𝓝 x`.  For item 12,
the induced topology is `TopologicalSpace.induced`, with the subtype
instance providing the topology on a subset.
-/

/-!
## Relative open coverings

`TopologicalSpace.IsOpenCover` covers the whole ambient space.  The source
allows a covering of an arbitrary set `U` by open subsets of `X`, so we use
a direct relative predicate needed for that statement.
-/

/-- An indexed family of open subsets of `X` whose union is `U`. -/
def IsOpenCoverOf (U : Set X) {ι : Type*} (u : ι → Set X) : Prop :=
  (∀ i, IsOpen (u i)) ∧ ⋃ i, u i = U

/-- A subcover obtained by restricting an open cover to an index subset. -/
def IsSubcoverOf (U : Set X) {ι : Type*} (u : ι → Set X) (I' : Set ι) : Prop :=
  IsOpenCoverOf U u ∧ IsOpenCoverOf U (fun i : I' => u i)

/-- One relative open cover refines another when every member of the former
is contained in some member of the latter. -/
def IsOpenCoverRefinement {ι κ : Type*} (U : Set X)
    (u : ι → Set X) (v : κ → Set X) : Prop :=
  IsOpenCoverOf U u ∧ IsOpenCoverOf U v ∧ ∀ j, ∃ i, v j ⊆ u i

/-!
The definition permits empty members of a cover.  It also gives the source's
empty-index convention: an empty-index family is a cover precisely of the
empty set.
-/

theorem isOpenCoverOf_empty_index_iff {U : Set X} :
    IsOpenCoverOf U (fun _ : Empty => (∅ : Set X)) ↔ U = ∅ := by
  simpa [IsOpenCoverOf] using (eq_comm : (∅ : Set X) = U ↔ U = ∅)

/-!
For item 16, a family `E : ι → Set X` is a fundamental system of
neighborhoods of `x` when it is a basis of the neighborhood filter.  This is
the standard `Filter.HasBasis` interface, specialized to a family whose
indices are all admissible.
-/

/-- `E` is a fundamental system of neighborhoods of `x`. -/
def IsFundamentalSystemOfNeighborhoods {ι : Type*} (x : X) (E : ι → Set X) : Prop :=
  (nhds x).HasBasis (fun _ : ι => True) E

/-!
Items 17--20 use the canonical Mathlib constructions directly:

* `T2Space X` is the Hausdorff/separated-space class and its field `T2Space.t2`
  has exactly the disjoint-open-neighborhood formulation in the source.
* the product topology is the instance on `X × Y`.
* for continuous maps `f : X → Y` and `g : Z → Y`, the topological fibre
  product is the categorical pullback `TopCat.pullback f g`; Mathlib also
  provides the concrete subtype model and its canonical topology.
* `DiscreteTopology` and `IndiscreteTopology` are the existing predicates for
  the discrete and indiscrete topologies.

The final `etc.` item is an intentionally open-ended catalogue entry, not a
precise assertion to formalize.
-/

end BasicNotions

end Formalization.Books.Topology.Unit02
