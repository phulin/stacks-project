import Formalization.Books.Topology.Unit08.IrreducibleComponents
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.WithTopology

/-!
# Topology, Chapter 9: Noetherian topological spaces

The source's Noetherian spaces use Mathlib's canonical `NoetherianSpace`
predicate.  Mathlib defines it using the ascending chain condition on opens;
the equivalent well-foundedness statement for closed sets is recorded below
in the source's convention.  Local Noetherianity is not present in Mathlib's
topology API, so it is defined here using neighborhoods and the induced
topology on a subset.
-/

namespace Formalization.Books.Topology.Unit09

open Set Function _root_.Topology TopologicalSpace

universe u v

section NoetherianTopologicalSpaces

variable {X : Type u} [TopologicalSpace X]

/-! ## Definition -/

/- The source's definition of a Noetherian space is Mathlib's canonical
   `TopologicalSpace.NoetherianSpace`; this equivalence exposes its closed-set
   descending-chain formulation. -/
theorem noetherianSpace_iff_descending_closed :
    NoetherianSpace X ↔ WellFoundedLT (Closeds X) :=
  (noetherianSpace_TFAE X).out 0 1

/- A neighborhood in the source is represented by membership in `𝓝 x`, and
   `NoetherianSpace U` uses the subtype topology induced from `X`. -/
class LocallyNoetherianSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_mem_nhds_noetherian :
    ∀ x : X, ∃ U : Set X, U ∈ 𝓝 x ∧ NoetherianSpace U

export LocallyNoetherianSpace (exists_mem_nhds_noetherian)

/-! ## Basic properties of Noetherian spaces -/

/- The first part of the source's lemma is already the canonical Mathlib
   subtype instance. -/
theorem noetherianSpace_subtype [NoetherianSpace X] (U : Set X) :
    NoetherianSpace U := by
  infer_instance

/- The second and third parts are the corresponding Mathlib theorems. -/
theorem noetherianSpace_finite_irreducibleComponents [NoetherianSpace X] :
    (irreducibleComponents X).Finite := by
  exact NoetherianSpace.finite_irreducibleComponents

theorem noetherianSpace_exists_isOpen_nonempty_subset_irreducibleComponent
    [NoetherianSpace X] (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ Z := by
  exact NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ

/-! ## Images and finite unions -/

theorem noetherianSpace_image {Y : Type v} [TopologicalSpace Y]
    [NoetherianSpace X] {f : X → Y} (hf : Continuous f) :
    NoetherianSpace (Set.range f) := by
  exact NoetherianSpace.range f hf

theorem locallyNoetherianSpace_image {Y : Type v} [TopologicalSpace Y]
    [LocallyNoetherianSpace X] {f : X → Y} (hf : Continuous f)
    (hopen : IsOpenMap f) :
    LocallyNoetherianSpace (Set.range f) := by
  sorry

theorem noetherianSpace_iUnion_of_finite {ι : Type v} [Finite ι]
    (U : ι → Set X) (hU : ∀ i, NoetherianSpace (U i)) :
    NoetherianSpace (⋃ i, U i) := by
  let _ : ∀ i, NoetherianSpace (U i) := hU
  exact NoetherianSpace.iUnion U

/-! ## Closed points and the source's example -/

theorem exists_closed_point_of_noetherian_t0
    [NoetherianSpace X] [T0Space X] [Nonempty X] :
    ∃ x : X, IsClosed ({x} : Set X) := by
  obtain ⟨x, _, hx⟩ :=
    IsClosed.exists_closed_singleton (S := (Set.univ : Set X)) isClosed_univ univ_nonempty
  exact ⟨x, hx⟩

/- The source uses the positive natural numbers.  `ℕ+` is the canonical
   positive-natural carrier, and `WithTopology` lets this example carry the
   source topology without changing the usual topology on `ℕ+` elsewhere. -/
def initialSegmentOpenSets : Set (Set ℕ+) :=
  ({∅, Set.univ} : Set (Set ℕ+)) ∪
    Set.range (fun n : ℕ+ => Set.Iic n)

@[instance_reducible]
def initialSegmentTopology : TopologicalSpace ℕ+ :=
  TopologicalSpace.generateFrom initialSegmentOpenSets

abbrev InitialSegmentSpace := WithTopology ℕ+ initialSegmentTopology

theorem initialSegmentSpace_isOpen_iff {U : Set InitialSegmentSpace} :
    IsOpen U ↔
      U = ∅ ∨ U = Set.univ ∨
        ∃ n : ℕ+, U =
          ((WithTopology.equiv ℕ+ initialSegmentTopology) ⁻¹' (Set.Iic n)) := by
  sorry

theorem initialSegmentSpace_locallyNoetherian :
    LocallyNoetherianSpace InitialSegmentSpace := by
  sorry

theorem initialSegmentSpace_has_no_closed_points :
    ∀ x : InitialSegmentSpace, ¬ IsClosed ({x} : Set InitialSegmentSpace) := by
  sorry

/- The last sentence of the source refers to the later scheme-theoretic
   closed-point lemma.  Mathlib's canonical interface for that source notion
   is used here to state the cross-reference without importing a later project
   chapter. -/
theorem initialSegmentSpace_not_underlying_locallyNoetherian_scheme :
    ¬ ∃ S : AlgebraicGeometry.Scheme,
      AlgebraicGeometry.IsLocallyNoetherian S ∧
        Nonempty (S ≃ₜ InitialSegmentSpace) := by
  sorry

/-! ## Local connectedness -/

theorem locallyConnectedSpace_of_locallyNoetherian
    [LocallyNoetherianSpace X] : LocallyConnectedSpace X := by
  sorry

end NoetherianTopologicalSpaces

end Formalization.Books.Topology.Unit09
