import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.CardComponents
import Mathlib.Topology.Instances.RatLemmas

/-!
# Topology, Chapter 7: Connected components

The source's connected spaces, connected subsets, connected components, and
the quotient by connected components are represented by Mathlib's canonical
`ConnectedSpace`, `IsConnected`, `connectedComponent`, and
`ConnectedComponents` declarations.  The source's total and local
connectedness notions are likewise recorded through Mathlib's
`TotallyDisconnectedSpace` and `LocallyConnectedSpace` APIs.
-/

namespace Formalization.Books.Topology.Unit07

open Set Function _root_.Topology TopologicalSpace

universe u v

section ConnectedComponents

variable {X : Type u} [TopologicalSpace X]

/-! ## Connected spaces and connected components -/

/- The source's definition of a connected space is Mathlib's canonical class.
   The clopen characterization is the source-facing form of that class. -/
theorem connectedSpace_iff_clopen_partition :
    ConnectedSpace X ↔
      Nonempty X ∧ ∀ T : Set X, IsClopen T → T = ∅ ∨ T = Set.univ :=
  connectedSpace_iff_clopen

/- `connectedComponent` is Mathlib's canonical maximal connected subset. -/
theorem connectedComponent_is_connected (x : X) :
    IsConnected (connectedComponent x) := by
  exact isConnected_connectedComponent

theorem connectedComponent_is_maximal_connected {T : Set X} {x : X}
    (hT : IsConnected T) (hx : x ∈ T) : T ⊆ connectedComponent x := by
  exact hT.subset_connectedComponent hx

theorem connectedComponent_eq_of_mem {x y : X}
    (hy : y ∈ connectedComponent x) :
    connectedComponent x = connectedComponent y := by
  exact connectedComponent_eq hy

theorem connectedComponent_is_closed (x : X) :
    IsClosed (connectedComponent x) := by
  exact isClosed_connectedComponent

theorem not_connectedSpace_of_isEmpty [IsEmpty X] : ¬ ConnectedSpace X := by
  sorry

theorem image_of_connected {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    {E : Set X} (hE : IsConnected E) (hf : Continuous f) :
    IsConnected (f '' E) := by
  exact hE.image f hf.continuousOn

theorem closure_of_connected {T : Set X} (hT : IsConnected T) :
    IsConnected (closure T) := by
  exact hT.closure

/- The unique component containing a connected subset, expressed using the
   canonical component sets rather than a parallel component predicate. -/
theorem existsUnique_connectedComponent_containing {T : Set X}
    (hT : IsConnected T) :
    ∃! C : Set X, (∃ x : X, C = connectedComponent x) ∧ T ⊆ C := by
  sorry

theorem existsUnique_connectedComponent_containing_point (x : X) :
    ∃! C : Set X, (∃ y : X, C = connectedComponent y) ∧ x ∈ C := by
  sorry

theorem connectedComponent_cover :
    (⋃ x : X, connectedComponent x) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro x _
    exact mem_iUnion_of_mem x mem_connectedComponent

theorem connectedComponent_disjoint_of_ne {x y : X}
    (h : connectedComponent x ≠ connectedComponent y) :
    Disjoint (connectedComponent x) (connectedComponent y) := by
  exact connectedComponent_disjoint h

/- This records the source's warning that components need not be open. -/
theorem infinite_binary_product_has_singleton_components :
    ∀ x : ℕ → Bool,
      connectedComponent x = {x} ∧
        ¬ IsOpen ({x} : Set (ℕ → Bool)) := by
  sorry

/-! ## Quasi-components -/

theorem connectedComponent_subset_quasiComponent (x : X) :
    connectedComponent x ⊆
      ⋂ Z : {Z : Set X // IsClopen Z ∧ x ∈ Z}, (Z : Set X) := by
  exact connectedComponent_subset_iInter_isClopen

/- The following concrete carrier and basis encode the example in the
   source.  The named constructors play the roles of `x`, `y`, and `z_n`.
   A separate carrier is used so this example's topology does not replace the
   canonical topology on `Bool ⊕ ℕ`. -/
inductive QuasiComponentExample where
  | x
  | y
  | z (n : ℕ)

def quasiComponentExampleX : QuasiComponentExample := .x

def quasiComponentExampleY : QuasiComponentExample := .y

def quasiComponentExampleTail (n : ℕ) : Set QuasiComponentExample :=
  Set.range (fun k : ℕ => QuasiComponentExample.z (n + k))

def quasiComponentExampleBasis : Set (Set QuasiComponentExample) :=
  Set.range (fun n : ℕ =>
    ({QuasiComponentExample.z n} : Set QuasiComponentExample)) ∪
    Set.range (fun n : ℕ => insert quasiComponentExampleX (quasiComponentExampleTail n)) ∪
    Set.range (fun n : ℕ => insert quasiComponentExampleY (quasiComponentExampleTail n))

instance quasiComponentExample_topologicalSpace :
    TopologicalSpace QuasiComponentExample :=
  TopologicalSpace.generateFrom quasiComponentExampleBasis

theorem quasiComponentExample_basis_is_basis :
    TopologicalSpace.IsTopologicalBasis quasiComponentExampleBasis := by
  sorry

theorem quasiComponentExample_components :
    connectedComponent quasiComponentExampleX = {quasiComponentExampleX} ∧
      (⋂ Z :
          {Z : Set QuasiComponentExample //
            IsClopen Z ∧ quasiComponentExampleX ∈ Z},
          (Z : Set QuasiComponentExample)) =
        {quasiComponentExampleX, quasiComponentExampleY} := by
  sorry

/-! ## Quotienting by connected components -/

theorem connected_fibres_quotient_connectedComponents_bijective
    {Y : Type v} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hfib : ∀ y : Y, IsConnected (f ⁻¹' ({y} : Set Y)))
    (hclosed : ∀ T : Set Y,
      IsClosed T ↔ IsClosed (f ⁻¹' T)) :
    Function.Bijective hf.connectedComponentsMap := by
  sorry

theorem open_connected_fibres_connectedComponents_bijective
    {Y : Type v} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hopen : IsOpenMap f)
    (hfib : ∀ y : Y, IsConnected (f ⁻¹' ({y} : Set Y))) :
    Function.Bijective hf.connectedComponentsMap := by
  sorry

/-! ## A finite-fibre consequence -/

theorem finite_fibre_connectedComponents_at_most
    {Y : Type v} [TopologicalSpace Y] [Nonempty X] [ConnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (hopen : IsOpenMap f)
    (hclosed : IsClosedMap f) {y : Y}
    (hy : (f ⁻¹' ({y} : Set Y)).Finite) :
    ENat.card (ConnectedComponents X) ≤ (f ⁻¹' ({y} : Set Y)).encard := by
  sorry

theorem finite_fibre_connectedComponent_properties
    {Y : Type v} [TopologicalSpace Y] [Nonempty X] [ConnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (hopen : IsOpenMap f)
    (hclosed : IsClosedMap f) {y : Y}
    (hy : (f ⁻¹' ({y} : Set Y)).Finite) (x : X) :
    IsOpen (connectedComponent x) ∧
      IsClosed (connectedComponent x) ∧
      (f '' connectedComponent x).Nonempty ∧
      IsOpen (f '' connectedComponent x) ∧
      IsClosed (f '' connectedComponent x) ∧
      f '' connectedComponent x = (Set.univ : Set Y) := by
  sorry

/-! ## Totally disconnected spaces -/

theorem totallyDisconnectedSpace_iff_components_singletons :
    TotallyDisconnectedSpace X ↔
      ∀ x : X, connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton

theorem discreteSpace_totallyDisconnected [DiscreteTopology X] :
    TotallyDisconnectedSpace X := by
  infer_instance

theorem rational_subset_real_totallyDisconnected_not_discrete :
    IsTotallyDisconnected (Set.range ((↑) : ℚ → ℝ)) ∧
      ¬ DiscreteTopology (Set.range ((↑) : ℚ → ℝ)) := by
  sorry

/-! ## The quotient space of connected components -/

theorem connectedComponents_quotientMap :
    IsQuotientMap (ConnectedComponents.mk : X → ConnectedComponents X) := by
  exact ConnectedComponents.isQuotientMap_coe

theorem connectedComponents_map_continuous :
    Continuous (ConnectedComponents.mk : X → ConnectedComponents X) := by
  exact ConnectedComponents.continuous_coe

theorem connectedComponents_totallyDisconnected :
    TotallyDisconnectedSpace (ConnectedComponents X) := by
  infer_instance

theorem continuous_map_factors_through_connectedComponents
    {Y : Type v} [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) :
    ∃ g : ConnectedComponents X → Y,
      Continuous g ∧
        g ∘ ((↑) : X → ConnectedComponents X) = f := by
  sorry

/-! ## Locally connected spaces -/

theorem locallyConnectedSpace_iff_connected_neighborhood_basis :
    LocallyConnectedSpace X ↔
      ∀ x : X,
        (𝓝 x).HasBasis
          (fun s : Set X => s ∈ 𝓝 x ∧ IsConnected s) (fun s => s) := by
  sorry

theorem isLocallyConnected_open [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) : LocallyConnectedSpace U := by
  exact hU.locallyConnectedSpace

theorem isOpen_connectedComponent_of_locallyConnected
    [LocallyConnectedSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  exact isOpen_connectedComponent

theorem isClopen_connectedComponent_of_locallyConnected
    [LocallyConnectedSpace X] (x : X) :
    IsClopen (connectedComponent x) := by
  exact isClopen_connectedComponent

theorem isOpen_connectedComponent_of_open_subset
    [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) (x : X) :
    IsOpen (connectedComponentIn U x) := by
  exact hU.connectedComponentIn

theorem locallyConnected_open_connected_neighborhood_basis
    [LocallyConnectedSpace X] (x : X) :
    (𝓝 x).HasBasis
      (fun s : Set X => IsOpen s ∧ x ∈ s ∧ IsConnected s) (fun s => s) :=
  LocallyConnectedSpace.open_connected_basis x

end ConnectedComponents

end Formalization.Books.Topology.Unit07
