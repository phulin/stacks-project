import Formalization.Books.Topology.Unit05.Bases
import Formalization.Books.Topology.Unit09.NoetherianSpaces
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructible
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Spectral.Prespectral

/-!
# Topology, Chapter 12: Quasi-compact spaces and maps

The source's quasi-compact spaces are represented by Mathlib's `CompactSpace`
class and `IsCompact` predicate, which do not include a Hausdorff assumption.
The source's quasi-compact maps are Mathlib's `IsSpectralMap`, and its
retrocompact subsets are Mathlib's `IsRetrocompact`.  The compact-open basis
and finite-intersection hypotheses are likewise represented by the canonical
`PrespectralSpace` and `QuasiSeparatedSpace` interfaces.
-/

namespace Formalization.Books.Topology.Unit12

open Set Function _root_.Topology TopologicalSpace

universe u v w

section QuasiCompactSpacesAndMaps

variable {X : Type u} [TopologicalSpace X]

/-!
The first source definition is Mathlib's `CompactSpace X`, equivalently
`IsCompact (Set.univ : Set X)`.  The source's map definition is exactly
`IsSpectralMap`: continuity together with compactness of inverse images of
compact opens.  The source's subset definition is Mathlib's `IsRetrocompact`,
whose canonical API also records the equivalent subtype-map formulation.
-/

theorem compactSpace_iff_isCompact_univ :
    CompactSpace X ↔ IsCompact (Set.univ : Set X) := by
  exact isCompact_univ_iff.symm

theorem isSpectralMap_iff {Y : Type v} [TopologicalSpace Y] {f : X → Y} :
    IsSpectralMap f ↔
      Continuous f ∧
        ∀ ⦃V : Set Y⦄, IsOpen V → IsCompact V → IsCompact (f ⁻¹' V) := by
  sorry

theorem compactSpace_iff_finite_subcover :
    CompactSpace X ↔
      ∀ {ι : Type v} (U : ι → Set X),
        (∀ i, IsOpen (U i)) →
          (⋃ i, U i) = (Set.univ : Set X) →
            ∃ s : Finset ι, (⋃ i ∈ s, U i) = (Set.univ : Set X) := by
  sorry

/-! ### Composition and closed subsets -/

theorem isSpectralMap_comp {Y : Type v} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : IsSpectralMap f) (hg : IsSpectralMap g) :
    IsSpectralMap (g ∘ f) := by
  sorry

theorem isCompact_of_isClosed [CompactSpace X] {E : Set X} (hE : IsClosed E) :
    IsCompact E := by
  sorry

/-! ### Compact subsets of Hausdorff spaces -/

theorem isClosed_of_isCompact [T2Space X] {E : Set X} (hE : IsCompact E) :
    IsClosed E := by
  sorry

theorem separatedNhds_of_disjoint_isCompact [T2Space X]
    {E₁ E₂ : Set X} (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂)
    (hdisj : Disjoint E₁ E₂) :
    SeparatedNhds E₁ E₂ := by
  sorry

theorem isClosed_iff_isCompact_of_compactSpace [CompactSpace X] [T2Space X]
    {E : Set X} :
    IsClosed E ↔ IsCompact E := by
  sorry

/-! ### The finite-intersection characterization -/

theorem nonempty_iInter_of_finite_iInter_nonempty [CompactSpace X]
    {ι : Type v} {Z : ι → Set X}
    (hclosed : ∀ i, IsClosed (Z i))
    (hfinite : ∀ s : Finset ι, (⋂ i ∈ s, Z i).Nonempty) :
    (⋂ i, Z i).Nonempty := by
  sorry

/-! ### Images and closed points -/

theorem isCompact_range_of_compactSpace {Y : Type v} [TopologicalSpace Y]
    [CompactSpace X] {f : X → Y} (hf : Continuous f) :
    IsCompact (Set.range f) := by
  sorry

theorem isRetrocompact_range_of_isSpectralMap {Y : Type v} [TopologicalSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) :
    IsRetrocompact (Set.range f) := by
  sorry

theorem exists_closed_point [CompactSpace X] [T0Space X] [Nonempty X] :
    ∃ x : X, IsClosed ({x} : Set X) := by
  sorry

theorem isCompact_closedPoints [CompactSpace X] [T0Space X] :
    IsCompact (closedPoints X) := by
  sorry

/-! ### Connected components -/

theorem connectedComponent_eq_iInter_isClopen_of_compact_prespectral
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] (x : X) :
    connectedComponent x =
      ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X) := by
  sorry

theorem connectedComponent_eq_iInter_isClopen_of_compact_Hausdorff
    [CompactSpace X] [T2Space X] (x : X) :
    connectedComponent x =
      ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X) := by
  sorry

/-! ### Closed unions of connected components -/

/-- A subset which is an intersection of open-and-closed subsets. -/
def IsIntersectionOfClopens (T : Set X) : Prop :=
  ∃ S : Set (Set X), T = ⋂₀ S ∧ ∀ U ∈ S, IsClopen U

/-- A subset which is a union of connected components. -/
def IsUnionOfConnectedComponents (T : Set X) : Prop :=
  ∃ S : Set X, T = ⋃ x ∈ S, connectedComponent x

theorem isIntersectionOfClopens_iff_isClosed_isUnionOfConnectedComponents
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] {T : Set X} :
    IsIntersectionOfClopens T ↔
      IsClosed T ∧ IsUnionOfConnectedComponents T := by
  sorry

/-! ### Noetherian spaces -/

theorem noetherianSpace_isCompactSpace [NoetherianSpace X] : CompactSpace X := by
  infer_instance

theorem isRetrocompact_of_noetherianSpace [NoetherianSpace X] (Z : Set X) :
    IsRetrocompact Z := by
  sorry

theorem noetherianSpace_of_compactSpace_of_locallyNoetherianSpace
    [CompactSpace X]
    [Formalization.Books.Topology.Unit09.LocallyNoetherianSpace X] :
    NoetherianSpace X := by
  sorry

/-! ### Alexander subbase theorem -/

theorem compactSpace_of_isSubbasis
    {𝔅 : Set (Set X)}
    (h𝔅 : Formalization.Books.Topology.Unit05.IsSubbasis 𝔅)
    (hcover : ∀ P : Set (Set X), P ⊆ 𝔅 →
      ⋃₀ P = (Set.univ : Set X) →
        ∃ Q : Set (Set X), Q ⊆ P ∧ Q.Finite ∧ ⋃₀ Q = (Set.univ : Set X)) :
    CompactSpace X := by
  sorry

end QuasiCompactSpacesAndMaps

end Formalization.Books.Topology.Unit12
