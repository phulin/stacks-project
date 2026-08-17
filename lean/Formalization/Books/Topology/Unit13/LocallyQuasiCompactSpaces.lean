import Formalization.Books.Topology.Unit12.QuasiCompactSpacesAndMaps
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.ShrinkingLemma

/-!
# Topology, Chapter 13: Locally quasi-compact spaces

The source's locally quasi-compact condition is Mathlib's
`LocallyCompactSpace`: its `local_compact_nhds` field says that every
neighbourhood of a point contains a compact neighbourhood of that point.
The weaker condition that every point merely has one compact neighbourhood is
Mathlib's `WeaklyLocallyCompactSpace`.  Neighbourhoods below are expressed by
membership in `𝓝`, so they are not required to be open.

The source uses `p + 1`-tuples of indices.  We represent such a tuple by a
function `Fin (p + 1) → I`, which also handles repetitions without adding
extra cases to the interfaces.
-/

namespace Formalization.Books.Topology.Unit13

open Set Function Filter _root_.Topology TopologicalSpace

universe u v w

section LocallyQuasiCompactSpaces

variable {X : Type u} [TopologicalSpace X]

/-! ### Locally quasi-compact spaces -/

theorem locallyCompactSpace_iff_weaklyLocallyCompactSpace [T2Space X] :
    LocallyCompactSpace X ↔ WeaklyLocallyCompactSpace X := by
  constructor
  · intro h
    let : LocallyCompactSpace X := h
    infer_instance
  · intro h
    let : WeaklyLocallyCompactSpace X := h
    infer_instance

/-! ### Baire category -/

theorem dense_iInter_of_isOpen_of_locallyCompactSpace
    [T2Space X] [LocallyCompactSpace X]
    (U : ℕ → Set X)
    (hUopen : ∀ n, 1 ≤ n → IsOpen (U n))
    (hUdense : ∀ n, 1 ≤ n → Dense (U n)) :
    Dense (⋂ (n : ℕ) (_h : 1 ≤ n), U n) := by
  sorry

/-! ### Relatively compact refinements -/

theorem exists_closure_subset_of_compactSpace
    [CompactSpace X] [T2Space X] {I : Type v}
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (⋃ i, U i) = (Set.univ : Set X)) :
    ∃ V : I → Set X,
      (⋃ i, V i) = (Set.univ : Set X) ∧
        (∀ i, IsOpen (V i)) ∧
          ∀ i, closure (V i) ⊆ U i := by
  sorry

/-! ### Refinements controlling multiple intersections -/

theorem exists_refinement_of_compactSpace
    [CompactSpace X] [T2Space X] (p : ℕ) {I : Type v}
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (⋃ i, U i) = (Set.univ : Set X))
    {κ : (Fin (p + 1) → I) → Type w}
    (W : ∀ a : Fin (p + 1) → I, κ a → Set X)
    (hWopen : ∀ (a : Fin (p + 1) → I) (k : κ a), IsOpen (W a k))
    (hWcover : ∀ a : Fin (p + 1) → I,
      (⋂ j, U (a j)) = ⋃ k, W a k) :
    ∃ (J : Type w) (V : J → Set X) (α : J → I),
      (⋃ j, V j) = (Set.univ : Set X) ∧
        (∀ j, IsOpen (V j)) ∧
          (∀ j, closure (V j) ⊆ U (α j)) ∧
            ∀ a : Fin (p + 1) → J,
              ∃ k : κ (fun j => α (a j)),
                (⋂ j, V (a j)) ⊆ W (fun j => α (a j)) k := by
  sorry

/-! ### Lifting a cover from a compact closed subset -/

theorem exists_lift_covering_of_isCompact
    [T2Space X] [LocallyCompactSpace X] {Z : Set X}
    (hZ : IsCompact Z) (p : ℕ) {I : Type v}
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (W : (Fin (p + 1) → I) → Set X)
    (hWopen : ∀ a, IsOpen (W a))
    (hWsubset : ∀ a, W a ⊆ ⋂ j, U (a j))
    (hZcover : Z ⊆ ⋃ i, U i)
    (hWZ : ∀ a, W a ∩ Z = (⋂ j, U (a j)) ∩ Z) :
    ∃ V : I → Set X,
      Z ⊆ ⋃ i, V i ∧
        (∀ i, IsOpen (V i)) ∧
          (∀ i, closure (V i) ⊆ U i) ∧
            ∀ a, (⋂ j, V (a j)) ⊆ W a := by
  sorry

/-! ### Lifting a cover from a quasi-compact Hausdorff subset -/

theorem exists_lift_covering_of_isCompact_of_pairwise_separated
    {Z : Set X} (hZ : IsCompact Z)
    (hZsep : ∀ ⦃x y : X⦄, x ∈ Z → y ∈ Z → x ≠ y →
      ∃ A B : Set X,
        IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) {I : Type v}
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (W : (Fin (p + 1) → I) → Set X)
    (hWopen : ∀ a, IsOpen (W a))
    (hWsubset : ∀ a, W a ⊆ ⋂ j, U (a j))
    (hZcover : Z ⊆ ⋃ i, U i)
    (hWZ : ∀ a, W a ∩ Z = (⋂ j, U (a j)) ∩ Z) :
    ∃ V : I → Set X,
      Z ⊆ ⋃ i, V i ∧
        (∀ i, IsOpen (V i)) ∧
          (∀ i, V i ⊆ U i) ∧
            (∀ i, closure (V i) ∩ Z ⊆ U i) ∧
              ∀ a, (⋂ j, V (a j)) ⊆ W a := by
  sorry

end LocallyQuasiCompactSpaces

end Formalization.Books.Topology.Unit13
