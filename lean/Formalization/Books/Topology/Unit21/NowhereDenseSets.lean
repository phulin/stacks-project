import Formalization.Books.Topology.Unit15.ConstructibleSets
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Maps.Basic

/-!
# Topology, Chapter 21: Nowhere dense sets

The source's interior and nowhere-dense predicates are Mathlib's canonical
`interior` and `IsNowhereDense`.  Relative statements are expressed in the
subtype topology, and a map that is a homeomorphism onto a closed subspace is
represented by `IsClosedEmbedding`.
-/

namespace Formalization.Books.Topology.Unit21

open Set Function _root_.Topology TopologicalSpace

universe u v

section NowhereDenseSets

variable {X : Type u} [TopologicalSpace X]

/-!
The first item of the source definition is already the canonical `interior`.
Its largest-open-subset property is provided by Mathlib's
`interior_maximal`.  The second item is exactly Mathlib's `IsNowhereDense`,
defined by `interior (closure T) = ∅`; no parallel local definitions are
introduced.
-/

/-! ### Finite unions -/

theorem isNowhereDense_sUnion {S : Set (Set X)} (hS : S.Finite)
    (hT : ∀ T ∈ S, IsNowhereDense T) :
    IsNowhereDense (⋃₀ S) := by
  sorry

/-! ### Open subspaces and open coverings -/

theorem isNowhereDense_of_isOpen_subspace
    {U : Set X} (hU : IsOpen U) {T : Set X} (hTU : T ⊆ U)
    (hT : IsNowhereDense ((Subtype.val : U → X) ⁻¹' T)) :
    IsNowhereDense T := by
  sorry

theorem isNowhereDense_of_isOpen_cover
    {ι : Type v} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : ⋃ i, U i = (univ : Set X))
    {T : Set X}
    (hT : ∀ i, IsNowhereDense
      ((Subtype.val : U i → X) ⁻¹' (T ∩ U i))) :
    IsNowhereDense T := by
  sorry

/-! ### Images under closed embeddings -/

theorem isNowhereDense_image_of_isClosedEmbedding
    {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (hclosed : IsClosedEmbedding f) {T : Set X}
    (hT : IsNowhereDense T) :
    IsNowhereDense (f '' T) := by
  sorry

/-! ### Preimages under open maps -/

theorem isClosed_isNowhereDense_preimage_of_isOpenMap
    {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (hopen : IsOpenMap f) {T : Set Y}
    (hTclosed : IsClosed T) (hT : IsNowhereDense T) :
    IsClosed (f ⁻¹' T) ∧ IsNowhereDense (f ⁻¹' T) := by
  sorry

theorem isClosed_isNowhereDense_iff_preimage_of_surjective_isOpenMap
    {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (hsurjective : Surjective f) (hopen : IsOpenMap f) {T : Set Y} :
    (IsClosed T ∧ IsNowhereDense T) ↔
      (IsClosed (f ⁻¹' T) ∧ IsNowhereDense (f ⁻¹' T)) := by
  sorry

/-! ### Dense open subsets of closures -/

theorem exists_dense_open_subset_of_closure_of_finite_union_isLocallyClosed
    {E : Set X}
    (hE : ∃ S : Set (Set X), S.Finite ∧
      (∀ T ∈ S, IsLocallyClosed T) ∧ E = ⋃₀ S) :
    ∃ U : Set (closure E), IsOpen U ∧ Dense U ∧ (U : Set X) ⊆ E := by
  sorry

/- The source's parenthetical example follows from the earlier chapter's
   finite-locally-closed description of constructible sets. -/
theorem exists_dense_open_subset_of_closure_of_isConstructible
    {E : Set X} (hE : IsConstructible E) :
    ∃ U : Set (closure E), IsOpen U ∧ Dense U ∧ (U : Set X) ⊆ E := by
  apply exists_dense_open_subset_of_closure_of_finite_union_isLocallyClosed
  exact Formalization.Books.Topology.Unit15.isConstructible_isFiniteUnion_isLocallyClosed hE

end NowhereDenseSets

end Formalization.Books.Topology.Unit21
