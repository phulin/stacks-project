import Formalization.Books.Topology.Unit09.NoetherianSpaces
import Formalization.Books.Topology.Unit15.ConstructibleSets

/-!
# Topology, Chapter 16: Constructible sets and Noetherian spaces

The source's constructible sets are Mathlib's `IsConstructible` predicate,
locally closed sets are `IsLocallyClosed`, and Noetherian spaces are
`NoetherianSpace`.  Relative open sets and density on a subset are expressed
using the induced topology on its subtype.
-/

namespace Formalization.Books.Topology.Unit16

open Set Function _root_.Topology TopologicalSpace

universe u v

section ConstructibleSetsAndNoetherianSpaces

variable {X : Type u} [TopologicalSpace X]

/-!
### Constructible sets and Noetherian spaces

The following declarations formalize the five lemmas in the source section,
in their source order.  A finite union of locally closed sets is represented
by a finite set of subsets and `Set.sUnion`; for a subset `Z`, an open or dense
intersection with `E` is represented by the preimage along the subtype
inclusion `Z → X`.
-/

/- The source's first lemma, using the finite-union normal form already exposed
   for constructible sets in Chapter 15. -/
theorem isConstructible_iff_finite_union_isLocallyClosed
    [NoetherianSpace X] {E : Set X} :
    IsConstructible E ↔
      ∃ S : Set (Set X), S.Finite ∧
        (∀ T ∈ S, IsLocallyClosed T) ∧ E = ⋃₀ S := by
  sorry

/- The source's second lemma: continuous preimages preserve the finite-union
   locally-closed description when both spaces are Noetherian. -/
theorem isConstructible_preimage_of_continuous
    {Y : Type v} [TopologicalSpace Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (f : X → Y) (hf : Continuous f) {E : Set Y}
    (hE : IsConstructible E) :
    IsConstructible (f ⁻¹' E) := by
  sorry

/- The source's third lemma, with "contains a nonempty open of Z" and
   "dense in Z" written in the subtype topology on Z. -/
theorem isConstructible_iff_irreducible_closed
    [NoetherianSpace X] {E : Set X} :
    IsConstructible E ↔
      ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
        ((∃ U : Set Z,
            IsOpen U ∧ U.Nonempty ∧
              U ⊆ (Subtype.val : Z → X) ⁻¹' E) ∨
          ¬ Dense ((Subtype.val : Z → X) ⁻¹' E)) := by
  sorry

/- The source's fourth lemma.  Membership in `𝓝 x` is the canonical
   neighborhood predicate for the ambient set E. -/
theorem isConstructible_iff_mem_nhds_of_irreducible_closed
    [NoetherianSpace X] (x : X) {E : Set X}
    (hE : IsConstructible E) :
    E ∈ 𝓝 x ↔
      ∀ Y : Set X, IsIrreducible Y → IsClosed Y → x ∈ Y →
        Dense ((Subtype.val : Y → X) ⁻¹' E) := by
  sorry

/- The source's fifth lemma, characterizing open sets by their intersections
   with irreducible closed subsets. -/
theorem isOpen_iff_irreducible_closed
    [NoetherianSpace X] {E : Set X} :
    IsOpen E ↔
      ∀ Y : Set X, IsIrreducible Y → IsClosed Y →
        (((Subtype.val : Y → X) ⁻¹' E = ∅) ∨
          ∃ U : Set Y,
            IsOpen U ∧ U.Nonempty ∧
              U ⊆ (Subtype.val : Y → X) ⁻¹' E) := by
  sorry

end ConstructibleSetsAndNoetherianSpaces

end Formalization.Books.Topology.Unit16
