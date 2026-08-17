import Mathlib.Topology.SeparatedMap

/-!
# Topology, Chapter 4: Separated maps

The source defines separatedness for a continuous map by requiring its
diagonal into the topological fibre product to be a closed map.  Mathlib's
`IsSeparatedMap` is the canonical predicate for this notion, and its
`toPullbackDiag` and `Function.pullbackDiagonal` APIs provide the diagonal
map and its image.
-/

namespace Formalization.Books.Topology.Unit04

open Set

universe u v w

section SeparatedMaps

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-!
The source's definition is represented by Mathlib's existing
`IsSeparatedMap` predicate and its equivalent closed-map formulation.  The
continuity hypothesis is retained in the chapter-facing statement, even
though the canonical equivalence is valid without it.
-/

theorem separated_iff_closed_map {f : X → Y} (_hf : Continuous f) :
    IsSeparatedMap f ↔ IsClosedMap (toPullbackDiag f) :=
  isSeparatedMap_iff_isClosedMap

/-!
The first two alternatives in the source's characterization lemma are the
canonical closed-map and closed-diagonal formulations.
-/

theorem separated_iff_closed_diagonal {f : X → Y} (_hf : Continuous f) :
    IsSeparatedMap f ↔ IsClosed (Function.pullbackDiagonal f) :=
  isSeparatedMap_iff_isClosed_diagonal

/-!
Unfolding `IsSeparatedMap` gives the source's pointwise formulation: points
in one fibre, when distinct, have disjoint open neighbourhoods.
-/

theorem separated_iff_fiberwise_disjoint_opens {f : X → Y} (_hf : Continuous f) :
    IsSeparatedMap f ↔
      ∀ x x', f x = f x' → x ≠ x' →
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ x' ∈ V ∧ Disjoint U V := by
  rfl

/-!
Mathlib's stronger result for Hausdorff domains directly gives the source's
lemma that every continuous map out of a Hausdorff space is separated.
-/

theorem isSeparatedMap_of_t2Space [T2Space X] {f : X → Y} (_hf : Continuous f) :
    IsSeparatedMap f :=
  T2Space.isSeparatedMap f

/-!
For a base change `g : Y' → Y`, Mathlib represents the fibre product as
`Function.Pullback f g = {p : X × Y' // f p.1 = g p.2}`.  Thus its `snd`
projection is the source's map `Y' ×_Y X → Y'`, up to the harmless reversal
of the two factors in the subtype model.
-/

theorem isSeparatedMap_baseChange
    {Y' : Type w} [TopologicalSpace Y'] {f : X → Y} {g : Y' → Y}
    (_hf : Continuous f) (_hg : Continuous g) (hsep : IsSeparatedMap f) :
    IsSeparatedMap (@Function.Pullback.snd X Y Y' f g) :=
  hsep.pullback g

end SeparatedMaps

end Formalization.Books.Topology.Unit04
