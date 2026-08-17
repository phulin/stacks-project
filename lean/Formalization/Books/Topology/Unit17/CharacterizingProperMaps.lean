import Mathlib.Data.Set.Prod
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.SeparatedMap

/-!
# Topology, Chapter 17: Characterizing proper maps

The source uses `IsClosedMap` for closed maps, `IsSeparatedMap` for separated
maps, `IsCompact` for quasi-compact subsets, and Mathlib's `IsProperMap` for
the Bourbaki-proper condition.  The source's universal-closed condition is
phrased using the concrete topological pullback `Function.Pullback`; it is
defined here because it is the base-change formulation, whereas Mathlib's
`IsProperMap` is the canonical Bourbaki-proper interface.
-/

namespace Formalization.Books.Topology.Unit17

open Set Function

universe u v w

section CharacterizingProperMaps

variable {X : Type u} [TopologicalSpace X]

/-! ### The Tube lemma -/

/- The source's closed-map terminology is Mathlib's existing `IsClosedMap`.
   Its Tube lemma is exactly `generalized_tube_lemma`, so the chapter-facing
   name below is a direct reuse of that result. -/

theorem tube_lemma {Y : Type v} [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {W : Set (X × Y)}
    (hA : IsCompact A) (hB : IsCompact B) (hW : IsOpen W)
    (hAB : A ×ˢ B ⊆ W) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ U ×ˢ V ⊆ W := by
  exact generalized_tube_lemma hA hB hW hAB

/-! ### Properness notions -/

/-!
The source's Bourbaki-proper map is Mathlib's `IsProperMap`.  Mathlib's
definition includes continuity, which is already part of the source's
standing hypothesis that `f` is a continuous map.
-/

/- A map is quasi-proper when inverse images of quasi-compact subsets are
   quasi-compact. -/
def IsQuasiProper {Y : Type v} [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ ⦃V : Set Y⦄, IsCompact V → IsCompact (f ⁻¹' V)

/- The introductory comparison with the usual locally compact Hausdorff
   terminology is Mathlib's compact-preimage characterization of
   `IsProperMap`. -/
theorem isProperMap_iff_isQuasiProper_of_locallyCompact_Hausdorff
    {Y : Type v} [TopologicalSpace Y]
    [LocallyCompactSpace Y] [T2Space Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ IsQuasiProper f := by
  exact isProperMap_iff_isCompact_preimage

/- A map is universally closed when every continuous base change has a closed
   projection to the base.  `Function.Pullback.snd` is the projection from
   `X ×_Y Z` to `Z`, with the factors ordered so that the source factor is
   first. -/
def IsUniversallyClosed {Y : Type v} [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ (Z : Type w) [TopologicalSpace Z] (g : Z → Y), Continuous g →
    IsClosedMap (@Function.Pullback.snd X Y Z f g)

/- The source's proper map includes the standing continuity requirement, and
   then asks for separatedness and universal closedness.  The longer name
   distinguishes it from Mathlib's `IsProperMap`, which intentionally denotes
   Bourbaki properness without the extra separatedness condition. -/
def IsProperTopologicalMap {Y : Type v} [TopologicalSpace Y] (f : X → Y) : Prop :=
  Continuous f ∧ IsSeparatedMap f ∧ IsUniversallyClosed.{u, v, w} f

/-! ### Characterization of quasi-compact spaces -/

theorem compactSpace_iff_isClosedMap_prod_fst :
    CompactSpace X ↔
      ∀ (Z : Type*) [TopologicalSpace Z],
        IsClosedMap (Prod.fst : Z × X → Z) := by
  sorry

/-! ### Characterization of Bourbaki-proper and universally closed maps -/

theorem proper_map_characterization_TFAE {Y : Type v} [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) :
    List.TFAE
      [IsQuasiProper f ∧ IsClosedMap f,
        IsProperMap f,
        IsUniversallyClosed.{u, v, w} f,
        IsClosedMap f ∧ ∀ y, IsCompact (f ⁻¹' {y})] := by
  sorry

/-! ### Compact-to-Hausdorff and bijective-map consequences -/

theorem isUniversallyClosed_of_compactSpace_of_t2Space
    {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) [CompactSpace X] [T2Space Y] :
    IsUniversallyClosed.{u, v, w} f := by
  sorry

theorem isHomeomorph_of_continuous_bijective_of_compactSpace_of_t2Space
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hbij : Function.Bijective f) [CompactSpace X] :
    IsHomeomorph f := by
  sorry

end CharacterizingProperMaps

end Formalization.Books.Topology.Unit17
