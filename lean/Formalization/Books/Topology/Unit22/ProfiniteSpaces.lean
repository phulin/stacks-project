import Formalization.Books.Topology.Unit07.ConnectedComponents
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Separation.DisjointCover

/-!
# Topology, Chapter 22: Profinite spaces

This file formalizes the source section on profinite spaces.  Mathlib's
`Profinite` category is the canonical bundled interface for compact,
Hausdorff, totally disconnected spaces; its `asLimit` construction presents
each such object as a cofiltered limit of finite discrete spaces.
-/

namespace Formalization.Books.Topology.Unit22

open CategoryTheory CategoryTheory.Limits
open Set TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]

section ProfiniteSpaces

/- The source defines profiniteness by a finite-discrete limit presentation.
   `Profinite` is Mathlib's canonical bundled version of exactly this notion:
   every object has the finite-discrete presentation `P.asLimit`. -/

/-- A topological space is profinite when it is homeomorphic to a Mathlib
`Profinite` object, hence to its canonical limit of finite discrete spaces. -/
def IsProfiniteSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ P : Profinite.{u}, Nonempty (X ≃ₜ (P : Type u))

/-- A bundled profinite space is profinite in the source-facing predicate. -/
theorem isProfiniteSpace_of_profinite (P : Profinite.{u}) :
    IsProfiniteSpace (P : Type u) := by
  exact ⟨P, ⟨Homeomorph.refl P⟩⟩

/-- Profinite spaces are exactly the Hausdorff, quasi-compact, totally
disconnected spaces. -/
theorem isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected :
    IsProfiniteSpace X ↔
      T2Space X ∧ CompactSpace X ∧ TotallyDisconnectedSpace X := by
  sorry

/-- A profinite space admits a cofiltered finite-discrete limit presentation.

The diagram and cone are Mathlib's canonical `P.fintypeDiagram` and
`P.asLimitCone`, transported to `TopCat`; the index `DiscreteQuotient P` is
cofiltered and each diagram object is finite discrete. -/
theorem profiniteSpace_has_cofiltered_finite_discrete_limit
    (hX : IsProfiniteSpace X) :
    ∃ (P : Profinite.{u}),
      Nonempty (X ≃ₜ (P : Type u)) ∧
        IsCofiltered (DiscreteQuotient P) ∧
          Nonempty (IsLimit (Profinite.toTopCat.mapCone P.asLimitCone)) := by
  rcases hX with ⟨P, hP⟩
  refine ⟨P, hP, inferInstance, ?_⟩
  exact ⟨isLimitOfPreserves Profinite.toTopCat P.asLimit⟩

/-- The limit of a diagram of profinite spaces is profinite. -/
theorem limit_of_profinite_spaces_is_profinite
    {J : Type v} [SmallCategory J]
    (F : J ⥤ Profinite.{max u v}) :
    IsProfiniteSpace ((Profinite.limitCone F).pt : Type (max u v)) := by
  exact isProfiniteSpace_of_profinite (Profinite.limitCone F).pt

/- Mathlib proves a stronger form of the source's finite clopen refinement:
the pieces are nonempty and pairwise disjoint, and the result is bundled as
`Clopens`. -/

/-- Every open cover of a profinite space has a finite disjoint clopen
refinement. -/
theorem profiniteSpace_open_cover_has_finite_clopen_refinement
    (hX : IsProfiniteSpace X) {ι : Type v} (U : ι → Opens X)
    (hU : IsOpenCover U) :
    ∃ (n : ℕ) (V : Fin n → Clopens X),
      (∀ j, V j ≠ ⊥ ∧ ∃ i, (V j : Set X) ⊆ U i) ∧
        (univ : Set X) ⊆ ⋃ j, (V j : Set X) ∧
          Pairwise (fun i j => Disjoint (V i) (V j)) := by
  have hprops :=
    (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp hX)
  exact @TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover
    ι X inferInstance hprops.2.2 hprops.1 hprops.2.1 U hU

/-- The connected-components space is profinite under the source's
quasi-compactness and component-intersection hypothesis. -/
theorem connectedComponents_is_profinite
    [CompactSpace X]
    (hcomponents :
      ∀ x : X,
        connectedComponent x =
          ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X)) :
    IsProfiniteSpace (ConnectedComponents X) := by
  sorry

end ProfiniteSpaces

end Formalization.Books.Topology.Unit22
