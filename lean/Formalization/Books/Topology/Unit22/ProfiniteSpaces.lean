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
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    exact ⟨e.symm.t2Space, e.symm.compactSpace, e.symm.totallyDisconnectedSpace⟩
  · rintro ⟨hT2, hCompact, hTD⟩
    let _ : T2Space X := hT2
    let _ : CompactSpace X := hCompact
    let _ : TotallyDisconnectedSpace X := hTD
    exact ⟨Profinite.of X, ⟨Homeomorph.refl X⟩⟩

/-- A profinite space admits a cofiltered finite-discrete limit presentation.

The diagram and cone are Mathlib's canonical `P.fintypeDiagram` and
`P.asLimitCone`, transported to `TopCat`; the index `DiscreteQuotient P` is
cofiltered and each diagram object is finite discrete. -/
theorem profiniteSpace_has_cofiltered_finite_discrete_limit
    (hX : IsProfiniteSpace X) :
    ∃ (P : Profinite.{u}),
      Nonempty (X ≃ₜ (P : Type u)) ∧
          IsCofiltered (DiscreteQuotient P) ∧
          (∀ i : DiscreteQuotient P,
            Finite (P.fintypeDiagram.obj i) ∧
              @DiscreteTopology (P.fintypeDiagram.obj i)
                (FintypeCat.botTopology (P.fintypeDiagram.obj i))) ∧
          Nonempty (IsLimit (Profinite.toTopCat.mapCone P.asLimitCone)) := by
  rcases hX with ⟨P, hP⟩
  refine ⟨P, hP, inferInstance, ?_, ?_⟩
  · intro i
    exact ⟨inferInstance, FintypeCat.discreteTopology _⟩
  · exact ⟨isLimitOfPreserves Profinite.toTopCat P.asLimit⟩

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
        (⋃ j, (V j : Set X)) = (univ : Set X) ∧
          Pairwise (fun i j => Disjoint (V i) (V j)) := by
  have hprops :=
    (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp hX)
  obtain ⟨n, V, hV, hcover, hdisj⟩ :=
    @TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover
      ι X inferInstance hprops.2.2 hprops.1 hprops.2.1 U hU
  refine ⟨n, V, hV, ?_, hdisj⟩
  exact Set.Subset.antisymm (Set.subset_univ _) hcover

/-- The connected-components space is profinite under the source's
quasi-compactness and component-intersection hypothesis. -/
theorem connectedComponents_is_profinite
    [CompactSpace X]
    (hcomponents :
      ∀ x : X,
        connectedComponent x =
          ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X)) :
    IsProfiniteSpace (ConnectedComponents X) := by
  let _ : T2Space (ConnectedComponents X) := by
    refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b ne => ?_⟩
    rw [ConnectedComponents.coe_ne_coe] at ne
    have h := connectedComponent_disjoint ne
    rw [hcomponents b, disjoint_iff_inter_eq_empty] at h
    obtain ⟨U, V, hU, ha, hb, rfl⟩ :
        ∃ (U : Set X) (V : Set (ConnectedComponents X)),
          IsClopen U ∧ connectedComponent a ∩ U = ∅ ∧ connectedComponent b ⊆ U ∧
            (↑) ⁻¹' V = U := by
      have h :=
        (isClosed_connectedComponent (α := X)).isCompact.elim_finite_subfamily_closed
          _ (fun s : { s : Set X // IsClopen s ∧ b ∈ s } => s.2.1.1) h
      obtain ⟨fin_a, ha⟩ := h
      set U : Set X := ⋂ (i : { s // IsClopen s ∧ b ∈ s }) (_ : i ∈ fin_a), i
      have hU : IsClopen U := isClopen_biInter_finset fun i _ => i.2.1
      exact
        ⟨U, (↑) '' U, hU, ha,
          subset_iInter₂ fun s _ => s.2.1.connectedComponent_subset s.2.2,
          (connectedComponents_preimage_image U).symm ▸ hU.biUnion_connectedComponent_eq⟩
    rw [ConnectedComponents.isQuotientMap_coe.isClopen_preimage] at hU
    refine
      ⟨Vᶜ, V, hU.compl.isOpen, hU.isOpen, ?_, hb mem_connectedComponent,
        disjoint_compl_left⟩
    exact fun h => flip Set.Nonempty.ne_empty ha ⟨a, mem_connectedComponent, h⟩
  exact isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

end ProfiniteSpaces

end Formalization.Books.Topology.Unit22
