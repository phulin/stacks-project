import Formalization.Books.MoreAlgebra.Unit36.TopologicalGroups
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.LinearTopology

namespace Formalization.Books.MoreAlgebra.Unit36

open Set
open Filter
open scoped Uniformity

universe u

noncomputable section

/-- The Baire theorem in the linearly topologized, complete, countable-basis form used here. -/
theorem dense_iInter_of_complete_linearlyTopologized
    (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [IsLinearTopology ℤ M]
    (hcomplete : IsCompleteTopologicalAddGroup M)
    (hcountable : HasCountableNeighborhoodBasisAtZero M)
    (U : {n : ℕ // 1 ≤ n} → Set M)
    (hU : ∀ n, IsOpen (U n) ∧ Dense (U n)) :
    Dense (⋂ n, U n) := by
  let u : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  rcases hcountable with ⟨b, hb⟩
  let hnhds : (nhds (0 : M)).IsCountablyGenerated := hb.isCountablyGenerated
  let hu : @Filter.IsCountablyGenerated (M × M) (𝓤 M) :=
    @IsUniformAddGroup.uniformity_countably_generated M u _
      (isUniformAddGroup_of_addCommGroup) hnhds
  let pmetric : @PseudoMetricSpace M := @UniformSpace.pseudoMetricSpace M u hu
  have hpcomplete : @CompleteSpace M pmetric.toUniformSpace := by
    change @CompleteSpace M u
    exact hcomplete.1
  let hcm : TopologicalSpace.IsCompletelyPseudoMetrizableSpace M :=
    ⟨⟨pmetric, rfl, hpcomplete⟩⟩
  let hbspace : BaireSpace M := @BaireSpace.of_completelyPseudoMetrizable M _ hcm
  exact @dense_iInter_of_isOpen M {n : ℕ // 1 ≤ n} _ hbspace inferInstance U
    (fun n => (hU n).1) (fun n => (hU n).2)

/-- A countable closed-subgroup cover contains an open subgroup. -/
theorem exists_isOpen_closed_addSubgroup_of_iUnion
    (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [IsLinearTopology ℤ M]
    (hcomplete : IsCompleteTopologicalAddGroup M)
    (hcountable : HasCountableNeighborhoodBasisAtZero M)
    (N : {n : ℕ // 1 ≤ n} → AddSubgroup M)
    (hclosed : ∀ n, IsClosed (N n : Set M))
    (hcover : (⋃ n, (N n : Set M)) = (Set.univ : Set M)) :
    ∃ n, IsOpen (N n : Set M) := by
  by_contra h
  push Not at h
  have hinterior_empty : ∀ n, interior (N n : Set M) = ∅ := by
    intro n
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    apply h n
    have hopen : IsOpen ((fun y : M => -x + y) '' interior (N n : Set M)) :=
      (isOpenMap_add_left (-x)) _ isOpen_interior
    have hzero : (0 : M) ∈ (fun y : M => -x + y) '' interior (N n : Set M) := by
      exact ⟨x, hx, by simp⟩
    have hsub : (fun y : M => -x + y) '' interior (N n : Set M) ⊆ (N n : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact (N n).add_mem ((N n).neg_mem (interior_subset hx)) (interior_subset hz)
    exact AddSubgroup.isOpen_of_mem_nhds (N n)
      (Filter.mem_of_superset (hopen.mem_nhds hzero) hsub)
  have hdense : Dense (⋂ n, (N n : Set M)ᶜ) :=
    dense_iInter_of_complete_linearlyTopologized M hcomplete hcountable
      (fun n => (N n : Set M)ᶜ) (fun n =>
        ⟨(hclosed n).isOpen_compl,
          interior_eq_empty_iff_dense_compl.1 (hinterior_empty n)⟩)
  rcases hdense.nonempty with ⟨x, hx⟩
  have hxcover : x ∈ ⋃ n, (N n : Set M) := by
    rw [hcover]
    trivial
  rcases mem_iUnion.1 hxcover with ⟨n, hn⟩
  exact (mem_iInter.1 hx n) hn

end

end Formalization.Books.MoreAlgebra.Unit36
