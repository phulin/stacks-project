import Mathlib.Data.Set.Prod
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Separation.Hausdorff

/-!
# Topology, Chapter 3: Hausdorff spaces

The source section begins with the finite-product assertion for topological
spaces and then records four closed-set consequences of the Hausdorff
condition.  The canonical Mathlib interfaces are used directly: `T2Space`
for Hausdorff
spaces, `Set.diagonal` for the diagonal, `Set.graphOn` for a graph, and the
categorical topological pullback together with its concrete subtype carrier.
-/

namespace Formalization.Books.Topology.Unit03

open CategoryTheory CategoryTheory.Limits
open Set
open TopologicalSpace

universe u v w

section HausdorffSpaces

/- The stronger existing `TopCat.topCat_hasLimits` instance supplies this
   source assertion through the standard finite-products consequence. -/
theorem topological_spaces_have_finite_products :
    HasFiniteProducts (TopCat.{u}) := by
  infer_instance

/-- A topological space is Hausdorff exactly when its diagonal is closed. -/
theorem hausdorff_iff_isClosed_diagonal {X : Type u} [TopologicalSpace X] :
    T2Space X ↔ IsClosed (diagonal X) :=
  by
    rw [t2Space_iff_disjoint_nhds]
    simp only [← isOpen_compl_iff, isOpen_iff_mem_nhds, Prod.forall, nhds_prod_eq,
      mem_compl_iff, mem_diagonal_iff]
    constructor
    · intro h a b hab
      rcases Filter.disjoint_iff.mp (h hab) with ⟨u, hu, v, hv, huv⟩
      exact Filter.mem_prod_iff.mpr ⟨u, hu, v, hv,
        prod_subset_compl_diagonal_iff_disjoint.mpr huv⟩
    · intro h a b hab
      rcases Filter.mem_prod_iff.mp (h a b hab) with ⟨u, hu, v, hv, huv⟩
      exact Filter.disjoint_iff.mpr ⟨u, hu, v, hv,
        prod_subset_compl_diagonal_iff_disjoint.mp huv⟩

/-- The graph of a continuous map into a Hausdorff space is closed. -/
theorem isClosed_graph_of_continuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    [T2Space Y] :
    IsClosed (Set.univ.graphOn f) := by
  have hmap : Continuous (fun p : X × Y => (f p.1, p.2)) :=
    (hf.comp continuous_fst).prodMk continuous_snd
  have hgraph : Set.univ.graphOn f =
      (fun p : X × Y => (f p.1, p.2)) ⁻¹' diagonal Y := by
    ext p
    simp [Set.mem_graphOn]
  rw [hgraph]
  exact IsClosed.preimage hmap isClosed_diagonal

/-- The image of a continuous section into a Hausdorff space is closed. -/
theorem isClosed_range_of_continuous_section {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (s : Y → X)
    (hf : Continuous f) (hs : Continuous s) (hfs : f ∘ s = id) [T2Space X] :
    IsClosed (Set.range s) := by
  refine Function.LeftInverse.isClosed_range (f := f) (g := s) ?_ hf hs
  intro y
  simpa [Function.comp_def] using congrFun hfs y

/-- The underlying set of a topological fibre product is closed in the
product when the target is Hausdorff. -/
theorem isClosed_fiberProduct {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Z) (g : Y → Z) (hf : Continuous f) (hg : Continuous g)
    [T2Space Z] :
    IsClosed {p : X × Y | f p.1 = g p.2} := by
  have hmap : Continuous (fun p : X × Y => (f p.1, g p.2)) :=
    (hf.comp continuous_fst).prodMk (hg.comp continuous_snd)
  have hfiber :
      {p : X × Y | f p.1 = g p.2} =
        (fun p : X × Y => (f p.1, g p.2)) ⁻¹' diagonal Z := by
    ext p
    simp
  rw [hfiber]
  exact IsClosed.preimage hmap isClosed_diagonal

end HausdorffSpaces

end Formalization.Books.Topology.Unit03
