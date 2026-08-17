import Formalization.Books.MoreAlgebra.Unit36.BaireCategory
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.GDelta.Basic

namespace Formalization.Books.MoreAlgebra.Unit36

open Set

universe u

noncomputable section

/-- The open-map alternative for a continuous homomorphism under the source hypotheses. -/
theorem openMapping_or_nowhereDense_image
    {N M : Type u} [AddCommGroup N] [AddCommGroup M]
    [TopologicalSpace N] [TopologicalSpace M]
    [IsTopologicalAddGroup N] [IsTopologicalAddGroup M]
    (u : N →+ M) (hu : Continuous u) (hM : T2Space M)
    (hNcomplete : IsCompleteTopologicalAddGroup N)
    (hNlinear : IsLinearTopology ℤ N)
    (hNcountable : HasCountableNeighborhoodBasisAtZero N) :
    Xor (IsOpenMap u)
      (∃ N' : AddSubgroup N,
        IsOpen (N' : Set N) ∧ IsNowhereDense (u '' (N' : Set N))) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit36
