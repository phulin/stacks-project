import Formalization.Books.Topology.Unit05.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Constructible
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Spectral.Prespectral

/-!
# Topology, Chapter 26: Miscellany

The compact-open basis and compact-intersection hypotheses in the source are
Mathlib's `PrespectralSpace` and `QuasiSeparatedSpace` interfaces.  Relative
open covers use the Chapter 2 predicate `IsOpenCoverOf`; the cofinal-cover
assertion is expressed by saying that every such cover has a finite
refinement by compact open sets whose pairwise intersections are compact.
The fourth item in the source list is an unfinished placeholder and has no
mathematical statement to formalize.
-/

namespace Formalization.Books.Topology.Unit26

open Set TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]

section Miscellany

/-! ### Topological spaces with a compact-open basis -/

/- The first conclusion of the source lemma is already supplied by
   Mathlib's `instLocallyCompactSpaceOfPrespectralSpace`; this chapter-facing
   theorem records that conclusion while retaining the canonical interface. -/

/-- A space with a compact-open basis is locally quasi-compact. -/
theorem locallyCompactSpace_of_prespectralSpace
    [PrespectralSpace X] : LocallyCompactSpace X := by
  infer_instance

/- The second conclusion is the canonical `IsCompact.isRetrocompact` result.
   The source's quasi-separated hypothesis is exactly Mathlib's typeclass. -/

/-- A compact open subset of a quasi-separated space is retrocompact. -/
theorem isRetrocompact_of_isOpen_of_isCompact
    [QuasiSeparatedSpace X] {U : Set X}
    (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    IsRetrocompact U := by
  exact hUcompact.isRetrocompact hUopen

/- The source's "cofinal system" is made explicit using the existing
   relative-cover refinement predicate: every relative open cover of a
   quasi-compact open has a finite compact-open refinement. -/

/-- Every open cover of a compact open has a finite compact-open refinement
whose members have compact pairwise intersections. -/
theorem exists_finite_compact_open_refinement
    [PrespectralSpace X] [QuasiSeparatedSpace X] {U : Set X}
    (hUopen : IsOpen U) (hUcompact : IsCompact U)
    {ι : Type v} (𝒰 : ι → Set X)
    (h𝒰 : Formalization.Books.Topology.Unit02.IsOpenCoverOf U 𝒰) :
    ∃ (n : ℕ) (V : Fin n → Set X),
      Formalization.Books.Topology.Unit02.IsOpenCoverRefinement U 𝒰 V ∧
        (∀ j, IsCompact (V j)) ∧
          (∀ j j', IsCompact (V j ∩ V j')) := by
  sorry

/-! ### Isolated points -/

/-- A point is isolated when its singleton is open. -/
def IsolatedPoint (x : X) : Prop :=
  IsOpen ({x} : Set X)

end Miscellany

end Formalization.Books.Topology.Unit26
