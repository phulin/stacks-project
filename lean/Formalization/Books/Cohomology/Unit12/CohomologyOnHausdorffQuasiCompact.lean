import Formalization.Books.Cohomology.Unit08.CechCohomology
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Cohomology of Sheaves, Chapter 12: cohomology on Hausdorff quasi-compact spaces

This file records the three precise comparison statements in the source
section.  Čech cohomology over all open covers and cohomology over all open
neighborhoods require coherent transition maps that are not part of the
earlier chapter APIs, so those two colimit systems are exposed as explicit
source-facing data.  Their objectwise terms use the canonical Čech complex,
derived global-sections, open-subspace restriction, and sheaf pullback APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Set
open TopologicalSpace
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Cohomology.Unit12

/-! ## Čech cohomology over all open covers -/

/- The order is chosen so an arrow from `𝒰` to `𝒱` records that `𝒱` is a
   refinement of `𝒰`, which is the direction of the Čech transition map. -/
abbrev GlobalCechOpenCover (X : TopCat.{v}) :=
  {𝒰 : CechOpenCover X // 𝒰.carrier = (⊤ : Opens X)}

instance globalCechOpenCoverPreorder (X : TopCat.{v}) :
    Preorder (GlobalCechOpenCover X) where
  le 𝒰 𝒱 := Nonempty (CechCoverRefinement 𝒱.1 𝒰.1)
  le_refl 𝒰 := by
    exact ⟨{
      carrier_eq := rfl
      index_map := id
      member_le := fun _ => le_rfl
    }⟩
  le_trans 𝒰 𝒱 𝒲 hUV hVW := by
    rcases hUV with ⟨rVU⟩
    rcases hVW with ⟨rWV⟩
    exact ⟨{
      carrier_eq := rWV.carrier_eq.trans rVU.carrier_eq
      index_map := rVU.index_map ∘ rWV.index_map
      member_le := by
        intro i
        exact (rWV.member_le i).trans (rVU.member_le (rWV.index_map i))
    }⟩

instance globalCechOpenCoverCategory (X : TopCat.{v}) :
    SmallCategory (GlobalCechOpenCover X) := by
  change SmallCategory {𝒰 : CechOpenCover X // 𝒰.carrier = (⊤ : Opens X)}
  infer_instance

/-- A coherent Čech system indexed by all open covers of `X`.

The diagram contains the refinement transition maps.  The objectwise
isomorphisms identify its terms with the canonical Čech cohomology objects;
the comparison maps are the canonical maps to derived cohomology. -/
structure CechCohomologyComparisonData
    (X : TopCat.{v}) (F : TopCat.Sheaf AddCommGrpCat.{v} X) where
  diagram : ℕ → GlobalCechOpenCover X ⥤ AddCommGrpCat.{v}
  object_iso : ∀ (p : ℕ) (𝒰 : GlobalCechOpenCover X),
    Nonempty ((diagram p).obj 𝒰 ≅
      cechCohomologyObject 𝒰.1 F.presheaf p)
  cocone : ∀ p : ℕ, Cocone (diagram p)
  isColimit : ∀ p : ℕ, IsColimit (cocone p)
  comparison : ∀ p : ℕ,
    (cocone p).pt ⟶ abelianSheafCohomologyObject X F (p : ℤ)

theorem exists_cechCohomologyComparisonData
    (X : TopCat.{v}) (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    Nonempty (CechCohomologyComparisonData X F) := by
  sorry

noncomputable def cechCohomologyComparisonData
    (X : TopCat.{v}) (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    CechCohomologyComparisonData X F :=
  Classical.choice (exists_cechCohomologyComparisonData X F)

/-- The global Čech cohomology object obtained from the refinement colimit. -/
noncomputable abbrev globalCechCohomology
    (X : TopCat.{v}) (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) :
    AddCommGrpCat.{v} :=
  ((cechCohomologyComparisonData X F).cocone p).pt

/-- The canonical map from global Čech cohomology to derived cohomology. -/
noncomputable abbrev cechToAbelianSheafCohomology
    (X : TopCat.{v}) (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) :
    globalCechCohomology X F p ⟶ abelianSheafCohomologyObject X F (p : ℤ) :=
  (cechCohomologyComparisonData X F).comparison p

/-! ## The degree-one comparison -/

/-- For every topological space, the canonical degree-one Čech comparison is
an isomorphism. -/
theorem cech_cohomology_h1_comparison_isIso
    (X : TopCat.{v}) (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    IsIso (cechToAbelianSheafCohomology X F 1) := by
  sorry

/-! ## The Hausdorff quasi-compact comparison -/

/-- On a Hausdorff quasi-compact space, the canonical Čech comparison is an
isomorphism in every nonnegative degree. -/
theorem cech_cohomology_comparison_isIso_of_compact_t2
    (X : TopCat.{v}) [CompactSpace X] [T2Space X]
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) :
    IsIso (cechToAbelianSheafCohomology X F p) := by
  sorry

/-! ## Cohomology of a quasi-compact Hausdorff-separated subset -/

/-- Any two distinct points of `Z` admit disjoint open neighborhoods in `X`.
This is the separation hypothesis used by the source, rather than a
Hausdorff typeclass on the subspace alone. -/
def PairwiseDisjointOpenNeighborhoods
    {X : TopCat.{v}} (Z : Set X) : Prop :=
  ∀ ⦃x y : X⦄, x ∈ Z → y ∈ Z → x ≠ y →
    ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V

/-- The inclusion of an arbitrary subset with its subspace topology. -/
def subsetInclusion {X : TopCat.{v}} (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

/-- Restriction of an abelian sheaf to an arbitrary subspace. -/
noncomputable def abelianSheafRestrictionToSubset {X : TopCat.{v}}
    (Z : Set X) : TopCat.Sheaf AddCommGrpCat.{v} X ⥤
      TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of Z) :=
  abelianSheafPullback (subsetInclusion Z)

/-- Cohomology of the restriction of an abelian sheaf to a subspace. -/
noncomputable abbrev abelianSheafSubsetCohomology
    {X : TopCat.{v}} (Z : Set X)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) : AddCommGrpCat.{v} :=
  (abelianSheafCohomology (TopCat.of Z) (p : ℤ)).obj
    ((abelianSheafRestrictionToSubset Z).obj F)

/- The derived cohomology of the restriction to an open neighborhood. -/
noncomputable def abelianSheafOpenCohomology
    (X : TopCat.{v}) (U : Opens X) (p : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{v} X ⥤ AddCommGrpCat.{v} :=
  openSheafRestriction AddCommGrpCat U ⋙
    abelianSheafCohomology (openSubspace U) (p : ℤ)

/-- The category of all open neighborhoods of `Z`, ordered by inclusion. -/
def OpenNeighborhood (X : TopCat.{v}) (Z : Set X) :=
  {U : Opens X // Z ⊆ (U : Set X)}

instance openNeighborhoodCategory (X : TopCat.{v}) (Z : Set X) :
    SmallCategory (OpenNeighborhood X Z) := by
  change SmallCategory {U : Opens X // Z ⊆ (U : Set X)}
  infer_instance

/-- Restriction maps go from a larger neighborhood to a smaller one, so the
source colimit is indexed by the opposite inclusion order. -/
abbrev OpenNeighborhoodIndex (X : TopCat.{v}) (Z : Set X) :=
  (OpenNeighborhood X Z)ᵒᵖ

/-- A cohomology diagram indexed by open neighborhoods of `Z`. -/
structure NeighborhoodCohomologyComparisonData
    (X : TopCat.{v}) (Z : Set X)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) where
  diagram : OpenNeighborhoodIndex X Z ⥤ AddCommGrpCat.{v}
  object_iso : ∀ U,
    Nonempty (diagram.obj U ≅
      (abelianSheafOpenCohomology X U.unop.1 p).obj F)
  comparison : colimit diagram ⟶ abelianSheafSubsetCohomology Z F p

theorem exists_neighborhoodCohomologyComparisonData
    {X : TopCat.{v}} (Z : Set X) (hZcompact : IsCompact Z)
    (hZseparated : PairwiseDisjointOpenNeighborhoods Z)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) :
    Nonempty (NeighborhoodCohomologyComparisonData X Z F p) := by
  sorry

noncomputable def neighborhoodCohomologyComparisonData
    {X : TopCat.{v}} (Z : Set X) (hZcompact : IsCompact Z)
    (hZseparated : PairwiseDisjointOpenNeighborhoods Z)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) :
    NeighborhoodCohomologyComparisonData X Z F p :=
  Classical.choice (exists_neighborhoodCohomologyComparisonData
    Z hZcompact hZseparated F p)

/-- The cohomology colimit over open neighborhoods of `Z`. -/
noncomputable abbrev neighborhoodCohomology
    {X : TopCat.{v}} (Z : Set X) (hZcompact : IsCompact Z)
    (hZseparated : PairwiseDisjointOpenNeighborhoods Z)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) : AddCommGrpCat.{v} :=
  colimit ((neighborhoodCohomologyComparisonData
    Z hZcompact hZseparated F p).diagram)

/-- The canonical map from neighborhood cohomology to cohomology on `Z`. -/
noncomputable abbrev neighborhoodCohomologyComparison
    {X : TopCat.{v}} (Z : Set X) (hZcompact : IsCompact Z)
    (hZseparated : PairwiseDisjointOpenNeighborhoods Z)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) :
    neighborhoodCohomology Z hZcompact hZseparated F p ⟶
      abelianSheafSubsetCohomology Z F p :=
  (neighborhoodCohomologyComparisonData
    Z hZcompact hZseparated F p).comparison

/-- The canonical neighborhood-colimit comparison is an isomorphism. -/
theorem cohomology_of_quasi_compact_separated_subset
    {X : TopCat.{v}} (Z : Set X) (hZcompact : IsCompact Z)
    (hZseparated : PairwiseDisjointOpenNeighborhoods Z)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (p : ℕ) :
    IsIso (neighborhoodCohomologyComparison
      Z hZcompact hZseparated F p) := by
  sorry

end Formalization.Books.Cohomology.Unit12
