import Formalization.Books.Cohomology.Unit15.CohomologyAndColimits
import Formalization.Books.Cohomology.Unit17.CohomologyWithSupport
import Formalization.Books.Topology.Unit24.LimitsOfSpectralSpaces

/-!
# Cohomology of Sheaves, Chapter 18: cohomology on spectral spaces

This file formalizes the precise statements in the source section
`Cohomology on spectral spaces`.  The spectral-space, specialization,
profinite, and cohomology constructions are the canonical declarations from
the earlier chapters.  The neighborhood colimits and restriction maps are
exposed through small source-facing interfaces because their comparison maps
are not part of the earlier abelian-sheaf API.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Set
open _root_.Topology
open TopologicalSpace
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit15
open Formalization.Books.Cohomology.Unit17
open Formalization.Books.Modules.Unit06
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Topology.Unit22
open Formalization.Books.Topology.Unit24

universe v

namespace Formalization.Books.Cohomology.Unit18

/-! ## Cohomology of neighborhoods of a quasi-compact subset -/

/-- The topological subspace inclusion associated to an arbitrary subset. -/
def subsetInclusion {X : TopCat.{v}} (S : Set X) : TopCat.of S ⟶ X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

/-- Restriction of an abelian sheaf to an arbitrary subspace. -/
noncomputable def abelianSheafRestrictionToSubset {X : TopCat.{v}}
    (S : Set X) : Ab X ⥤ Ab (TopCat.of S) :=
  abelianSheafPullback (subsetInclusion S)

/-- Cohomology of the restriction of an abelian sheaf to a subspace. -/
noncomputable abbrev abelianSheafSubsetCohomology
    {X : TopCat.{v}} (S : Set X) (F : Ab X) (p : ℕ) : AddCommGrpCat.{v} :=
  (abelianSheafCohomology (TopCat.of S) (p : ℤ)).obj
    ((abelianSheafRestrictionToSubset S).obj F)

/-- The category of quasi-compact open neighborhoods of `E`, ordered by
inclusion.  Its objects are exactly the opens indexing the source colimit. -/
def QuasiCompactOpenNeighborhood (X : TopCat.{v}) (E : Set X) :=
  {U : Opens X // E ⊆ (U : Set X) ∧ IsCompact (U : Set X)}

instance quasiCompactOpenNeighborhoodCategory
    (X : TopCat.{v}) (E : Set X) : SmallCategory
      (QuasiCompactOpenNeighborhood X E) := by
  change SmallCategory {U : Opens X // E ⊆ (U : Set X) ∧ IsCompact (U : Set X)}
  infer_instance

/-- The source colimit is indexed by the opposite of the inclusion order:
restriction maps go from a larger neighborhood to a smaller one. -/
abbrev QuasiCompactOpenNeighborhoodIndex (X : TopCat.{v}) (E : Set X) :=
  (QuasiCompactOpenNeighborhood X E)ᵒᵖ

/-- A diagram whose objects are the cohomology groups on the quasi-compact
open neighborhoods of `E`. -/
structure NeighborhoodCohomologyDiagram
    (X : TopCat.{v}) (E : Set X) (F : Ab X) (p : ℕ) where
  diagram : QuasiCompactOpenNeighborhoodIndex X E ⥤ AddCommGrpCat.{v}
  object_iso : ∀ U,
    Nonempty (diagram.obj U ≅
      abelianSheafSubsetCohomology (U.unop.1 : Set X) F p)

/-- The analogous diagram for the complements of a constructible subset. -/
structure NeighborhoodDifferenceCohomologyDiagram
    (X : TopCat.{v}) (E : Set X) (F : Ab X) (p : ℕ) where
  diagram : QuasiCompactOpenNeighborhoodIndex X E ⥤ AddCommGrpCat.{v}
  object_iso : ∀ U,
    Nonempty (diagram.obj U ≅
      abelianSheafSubsetCohomology ((U.unop.1 : Set X) \ E) F p)

/-- The set of points specializing to a point of `E`. -/
abbrev specializationNeighborhoodSet {X : TopCat.{v}} (E : Set X) : Set X :=
  pointsSpecializingTo E

/-- Cohomology commutes with the neighborhood colimit around a quasi-compact
subset of a spectral space, including the constructible-complement variant. -/
theorem cohomology_of_neighborhoods_of_closed
    {X : TopCat.{v}} (hX : SpectralSpace X) (F : Ab X)
    (E : Set X) (hE : IsCompact E) (p : ℕ) :
    (∃ D : NeighborhoodCohomologyDiagram X E F p,
      Nonempty (colimit D.diagram ≅
        abelianSheafSubsetCohomology (specializationNeighborhoodSet E) F p)) ∧
      (IsConstructible E →
        ∃ D : NeighborhoodDifferenceCohomologyDiagram X E F p,
          Nonempty (colimit D.diagram ≅
            abelianSheafSubsetCohomology
              (specializationNeighborhoodSet E \ E) F p)) := by
  sorry

/-! ## Proper base change on a spectral space -/

/-- The stalk of the `p`th higher direct image. -/
noncomputable abbrev abelianSheafHigherDirectImageStalk
    {X Y : TopCat.{v}} (f : X ⟶ Y) (F : Ab X) (y : Y) (p : ℕ) :
    AddCommGrpCat.{v} :=
  ((abelianSheafHigherDirectImage f (p : ℤ)).obj F).presheaf.stalk y

/-- Proper-base-change-on-a-spectral-space, with the specialization set in
the fiber made explicit as a subspace. -/
theorem proper_base_change_spectral
    {X Y : TopCat.{v}} (hX : SpectralSpace X) (hY : SpectralSpace Y)
    (f : X ⟶ Y) (hf : IsSpectralMap f.hom) (y : Y) (F : Ab X) (p : ℕ) :
    Nonempty (abelianSheafHigherDirectImageStalk f F y p ≅
      abelianSheafSubsetCohomology
        (f.hom ⁻¹' specializationNeighborhoodSet ({y} : Set Y)) F p) := by
  sorry

/-! ## Vanishing on profinite spaces -/

/-- Higher cohomology vanishes on a profinite space. -/
theorem cohomology_vanishing_for_profinite
    (X : TopCat.{v}) (hX : IsProfiniteSpace X) (F : Ab X) :
    ∀ q : ℕ, 0 < q →
      IsZero (abelianSheafCohomologyObject X F (q : ℤ)) := by
  sorry

/-! ## Cohomological dimension of a spectral space -/

/-- A source-facing type for the restriction map in cohomology from `X` to an
open subspace. -/
abbrev abelianSheafCohomologyRestrictionMap
    {X : TopCat.{v}} (U : Opens X) (F : Ab X) (p : ℕ) : Type v :=
  abelianSheafCohomologyObject X F (p : ℤ) ⟶
    abelianSheafCohomologyObject (openSubspace U)
      ((openSheafRestriction AddCommGrpCat U).obj F) p

/-- The surjectivity assertion for the canonical restriction map in the
source's cohomological-dimension proposition. -/
def CohomologyRestrictionSurjective
    (X : TopCat.{v}) (F : Ab X) (p : ℕ) : Prop :=
  ∀ U : Opens X, IsCompact (U : Set X) →
    ∃ r : abelianSheafCohomologyRestrictionMap U F p,
      Function.Surjective r.hom

/-- The three assertions of the cohomological-dimension proposition. -/
theorem proposition_cohomological_dimension_spectral
    (X : TopCat.{v}) (hX : SpectralSpace X) (d : ℕ)
    (hd : topologicalKrullDim (X : Type v) = d) (F : Ab X) :
    (∀ q : ℕ, d < q →
      IsZero (abelianSheafCohomologyObject X F (q : ℤ))) ∧
      CohomologyRestrictionSurjective X F d ∧
    (∀ Z : Set X, (hZ : IsClosed Z) → IsConstructible Z →
        ∀ q : ℕ, d < q →
          IsZero (sectionsWithSupportCohomologyObject Z hZ F (q : ℤ))) := by
  sorry

end Formalization.Books.Cohomology.Unit18
