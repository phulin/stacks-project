import Formalization.Books.Cohomology.Unit20.UnboundedComplexes

/-!
# Cohomology of Sheaves, Chapter 20, Section 3: Cohomology of filtered complexes
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Homology.Unit24
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v

namespace Formalization.Books.Cohomology.Unit20

def FilteredCohomologyBoundedCondition
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf)) : Prop :=
  FilteredComplexTrivialConvergenceHypotheses K

structure FilteredCohomologySpectralSequenceData
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf)) where
  globalFiltered : FilteredComplex (GlobalModuleCategory X)
  spectral : FilteredComplexSpectralSequence globalFiltered
  e₁_page : ∀ (p q : ℤ),
    Nonempty (spectral.page 1 (p, q) ≅
      (globalCohomologyObject X (p + q)).obj
        (derivedObjectOfComplex X (filteredComplexGradedPiece K p)))
  bounded_and_convergent : FilteredCohomologyBoundedCondition K →
    filteredComplexBounded spectral ∧ filteredComplexConverges globalFiltered

theorem exists_filteredCohomologySpectralSequence
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf)) :
    Nonempty (FilteredCohomologySpectralSequenceData K) := by
  sorry

noncomputable def filteredCohomologySpectralSequence
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf)) :
    FilteredCohomologySpectralSequenceData K :=
  Classical.choice (exists_filteredCohomologySpectralSequence K)

/-! The bounded-below finite-filtration construction. -/

structure FilteredInjectiveResolutionData
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf)) where
  resolution : FilteredComplex (Mod X.structureSheaf)
  quasiIso : Prop
  boundedBelow : IsBoundedBelow resolution
  finiteFiltration : FilteredComplexFiniteFiltration resolution
  gradedTermsInjective : ∀ n : ℤ, Injective (resolution.X n).carrier

theorem exists_filteredInjectiveResolution
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf))
    (hK : IsBoundedBelow K)
    (hfinite : FilteredComplexFiniteFiltration K) :
    Nonempty (FilteredInjectiveResolutionData K) := by
  sorry

theorem filteredCohomology_bounded_finite_filtration
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf))
    (hK : IsBoundedBelow K)
    (hfinite : FilteredComplexFiniteFiltration K) :
    filteredComplexConverges (filteredCohomologySpectralSequence K).globalFiltered := by
  sorry

/-! The two standard filtrations and the two source examples. -/

structure CohomologySpectralSequenceExampleData
    (X : RingedSpace.{v}) (K : ModuleComplex X) where
  globalFiltered : FilteredComplex (GlobalModuleCategory X)
  spectral : FilteredComplexSpectralSequence globalFiltered
  e₂_object : ℤ × ℤ → GlobalModuleCategory X
  e₂_page : ∀ i j : ℤ,
    Nonempty (spectral.page 2 (i, j) ≅ e₂_object (i, j))
  bounded_below_converges : Prop

theorem exists_truncation_spectral_sequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) :
    Nonempty (CohomologySpectralSequenceExampleData X K) := by
  sorry

noncomputable def truncationSpectralSequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) :
    CohomologySpectralSequenceExampleData X K :=
  Classical.choice (exists_truncation_spectral_sequence X K)

structure TermwiseSpectralSequenceExampleData
    (X : RingedSpace.{v}) (K : ModuleComplex X) where
  globalFiltered : FilteredComplex (GlobalModuleCategory X)
  spectral : FilteredComplexSpectralSequence globalFiltered
  e₁_object : ℤ × ℤ → GlobalModuleCategory X
  e₁_page : ∀ p q : ℤ,
    Nonempty (spectral.page 1 (p, q) ≅ e₁_object (p, q))
  bounded_below : IsBoundedBelow K
  converges : Prop
  agrees_with_cartan_eilenberg : Prop

theorem exists_termwise_spectral_sequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) :
    Nonempty (TermwiseSpectralSequenceExampleData X K) := by
  sorry

noncomputable def termwiseSpectralSequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) :
    TermwiseSpectralSequenceExampleData X K :=
  Classical.choice (exists_termwise_spectral_sequence X K)

/-! The relative filtered-complex spectral sequence. -/

structure RelativeFilteredCohomologySpectralSequenceData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : FilteredComplex (Mod X.structureSheaf)) where
  targetFiltered : FilteredComplex (Mod Y.structureSheaf)
  spectral : FilteredComplexSpectralSequence targetFiltered
  e₁_page : ∀ (p q : ℤ),
    Nonempty (spectral.page 1 (p, q) ≅
      (derivedPushforwardCohomology f (p + q)).obj
        (derivedObjectOfComplex X (filteredComplexGradedPiece K p)))
  bounded_and_convergent : FilteredCohomologyBoundedCondition K →
    filteredComplexBounded spectral ∧ filteredComplexConverges targetFiltered

theorem exists_relativeFilteredCohomologySpectralSequence
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : FilteredComplex (Mod X.structureSheaf)) :
    Nonempty (RelativeFilteredCohomologySpectralSequenceData f K) := by
  sorry

end Formalization.Books.Cohomology.Unit20
