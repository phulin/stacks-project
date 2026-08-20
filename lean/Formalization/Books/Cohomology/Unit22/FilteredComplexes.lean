import Formalization.Books.Cohomology.Unit21.UnboundedComplexes
import Formalization.Books.Cohomology.Unit02.CohomologyOfSheaves
import Formalization.Books.Derived.Unit21.CartanEilenbergResolutions
import Formalization.Books.Homology.Unit24.FilteredComplexes

/-!
# Cohomology of Sheaves, Chapter 22: cohomology of filtered complexes

This file records the filtered-complex spectral sequences attached to global
sections and to a ringed-space pushforward, together with the two standard
filtrations of a complex and the bounded-below filtered-injective
construction.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Cohomology.Unit21
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit21
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit20
open Formalization.Books.Homology.Unit24
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit25
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v u

namespace Formalization.Books.Cohomology.Unit22

/-! ## The source notation -/

abbrev ModuleComplex (X : RingedSpace.{v}) :=
  CochainComplex (Mod X.structureSheaf) ℤ

abbrev ModuleDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleDerived X

abbrev GlobalModuleCategory (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.GlobalModuleCategory X

abbrev FilteredComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  Formalization.Books.Homology.Unit24.FilteredComplex C

abbrev FilteredComplexSpectralSequence {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) :=
  Formalization.Books.Homology.Unit24.FilteredComplexSpectralSequence K

abbrev filteredComplexFiltrationStep {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit24.filteredComplexFiltrationStep K p

abbrev filteredComplexGradedPiece {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit24.filteredComplexGradedPiece K p

abbrev filteredComplexFiniteFiltration {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  Formalization.Books.Homology.Unit24.FilteredComplexFiniteFiltration K

/-! ## Cohomology of a filtered complex -/

/-- The module `Hⁿ(X, K)` for a complex of sheaves of modules. -/
noncomputable def sheafComplexCohomology
    (X : RingedSpace.{v}) (K : CochainComplex (Mod X.structureSheaf) ℤ)
    (n : ℤ) :
    GlobalModuleCategory X :=
  (Formalization.Books.Cohomology.Unit21.globalCohomologyObject X n).obj
    (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex X K)

/-- The map on cohomology induced by `FᵖK ⟶ K`. -/
noncomputable def sheafComplexFiltrationCohomologyMap
    (X : RingedSpace.{v}) (K : FilteredComplex (Mod X.structureSheaf))
    (n p : ℤ) :
    sheafComplexCohomology X (filteredComplexFiltrationStep K p) n ⟶
      sheafComplexCohomology X
        (Formalization.Books.Homology.Unit24.filteredComplexUnderlying K) n :=
  (Formalization.Books.Cohomology.Unit21.globalCohomologyObject X n).map
    ((Formalization.Books.Cohomology.Unit20.ModuleDerivedQuotient X).map
      (Formalization.Books.Homology.Unit20.filteredComplexStepToUnderlying K p))

/-- The boundedness hypotheses in the filtered-complex spectral-sequence
lemma: sufficiently high filtration steps have zero cohomology and
sufficiently low steps map isomorphically to the total cohomology. -/
def FilteredCohomologyBoundedCondition
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf)) : Prop :=
  ∀ n : ℤ,
    (∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (sheafComplexCohomology X
        (filteredComplexFiltrationStep K p) n)) ∧
    (∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      IsIso (sheafComplexFiltrationCohomologyMap X K n p))

/-- Data for the canonical spectral sequence of global sections of a filtered
complex.  The `page` and `differential` fields of `spectral` record the
bigrading and the differential of bidegree `(r, -r + 1)`. -/
structure FilteredCohomologySpectralSequenceData
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf)) where
  globalFiltered : FilteredComplex (GlobalModuleCategory X)
  spectral : FilteredComplexSpectralSequence globalFiltered
  e₁_page : ∀ (p q : ℤ),
    Nonempty (spectral.page 1 (p, q) ≅
      sheafComplexCohomology X (filteredComplexGradedPiece K p) (p + q))
  abutment : ∀ n : ℤ,
    Nonempty (Formalization.Books.Homology.Unit24.filteredComplexCohomology
      globalFiltered n ≅
      sheafComplexCohomology X
        (Formalization.Books.Homology.Unit24.filteredComplexUnderlying K) n)
  bounded_and_convergent : FilteredCohomologyBoundedCondition K →
    filteredComplexBounded spectral ∧
      filteredComplexConvergesAt globalFiltered spectral

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

/-! ## The bounded-below finite-filtration construction -/

/-- A filtered quasi-isomorphic replacement whose associated graded terms are
injective.  This is the resolution used in the bounded-below remark. -/
def FilteredQuasiIso {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (f : K ⟶ L) : Prop :=
  ∀ p : ℤ, QuasiIso
    (((Formalization.Books.Homology.Unit20.filteredComplexStepFunctor (C := C) p).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)

structure FilteredInjectiveResolutionData
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf)) where
  resolution : FilteredComplex (Mod X.structureSheaf)
  resolutionMap : K ⟶ resolution
  quasiIso : FilteredQuasiIso resolutionMap
  boundedBelow : IsBoundedBelow resolution
  finiteFiltration : filteredComplexFiniteFiltration resolution
  gradedTermsInjective : ∀ (n p : ℤ),
    Injective ((filteredComplexGradedPiece resolution p).X n)

theorem exists_filteredInjectiveResolution
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf))
    (hK : IsBoundedBelow K)
    (hfinite : filteredComplexFiniteFiltration K) :
    Nonempty (FilteredInjectiveResolutionData K) := by
  sorry

theorem filteredCohomology_bounded_finite_filtration
    {X : RingedSpace.{v}}
    (K : FilteredComplex (Mod X.structureSheaf))
    (hK : IsBoundedBelow K)
    (hfinite : filteredComplexFiniteFiltration K) :
    Nonempty (FilteredInjectiveResolutionData K) := by
  exact exists_filteredInjectiveResolution K hK hfinite

/-! ## The truncation filtration -/

/-- The derived object represented by the `p`th step of the truncation
filtration `FᵖK = τ≤₋p K`. -/
noncomputable def truncationFiltrationStep
    (X : RingedSpace.{v}) (K : ModuleComplex X) (p : ℤ) : ModuleDerived X :=
  ((DerivedCategory.TStructure.t (C := Mod X.structureSheaf)).truncLE (-p)).obj
    (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex X K)

abbrev sheafComplexHomologyObject
    (X : RingedSpace.{v}) (K : ModuleComplex X) (j : ℤ) : Mod X.structureSheaf :=
  (HomologicalComplex.homologyFunctor (Mod X.structureSheaf)
    (ComplexShape.up ℤ) j).obj K

noncomputable def truncationShiftedHomologyObject
    (X : RingedSpace.{v}) (K : ModuleComplex X) (p : ℤ) : ModuleDerived X :=
  (shiftFunctor (ModuleDerived X) p).obj
    ((DerivedCategory.singleFunctor (Mod X.structureSheaf) 0).obj
      (sheafComplexHomologyObject X K (-p)))

noncomputable def truncationE₁Object
    (X : RingedSpace.{v}) (K : ModuleComplex X) (p q : ℤ) :
    GlobalModuleCategory X :=
  (Formalization.Books.Cohomology.Unit21.globalCohomologyObject X (p + q)).obj
    (truncationShiftedHomologyObject X K p)

noncomputable abbrev truncationE₁FormulaObject
    (X : RingedSpace.{v}) (K : ModuleComplex X) (p q : ℤ) :
    GlobalModuleCategory X :=
  Formalization.Books.Cohomology.Unit02.ringedSpaceModuleCohomologyObject X
    (sheafComplexHomologyObject X K (-p)) (2 * p + q)

noncomputable abbrev truncationE₂Object
    (X : RingedSpace.{v}) (K : ModuleComplex X) (i j : ℤ) :
    GlobalModuleCategory X :=
  Formalization.Books.Cohomology.Unit02.ringedSpaceModuleCohomologyObject X
    (sheafComplexHomologyObject X K j) i

structure TruncationSpectralSequenceData
    (X : RingedSpace.{v}) (K : ModuleComplex X) where
  filtered : FilteredComplex (Mod X.structureSheaf)
  filtration_step : ∀ p : ℤ,
    Nonempty (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex X
      (filteredComplexFiltrationStep filtered p) ≅
      truncationFiltrationStep X K p)
  globalFiltered : FilteredComplex (GlobalModuleCategory X)
  spectral : FilteredComplexSpectralSequence globalFiltered
  e₁_page : ∀ (p q : ℤ),
    Nonempty (spectral.page 1 (p, q) ≅ truncationE₁Object X K p q)
  e₁_formula : ∀ (p q : ℤ),
    Nonempty (truncationE₁Object X K p q ≅ truncationE₁FormulaObject X K p q)
  e₂_page : ∀ (i j : ℤ),
    Nonempty (spectral.page 2 (-j, i + 2 * j) ≅ truncationE₂Object X K i j)
  abutment : ∀ n : ℤ,
    Nonempty (Formalization.Books.Homology.Unit24.filteredComplexCohomology
      globalFiltered n ≅
      sheafComplexCohomology X K n)
  bounded_below_converges : IsBoundedBelow K →
    filteredComplexBounded spectral ∧
      filteredComplexConvergesAt globalFiltered spectral

theorem exists_truncation_spectral_sequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) :
    Nonempty (TruncationSpectralSequenceData X K) := by
  sorry

noncomputable def truncationSpectralSequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) :
    TruncationSpectralSequenceData X K :=
  Classical.choice (exists_truncation_spectral_sequence X K)

/-! ## The termwise (stupid) filtration -/

noncomputable abbrev termwiseFilteredTotal
    (X : RingedSpace.{v}) (K : ModuleComplex X) (hK : IsBoundedBelow K)
    (R : CartanEilenbergResolution K hK) :
    FilteredComplex (GlobalModuleCategory X) :=
  Formalization.Books.Homology.Unit25.doubleComplexFirstFilteredTotal
    (mapDoubleComplex
      (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections X)
      (left_or_right_exact_additive
        (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections X)
        (Or.inl (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections_isLeftExact X)))
      R.doubleComplex)

noncomputable abbrev termwiseCartanSpectralSequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) (hK : IsBoundedBelow K)
    (R : CartanEilenbergResolution K hK) :
    FilteredComplexSpectralSequence (termwiseFilteredTotal X K hK R) :=
  cartanEilenbergFirstSpectralSequence
    (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections X)
    (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections_isLeftExact X)
    R

/- The stupid filtration is `Kⁿ` in filtration degrees `p ≤ n` and zero in
   degrees `p > n`.  Stating it at the level of filtration-step objects keeps
   the source convention explicit without introducing a parallel complex API. -/
def TermwiseFiltrationCondition
    (X : RingedSpace.{v}) (K : ModuleComplex X)
    (F : FilteredComplex (Mod X.structureSheaf)) : Prop :=
  ∀ (n p : ℤ),
    (p ≤ n → Nonempty ((filteredComplexFiltrationStep F p).X n ≅ K.X n)) ∧
    (n < p → IsZero ((filteredComplexFiltrationStep F p).X n))

structure TermwiseSpectralSequenceExampleData
    (X : RingedSpace.{v}) (K : ModuleComplex X)
  (hK : IsBoundedBelow K) where
  resolution : CartanEilenbergResolution K hK
  filtered : FilteredComplex (Mod X.structureSheaf)
  filtration_is_termwise : TermwiseFiltrationCondition X K filtered
  spectral : FilteredComplexSpectralSequence
    (termwiseFilteredTotal X K hK resolution)
  agrees_with_cartan_eilenberg :
    spectral = termwiseCartanSpectralSequence X K hK resolution
  e₁_page : ∀ (p q : ℤ),
    Nonempty (spectral.page 1 (p, q) ≅
      (Formalization.Books.Derived.Unit20.higherRightDerivedFunctor
        (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections X)
        (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections_isLeftExact X) q).obj (K.X p))
  bounded : filteredComplexBounded spectral
  converges : filteredComplexConvergesAt
    (termwiseFilteredTotal X K hK resolution) spectral
  finite_filtration : FilteredComplexCohomologyFiniteFiltration
    (termwiseFilteredTotal X K hK resolution)
  abutment : ∀ n : ℤ,
    Nonempty (doubleComplexFirstTotalCohomology
      (mapDoubleComplex
        (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections X)
        (left_or_right_exact_additive
          (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections X)
          (Or.inl (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections_isLeftExact X)))
        resolution.doubleComplex) n ≅
      cartanEilenbergRightDerivedCohomology
        (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections X)
        (Formalization.Books.Cohomology.Unit02.ringedSpaceModuleGlobalSections_isLeftExact X)
        hK n)

theorem exists_termwise_spectral_sequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) (hK : IsBoundedBelow K) :
    Nonempty (TermwiseSpectralSequenceExampleData X K hK) := by
  sorry

noncomputable def termwiseSpectralSequence
    (X : RingedSpace.{v}) (K : ModuleComplex X) (hK : IsBoundedBelow K) :
    TermwiseSpectralSequenceExampleData X K hK :=
  Classical.choice (exists_termwise_spectral_sequence X K hK)

/-! ## The relative spectral sequence -/

def RelativeFilteredCohomologyBoundedCondition
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : FilteredComplex (Mod X.structureSheaf)) : Prop :=
  ∀ n : ℤ,
    (∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((Formalization.Books.Cohomology.Unit21.derivedPushforwardCohomology f n).obj
        (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex X
          (filteredComplexFiltrationStep K p)))) ∧
    (∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      IsIso ((Formalization.Books.Cohomology.Unit21.derivedPushforwardCohomology f n).map
        ((Formalization.Books.Cohomology.Unit20.ModuleDerivedQuotient X).map
          (Formalization.Books.Homology.Unit20.filteredComplexStepToUnderlying K p))))

structure RelativeFilteredCohomologySpectralSequenceData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : FilteredComplex (Mod X.structureSheaf)) where
  targetFiltered : FilteredComplex (Mod Y.structureSheaf)
  spectral : FilteredComplexSpectralSequence targetFiltered
  e₁_page : ∀ (p q : ℤ),
    Nonempty (spectral.page 1 (p, q) ≅
      (Formalization.Books.Cohomology.Unit21.derivedPushforwardCohomology
        f (p + q)).obj
        (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex X
          (filteredComplexGradedPiece K p)))
  abutment : ∀ n : ℤ,
    Nonempty (Formalization.Books.Homology.Unit24.filteredComplexCohomology
      targetFiltered n ≅
      (Formalization.Books.Cohomology.Unit21.derivedPushforwardCohomology f n).obj
        (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex X
          (Formalization.Books.Homology.Unit24.filteredComplexUnderlying K)))
  bounded_and_convergent : RelativeFilteredCohomologyBoundedCondition f K →
    filteredComplexBounded spectral ∧
      filteredComplexConvergesAt targetFiltered spectral

theorem exists_relativeFilteredCohomologySpectralSequence
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : FilteredComplex (Mod X.structureSheaf)) :
    Nonempty (RelativeFilteredCohomologySpectralSequenceData f K) := by
  sorry

noncomputable def relativeFilteredCohomologySpectralSequence
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : FilteredComplex (Mod X.structureSheaf)) :
    RelativeFilteredCohomologySpectralSequenceData f K :=
  Classical.choice (exists_relativeFilteredCohomologySpectralSequence f K)

end Formalization.Books.Cohomology.Unit22
