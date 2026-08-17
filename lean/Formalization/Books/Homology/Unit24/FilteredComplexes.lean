import Formalization.Books.Homology.Unit20.FilteredComplexes
import Formalization.Books.Homology.Unit13.Complexes
import Formalization.Books.Homology.Unit11.KGroups
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Homological Algebra, Chapter 24: Spectral sequences: filtered complexes

This file gives the source-facing interface for a filtered cochain complex.
The filtered-object, subobject, cohomology, and categorical quotient
constructions are inherited from the preceding chapters.  The extra
reindexing in `filteredComplexGradedPiece` is intentional: the source uses
`(p, q)` with total degree `p + q`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit20
open Formalization.Books.Homology.Unit13
open Formalization.Books.Homology.Unit11
open scoped BigOperators

universe v u

namespace Formalization.Books.Homology.Unit24

/-! ## Filtered complexes and their first pages -/

/-- A filtered complex is a cochain complex in the category of filtered
objects.  This is the canonical filtered-object definition from Chapter 20.
-/
abbrev FilteredComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  Formalization.Books.Homology.Unit20.FilteredComplex C

abbrev filteredComplexTerm {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) : FilteredObject C := K.X n

def filteredComplexDifferential {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) :
    (K.X n).carrier ⟶ (K.X (n + 1)).carrier :=
  FilteredHom.hom (K.d n (n + 1))

/- The filtration step is itself a cochain complex.  This is the canonical
   construction from the preceding chapter, and records the source's
   observation that every `F^p K` is a complex. -/
abbrev filteredComplexFiltrationStep {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexStepComplex K p

/-- The `p`th associated-graded complex, reindexed so that degree `q` is
`gr^p K^(p+q)`. -/
def filteredComplexGradedPiece {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ where
  X q := gradedPiece (K.X (p + q)) p
  d q r := if h : q + 1 = r then
      h ▸ gradedPieceMap (K.d (p + q) (p + r)) p
    else 0
  shape q r hqr := by
    classical
    split_ifs with h
    · exact (hqr h).elim
    · rfl
  d_comp_d' q r s hqr hrs := by
    sorry

abbrev filteredComplexE₀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) : C :=
  (filteredComplexGradedPiece K p).X q

def filteredComplexD₀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexE₀ K p q ⟶ filteredComplexE₀ K p (q + 1) :=
  (filteredComplexGradedPiece K p).d q (q + 1)

abbrev filteredComplexE₁ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj
    (filteredComplexGradedPiece K p)

theorem filteredComplex_E₀_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexE₀ K p q = gradedPiece (K.X (p + q)) p := rfl

theorem filteredComplex_D₀_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexD₀ K p q =
      (filteredComplexGradedPiece K p).d q (q + 1) := rfl

def filteredComplexSourceD₀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) :
    gradedPiece (K.X (p + q)) p ⟶ gradedPiece (K.X (p + q + 1)) p :=
  gradedPieceMap (K.d (p + q) (p + q + 1)) p

theorem filteredComplex_D₀_source_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexD₀ K p q =
      filteredComplexSourceD₀ K p q ≫
        eqToHom (congrArg (fun n : ℤ => gradedPiece (K.X n) p) (by omega)) := by
  sorry

theorem filteredComplex_E₁_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexE₁ K p q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj
        (filteredComplexGradedPiece K p) := rfl

abbrev filteredComplexUnshiftedGradedPiece {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p : ℤ) :
    CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexGradedPiece K p

theorem filteredComplex_E₁_source_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    Nonempty (filteredComplexE₁ K p q ≅
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (p + q)).obj
        (filteredComplexUnshiftedGradedPiece K p)) := by
  sorry

/-! The countable-direct-sum warning and the temporary hypothesis used in the
direct-sum construction.  The general construction below does not require
this hypothesis. -/

abbrev CountableDirectSumsExact (C : Type u) [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C] : Prop :=
  Formalization.Books.Homology.Unit20.CountableDirectSumsExact C

abbrev NonExactCountableDirectSumsExample :=
  Formalization.Books.Homology.Unit16.NonExactGradedTotalExample

theorem exists_nonExactCountableDirectSumsExample :
    Nonempty (NonExactCountableDirectSumsExample.{u}) := by
  exact Formalization.Books.Homology.Unit16.exists_nonExactGradedTotalExample

/-! ### `Zᵣ`, `Bᵣ`, pages, and page differentials -/

def filteredComplexCycleCore {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  (Subobject.pullback (filteredComplexDifferential K (p + q))).obj
      ((K.X (p + q + 1)).filtration.obj (p + r)) ⊓
    (K.X (p + q)).filtration.obj p

def filteredComplexBoundaryCore {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  (Subobject.«exists» (FilteredHom.hom (K.d (p + q - 1) (p + q)))).obj
      ((K.X (p + q - 1)).filtration.obj (p - r + 1)) ⊓
    (K.X (p + q)).filtration.obj p

def filteredComplexCyclePlus {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  filteredComplexCycleCore K r p q ⊔ (K.X (p + q)).filtration.obj (p + 1)

def filteredComplexBoundaryPlus {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  filteredComplexBoundaryCore K r p q ⊔ (K.X (p + q)).filtration.obj (p + 1)

theorem filteredComplex_boundary_le_cycle
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (r p q : ℤ) :
    filteredComplexBoundaryPlus K r p q ≤ filteredComplexCyclePlus K r p q := by
  sorry

theorem filteredComplex_boundary_monotone
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (r p q : ℤ) :
    filteredComplexBoundaryPlus K r p q ≤
      filteredComplexBoundaryPlus K (r + 1) p q := by
  sorry

theorem filteredComplex_cycle_antitone
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (r p q : ℤ) :
    filteredComplexCyclePlus K (r + 1) p q ≤
      filteredComplexCyclePlus K r p q := by
  sorry

/-- The source's `Zᵣ^{p,q}` and `Bᵣ^{p,q}` as categorical subquotients of
`K^(p+q)`. -/
noncomputable def filteredComplexZ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (r p q : ℤ) : C :=
  subquotientObject ((K.X (p + q)).filtration.obj (p + 1))
    (filteredComplexCyclePlus K r p q)
    (le_sup_right)

noncomputable def filteredComplexB {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (r p q : ℤ) : C :=
  subquotientObject ((K.X (p + q)).filtration.obj (p + 1))
    (filteredComplexBoundaryPlus K r p q)
    (le_sup_right)

noncomputable def filteredComplexPage {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (r p q : ℤ) : C :=
  subquotientObject (filteredComplexBoundaryPlus K r p q)
    (filteredComplexCyclePlus K r p q)
    (filteredComplex_boundary_le_cycle K r p q)

noncomputable def filteredComplexPageClass {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (r p q : ℤ) {T : C}
    (z : T ⟶ (filteredComplexCyclePlus K r p q : C)) :
    T ⟶ filteredComplexPage K r p q :=
  z ≫ cokernel.π (Subobject.ofLE (filteredComplexBoundaryPlus K r p q)
    (filteredComplexCyclePlus K r p q)
    (filteredComplex_boundary_le_cycle K r p q))

structure FilteredComplexPageSubobjectData {C : Type u}
    [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) where
  B : Subobject (filteredComplexE₀ K p q)
  Z : Subobject (filteredComplexE₀ K p q)
  B_le_Z : B ≤ Z
  B_component : Nonempty ((B : C) ≅ filteredComplexB K r p q)
  Z_component : Nonempty ((Z : C) ≅ filteredComplexZ K r p q)

theorem filteredComplex_page_subobjects_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Nonempty (FilteredComplexPageSubobjectData K r p q) := by
  sorry

structure FilteredComplexPageDifferentials {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) where
  differential : ∀ r p q : ℤ,
    filteredComplexPage K r p q ⟶ filteredComplexPage K r (p + r) (q - r + 1)
  square_zero : ∀ r p q : ℤ,
    differential r p q ≫ differential r (p + r) (q - r + 1) = 0
  lift_rule : ∀ (r p q : ℤ) {T : C}
    (z : T ⟶ (filteredComplexCyclePlus K r p q : C))
    (zNext : T ⟶
      (filteredComplexCyclePlus K r (p + r) (q - r + 1) : C))
    (_hz : zNext ≫
        (filteredComplexCyclePlus K r (p + r) (q - r + 1)).arrow =
      z ≫ (filteredComplexCyclePlus K r p q).arrow ≫
        filteredComplexDifferential K (p + q) ≫
          eqToHom (congrArg (fun n : ℤ => (K.X n).carrier)
            (by omega))),
    filteredComplexPageClass K r p q z ≫ differential r p q =
      filteredComplexPageClass K r (p + r) (q - r + 1) zNext

theorem filteredComplex_page_differentials_exists
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    Nonempty (FilteredComplexPageDifferentials K) := by
  sorry

noncomputable def filteredComplexPageDifferentials
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    FilteredComplexPageDifferentials K :=
  Classical.choice (filteredComplex_page_differentials_exists K)

abbrev filteredComplexD {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    filteredComplexPage K r p q ⟶ filteredComplexPage K r (p + r) (q - r + 1) :=
  (filteredComplexPageDifferentials K).differential r p q

theorem filteredComplexD_squared
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    filteredComplexD K r p q ≫ filteredComplexD K r (p + r) (q - r + 1) = 0 := by
  exact (filteredComplexPageDifferentials K).square_zero r p q

/-! ### The bigraded spectral sequence -/

def bigradedShift {C : Type u} [Category.{v} C] (a b : ℤ) :
    GradedObject (ℤ × ℤ) C ⥤ GradedObject (ℤ × ℤ) C :=
  GradedObject.comap C (fun x => (a + x.1, b + x.2))

structure FilteredComplexSpectralSequence {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) where
  page : ℕ → GradedObject (ℤ × ℤ) C
  differential : ∀ r : ℕ,
    page r ⟶ (bigradedShift r (-r + 1)).obj (page r)
  square_zero : ∀ r : ℕ,
    differential r ≫ (bigradedShift r (-r + 1)).map (differential r) = 0
  next_page : ∀ (r : ℕ) (p q : ℤ), Nonempty
    (page (r + 1) (p, q) ≅
      subquotientObject
        (Subobject.mk (Abelian.image.ι
          (differential r (p - r, q + r - 1) ≫
            (eqToHom (by
              change page r
                (r + (p - r), (-r + 1) + (q + r - 1)) = page r (p, q)
              congr 1; ring_nf) :
              (bigradedShift r (-r + 1)).obj (page r)
                  (p - r, q + r - 1) ⟶ page r (p, q)))))
        (Subobject.mk (kernel.ι (differential r (p, q))))
        (by sorry))
  component_iso : ∀ (r : ℕ) (p q : ℤ),
    Nonempty (page r (p, q) ≅ filteredComplexPage K (r : ℤ) p q)
  zero_page : ∀ p q : ℤ,
    Nonempty (page 0 (p, q) ≅ filteredComplexE₀ K p q)
  first_page : ∀ p q : ℤ,
    Nonempty (page 1 (p, q) ≅ filteredComplexE₁ K p q)

theorem filteredComplex_spectral_sequence_exists
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    Nonempty (FilteredComplexSpectralSequence K) := by
  sorry

noncomputable def filteredComplexSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    FilteredComplexSpectralSequence K :=
  Classical.choice (filteredComplex_spectral_sequence_exists K)

/-! ### The `d₁` exact sequence and filtration-raising case -/

abbrev filteredComplexStepComplex {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexStepComplex K p

abbrev filteredComplexD1ShortExact {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  Formalization.Books.Homology.Unit20.filteredComplexD1ShortExact K p

theorem filteredComplexD1_short_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) :
    (filteredComplexD1ShortExact K p).ShortExact := by
  exact Formalization.Books.Homology.Unit20.filteredComplexD1_boundary_description K p

noncomputable def filteredComplexD1Boundary {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    (filteredComplexD1ShortExact K p).X₃.homology (p + q) ⟶
      (filteredComplexD1ShortExact K p).X₁.homology (p + q + 1) :=
  cochainConnectingMap (filteredComplexD1_short_exact K p) (p + q)

structure FilteredComplexD1BoundaryData {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) where
  d₁ : ∀ p q : ℤ, filteredComplexE₁ K p q ⟶ filteredComplexE₁ K (p + 1) q
  boundary : ∀ p q : ℤ,
    filteredComplexE₁ K p q ⟶ filteredComplexE₁ K (p + 1) q
  boundary_is_connecting : ∀ p q : ℤ,
    ∃ e₀ : filteredComplexE₁ K p q ≅
        (filteredComplexD1ShortExact K p).X₃.homology (p + q),
      ∃ e₁ : filteredComplexE₁ K (p + 1) q ≅
        (filteredComplexD1ShortExact K p).X₁.homology (p + q + 1),
        boundary p q = e₀.hom ≫ filteredComplexD1Boundary K p q ≫ e₁.inv
  d₁_is_boundary : ∀ p q : ℤ, d₁ p q = boundary p q

theorem filteredComplex_d1_boundary_data_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    Nonempty (FilteredComplexD1BoundaryData K) := by
  sorry

def FilteredComplexRaisesFiltration {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ (n p : ℤ),
    (K.X n).filtration.obj p ≤
      (Subobject.pullback (filteredComplexDifferential K n)).obj
        ((K.X (n + 1)).filtration.obj (p + 1))

theorem filteredComplexRaisesFiltration_zero_graded_differential
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexRaisesFiltration K) (p q : ℤ) :
    filteredComplexD₀ K p q = 0 := by
  sorry

theorem filteredComplexRaisesFiltration_E₁_source_formula
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexRaisesFiltration K) (p q : ℤ) :
    Nonempty (filteredComplexE₁ K p q ≅ gradedPiece (K.X (p + q)) p) := by
  sorry

/-! ### Functoriality -/

structure FilteredComplexSpectralSequenceHom {C : Type u}
    [Category.{v} C] [Abelian C] {K L : FilteredComplex C}
    (Sₖ : FilteredComplexSpectralSequence K)
    (Sₗ : FilteredComplexSpectralSequence L) where
  pageHom : ∀ r : ℕ, Sₖ.page r ⟶ Sₗ.page r
  compatible : ∀ r : ℕ,
    pageHom r ≫ Sₗ.differential r =
      Sₖ.differential r ≫ (bigradedShift r (-r + 1)).map (pageHom r)

theorem filteredComplex_functoriality
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (f : K ⟶ L) :
    ∀ (Sₖ : FilteredComplexSpectralSequence K)
      (Sₗ : FilteredComplexSpectralSequence L),
      Nonempty (FilteredComplexSpectralSequenceHom Sₖ Sₗ) := by
  sorry

/-! ## Induced cohomology filtration -/

abbrev filteredComplexUnderlying {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexUnderlying K

abbrev filteredComplexCohomology {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredComplexCohomology K n

abbrev filteredComplexStepCohomology {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredComplexStepCohomology K n p

abbrev filteredComplexCohomologyFilteredObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n : ℤ) :
    FilteredObject C :=
  Formalization.Books.Homology.Unit20.filteredComplexCohomologyFilteredObject K n

theorem filteredComplex_induced_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) :
    (filteredComplexCohomologyFilteredObject K n).filtration.obj p =
      Formalization.Books.Homology.Unit20.filteredComplexCohomologyFiltrationStep
        K n p := rfl

def filteredComplexKernelSubobject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n : ℤ) :
  Subobject (K.X n).carrier :=
  kernelSubobject ((filteredComplexUnderlying K).d n (n + 1))

def filteredComplexImageSubobject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n : ℤ) :
    Subobject (K.X n).carrier :=
  (Subobject.«exists» ((filteredComplexUnderlying K).d (n - 1) n)).obj ⊤

def filteredComplexCohomologyNumerator {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) :
    Subobject (K.X n).carrier :=
  (filteredComplexKernelSubobject K n ⊓ (K.X n).filtration.obj p) ⊔
    filteredComplexImageSubobject K n

def filteredComplexCohomologyGradedDenominator {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) :
    Subobject (K.X n).carrier :=
  (filteredComplexKernelSubobject K n ⊓ (K.X n).filtration.obj (p + 1)) ⊔
    (filteredComplexImageSubobject K n ⊓ (K.X n).filtration.obj p)

noncomputable def filteredComplexCohomologyFormulaObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) : C :=
  subquotientObject (filteredComplexImageSubobject K n)
    (filteredComplexCohomologyNumerator K n p) le_sup_right

noncomputable def filteredComplexCohomologyGradedFormulaObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) : C :=
  subquotientObject (filteredComplexCohomologyGradedDenominator K n p)
    (filteredComplexKernelSubobject K n ⊓ (K.X n).filtration.obj p)
    (by sorry)

theorem filteredComplex_cohomology_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) :
    Nonempty (((filteredComplexCohomologyFilteredObject K n).filtration.obj p : C)
      ≅ filteredComplexCohomologyFormulaObject K n p) := by
  sorry

theorem filteredComplex_cohomology_graded_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) :
    Nonempty (gradedPiece (filteredComplexCohomologyFilteredObject K n) p ≅
      filteredComplexCohomologyGradedFormulaObject K n p) := by
  sorry

/-! ## Limits and convergence -/

structure FilteredComplexLimitData {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) where
  Binf : ∀ p q : ℤ, Subobject (K.X (p + q)).carrier
  Zinf : ∀ p q : ℤ, Subobject (K.X (p + q)).carrier
  Binf_upper : ∀ p q : ℤ, ∀ r : ℕ,
    filteredComplexBoundaryPlus K (r : ℤ) p q ≤ Binf p q
  Binf_least : ∀ p q : ℤ, ∀ Y : Subobject (K.X (p + q)).carrier,
    (∀ r : ℕ, filteredComplexBoundaryPlus K (r : ℤ) p q ≤ Y) → Binf p q ≤ Y
  Zinf_lower : ∀ p q : ℤ, ∀ r : ℕ,
    Zinf p q ≤ filteredComplexCyclePlus K (r : ℤ) p q
  Zinf_greatest : ∀ p q : ℤ, ∀ Y : Subobject (K.X (p + q)).carrier,
    (∀ r : ℕ, Y ≤ filteredComplexCyclePlus K (r : ℤ) p q) → Y ≤ Zinf p q
  Binf_le_Zinf : ∀ p q : ℤ, Binf p q ≤ Zinf p q

noncomputable def filteredComplexLimitPage {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (L : FilteredComplexLimitData K)
    (p q : ℤ) : C :=
  subquotientObject (L.Binf p q) (L.Zinf p q) (L.Binf_le_Zinf p q)

def filteredComplexAssociatedGradedCohomology {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    GradedObject (ℤ × ℤ) C :=
  fun pq => gradedPiece
    (filteredComplexCohomologyFilteredObject K (pq.1 + pq.2)) pq.1

def FilteredComplexLimitGradedSubquotient {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (L : FilteredComplexLimitData K) : Prop :=
  ∀ p q : ℤ,
    IsSubquotientOf
      (X := gradedPiece (filteredComplexCohomologyFilteredObject K (p + q)) p)
      (Y := filteredComplexLimitPage K L p q)

theorem filteredComplex_limit_graded_subquotient {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (L : FilteredComplexLimitData K) :
    FilteredComplexLimitGradedSubquotient K L := by
  sorry

def filteredComplexCycleLimitRepresentative {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  (filteredComplexKernelSubobject K (p + q) ⊓
      (K.X (p + q)).filtration.obj p) ⊔
    (K.X (p + q)).filtration.obj (p + 1)

def filteredComplexBoundaryLimitRepresentative {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  (filteredComplexImageSubobject K (p + q) ⊓
      (K.X (p + q)).filtration.obj p) ⊔
    (K.X (p + q)).filtration.obj (p + 1)

def FilteredComplexTopBigradedInclusion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) : Prop :=
  ∀ r : ℕ,
    filteredComplexCycleLimitRepresentative K p q ≤
      filteredComplexCyclePlus K (r : ℤ) p q

def FilteredComplexBottomBigradedInclusion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) : Prop :=
  ∀ r : ℕ,
    filteredComplexBoundaryPlus K (r : ℤ) p q ≤
      filteredComplexBoundaryLimitRepresentative K p q

theorem filteredComplex_on_top_bigraded
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (p q : ℤ) : FilteredComplexTopBigradedInclusion K p q := by
  sorry

theorem filteredComplex_at_bottom_bigraded
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (p q : ℤ) : FilteredComplexBottomBigradedInclusion K p q := by
  sorry

def FilteredComplexLimitEquationsHold {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (L : FilteredComplexLimitData K) : Prop :=
  ∀ p q : ℤ,
    L.Binf p q = filteredComplexBoundaryLimitRepresentative K p q ∧
      L.Zinf p q = filteredComplexCycleLimitRepresentative K p q

def filteredComplexWeaklyConverges {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∃ L : FilteredComplexLimitData K,
    Nonempty (filteredComplexAssociatedGradedCohomology K ≅
      fun pq => filteredComplexLimitPage K L pq.1 pq.2)

def filteredComplexKernelImageFiltration {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n : ℤ) :
    DecreasingFiltration C (K.X n).carrier where
  obj p :=
    (filteredComplexKernelSubobject K n ⊓ (K.X n).filtration.obj p) ⊔
      filteredComplexImageSubobject K n
  antitone := by
    intro p q hpq
    exact sup_le_sup
      (inf_le_inf_left _ ((K.X n).filtration.antitone hpq)) le_rfl

def FilteredComplexAbutmentCriterion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ,
    ∃ hF : HasIntersection (filteredComplexKernelImageFiltration K n),
      ∃ hU : HasUnion (filteredComplexKernelImageFiltration K n),
        intersection hF = filteredComplexImageSubobject K n ∧
          union hU = filteredComplexKernelSubobject K n

def filteredComplexAbuts {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  filteredComplexWeaklyConverges K ∧ FilteredComplexAbutmentCriterion K

abbrev FilteredComplexCohomologyComplete {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) : Prop :=
  Formalization.Books.Homology.Unit20.FilteredComplexCohomologyComplete K

def filteredComplexRegular {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
    S.differential r (p, q) = 0

def filteredComplexCoregular {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
    S.differential r (p - r, q + r - 1) = 0

def filteredComplexBounded {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ n : ℤ, Set.Finite {p : ℤ | ¬ IsZero (S.page 0 (p, n - p))}

def filteredComplexBoundedBelow {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, b ≤ p → IsZero (S.page 0 (p, n - p))

def filteredComplexBoundedAbove {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, p ≤ b → IsZero (S.page 0 (p, n - p))

theorem filteredComplex_regular_iff_stable_cycles
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexRegular S ↔
      ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
        filteredComplexCyclePlus K (r : ℤ) p q =
          filteredComplexCyclePlus K (r + 1 : ℤ) p q := by
  sorry

theorem filteredComplex_coregular_iff_stable_boundaries
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexCoregular S ↔
      ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
        filteredComplexBoundaryPlus K (r : ℤ) p q =
          filteredComplexBoundaryPlus K (r + 1 : ℤ) p q := by
  sorry

theorem filteredComplex_bounded_iff_below_and_above
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexBounded S ↔
      filteredComplexBoundedBelow S ∧ filteredComplexBoundedAbove S := by
  sorry

theorem filteredComplex_bounded_below_regular
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexBoundedBelow S → filteredComplexRegular S := by
  sorry

theorem filteredComplex_bounded_above_coregular
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexBoundedAbove S → filteredComplexCoregular S := by
  sorry

def filteredComplexConverges {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∃ S : FilteredComplexSpectralSequence K,
    filteredComplexRegular S ∧ filteredComplexAbuts K ∧
      FilteredComplexCohomologyComplete K

theorem filteredComplex_weak_convergence_iff_limit_equations
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (L : FilteredComplexLimitData K) :
    Nonempty (filteredComplexAssociatedGradedCohomology K ≅
      (fun pq => filteredComplexLimitPage K L pq.1 pq.2)) ↔
      FilteredComplexLimitEquationsHold K L := by
  sorry

theorem filteredComplex_weak_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    filteredComplexWeaklyConverges K ↔
      ∃ L : FilteredComplexLimitData K, FilteredComplexLimitEquationsHold K L := by
  sorry

theorem filteredComplex_abutment_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    filteredComplexAbuts K ↔
      filteredComplexWeaklyConverges K ∧ FilteredComplexAbutmentCriterion K := by
  sorry

theorem filteredComplex_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    filteredComplexConverges K ↔
      ∃ S : FilteredComplexSpectralSequence K,
        filteredComplexRegular S ∧ filteredComplexAbuts K ∧
          FilteredComplexCohomologyComplete K := by
  sorry

/-! ## Finite filtrations and the `K₀` relation -/

def FilteredComplexFiniteFiltration {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ, (K.X n).IsFinite

def FilteredComplexCohomologyFiniteFiltration {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ,
    (filteredComplexCohomologyFilteredObject K n).IsFinite

theorem filteredComplex_finite_filtration_is_bounded
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K) :
    ∀ S : FilteredComplexSpectralSequence K, filteredComplexBounded S := by
  sorry

theorem filteredComplex_finite_filtration_on_cohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K) :
    FilteredComplexCohomologyFiniteFiltration K := by
  sorry

theorem filteredComplex_finite_filtration_converges
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexFiniteFiltration K) :
    filteredComplexWeaklyConverges K ∧ filteredComplexAbuts K := by
  sorry

theorem filteredComplex_finite_filtration_converges_to_cohomology
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexFiniteFiltration K) :
    filteredComplexConverges K := by
  sorry

theorem filteredComplex_finite_filtration_weak_serre_membership
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ, P (S.page r (p, q))) :
    ∀ n : ℤ, P (filteredComplexCohomology K n) := by
  sorry

abbrev filteredComplexAlternatingSign :=
  Formalization.Books.Homology.Unit20.filteredComplexAlternatingSign

structure FilteredComplexK0AlternatingSumStatement {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass] where
  finite_cohomology : Set.Finite
    {n : ℤ | ¬ IsZero (filteredComplexCohomology K n)}
  finite_page : Set.Finite {pq : ℤ × ℤ | ¬ IsZero (S.page r pq)}
  page_mem : ∀ p q : ℤ, P (S.page r (p, q))
  cohomology_mem : ∀ n : ℤ, P (filteredComplexCohomology K n)
  alternating_relation : ∃ s : Finset ℤ, ∃ t : Finset (ℤ × ℤ),
    (∀ n : ℤ, ¬ IsZero (filteredComplexCohomology K n) → n ∈ s) ∧
      (∀ pq : ℤ × ℤ, ¬ IsZero (S.page r pq) → pq ∈ t) ∧
      (Finset.sum s (fun n =>
        filteredComplexAlternatingSign n •
          KZero.classOf (⟨filteredComplexCohomology K n, cohomology_mem n⟩ :
            P.FullSubcategory))) =
        Finset.sum t (fun pq =>
          filteredComplexAlternatingSign (pq.1 + pq.2) •
            KZero.classOf (⟨S.page r pq, page_mem pq.1 pq.2⟩ :
              P.FullSubcategory))

def IsWeakSerreClosureOfPage {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) : Prop :=
  P.IsWeakSerreClass ∧
    (∀ p q : ℤ, P (S.page r (p, q))) ∧
    (∀ Q : ObjectProperty C, Q.IsWeakSerreClass →
      (∀ p q : ℤ, Q (S.page r (p, q))) → ∀ X : C, P X → Q X)

theorem filteredComplex_K0_alternating_sum
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : IsWeakSerreClosureOfPage S r P)
    (hS : Set.Finite {pq : ℤ × ℤ | ¬ IsZero (S.page r pq)}) :
    Nonempty (FilteredComplexK0AlternatingSumStatement K S r P) := by
  sorry

/-! ## The trivial convergence criterion -/

abbrev FilteredComplexTrivialConvergenceHypotheses {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) :=
  Formalization.Books.Homology.Unit20.FilteredComplexTrivialConvergenceHypotheses K

structure FilteredComplexTrivialConvergenceConclusion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) where
  bounded : ∀ S : FilteredComplexSpectralSequence K, filteredComplexBounded S
  cohomology_filtration_finite : FilteredComplexCohomologyFiniteFiltration K
  converges : filteredComplexConverges K

theorem filteredComplex_trivial_convergence
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexTrivialConvergenceHypotheses K) :
    Nonempty (FilteredComplexTrivialConvergenceConclusion K) := by
  sorry

end Formalization.Books.Homology.Unit24
