import Formalization.Books.Homology.Unit20.DifferentialObjects
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Filtered differential objects

The filtration itself is the canonical `Unit19.FilteredObject`.  The
differential-object API from the preceding section is reused over the
category of filtered objects; this keeps the factorization data of a filtered
morphism visible in every declaration below.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit16

universe v u

namespace Formalization.Books.Homology.Unit20

/-! ## 20.4 Filtered differential objects -/

/-- A filtered differential object is a differential object in `Fil(C)`. -/
abbrev FilteredDifferentialObject (C : Type u) [Category.{v} C] [Abelian C] :=
  PlainDifferentialObject (FilteredObject C)

/-- A filtered map commuting with the differentials. -/
abbrev FilteredDifferentialObjectHom {C : Type u} [Category.{v} C] [Abelian C]
    (A B : FilteredDifferentialObject C) :=
  PlainDifferentialObjectHom A B

abbrev filteredDifferentialUnderlying {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) :
    K.carrier.carrier ⟶ K.carrier.carrier :=
  FilteredHom.hom K.d

/-- The hypothesis that countable direct sums are exact, expressed by the
canonical totalization functor from the graded-object chapter. -/
abbrev CountableDirectSumsExact (C : Type u) [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] : Prop :=
  gradedTotalIsExact C

/-- The differential induced on one filtration step. -/
def filteredStepDifferential {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    (K.carrier.filtration.obj p : C) ⟶ (K.carrier.filtration.obj p : C) :=
  (K.carrier.filtration.obj p).factorThru
    ((K.carrier.filtration.obj p).arrow ≫ filteredDifferentialUnderlying K)
    (FilteredHom.map_filtration K.d p)

def filteredDifferentialSummands {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) : GradedObject ℤ C :=
  fun p => (K.carrier.filtration.obj p : C)

def filteredDifferentialDirectSumCarrier {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) : C :=
  ∐ filteredDifferentialSummands K

/-- The componentwise differential on `⊕ₚ FᵖK`. -/
def filteredDifferentialDirectSumMap {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialDirectSumCarrier K ⟶ filteredDifferentialDirectSumCarrier K :=
  Limits.Sigma.map (fun p : ℤ => filteredStepDifferential K p)

/-- The graded direct-sum differential object used in the exact-couple
construction. -/
def filteredDifferentialDirectSumObject {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) : PlainDifferentialObject C where
  carrier := filteredDifferentialDirectSumCarrier K
  d := filteredDifferentialDirectSumMap K
  d_squared := by
    sorry

def filteredDifferentialDirectSumPair {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) : GradedPair C where
  carrier := filteredDifferentialDirectSumCarrier K
  component := filteredDifferentialSummands K
  decomposition := Iso.refl _

/-- The shift-by-one inclusion map on the direct sum of filtration steps. -/
def filteredDifferentialDirectSumAlpha {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialDirectSumCarrier K ⟶ filteredDifferentialDirectSumCarrier K :=
  Limits.Sigma.desc (fun p =>
    Subobject.ofLE (K.carrier.filtration.obj p)
      (K.carrier.filtration.obj (p - 1))
      (K.carrier.filtration.antitone (by omega)) ≫
      Limits.Sigma.ι (filteredDifferentialSummands K) (p - 1))

theorem filteredDifferentialDirectSumAlpha_mono {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    Mono (filteredDifferentialDirectSumAlpha K) := by
  sorry

def filteredDifferentialDirectSumAlphaHom {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    PlainDifferentialObjectHom (filteredDifferentialDirectSumObject K)
      (filteredDifferentialDirectSumObject K) where
  hom := filteredDifferentialDirectSumAlpha K
  comm := by
    sorry

def filteredDifferentialDirectSumInjectiveSelfMap {C : Type u}
    [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    PlainDifferentialInjectiveEndomorphism (filteredDifferentialDirectSumObject K) where
  hom := filteredDifferentialDirectSumAlphaHom K
  injective := filteredDifferentialDirectSumAlpha_mono K

/-! ### The first two pages -/

def filteredGradedDifferentialObject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    PlainDifferentialObject C where
  carrier := gradedPiece K.carrier p
  d := gradedPieceMap K.d p
  d_squared := by
    sorry

abbrev filteredDifferentialE₀ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  gradedPiece K.carrier p

abbrev filteredDifferentialD₀ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialE₀ K p ⟶ filteredDifferentialE₀ K p :=
  gradedPieceMap K.d p

abbrev filteredDifferentialE₁ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  plainDifferentialHomology (filteredGradedDifferentialObject K p)

theorem filteredDifferential_E₀_is_gradedPiece
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialE₀ K p = gradedPiece K.carrier p := rfl

theorem filteredDifferential_E₁_is_graded_homology
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialE₁ K p =
      plainDifferentialHomology (filteredGradedDifferentialObject K p) := rfl

/-! ### The `Zᵣ`, `Bᵣ`, page, and lift-rule formulae -/

def filteredDifferentialCycleCore {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) (r : ℕ) :
    Subobject K.carrier.carrier :=
  (Subobject.pullback (filteredDifferentialUnderlying K)).obj
      (K.carrier.filtration.obj (p + r)) ⊓ K.carrier.filtration.obj p

def filteredDifferentialBoundaryCore {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) (r : ℕ) :
    Subobject K.carrier.carrier :=
  (Subobject.«exists» (filteredDifferentialUnderlying K)).obj
      (K.carrier.filtration.obj (p - r + 1)) ⊓ K.carrier.filtration.obj p

def filteredDifferentialCyclePlus {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) (r : ℕ) :
    Subobject K.carrier.carrier :=
  filteredDifferentialCycleCore K p r ⊔ K.carrier.filtration.obj (p + 1)

def filteredDifferentialBoundaryPlus {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) (r : ℕ) :
    Subobject K.carrier.carrier :=
  filteredDifferentialBoundaryCore K p r ⊔ K.carrier.filtration.obj (p + 1)

theorem filteredDifferential_boundary_le_cycle
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) (r : ℕ) :
    filteredDifferentialBoundaryPlus K p r ≤ filteredDifferentialCyclePlus K p r := by
  sorry

noncomputable def filteredDifferentialPage {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) : C :=
  subquotientObject (filteredDifferentialBoundaryPlus K p r)
    (filteredDifferentialCyclePlus K p r)
    (filteredDifferential_boundary_le_cycle K p r)

noncomputable def filteredDifferentialPageClass {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ)
    {T : C} (z : T ⟶ (filteredDifferentialCyclePlus K p r : C)) :
    T ⟶ filteredDifferentialPage K r p :=
  z ≫ cokernel.π (Subobject.ofLE (filteredDifferentialBoundaryPlus K p r)
    (filteredDifferentialCyclePlus K p r)
    (filteredDifferential_boundary_le_cycle K p r))

structure FilteredDifferentialPageDifferentials {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) where
  differential : ∀ (r : ℕ) (p : ℤ),
    filteredDifferentialPage K r p ⟶ filteredDifferentialPage K r (p + r)
  square_zero : ∀ (r : ℕ) (p : ℤ),
    differential r p ≫ differential r (p + r) = 0
  lift_rule : ∀ (r : ℕ) (p : ℤ) {T : C}
    (z : T ⟶ (filteredDifferentialCyclePlus K p r : C))
    (zNext : T ⟶ (filteredDifferentialCyclePlus K (p + r) r : C))
    (_hz : zNext ≫ (filteredDifferentialCyclePlus K (p + r) r).arrow =
      z ≫ (filteredDifferentialCyclePlus K p r).arrow ≫
        filteredDifferentialUnderlying K),
    filteredDifferentialPageClass K r p z ≫ differential r p =
      filteredDifferentialPageClass K r (p + r) zNext

theorem filteredDifferential_page_differentials_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    Nonempty (FilteredDifferentialPageDifferentials K) := by
  sorry

/-! The associated sequence is graded: its `p`th component is the page
    quotient in filtration degree `p`, and its differential has degree `r`. -/
structure FilteredDifferentialSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) where
  page : ℕ → GradedObject ℤ C
  differential : ∀ r : ℕ,
    page r ⟶ (gradedShift C (r : ℤ)).obj (page r)
  square_zero : ∀ r : ℕ,
    differential r ≫ (gradedShift C (r : ℤ)).map (differential r) = 0
  page_differentials : ∀ r : ℕ, FilteredDifferentialPageDifferentials K
  component_iso : ∀ (r : ℕ) (p : ℤ),
    page r p ≅ filteredDifferentialPage K r p
  differential_compatibility : ∀ (r : ℕ) (p : ℤ),
    differential r p ≫ eqToHom (by
      change page r (r + p) = page r (p + r)
      congr 1 <;> ring) ≫ (component_iso r (p + r)).hom =
      (component_iso r p).hom ≫ (page_differentials r).differential r p
  zero_page : ∀ p : ℤ,
    Nonempty (page 0 p ≅ filteredDifferentialE₀ K p)
  first_page : ∀ p : ℤ,
    Nonempty (page 1 p ≅ filteredDifferentialE₁ K p)

theorem filteredDifferentialAssociatedSpectralSequence_exists
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (_hExact : CountableDirectSumsExact C) (K : FilteredDifferentialObject C) :
    Nonempty (FilteredDifferentialSpectralSequence K) := by
  sorry

noncomputable def filteredDifferentialAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (hExact : CountableDirectSumsExact C) (K : FilteredDifferentialObject C) :
    FilteredDifferentialSpectralSequence K :=
  Classical.choice (filteredDifferentialAssociatedSpectralSequence_exists hExact K)

theorem filteredDifferential_E₀_page
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (filteredDifferentialPage K 0 p ≅ filteredDifferentialE₀ K p) := by
  sorry

theorem filteredDifferential_E₁_page
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (filteredDifferentialPage K 1 p ≅ filteredDifferentialE₁ K p) := by
  sorry

/-! ### The `d₁` boundary description and the induced homology filtration -/

def filteredDifferentialTwoStepSubobjectMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    (K.carrier.filtration.obj (p + 2) : C) ⟶
      (K.carrier.filtration.obj p : C) :=
  Subobject.ofLE (K.carrier.filtration.obj (p + 2))
    (K.carrier.filtration.obj p) (K.carrier.filtration.antitone (by omega))

def filteredDifferentialTwoStepQuotientCarrier
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  cokernel (filteredDifferentialTwoStepSubobjectMap K p)

structure FilteredDifferentialTwoStepQuotientData
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) where
  differential : filteredDifferentialTwoStepQuotientCarrier K p ⟶
    filteredDifferentialTwoStepQuotientCarrier K p
  square_zero : differential ≫ differential = 0
  induced : cokernel.π (filteredDifferentialTwoStepSubobjectMap K p) ≫ differential =
    filteredStepDifferential K p ≫
      cokernel.π (filteredDifferentialTwoStepSubobjectMap K p)

theorem filteredDifferentialTwoStepQuotientData_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (FilteredDifferentialTwoStepQuotientData K p) := by
  sorry

noncomputable def filteredDifferentialTwoStepQuotientData
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    FilteredDifferentialTwoStepQuotientData K p :=
  Classical.choice (filteredDifferentialTwoStepQuotientData_exists K p)

def filteredDifferentialTwoStepQuotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    PlainDifferentialObject C where
  carrier := filteredDifferentialTwoStepQuotientCarrier K p
  d := (filteredDifferentialTwoStepQuotientData K p).differential
  d_squared := (filteredDifferentialTwoStepQuotientData K p).square_zero

theorem filteredDifferentialD1ShortExact_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (PlainDifferentialShortExact
      (filteredGradedDifferentialObject K (p + 1))
      (filteredDifferentialTwoStepQuotient K p)
      (filteredGradedDifferentialObject K p)) := by
  sorry

noncomputable def filteredDifferentialD1ShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    PlainDifferentialShortExact
      (filteredGradedDifferentialObject K (p + 1))
      (filteredDifferentialTwoStepQuotient K p)
      (filteredGradedDifferentialObject K p) :=
  Classical.choice (filteredDifferentialD1ShortExact_exists K p)

def filteredDifferentialD1ShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (filteredDifferentialD1ShortExact K p).f.hom
    (filteredDifferentialD1ShortExact K p).g.hom
    (filteredDifferentialD1ShortExact K p).complex

theorem filteredDifferentialD1_boundary_description
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    (filteredDifferentialD1ShortComplex K p).ShortExact :=
  (filteredDifferentialD1ShortExact K p).exact

def filteredDifferentialUnderlyingObject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) : PlainDifferentialObject C where
  carrier := K.carrier.carrier
  d := filteredDifferentialUnderlying K
  d_squared := by
    sorry

abbrev filteredDifferentialUnderlyingHomology {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) : C :=
  plainDifferentialHomology (filteredDifferentialUnderlyingObject K)

noncomputable def filteredDifferentialHomologyProjection {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) :
    kernel (filteredDifferentialUnderlying K) ⟶
      filteredDifferentialUnderlyingHomology K :=
  cokernel.π (kernel.lift (filteredDifferentialUnderlying K)
    (Abelian.image.ι (filteredDifferentialUnderlying K))
    (Abelian.image_ι_comp_eq_zero
      (filteredDifferentialUnderlyingObject K).d_squared))

noncomputable def filteredDifferentialHomologyCycleObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    C :=
  pullback (kernel.ι (filteredDifferentialUnderlying K))
    (K.carrier.filtration.obj p).arrow

noncomputable def filteredDifferentialHomologyCycleMap {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialHomologyCycleObject K p ⟶
      filteredDifferentialUnderlyingHomology K :=
  pullback.fst (kernel.ι (filteredDifferentialUnderlying K))
      (K.carrier.filtration.obj p).arrow ≫
    filteredDifferentialHomologyProjection K

def filteredDifferentialHomologyTop {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject (filteredDifferentialUnderlyingHomology K) :=
  Subobject.mk (Abelian.image.ι (filteredDifferentialHomologyCycleMap K p))

def filteredDifferentialHomologyBottom {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject (filteredDifferentialUnderlyingHomology K) :=
  filteredDifferentialHomologyTop K (p + 1)

theorem filteredDifferentialHomologyFiltration_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    Nonempty (DecreasingFiltration C (filteredDifferentialUnderlyingHomology K)) := by
  sorry

noncomputable def filteredDifferentialHomologyFiltration {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) :
    DecreasingFiltration C (filteredDifferentialUnderlyingHomology K) where
  obj p := filteredDifferentialHomologyTop K p
  antitone := by
    intro p q hpq
    sorry

def filteredDifferentialHomologyFilteredObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) : FilteredObject C where
  carrier := filteredDifferentialUnderlyingHomology K
  filtration := filteredDifferentialHomologyFiltration K

theorem filteredDifferentialHomology_bottom_le_top
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialHomologyBottom K p ≤ filteredDifferentialHomologyTop K p := by
  sorry

theorem filteredDifferentialHomologyFiltration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    (filteredDifferentialHomologyFilteredObject K).filtration.obj p =
      filteredDifferentialHomologyTop K p := rfl

theorem filteredDifferentialHomologyGradedPiece_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (gradedPiece (filteredDifferentialHomologyFilteredObject K) p ≅
      subquotientObject (filteredDifferentialHomologyBottom K p)
        (filteredDifferentialHomologyTop K p)
        (filteredDifferentialHomology_bottom_le_top K p)) := by
  sorry

/-! ### Limits and convergence -/

def filteredDifferentialLimitBoundary {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : Prop :=
  ∃ B : Subobject K.carrier.carrier,
    (∀ r : ℕ, filteredDifferentialBoundaryPlus K p r ≤ B) ∧
      ∀ B' : Subobject K.carrier.carrier,
        (∀ r : ℕ, filteredDifferentialBoundaryPlus K p r ≤ B') → B ≤ B'

def filteredDifferentialLimitCycle {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : Prop :=
  ∃ Z : Subobject K.carrier.carrier,
    (∀ r : ℕ, Z ≤ filteredDifferentialCyclePlus K p r) ∧
      ∀ Z' : Subobject K.carrier.carrier,
        (∀ r : ℕ, Z' ≤ filteredDifferentialCyclePlus K p r) → Z' ≤ Z

structure FilteredDifferentialLimitData {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) where
  Binf : ∀ _p, Subobject K.carrier.carrier
  Zinf : ∀ _p, Subobject K.carrier.carrier
  Binf_spec : ∀ p, ∀ r, filteredDifferentialBoundaryPlus K p r ≤ Binf p
  Binf_least : ∀ p Y,
    (∀ r, filteredDifferentialBoundaryPlus K p r ≤ Y) → Binf p ≤ Y
  Zinf_spec : ∀ p, ∀ r, Zinf p ≤ filteredDifferentialCyclePlus K p r
  Zinf_greatest : ∀ p Y,
    (∀ r, Y ≤ filteredDifferentialCyclePlus K p r) → Y ≤ Zinf p
  Binf_le_Zinf : ∀ p, Binf p ≤ Zinf p

noncomputable def filteredDifferentialLimitPage {C : Type u}
    [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (L : FilteredDifferentialLimitData K)
    (p : ℤ) : C :=
  subquotientObject (L.Binf p) (L.Zinf p) (L.Binf_le_Zinf p)

def IsSubquotientOf {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} : Prop :=
  ∃ B Z : Subobject Y, ∃ hBZ : B ≤ Z,
    Nonempty (X ≅ subquotientObject B Z hBZ)

def filteredDifferentialLimit_graded_subquotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (L : FilteredDifferentialLimitData K) :
  Prop :=
  ∀ p : ℤ,
    IsSubquotientOf
      (X := gradedPiece (filteredDifferentialHomologyFilteredObject K) p)
      (Y := filteredDifferentialLimitPage K L p)

def filteredDifferentialLimit_graded_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (L : FilteredDifferentialLimitData K) :
  Prop :=
  ∀ p : ℤ,
    Nonempty
      (gradedPiece (filteredDifferentialHomologyFilteredObject K) p ≅
        filteredDifferentialLimitPage K L p)

def filteredDifferentialWeaklyConverges
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) : Prop :=
  ∃ L : FilteredDifferentialLimitData K,
    filteredDifferentialLimit_graded_iso K L

def filteredDifferentialAbuts
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) : Prop :=
  filteredDifferentialWeaklyConverges K ∧
    ∃ hF : HasIntersection (filteredDifferentialHomologyFilteredObject K).filtration,
      ∃ hU : HasUnion (filteredDifferentialHomologyFilteredObject K).filtration,
        intersection hF = ⊥ ∧ union hU = ⊤

theorem filteredDifferentialWeakConvergence_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialWeaklyConverges K ↔
      ∃ L : FilteredDifferentialLimitData K,
        filteredDifferentialLimit_graded_iso K L := Iff.rfl

def filteredDifferentialAbutmentCriterion
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) : Prop :=
  ∃ hF : HasIntersection (filteredDifferentialHomologyFilteredObject K).filtration,
    ∃ hU : HasUnion (filteredDifferentialHomologyFilteredObject K).filtration,
      intersection hF = ⊥ ∧ union hU = ⊤

theorem filteredDifferentialAbutment_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialAbuts K ↔
      filteredDifferentialWeaklyConverges K ∧
        filteredDifferentialAbutmentCriterion K := Iff.rfl

end Formalization.Books.Homology.Unit20
