import Formalization.Books.Homology.Unit20.FilteredDifferentialObjects
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Homological Algebra, Chapter 23: Spectral sequences: filtered differential objects

This file gives the source-facing interfaces for the filtered-differential
object construction.  The filtered objects, their associated graded pieces,
and the categorical subquotient constructions are reused from Chapters 19
and 20; the declarations below record the graded page, boundary, limit, and
convergence statements in the notation of the source.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit16
open Formalization.Books.Homology.Unit19

universe v u

namespace Formalization.Books.Homology.Unit23

/-! ## 23.1 Filtered differential objects -/

/-! ### The filtered differential object and its direct-sum construction -/

/- The canonical definition is the differential-object structure on the
category of filtered objects from the preceding chapters. -/
abbrev FilteredDifferentialObject (C : Type u) [Category.{v} C] [Abelian C] :=
  Formalization.Books.Homology.Unit20.FilteredDifferentialObject C

abbrev FilteredDifferentialObjectHom {C : Type u} [Category.{v} C]
    [Abelian C] (A B : FilteredDifferentialObject C) :=
  Formalization.Books.Homology.Unit20.FilteredDifferentialObjectHom A B

abbrev filteredDifferentialUnderlying {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) :
    K.carrier.carrier ⟶ K.carrier.carrier :=
  Formalization.Books.Homology.Unit20.filteredDifferentialUnderlying K

/-- The source's countable-direct-sum exactness hypothesis. -/
abbrev CountableDirectSumsExact (C : Type u) [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C] : Prop :=
  Formalization.Books.Homology.Unit20.CountableDirectSumsExact C

/- The section's warning that countable direct sums need not be exact is
already packaged by Chapter 16. -/
abbrev NonExactCountableDirectSumsExample :=
  Formalization.Books.Homology.Unit16.NonExactGradedTotalExample

theorem exists_nonExactCountableDirectSumsExample :
    Nonempty (NonExactCountableDirectSumsExample.{u}) := by
  exact Formalization.Books.Homology.Unit16.exists_nonExactGradedTotalExample

/-- The differential induced on the filtration step `Fᵖ K`. -/
abbrev filteredStepDifferential {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    (K.carrier.filtration.obj p : C) ⟶ (K.carrier.filtration.obj p : C) :=
  Formalization.Books.Homology.Unit20.filteredStepDifferential K p

theorem filteredStepDifferential_squared
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredStepDifferential K p ≫ filteredStepDifferential K p = 0 := by
  sorry

def filteredDifferentialStepObject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Formalization.Books.Homology.Unit20.PlainDifferentialObject C where
  carrier := (K.carrier.filtration.obj p : C)
  d := filteredStepDifferential K p
  d_squared := filteredStepDifferential_squared K p

abbrev filteredDifferentialSummands {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) : GradedObject ℤ C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialSummands K

abbrev filteredDifferentialDirectSumCarrier {C : Type u}
    [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) : C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialDirectSumCarrier K

abbrev filteredDifferentialDirectSumMap {C : Type u}
    [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialDirectSumCarrier K ⟶ filteredDifferentialDirectSumCarrier K :=
  Formalization.Books.Homology.Unit20.filteredDifferentialDirectSumMap K

abbrev filteredDifferentialDirectSumObject {C : Type u}
    [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    Formalization.Books.Homology.Unit20.PlainDifferentialObject C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialDirectSumObject K

abbrev filteredDifferentialDirectSumPair {C : Type u}
    [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    Formalization.Books.Homology.Unit16.GradedPair C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialDirectSumPair K

abbrev filteredDifferentialDirectSumAlpha {C : Type u}
    [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialDirectSumCarrier K ⟶ filteredDifferentialDirectSumCarrier K :=
  Formalization.Books.Homology.Unit20.filteredDifferentialDirectSumAlpha K

theorem filteredDifferentialDirectSumAlpha_mono
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    Mono (filteredDifferentialDirectSumAlpha K) := by
  exact Formalization.Books.Homology.Unit20.filteredDifferentialDirectSumAlpha_mono K

abbrev filteredDifferentialDirectSumAlphaHom {C : Type u}
    [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    Formalization.Books.Homology.Unit20.PlainDifferentialObjectHom
      (filteredDifferentialDirectSumObject K)
      (filteredDifferentialDirectSumObject K) :=
  Formalization.Books.Homology.Unit20.filteredDifferentialDirectSumAlphaHom K

abbrev filteredDifferentialDirectSumInjectiveSelfMap {C : Type u}
    [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : FilteredDifferentialObject C) :
    Formalization.Books.Homology.Unit20.PlainDifferentialInjectiveEndomorphism
      (filteredDifferentialDirectSumObject K) :=
  Formalization.Books.Homology.Unit20.filteredDifferentialDirectSumInjectiveSelfMap K

theorem filteredDifferential_associated_spectral_sequence_exists
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (hExact : CountableDirectSumsExact C) (K : FilteredDifferentialObject C) :
    Nonempty (Formalization.Books.Homology.Unit20.PlainSpectralSequence C 0) := by
  sorry

noncomputable def filteredDifferential_associated_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (hExact : CountableDirectSumsExact C) (K : FilteredDifferentialObject C) :
    Formalization.Books.Homology.Unit20.PlainSpectralSequence C 0 :=
  Classical.choice (filteredDifferential_associated_spectral_sequence_exists hExact K)

/-! ### The associated graded object and the first two pages -/

/-- The graded object `gr(K)`. -/
def filteredDifferentialAssociatedGraded {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) : GradedObject ℤ C :=
  (associatedGraded (C := C)).obj K.carrier

/-- The graded map `gr(d)`. -/
def filteredDifferentialAssociatedGradedMap {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) :
    filteredDifferentialAssociatedGraded K ⟶ filteredDifferentialAssociatedGraded K :=
  (associatedGraded (C := C)).map K.d

theorem filteredDifferentialAssociatedGradedMap_squared
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialAssociatedGradedMap K ≫
        filteredDifferentialAssociatedGradedMap K = 0 := by
  sorry

/-- The differential object `(gr(K), gr(d))`. -/
def filteredDifferentialAssociatedGradedObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) :
    Formalization.Books.Homology.Unit20.PlainDifferentialObject (GradedObject ℤ C) where
  carrier := filteredDifferentialAssociatedGraded K
  d := filteredDifferentialAssociatedGradedMap K
  d_squared := filteredDifferentialAssociatedGradedMap_squared K

abbrev filteredGradedDifferentialObject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Formalization.Books.Homology.Unit20.PlainDifferentialObject C :=
  Formalization.Books.Homology.Unit20.filteredGradedDifferentialObject K p

abbrev filteredDifferentialE₀ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialE₀ K p

abbrev filteredDifferentialD₀ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialE₀ K p ⟶ filteredDifferentialE₀ K p :=
  Formalization.Books.Homology.Unit20.filteredDifferentialD₀ K p

abbrev filteredDifferentialE₁ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialE₁ K p

def filteredDifferentialE₀Object {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) : GradedObject ℤ C :=
  filteredDifferentialAssociatedGraded K

def filteredDifferentialD₀Object {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) :
    filteredDifferentialE₀Object K ⟶ filteredDifferentialE₀Object K :=
  filteredDifferentialAssociatedGradedMap K

def filteredDifferentialE₁Object {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) : GradedObject ℤ C :=
  fun p => filteredDifferentialE₁ K p

theorem filteredDifferential_E₀_component
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialE₀Object K p = gradedPiece K.carrier p := rfl

theorem filteredDifferential_E₁_component
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialE₁Object K p =
      Formalization.Books.Homology.Unit20.plainDifferentialHomology
        (filteredGradedDifferentialObject K p) := rfl

theorem filteredDifferential_D₀_component
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    (filteredDifferentialD₀Object K) p = filteredDifferentialD₀ K p := rfl

/-! ### The `Zᵣ`, `Bᵣ`, page, and differential formulae -/

abbrev filteredDifferentialZCore {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) :
    Subobject K.carrier.carrier :=
  Formalization.Books.Homology.Unit20.filteredDifferentialCycleCore K p r

abbrev filteredDifferentialBCore {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) :
    Subobject K.carrier.carrier :=
  Formalization.Books.Homology.Unit20.filteredDifferentialBoundaryCore K p r

abbrev filteredDifferentialZPlus {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) :
    Subobject K.carrier.carrier :=
  Formalization.Books.Homology.Unit20.filteredDifferentialCyclePlus K p r

abbrev filteredDifferentialBPlus {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) :
    Subobject K.carrier.carrier :=
  Formalization.Books.Homology.Unit20.filteredDifferentialBoundaryPlus K p r

noncomputable def filteredDifferentialZ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (K.carrier.filtration.obj (p + 1)) (filteredDifferentialZPlus K r p)
    (show K.carrier.filtration.obj (p + 1) ≤ filteredDifferentialZPlus K r p
      from le_sup_right)

noncomputable def filteredDifferentialB {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (K.carrier.filtration.obj (p + 1)) (filteredDifferentialBPlus K r p)
    (show K.carrier.filtration.obj (p + 1) ≤ filteredDifferentialBPlus K r p
      from le_sup_right)

/- The source also regards `Bᵣ` and `Zᵣ` as graded subobjects of `E₀`.
The component fields below record that assertion without replacing the
canonical categorical page object. -/
structure FilteredDifferentialPageSubobjectData {C : Type u}
    [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (r : ℕ) where
  B : Subobject (filteredDifferentialE₀Object K)
  Z : Subobject (filteredDifferentialE₀Object K)
  B_le_Z : B ≤ Z
  B_component : ∀ p : ℤ,
    Nonempty ((B : GradedObject ℤ C) p ≅ filteredDifferentialB K r p)
  Z_component : ∀ p : ℤ,
    Nonempty ((Z : GradedObject ℤ C) p ≅ filteredDifferentialZ K r p)

theorem filteredDifferential_page_subobjects_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (r : ℕ) :
    Nonempty (FilteredDifferentialPageSubobjectData K r) := by
  sorry

abbrev filteredDifferentialPage {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialPage K r p

theorem filteredDifferential_boundary_le_cycle
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) :
    filteredDifferentialBPlus K r p ≤ filteredDifferentialZPlus K r p := by
  exact Formalization.Books.Homology.Unit20.filteredDifferential_boundary_le_cycle K p r

theorem filteredDifferential_page_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) :
    filteredDifferentialPage K r p =
      Formalization.Books.Homology.Unit20.subquotientObject
        (filteredDifferentialBPlus K r p) (filteredDifferentialZPlus K r p)
        (filteredDifferential_boundary_le_cycle K r p) := rfl

abbrev FilteredDifferentialPageDifferentials {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) :=
  Formalization.Books.Homology.Unit20.FilteredDifferentialPageDifferentials K

theorem filteredDifferential_page_differentials_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    Nonempty (FilteredDifferentialPageDifferentials K) := by
  exact Formalization.Books.Homology.Unit20.filteredDifferential_page_differentials_exists K

noncomputable def filteredDifferentialPageDifferentials
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) : FilteredDifferentialPageDifferentials K :=
  Classical.choice (filteredDifferential_page_differentials_exists K)

abbrev filteredDifferentialD {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) :
    filteredDifferentialPage K r p ⟶ filteredDifferentialPage K r (p + r) :=
  (filteredDifferentialPageDifferentials K).differential r p

theorem filteredDifferentialD_squared
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) :
    filteredDifferentialD K r p ≫ filteredDifferentialD K r (p + r) = 0 := by
  exact (filteredDifferentialPageDifferentials K).square_zero r p

theorem filteredDifferentialD_lift_rule
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (r : ℕ) (p : ℤ) {T : C}
    (z : T ⟶ (filteredDifferentialZPlus K r p : C))
    (zNext : T ⟶ (filteredDifferentialZPlus K r (p + r) : C))
    (hz : zNext ≫ (filteredDifferentialZPlus K r (p + r)).arrow =
      z ≫ (filteredDifferentialZPlus K r p).arrow ≫ filteredDifferentialUnderlying K) :
    Formalization.Books.Homology.Unit20.filteredDifferentialPageClass K r p z ≫
        filteredDifferentialD K r p =
      Formalization.Books.Homology.Unit20.filteredDifferentialPageClass K r (p + r) zNext := by
  exact (filteredDifferentialPageDifferentials K).lift_rule r p z zNext hz

theorem filteredDifferential_E₀_page
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (filteredDifferentialPage K 0 p ≅ filteredDifferentialE₀ K p) := by
  exact Formalization.Books.Homology.Unit20.filteredDifferential_E₀_page K p

theorem filteredDifferential_E₁_page
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (filteredDifferentialPage K 1 p ≅ filteredDifferentialE₁ K p) := by
  exact Formalization.Books.Homology.Unit20.filteredDifferential_E₁_page K p

/-! ### The graded spectral-sequence interface -/

abbrev filteredDifferentialGradedShiftEquivalence (C : Type u)
    [Category.{v} C] [Abelian C] (r : ℤ) :
    GradedObject ℤ C ≌ GradedObject ℤ C :=
  GradedObject.comapEquiv C (Equiv.addLeft (-r))

def filteredDifferentialGradedShiftObjectIso (C : Type u)
    [Category.{v} C] [Abelian C] (r : ℤ) (A : GradedObject ℤ C) :
    (gradedShift C r).obj A ≅
      (filteredDifferentialGradedShiftEquivalence C r).functor.obj A :=
  (GradedObject.comapEq C (by
    ext p
    simp)).app A

abbrev filteredDifferentialGradedShiftSquareZero (C : Type u)
    [Category.{v} C] [Abelian C] (r : ℤ) {A : GradedObject ℤ C}
    (d' : A ⟶ (filteredDifferentialGradedShiftEquivalence C r).functor.obj A) : Prop :=
  d' ≫ (filteredDifferentialGradedShiftEquivalence C r).functor.map d' =
    @OfNat.ofNat
      (A ⟶ (filteredDifferentialGradedShiftEquivalence C r).functor.obj
        ((filteredDifferentialGradedShiftEquivalence C r).functor.obj A)) 0
      (@Zero.toOfNat0
        (A ⟶ (filteredDifferentialGradedShiftEquivalence C r).functor.obj
          ((filteredDifferentialGradedShiftEquivalence C r).functor.obj A))
        (@HasZeroMorphisms.zero (GradedObject ℤ C)
          (GradedObject.categoryOfGradedObjects ℤ)
          Preadditive.preadditiveHasZeroMorphisms A
          ((filteredDifferentialGradedShiftEquivalence C r).functor.obj
            ((filteredDifferentialGradedShiftEquivalence C r).functor.obj A))))

/-- A filtered-differential spectral sequence with the source's degree-
`r` differential convention.  The component page is identified with the
categorical `Zᵣ/Bᵣ` page above. -/
structure FilteredDifferentialSpectralSequence {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) where
  page : ℕ → GradedObject ℤ C
  differential : ∀ r : ℕ,
    page r ⟶ (gradedShift C (r : ℤ)).obj (page r)
  square_zero : ∀ r : ℕ,
    differential r ≫ (gradedShift C (r : ℤ)).map (differential r) = 0
  next_page : ∀ r : ℕ,
    ∃ d' : page r ⟶
        (filteredDifferentialGradedShiftEquivalence C (r : ℤ)).functor.obj (page r),
      d' = differential r ≫
        (filteredDifferentialGradedShiftObjectIso C (r : ℤ) (page r)).hom ∧
        ∃ hd' : filteredDifferentialGradedShiftSquareZero C (r : ℤ) d',
          Nonempty (Formalization.Books.Homology.Unit20.translatedDifferentialHomology
            (filteredDifferentialGradedShiftEquivalence C (r : ℤ)) d'
            (by simpa only [filteredDifferentialGradedShiftSquareZero] using hd') ≅
              page (r + 1))
  page_differentials : FilteredDifferentialPageDifferentials K
  component_iso : ∀ (r : ℕ) (p : ℤ),
    Nonempty (page r p ≅ filteredDifferentialPage K r p)
  component_differential_compatibility : ∀ (r : ℕ) (p : ℤ),
    ∃ e₀ : page r p ≅ filteredDifferentialPage K r p,
      ∃ e₁ : page r (r + p) ≅ filteredDifferentialPage K r (p + r),
        e₀.hom ≫ filteredDifferentialD K r p =
          differential r p ≫ e₁.hom
  zero_page : ∀ p : ℤ,
    Nonempty (page 0 p ≅ filteredDifferentialE₀ K p)
  first_page : ∀ p : ℤ,
    Nonempty (page 1 p ≅ filteredDifferentialE₁ K p)

theorem filteredDifferential_spectral_sequence_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    Nonempty (FilteredDifferentialSpectralSequence K) := by
  sorry

noncomputable def filteredDifferentialSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    FilteredDifferentialSpectralSequence K :=
  Classical.choice (filteredDifferential_spectral_sequence_exists K)

/-! ### The `d₁` boundary map -/

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
    Formalization.Books.Homology.Unit20.PlainDifferentialObject C where
  carrier := filteredDifferentialTwoStepQuotientCarrier K p
  d := (filteredDifferentialTwoStepQuotientData K p).differential
  d_squared := (filteredDifferentialTwoStepQuotientData K p).square_zero

theorem filteredDifferentialD1ShortExact_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (Formalization.Books.Homology.Unit20.PlainDifferentialShortExact
      (filteredGradedDifferentialObject K (p + 1))
      (filteredDifferentialTwoStepQuotient K p)
      (filteredGradedDifferentialObject K p)) := by
  sorry

noncomputable def filteredDifferentialD1ShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Formalization.Books.Homology.Unit20.PlainDifferentialShortExact
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

theorem filteredDifferentialD1ShortComplex_short_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    (filteredDifferentialD1ShortComplex K p).ShortExact :=
  (filteredDifferentialD1ShortExact K p).exact

theorem filteredDifferentialD1_homology_long_exact_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (Formalization.Books.Homology.Unit20.LongExactSequence
      (Formalization.Books.Homology.Unit20.differentialHomologyLongTerm
        (filteredGradedDifferentialObject K (p + 1))
        (filteredDifferentialTwoStepQuotient K p)
        (filteredGradedDifferentialObject K p))) := by
  exact Formalization.Books.Homology.Unit20.plainDifferentialShortExact_homology_long_exact
    (filteredDifferentialD1ShortExact K p)

structure FilteredDifferentialD1BoundaryData
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) where
  long_exact : Formalization.Books.Homology.Unit20.LongExactSequence
    (Formalization.Books.Homology.Unit20.differentialHomologyLongTerm
      (filteredGradedDifferentialObject K (p + 1))
      (filteredDifferentialTwoStepQuotient K p)
      (filteredGradedDifferentialObject K p))
  d₁ : filteredDifferentialE₁ K p ⟶ filteredDifferentialE₁ K (p + 1)
  boundary : filteredDifferentialE₁ K p ⟶ filteredDifferentialE₁ K (p + 1)
  boundary_is_long_exact_component :
    ∃ e₀ : Formalization.Books.Homology.Unit20.differentialHomologyLongTerm
        (filteredGradedDifferentialObject K (p + 1))
        (filteredDifferentialTwoStepQuotient K p)
        (filteredGradedDifferentialObject K p) 0 ≅ filteredDifferentialE₁ K p,
      ∃ e₁ : Formalization.Books.Homology.Unit20.differentialHomologyLongTerm
        (filteredGradedDifferentialObject K (p + 1))
        (filteredDifferentialTwoStepQuotient K p)
        (filteredGradedDifferentialObject K p) 1 ≅ filteredDifferentialE₁ K (p + 1),
        boundary = e₀.inv ≫ long_exact.differential 0 ≫ e₁.hom
  page_differential_is_d₁ :
    ∃ e₀ : filteredDifferentialPage K 1 p ≅ filteredDifferentialE₁ K p,
      ∃ e₁ : filteredDifferentialPage K 1 (p + 1) ≅
        filteredDifferentialE₁ K (p + 1),
        filteredDifferentialD K 1 p ≫ e₁.hom = e₀.hom ≫ d₁
  d₁_is_boundary : d₁ = boundary

theorem filteredDifferential_d1_boundary_data_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (FilteredDifferentialD1BoundaryData K p) := by
  sorry

/-! ### The induced filtration on homology -/

abbrev filteredDifferentialUnderlyingObject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) :
    Formalization.Books.Homology.Unit20.PlainDifferentialObject C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialUnderlyingObject K

abbrev filteredDifferentialUnderlyingHomology {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) : C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialUnderlyingHomology K

abbrev filteredDifferentialHomologyTop {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject (filteredDifferentialUnderlyingHomology K) :=
  Formalization.Books.Homology.Unit20.filteredDifferentialHomologyTop K p

abbrev filteredDifferentialHomologyBottom {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject (filteredDifferentialUnderlyingHomology K) :=
  Formalization.Books.Homology.Unit20.filteredDifferentialHomologyBottom K p

abbrev filteredDifferentialHomologyCycleObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialHomologyCycleObject K p

abbrev filteredDifferentialHomologyCycleMap {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialHomologyCycleObject K p ⟶
      filteredDifferentialUnderlyingHomology K :=
  Formalization.Books.Homology.Unit20.filteredDifferentialHomologyCycleMap K p

abbrev filteredDifferentialHomologyFilteredObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) :
    FilteredObject C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialHomologyFilteredObject K

theorem filteredDifferential_induced_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    (filteredDifferentialHomologyFilteredObject K).filtration.obj p =
      filteredDifferentialHomologyTop K p := rfl

def filteredDifferentialKernelSubobject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) :
    Subobject K.carrier.carrier :=
  Subobject.mk (kernel.ι (filteredDifferentialUnderlying K))

def filteredDifferentialImageSubobject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) :
    Subobject K.carrier.carrier :=
  Subobject.mk (Abelian.image.ι (filteredDifferentialUnderlying K))

def filteredDifferentialHomologyNumerator {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject K.carrier.carrier :=
    (filteredDifferentialKernelSubobject K ⊓ K.carrier.filtration.obj p) ⊔
    filteredDifferentialImageSubobject K

def filteredDifferentialHomologyKernelPiece {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject K.carrier.carrier :=
  filteredDifferentialKernelSubobject K ⊓ K.carrier.filtration.obj p

def filteredDifferentialHomologyDenominatorSecond {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject K.carrier.carrier :=
  (filteredDifferentialKernelSubobject K ⊓ K.carrier.filtration.obj (p + 1)) ⊔
    (filteredDifferentialImageSubobject K ⊓ K.carrier.filtration.obj p)

theorem filteredDifferential_homology_numerator_antitone
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) {p q : ℤ} (hpq : p ≤ q) :
    filteredDifferentialHomologyNumerator K q ≤
      filteredDifferentialHomologyNumerator K p := by
  exact sup_le_sup
    (inf_le_inf_left _ (K.carrier.filtration.antitone hpq)) le_rfl

theorem filteredDifferential_homology_denominator_second_le_numerator
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialHomologyDenominatorSecond K p ≤
      filteredDifferentialHomologyNumerator K p := by
  exact sup_le_sup
    (inf_le_inf_left _ (K.carrier.filtration.antitone (by omega)))
    (inf_le_left)

theorem filteredDifferential_image_le_homology_numerator
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialImageSubobject K ≤ filteredDifferentialHomologyNumerator K p := by
  exact le_sup_right

theorem filteredDifferential_homology_denominator_second_le_kernel_piece
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    filteredDifferentialHomologyDenominatorSecond K p ≤
      filteredDifferentialHomologyKernelPiece K p := by
  sorry

noncomputable def filteredDifferentialHomologyFiltrationFormulaObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (filteredDifferentialImageSubobject K)
    (filteredDifferentialHomologyNumerator K p)
    (filteredDifferential_image_le_homology_numerator K p)

theorem filteredDifferential_homology_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (((filteredDifferentialHomologyFilteredObject K).filtration.obj p : C) ≅
      filteredDifferentialHomologyFiltrationFormulaObject K p) := by
  sorry

noncomputable def filteredDifferentialHomologyGradedFormulaObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (filteredDifferentialHomologyNumerator K (p + 1))
    (filteredDifferentialHomologyNumerator K p)
    (filteredDifferential_homology_numerator_antitone K (by omega))

noncomputable def filteredDifferentialHomologyGradedFormulaObjectSecond
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (filteredDifferentialHomologyDenominatorSecond K p)
    (filteredDifferentialHomologyKernelPiece K p)
    (filteredDifferential_homology_denominator_second_le_kernel_piece K p)

theorem filteredDifferential_homology_graded_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (gradedPiece (filteredDifferentialHomologyFilteredObject K) p ≅
      filteredDifferentialHomologyGradedFormulaObject K p) := by
  sorry

theorem filteredDifferential_homology_graded_formula_second
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Nonempty (gradedPiece (filteredDifferentialHomologyFilteredObject K) p ≅
      filteredDifferentialHomologyGradedFormulaObjectSecond K p) := by
  sorry

/-! ### Limits and convergence -/

abbrev FilteredDifferentialLimitData {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) :=
  Formalization.Books.Homology.Unit20.FilteredDifferentialLimitData K

abbrev filteredDifferentialLimitBoundary {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : Prop :=
  Formalization.Books.Homology.Unit20.filteredDifferentialLimitBoundary K p

abbrev filteredDifferentialLimitCycle {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C) (p : ℤ) : Prop :=
  Formalization.Books.Homology.Unit20.filteredDifferentialLimitCycle K p

abbrev filteredDifferentialLimitPage {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredDifferentialObject C)
    (L : FilteredDifferentialLimitData K) (p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredDifferentialLimitPage K L p

noncomputable def filteredDifferentialBoundaryInfinity
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hB : filteredDifferentialLimitBoundary K p) :
    Subobject K.carrier.carrier :=
  Classical.choose hB

theorem filteredDifferentialBoundaryInfinity_upper
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hB : filteredDifferentialLimitBoundary K p) (r : ℕ) :
    filteredDifferentialBPlus K r p ≤ filteredDifferentialBoundaryInfinity K p hB :=
  (Classical.choose_spec hB).1 r

theorem filteredDifferentialBoundaryInfinity_least
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hB : filteredDifferentialLimitBoundary K p)
    (B' : Subobject K.carrier.carrier)
    (hB' : ∀ r : ℕ, filteredDifferentialBPlus K r p ≤ B') :
    filteredDifferentialBoundaryInfinity K p hB ≤ B' :=
  (Classical.choose_spec hB).2 B' hB'

noncomputable def filteredDifferentialCycleInfinity
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hZ : filteredDifferentialLimitCycle K p) :
    Subobject K.carrier.carrier :=
  Classical.choose hZ

theorem filteredDifferentialCycleInfinity_lower
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hZ : filteredDifferentialLimitCycle K p) (r : ℕ) :
    filteredDifferentialCycleInfinity K p hZ ≤ filteredDifferentialZPlus K r p :=
  (Classical.choose_spec hZ).1 r

theorem filteredDifferentialCycleInfinity_greatest
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hZ : filteredDifferentialLimitCycle K p)
    (Z' : Subobject K.carrier.carrier)
    (hZ' : ∀ r : ℕ, Z' ≤ filteredDifferentialZPlus K r p) :
    Z' ≤ filteredDifferentialCycleInfinity K p hZ :=
  (Classical.choose_spec hZ).2 Z' hZ'

noncomputable def filteredDifferentialBoundaryInfinityPiece
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hB : filteredDifferentialLimitBoundary K p) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (K.carrier.filtration.obj (p + 1))
    (filteredDifferentialBoundaryInfinity K p hB)
    (le_trans le_sup_right (filteredDifferentialBoundaryInfinity_upper K p hB 0))

noncomputable def filteredDifferentialCycleInfinityPiece
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hZ : filteredDifferentialLimitCycle K p) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (K.carrier.filtration.obj (p + 1))
    (filteredDifferentialCycleInfinity K p hZ)
    (filteredDifferentialCycleInfinity_greatest K p hZ _
      (fun _ => le_sup_right))

theorem filteredDifferentialBoundaryInfinity_le_cycleInfinity
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hB : filteredDifferentialLimitBoundary K p)
    (hZ : filteredDifferentialLimitCycle K p) :
    filteredDifferentialBoundaryInfinity K p hB ≤
      filteredDifferentialCycleInfinity K p hZ := by
  sorry

noncomputable def filteredDifferentialLimitPageFromExtrema
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hB : filteredDifferentialLimitBoundary K p)
    (hZ : filteredDifferentialLimitCycle K p) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (filteredDifferentialBoundaryInfinity K p hB)
    (filteredDifferentialCycleInfinity K p hZ)
    (filteredDifferentialBoundaryInfinity_le_cycleInfinity K p hB hZ)

def filteredDifferentialLimitGradedObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C)
    (L : FilteredDifferentialLimitData K) : GradedObject ℤ C :=
  fun p => filteredDifferentialLimitPage K L p

def filteredDifferentialAssociatedGradedHomology {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredDifferentialObject C) :
    GradedObject ℤ C :=
  (associatedGraded (C := C)).obj (filteredDifferentialHomologyFilteredObject K)

def GradedSubquotientOf {C : Type u} [Category.{v} C] [Abelian C]
    (X Y : GradedObject ℤ C) : Prop :=
  ∀ p : ℤ, Formalization.Books.Homology.Unit20.IsSubquotientOf
    (X := X p) (Y := Y p)

theorem filteredDifferential_limit_data_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C)
    (hB : ∀ p, filteredDifferentialLimitBoundary K p)
    (hZ : ∀ p, filteredDifferentialLimitCycle K p) :
    Nonempty (FilteredDifferentialLimitData K) := by
  sorry

theorem filteredDifferential_limit_graded_homology_subquotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (L : FilteredDifferentialLimitData K) :
    GradedSubquotientOf (filteredDifferentialAssociatedGradedHomology K)
      (filteredDifferentialLimitGradedObject K L) := by
  sorry

theorem filteredDifferential_limit_component_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (L : FilteredDifferentialLimitData K)
    (p : ℤ) :
    filteredDifferentialLimitGradedObject K L p =
      filteredDifferentialLimitPage K L p := rfl

def filteredDifferentialCycleLimitRepresentative
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject K.carrier.carrier :=
  (filteredDifferentialKernelSubobject K ⊓ K.carrier.filtration.obj p) ⊔
    K.carrier.filtration.obj (p + 1)

def filteredDifferentialBoundaryLimitRepresentative
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ) :
    Subobject K.carrier.carrier :=
  (filteredDifferentialImageSubobject K ⊓ K.carrier.filtration.obj p) ⊔
    K.carrier.filtration.obj (p + 1)

theorem filteredDifferential_limit_top_inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hZ : filteredDifferentialLimitCycle K p) :
    filteredDifferentialCycleLimitRepresentative K p ≤
      filteredDifferentialCycleInfinity K p hZ := by
  sorry

theorem filteredDifferential_limit_bottom_inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (p : ℤ)
    (hB : filteredDifferentialLimitBoundary K p) :
    filteredDifferentialBoundaryInfinity K p hB ≤
      filteredDifferentialBoundaryLimitRepresentative K p := by
  sorry

def FilteredDifferentialLimitEquationsHold
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (L : FilteredDifferentialLimitData K) : Prop :=
  ∀ p : ℤ,
    L.Binf p = filteredDifferentialBoundaryLimitRepresentative K p ∧
      L.Zinf p = filteredDifferentialCycleLimitRepresentative K p

def filteredDifferentialWeaklyConverges
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) : Prop :=
  ∃ L : FilteredDifferentialLimitData K,
    Nonempty (filteredDifferentialAssociatedGradedHomology K ≅
      filteredDifferentialLimitGradedObject K L)

def filteredDifferentialAbuts
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) : Prop :=
  filteredDifferentialWeaklyConverges K ∧
    ∃ hF : HasIntersection (filteredDifferentialHomologyFilteredObject K).filtration,
      ∃ hU : HasUnion (filteredDifferentialHomologyFilteredObject K).filtration,
        intersection hF = ⊥ ∧ union hU = ⊤

theorem filteredDifferential_weak_convergence_iff_limit_equations
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) (L : FilteredDifferentialLimitData K) :
    Nonempty (filteredDifferentialAssociatedGradedHomology K ≅
      filteredDifferentialLimitGradedObject K L) ↔
      FilteredDifferentialLimitEquationsHold K L := by
  sorry

theorem filteredDifferential_weak_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialWeaklyConverges K ↔
      ∃ L : FilteredDifferentialLimitData K,
        FilteredDifferentialLimitEquationsHold K L := by
  sorry

def filteredDifferentialKernelImageFiltration
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    DecreasingFiltration C K.carrier.carrier where
  obj p :=
    (filteredDifferentialKernelSubobject K ⊓ K.carrier.filtration.obj p) ⊔
      filteredDifferentialImageSubobject K
  antitone := by
    intro p q hpq
    exact sup_le_sup
      (inf_le_inf_left _ (K.carrier.filtration.antitone hpq)) le_rfl

def filteredDifferentialAbutmentCriterion
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) : Prop :=
  ∃ hF : HasIntersection (filteredDifferentialKernelImageFiltration K),
    ∃ hU : HasUnion (filteredDifferentialKernelImageFiltration K),
      intersection hF = filteredDifferentialImageSubobject K ∧
        union hU = filteredDifferentialKernelSubobject K

theorem filteredDifferential_abutment_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredDifferentialObject C) :
    filteredDifferentialAbuts K ↔
      filteredDifferentialWeaklyConverges K ∧
        filteredDifferentialAbutmentCriterion K := by
  sorry

end Formalization.Books.Homology.Unit23
