import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Formalization.Books.Homology.Unit20.FilteredComplexes
import Formalization.Books.Trace.Unit06.DerivedCategories

/-!
# The Trace Formula, Chapter 8: filtered derived functors

The filtered-object and filtered-complex constructions are supplied by the
Homology book.  The source's filtered derived category is not a canonical
Mathlib construction, so the data below records the categories, comparison
equivalences, localizations, and graded/forgetful functors used by the source.
This makes the two displayed diagrams and the spectral-sequence assertion
usable without introducing a competing derived-category implementation.
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit19
open Formalization.Books.Trace.Unit06

universe u v u' v' w w' x y

namespace Formalization.Books.Trace.Unit08

/-! ## The finite filtered objects used by the source -/

/-- The source's `Fil^f(A)`: filtered objects with a finite filtration. -/
def finiteFilteredProperty {A : Type u} [Category.{v} A] [Abelian A] :
    ObjectProperty (FilteredObject A) :=
  fun F => F.IsFinite

abbrev FiniteFilteredObject {A : Type u} [Category.{v} A] [Abelian A] :=
  (finiteFilteredProperty (A := A)).FullSubcategory

/-- Filtered injective objects, restricted to finite filtrations. -/
def filteredInjectiveProperty {A : Type u} [Category.{v} A] [Abelian A] :
    ObjectProperty (FilteredObject A) :=
  fun F => F.IsFinite ∧ Injective F

abbrev FilteredInjectiveObject {A : Type u} [Category.{v} A] [Abelian A] :=
  (filteredInjectiveProperty (A := A)).FullSubcategory

/-- Filtered projective objects, restricted to finite filtrations. -/
def filteredProjectiveProperty {A : Type u} [Category.{v} A] [Abelian A] :
    ObjectProperty (FilteredObject A) :=
  fun F => F.IsFinite ∧ Projective F

abbrev FilteredProjectiveObject {A : Type u} [Category.{v} A] [Abelian A] :=
  (filteredProjectiveProperty (A := A)).FullSubcategory

/-! ## The filtered derived-category interface -/

/--
The category-level data used for `DF⁺(A)` and `DF⁻(A)`.

The fields `plus_equivalence` and `minus_equivalence` formalize the preceding
identifications with homotopy categories of filtered injectives and
projectives.  The `filtered_plus` and `filtered_minus` categories are the
categories denoted `K⁺(Fil^f(A))` and `K⁻(Fil^f(A))` in the source, while the
two localization functors formalize the upward arrows in its diagrams.
-/
structure FilteredDerivedCategoryData
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] where
  plus : Type x
  plus_category : Category.{y} plus
  minus : Type x
  minus_category : Category.{y} minus
  injective_plus : Type x
  injective_plus_category : Category.{y} injective_plus
  projective_minus : Type x
  projective_minus_category : Category.{y} projective_minus
  filtered_plus : Type x
  filtered_plus_category : Category.{y} filtered_plus
  filtered_minus : Type x
  filtered_minus_category : Category.{y} filtered_minus
  plus_equivalence :
    @CategoryTheory.Equivalence plus injective_plus plus_category
      injective_plus_category
  minus_equivalence :
    @CategoryTheory.Equivalence minus projective_minus minus_category
      projective_minus_category
  localization_plus :
    @CategoryTheory.Functor filtered_plus filtered_plus_category plus plus_category
  localization_minus :
    @CategoryTheory.Functor filtered_minus filtered_minus_category minus minus_category
  graded_plus :
    ℤ → @CategoryTheory.Functor plus plus_category (DPlus A) inferInstance
  forget_plus :
    @CategoryTheory.Functor plus plus_category (DPlus A) inferInstance

instance filteredDerivedPlusCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) : Category.{y} d.plus :=
  d.plus_category

instance filteredDerivedMinusCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) : Category.{y} d.minus :=
  d.minus_category

instance filteredDerivedInjectivePlusCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) : Category.{y} d.injective_plus :=
  d.injective_plus_category

instance filteredDerivedProjectiveMinusCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) : Category.{y} d.projective_minus :=
  d.projective_minus_category

instance filteredDerivedFilteredPlusCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) : Category.{y} d.filtered_plus :=
  d.filtered_plus_category

instance filteredDerivedFilteredMinusCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) : Category.{y} d.filtered_minus :=
  d.filtered_minus_category

abbrev DFPlus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) := d.plus

abbrev DFMinus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) := d.minus

abbrev KPlusFilteredInjectives
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) :=
  d.injective_plus

abbrev KMinusFilteredProjectives
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) :=
  d.projective_minus

abbrev KPlusFilteredObjects
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) :=
  d.filtered_plus

abbrev KMinusFilteredObjects
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (d : FilteredDerivedCategoryData A) :=
  d.filtered_minus

/-! ## Filtered right-derived functors -/

/-- Data expressing the first displayed diagram in the source. -/
structure FilteredRightDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) where
  filtered_functor :
    @CategoryTheory.Functor dA.injective_plus dA.injective_plus_category
      dB.filtered_plus dB.filtered_plus_category
  functor :
    @CategoryTheory.Functor dA.plus dA.plus_category dB.plus dB.plus_category
  comparison :
    filtered_functor ⋙ dB.localization_plus ≅
      dA.plus_equivalence.inverse ⋙ functor

/-- The well-definedness assertion for the filtered right-derived functor. -/
theorem filteredRightDerivedFunctorData_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) :
    Nonempty (FilteredRightDerivedFunctorData T hT dA dB) := by
  sorry

noncomputable def filteredRightDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) :
    FilteredRightDerivedFunctorData T hT dA dB :=
  Classical.choice (filteredRightDerivedFunctorData_exists T hT dA dB)

/-- The filtered derived functor `RT : DF⁺(A) ⥤ DF⁺(B)`. -/
noncomputable def filteredRightDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) :
    @CategoryTheory.Functor dA.plus dA.plus_category dB.plus dB.plus_category :=
  (filteredRightDerivedFunctorData T hT dA dB).functor

/-- The comparison isomorphism recording the defining diagram for `RT`. -/
noncomputable def filteredRightDerivedFunctor_comparison
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) :
    (filteredRightDerivedFunctorData T hT dA dB).filtered_functor ⋙
        dB.localization_plus ≅
      dA.plus_equivalence.inverse ⋙
        filteredRightDerivedFunctor T hT dA dB :=
  (filteredRightDerivedFunctorData T hT dA dB).comparison

/-! ## Filtered left-derived functors -/

/-- Data expressing the second displayed diagram in the source. -/
structure FilteredLeftDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (G : A ⥤ B) (hG : IsRightExact G)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) where
  filtered_functor :
    @CategoryTheory.Functor dA.projective_minus dA.projective_minus_category
      dB.filtered_minus dB.filtered_minus_category
  functor :
    @CategoryTheory.Functor dA.minus dA.minus_category dB.minus dB.minus_category
  comparison :
    filtered_functor ⋙ dB.localization_minus ≅
      dA.minus_equivalence.inverse ⋙ functor

/-- The well-definedness assertion for the filtered left-derived functor. -/
theorem filteredLeftDerivedFunctorData_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) :
    Nonempty (FilteredLeftDerivedFunctorData G hG dA dB) := by
  sorry

noncomputable def filteredLeftDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) :
    FilteredLeftDerivedFunctorData G hG dA dB :=
  Classical.choice (filteredLeftDerivedFunctorData_exists G hG dA dB)

/-- The filtered derived functor `LG : DF⁻(A) ⥤ DF⁻(B)`. -/
noncomputable def filteredLeftDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type v} [Category.{w} B] [Abelian B]
    [HasDerivedCategory.{x} A] [HasDerivedCategory.{y} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) :
    @CategoryTheory.Functor dA.minus dA.minus_category dB.minus dB.minus_category :=
  (filteredLeftDerivedFunctorData G hG dA dB).functor

/-- The comparison isomorphism recording the defining diagram for `LG`. -/
noncomputable def filteredLeftDerivedFunctor_comparison
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type v} [Category.{w} B] [Abelian B]
    [HasDerivedCategory.{x} A] [HasDerivedCategory.{y} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) :
    (filteredLeftDerivedFunctorData G hG dA dB).filtered_functor ⋙
        dB.localization_minus ≅
      dA.minus_equivalence.inverse ⋙
        filteredLeftDerivedFunctor G hG dA dB :=
  (filteredLeftDerivedFunctorData G hG dA dB).comparison

/-! ## Graded comparison and the spectral sequence -/

/-- The source's commuting square, expressed by its canonical natural isomorphism. -/
theorem filteredRightDerivedFunctor_graded_comparison
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type v} [Category.{w} B] [Abelian B]
    [HasDerivedCategory.{x} A] [HasDerivedCategory.{y} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (dA : FilteredDerivedCategoryData A)
    (dB : FilteredDerivedCategoryData B) (p : ℤ) :
    Nonempty
      (filteredRightDerivedFunctor T hT dA dB ⋙ dB.graded_plus p ≅
        dA.graded_plus p ⋙ totalRightDerivedFunctor A B T hT) := by
  sorry

/-- A filtered derived spectral sequence attached to an object of `DF⁺(B)`. -/
structure FilteredDerivedSpectralSequence
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (dB : FilteredDerivedCategoryData B) (K : dB.plus) where
  spectral_sequence :
    CategoryTheory.CohomologicalSpectralSequence B 0
  first_page :
    ∀ p q : ℤ,
      Nonempty
        ((spectral_sequence.page 1).X (p, q) ≅
          (DerivedCategory.Plus.homologyFunctor B (p + q)).obj
            ((dB.graded_plus p).obj K))
  abutment : ℤ → FilteredObject B
  abutment_iso :
    ∀ n : ℤ,
      Nonempty
        ((abutment n).carrier ≅
          (DerivedCategory.Plus.homologyFunctor B n).obj
            ((dB.forget_plus).obj K))

/-- Every object of the bounded-below filtered derived category has the source's
spectral sequence, with `E₁^{p,q} = H^{p+q}(gr^p K)` and the stated abutment. -/
theorem filteredDerivedSpectralSequence_exists
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (dB : FilteredDerivedCategoryData B) (K : dB.plus) :
    Nonempty (FilteredDerivedSpectralSequence dB K) := by
  sorry

noncomputable def filteredDerivedSpectralSequence
    {B : Type v} [Category.{w} B] [Abelian B]
    [HasDerivedCategory.{x} B]
    (dB : FilteredDerivedCategoryData B) (K : dB.plus) :
    FilteredDerivedSpectralSequence dB K :=
  Classical.choice (filteredDerivedSpectralSequence_exists dB K)

end Formalization.Books.Trace.Unit08
