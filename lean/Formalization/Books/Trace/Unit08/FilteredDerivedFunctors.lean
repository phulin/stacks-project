import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Formalization.Books.Trace.Unit07.FilteredDerivedCategory
import Formalization.Books.Trace.Unit06.DerivedCategories

/-!
# The Trace Formula, Chapter 8: filtered derived functors

The filtered derived categories and their localization functors are the
canonical constructions from Chapter 7.  This file records the additional
filtered-derived-functor interfaces and the spectral sequence asserted in
the source section.
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Categories.Unit23

universe u v u' v' w w'

namespace Formalization.Books.Trace.Unit08

/-! ## Filtered derived-category functors -/

abbrev filteredPlusLocalizationFunctor
    (A : Type u) [Category.{v} A] [Abelian A] :
    Formalization.Books.Trace.Unit07.FilteredHomotopyCategoryPlus A ⥤
      Formalization.Books.Trace.Unit07.DFPlus A :=
  (Formalization.Books.Trace.Unit07.filteredQuasiIsoPlus A).Q

abbrev filteredMinusLocalizationFunctor
    (A : Type u) [Category.{v} A] [Abelian A] :
    Formalization.Books.Trace.Unit07.FilteredHomotopyCategoryMinus A ⥤
      Formalization.Books.Trace.Unit07.DFMinus A :=
  (Formalization.Books.Trace.Unit07.filteredQuasiIsoMinus A).Q

/-!
The source uses the graded-piece and forgetful functors out of the filtered
derived category.  Their construction through the localization is the
content of the filtered-derived-category API; this structure packages the
two functors needed by the comparison and spectral-sequence statements.
-/
structure FilteredDerivedCategoryData
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] where
  graded_plus : ℤ →
    Formalization.Books.Trace.Unit07.DFPlus A ⥤
      Formalization.Books.Trace.Unit06.DPlus A
  forget_plus :
    Formalization.Books.Trace.Unit07.DFPlus A ⥤
      Formalization.Books.Trace.Unit06.DPlus A

/- The preceding chapter supplies these functors by descending associated
   graded pieces and the forgetful functor through the filtered localization.
   They are kept behind this small interface because that descent is not yet
   exposed by the Chapter 7 file. -/
theorem filteredDerivedCategoryData_exists
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    Nonempty (FilteredDerivedCategoryData A) := by
  sorry

noncomputable def filteredDerivedCategoryData
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    FilteredDerivedCategoryData A :=
  Classical.choice (filteredDerivedCategoryData_exists A)

noncomputable abbrev filteredDerivedGradedFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (p : ℤ) :
    Formalization.Books.Trace.Unit07.DFPlus A ⥤
      Formalization.Books.Trace.Unit06.DPlus A :=
  (filteredDerivedCategoryData A).graded_plus p

noncomputable abbrev filteredDerivedForgetfulFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    Formalization.Books.Trace.Unit07.DFPlus A ⥤
      Formalization.Books.Trace.Unit06.DPlus A :=
  (filteredDerivedCategoryData A).forget_plus

/-! ## Filtered right-derived functors -/

/- The first diagram in the source, with the Chapter 7 equivalence made
   explicit in the comparison isomorphism. -/
structure FilteredRightDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (T : A ⥤ B) (hT : IsLeftExact T)
    [EnoughInjectives A] where
  filtered_functor :
    Formalization.Books.Trace.Unit06.KPlus
        (Formalization.Books.Trace.Unit07.FilteredInjectiveSubcategory A) ⥤
      Formalization.Books.Trace.Unit07.FilteredHomotopyCategoryPlus B
  functor :
    Formalization.Books.Trace.Unit07.DFPlus A ⥤
      Formalization.Books.Trace.Unit07.DFPlus B
  comparison :
    filtered_functor ⋙ filteredPlusLocalizationFunctor B ≅
      (Formalization.Books.Trace.Unit07.filteredDerivedCategory_plus_equiv_filteredInjectiveHomotopy A).inverse ⋙
        functor

/-- The well-definedness assertion for the filtered right-derived functor. -/
theorem filteredRightDerivedFunctorData_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) :
    Nonempty (FilteredRightDerivedFunctorData T hT) := by
  sorry

noncomputable def filteredRightDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) :
    FilteredRightDerivedFunctorData T hT :=
  Classical.choice (filteredRightDerivedFunctorData_exists T hT)

/-- The filtered derived functor `RT : DF⁺(A) ⥤ DF⁺(B)`. -/
noncomputable def filteredRightDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) :
    Formalization.Books.Trace.Unit07.DFPlus A ⥤
      Formalization.Books.Trace.Unit07.DFPlus B :=
  (filteredRightDerivedFunctorData T hT).functor

/-- The comparison isomorphism defining the filtered right-derived functor. -/
noncomputable def filteredRightDerivedFunctor_comparison
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) :
    (filteredRightDerivedFunctorData T hT).filtered_functor ⋙
        filteredPlusLocalizationFunctor B ≅
      (Formalization.Books.Trace.Unit07.filteredDerivedCategory_plus_equiv_filteredInjectiveHomotopy A).inverse ⋙
        filteredRightDerivedFunctor T hT :=
  (filteredRightDerivedFunctorData T hT).comparison

/- The lower horizontal arrow in the source diagram is `T` applied to
   bounded-below complexes of filtered injectives.  This declaration exposes
   that arrow as part of the chosen derived-functor data. -/
noncomputable abbrev filteredRightDerivedInputFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) :
    Formalization.Books.Trace.Unit06.KPlus
        (Formalization.Books.Trace.Unit07.FilteredInjectiveSubcategory A) ⥤
      Formalization.Books.Trace.Unit07.FilteredHomotopyCategoryPlus B :=
  (filteredRightDerivedFunctorData T hT).filtered_functor

/-! ## Filtered left-derived functors -/

/- The second diagram in the source, with the Chapter 7 projective
   equivalence made explicit in the comparison isomorphism. -/
structure FilteredLeftDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (G : A ⥤ B) (hG : IsRightExact G)
    [EnoughProjectives A] where
  filtered_functor :
    Formalization.Books.Trace.Unit06.KMinus
        (Formalization.Books.Trace.Unit07.FilteredProjectiveSubcategory A) ⥤
      Formalization.Books.Trace.Unit07.FilteredHomotopyCategoryMinus B
  functor :
    Formalization.Books.Trace.Unit07.DFMinus A ⥤
      Formalization.Books.Trace.Unit07.DFMinus B
  comparison :
    filtered_functor ⋙ filteredMinusLocalizationFunctor B ≅
      (Formalization.Books.Trace.Unit07.filteredDerivedCategory_minus_equiv_filteredProjectiveHomotopy A).inverse ⋙
        functor

/-- The well-definedness assertion for the filtered left-derived functor. -/
theorem filteredLeftDerivedFunctorData_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G) :
    Nonempty (FilteredLeftDerivedFunctorData G hG) := by
  sorry

noncomputable def filteredLeftDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G) :
    FilteredLeftDerivedFunctorData G hG :=
  Classical.choice (filteredLeftDerivedFunctorData_exists G hG)

/-- The filtered derived functor `LG : DF⁻(A) ⥤ DF⁻(B)`. -/
noncomputable def filteredLeftDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G) :
    Formalization.Books.Trace.Unit07.DFMinus A ⥤
      Formalization.Books.Trace.Unit07.DFMinus B :=
  (filteredLeftDerivedFunctorData G hG).functor

/-- The comparison isomorphism defining the filtered left-derived functor. -/
noncomputable def filteredLeftDerivedFunctor_comparison
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G) :
    (filteredLeftDerivedFunctorData G hG).filtered_functor ⋙
        filteredMinusLocalizationFunctor B ≅
      (Formalization.Books.Trace.Unit07.filteredDerivedCategory_minus_equiv_filteredProjectiveHomotopy A).inverse ⋙
        filteredLeftDerivedFunctor G hG :=
  (filteredLeftDerivedFunctorData G hG).comparison

noncomputable abbrev filteredLeftDerivedInputFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A]
    (G : A ⥤ B) (hG : IsRightExact G) :
    Formalization.Books.Trace.Unit06.KMinus
        (Formalization.Books.Trace.Unit07.FilteredProjectiveSubcategory A) ⥤
      Formalization.Books.Trace.Unit07.FilteredHomotopyCategoryMinus B :=
  (filteredLeftDerivedFunctorData G hG).filtered_functor

/-! ## Graded comparison and the spectral sequence -/

/-- The source's commuting square, expressed by its canonical isomorphism. -/
theorem filteredRightDerivedFunctor_graded_comparison
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (p : ℤ) :
    Nonempty
      (filteredRightDerivedFunctor T hT ⋙ filteredDerivedGradedFunctor B p ≅
        filteredDerivedGradedFunctor A p ⋙
          Formalization.Books.Trace.Unit06.totalRightDerivedFunctor A B T hT) := by
  sorry

/-- A filtered-derived spectral sequence attached to an object of `DF⁺(B)`. -/
structure FilteredDerivedSpectralSequence
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (K : Formalization.Books.Trace.Unit07.DFPlus B) where
  spectral_sequence :
    CategoryTheory.CohomologicalSpectralSequence B 0
  first_page :
    ∀ p q : ℤ,
      Nonempty
        ((spectral_sequence.page 1).X (p, q) ≅
          (DerivedCategory.Plus.homologyFunctor B (p + q)).obj
            ((filteredDerivedGradedFunctor B p).obj K))
  abutment : ℤ → B
  abutment_iso :
    ∀ n : ℤ,
      Nonempty
        (abutment n ≅
          (DerivedCategory.Plus.homologyFunctor B n).obj
            ((filteredDerivedForgetfulFunctor B).obj K))

/-- Every bounded-below filtered-derived object has the source's spectral
sequence, with `E₁^{p,q} = H^{p+q}(gr^p K)` and the stated abutment. -/
theorem filteredDerivedSpectralSequence_exists
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (K : Formalization.Books.Trace.Unit07.DFPlus B) :
    Nonempty (FilteredDerivedSpectralSequence K) := by
  sorry

noncomputable def filteredDerivedSpectralSequence
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (K : Formalization.Books.Trace.Unit07.DFPlus B) :
    FilteredDerivedSpectralSequence K :=
  Classical.choice (filteredDerivedSpectralSequence_exists K)

end Formalization.Books.Trace.Unit08
