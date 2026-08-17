import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Homology.Unit19.Filtrations

/-!
# Derived Categories, Chapter 13: filtered derived categories

The finite filtered objects, associated graded functors, and strictness API are
the canonical constructions from Homology, Chapter 19.  This file adds the
homotopy-category and localization interfaces used for the filtered derived
category in the source section.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit05
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit16
open Formalization.Books.Homology.Unit19
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit13

/-! ## Finite filtered objects and their functors -/

/-- The object property defining the finite filtered-object category. -/
def finiteFilteredProperty (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredObject C) :=
  fun A => A.IsFinite

/-- The source's `Fil^f(𝒜)`, as a full subcategory of filtered objects. -/
abbrev FiniteFilteredObject
    (C : Type u) [Category.{v} C] [Abelian C] :=
  (finiteFilteredProperty C).FullSubcategory

/-- The inclusion `Fil^f(𝒜) ⥤ Fil(𝒜)`. -/
abbrev finiteFilteredInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FiniteFilteredObject C ⥤ FilteredObject C :=
  (finiteFilteredProperty C).ι

/-- The additive-category structure on finite filtered objects. -/
theorem finiteFiltered_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FiniteFilteredObject C)) := by
  sorry

noncomputable instance finiteFiltered_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FiniteFilteredObject C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := by sorry }

/-- Forget the filtration and retain the underlying object of `𝒜`. -/
def filteredForgetful
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredObject C ⥤ C where
  obj A := A.carrier
  map {_A _B} f := f.hom
  map_id _A := rfl
  map_comp _f _g := rfl

noncomputable instance filteredForgetful_additive
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredForgetful C).Additive where
  map_add := by
    intro A B f g
    rfl

/-- The forgetful functor on finite filtered objects. -/
abbrev finiteForgetful
    (C : Type u) [Category.{v} C] [Abelian C] :
    FiniteFilteredObject C ⥤ C :=
  finiteFilteredInclusion C ⋙ filteredForgetful C

/-- The `p`th associated graded-piece functor on finite filtrations. -/
abbrev finiteGradedPieceFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    FiniteFilteredObject C ⥤ C :=
  finiteFilteredInclusion C ⋙ gradedPieceFunctor (C := C) p

/-- The associated graded functor on finite filtrations. -/
abbrev finiteAssociatedGraded
    (C : Type u) [Category.{v} C] [Abelian C] :
    FiniteFilteredObject C ⥤ GradedObject ℤ C :=
  finiteFilteredInclusion C ⋙ associatedGraded (C := C)

noncomputable instance finiteGradedPieceFunctor_additive
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    (finiteGradedPieceFunctor C p).Additive := by
  let _ : (gradedPieceFunctor (C := C) p).Additive :=
    gradedPieceFunctor_is_additive (C := C) p
  infer_instance

noncomputable instance finiteAssociatedGraded_additive
    (C : Type u) [Category.{v} C] [Abelian C] :
    (finiteAssociatedGraded C).Additive := by
  let _ : (associatedGraded (C := C)).Additive :=
    associatedGraded_is_additive (C := C)
  infer_instance

theorem finiteAssociatedGraded_piece
    (C : Type u) [Category.{v} C] [Abelian C]
    (A : FiniteFilteredObject C) (p : ℤ) :
    (finiteAssociatedGraded C).obj A p = gradedPiece A.obj p := rfl

theorem finiteAssociatedGraded_direct_sum_description
    (C : Type u) [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : FiniteFilteredObject C) :
    (gradedTotal C).obj ((finiteAssociatedGraded C).obj A) =
      ∐ fun p : ℤ => gradedPiece A.obj p := rfl

/-- The finite filtered category is not abelian in general. -/
theorem finiteFilteredCategory_not_abelian :
    ∃ (C : Type u) (_ : Category.{u} C) (_ : Abelian C),
      ¬ Nonempty (Abelian (FiniteFilteredObject C)) := by
  sorry

/-! ## The homotopy-category functors and filtered acyclicity -/

abbrev FilteredComplex
    (C : Type u) [Category.{v} C] [Abelian C] :=
  Comp (FiniteFilteredObject C)

abbrev FilteredHomotopyCategory
    (C : Type u) [Category.{v} C] [Abelian C] :=
  HomotopyCategory (FiniteFilteredObject C) (ComplexShape.up ℤ)

noncomputable instance filteredHomotopyCategory_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredHomotopyCategory C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := by sorry }

/-- The homotopy functor induced by the `p`th graded piece. -/
noncomputable abbrev filteredGradedPieceHomotopyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredHomotopyCategory C ⥤
      HomotopyCategory C (ComplexShape.up ℤ) :=
  (finiteGradedPieceFunctor C p).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The homotopy functor induced by the associated graded object. -/
noncomputable abbrev filteredAssociatedGradedHomotopyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤
      HomotopyCategory (GradedObject ℤ C) (ComplexShape.up ℤ) :=
  (finiteAssociatedGraded C).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The homotopy functor induced by forgetting the filtration. -/
noncomputable abbrev filteredForgetfulHomotopyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤
      HomotopyCategory C (ComplexShape.up ℤ) :=
  (finiteForgetful C).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The degree-`n` homology of the associated graded complex. -/
noncomputable abbrev filteredGradedHomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    FilteredHomotopyCategory C ⥤ GradedObject ℤ C :=
  filteredAssociatedGradedHomotopyFunctor C ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ C)
      (ComplexShape.up ℤ) n

/-- The degree-`n` homology of the `p`th graded-piece complex. -/
noncomputable abbrev filteredGradedPieceHomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p n : ℤ) :
    FilteredHomotopyCategory C ⥤ C :=
  filteredGradedPieceHomotopyFunctor C p ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n

/-- The degree-`n` homology after forgetting the filtration. -/
noncomputable abbrev filteredForgetfulHomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    FilteredHomotopyCategory C ⥤ C :=
  filteredForgetfulHomotopyFunctor C ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n

/-- The source's filtered-acyclic object property. -/
def filteredAcyclic
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredHomotopyCategory C) :=
  fun K => ∀ n : ℤ, IsZero ((filteredGradedHomologyFunctor C n).obj K)

/-- The quasi-isomorphism property on the `p`th graded-piece complex. -/
def filteredGradedPieceQuasiIso
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    MorphismProperty (FilteredHomotopyCategory C) :=
  (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).inverseImage
    (filteredGradedPieceHomotopyFunctor C p)

/-- The source's filtered quasi-isomorphism property. -/
def filteredQuasiIso
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (FilteredHomotopyCategory C) :=
  (HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor C)

theorem filteredAcyclic_iff_gr_piece_acyclic
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) :
    filteredAcyclic C K ↔
      ∀ p n : ℤ,
        IsZero ((filteredGradedPieceHomologyFunctor C p n).obj K) := by
  sorry

theorem filteredQuasiIso_iff_gr_piece
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L) :
    filteredQuasiIso C f ↔ ∀ p : ℤ, filteredGradedPieceQuasiIso C p f := by
  sorry

theorem filteredQuasiIso_iff_associated_grading
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L) :
    filteredQuasiIso C f ↔
      HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)
        ((filteredAssociatedGradedHomotopyFunctor C).map f) := Iff.rfl

/- The three homological functors in the source lemma. -/
noncomputable abbrev filteredGradedHomologyZeroFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤ GradedObject ℤ C :=
  filteredGradedHomologyFunctor C 0

noncomputable abbrev filteredGradedPieceHomologyZeroFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredHomotopyCategory C ⥤ C :=
  filteredGradedPieceHomologyFunctor C p 0

noncomputable abbrev filteredForgetfulHomologyZeroFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤ C :=
  filteredForgetfulHomologyFunctor C 0

theorem filteredGradedHomologyZero_is_homological
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredGradedHomologyZeroFunctor C).IsHomological := by
  sorry

theorem filteredGradedPieceHomologyZero_is_homological
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    (filteredGradedPieceHomologyZeroFunctor C p).IsHomological := by
  sorry

theorem filteredForgetfulHomologyZero_is_homological
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredForgetfulHomologyZeroFunctor C).IsHomological := by
  sorry

theorem filteredAcyclic_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    IsStrictlyFullSaturatedPretriangulated (filteredAcyclic C) := by
  sorry

theorem filteredQuasiIso_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (filteredQuasiIso C) ∧
      CompatibleWithTriangulation (filteredQuasiIso C) := by
  sorry

noncomputable instance filteredQuasiIso_leftCalculus
    (C : Type u) [Category.{v} C] [Abelian C] :
    LeftMultiplicativeSystem (filteredQuasiIso C) :=
  (filteredQuasiIso_properties C).1.1.1

noncomputable instance filteredQuasiIso_rightCalculus
    (C : Type u) [Category.{v} C] [Abelian C] :
    RightMultiplicativeSystem (filteredQuasiIso C) :=
  (filteredQuasiIso_properties C).1.1.2

noncomputable instance filteredQuasiIso_compatible
    (C : Type u) [Category.{v} C] [Abelian C] :
    CompatibleWithTriangulation (filteredQuasiIso C) :=
  (filteredQuasiIso_properties C).2

/-! ## The filtered derived category -/

/-- The filtered derived category `DF(𝒜)`. -/
abbrev FilteredDerivedCategory
    (C : Type u) [Category.{v} C] [Abelian C] :=
  (filteredQuasiIso C).Localization

noncomputable instance filteredDerivedCategory_hasShift
    (C : Type u) [Category.{v} C] [Abelian C] :
    HasShift (FilteredDerivedCategory C) ℤ := by
  sorry

noncomputable instance filteredDerivedCategory_all_shift_additive
    (C : Type u) [Category.{v} C] [Abelian C] :
    ∀ n : ℤ, (shiftFunctor (FilteredDerivedCategory C) n).Additive := by
  intro n
  sorry

/-- The localization functor `K(Fil^f(𝒜)) ⥤ DF(𝒜)`. -/
abbrev filteredLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤ FilteredDerivedCategory C :=
  (filteredQuasiIso C).Q

noncomputable instance filteredDerivedCategory_isTriangulated
    (C : Type u) [Category.{v} C] [Abelian C] :
    CategoryTheory.IsTriangulated (FilteredDerivedCategory C) := by
  exact localization_triangulated (S := filteredQuasiIso C)

theorem filteredLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredLocalizationFunctor C).IsLocalization (filteredQuasiIso C) := by
  infer_instance

theorem filteredDerivedLocalization_kernel
    (C : Type u) [Category.{v} C] [Abelian C] :
    functorKernel (filteredLocalizationFunctor C) = filteredAcyclic C := by
  sorry

theorem filteredQuasiIso_forgetful
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L)
    (hf : filteredQuasiIso C f) :
    HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
      ((filteredForgetfulHomotopyFunctor C).map f) := by
  sorry

theorem filteredQuasiIso_gr_piece
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L) (p : ℤ)
    (hf : filteredQuasiIso C f) :
    HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
      ((filteredGradedPieceHomotopyFunctor C p).map f) := by
  exact (filteredQuasiIso_iff_gr_piece C f).1 hf p

theorem filteredQuasiIso_associated_grading
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L)
    (hf : filteredQuasiIso C f) :
    HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)
      ((filteredAssociatedGradedHomotopyFunctor C).map f) :=
  hf

/-- The exact functor induced by the associated graded construction. -/
noncomputable def filteredDerivedGradedFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredDerivedCategory C ⥤ DerivedCategory (GradedObject ℤ C) :=
  Localization.lift
    (filteredAssociatedGradedHomotopyFunctor C ⋙
      DerivedCategory.Qh (C := GradedObject ℤ C))
    (by
      intro K L f hf
      exact Localization.inverts (DerivedCategory.Qh (C := GradedObject ℤ C))
        (HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)) _
        (filteredQuasiIso_associated_grading C f hf))
    (filteredLocalizationFunctor C)

/-- The exact functor induced by the `p`th graded piece. -/
noncomputable def filteredDerivedGradedPieceFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ)
    [HasDerivedCategory.{w} C] :
    FilteredDerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift
    (filteredGradedPieceHomotopyFunctor C p ⋙
      DerivedCategory.Qh (C := C))
    (by
      intro K L f hf
      exact Localization.inverts (DerivedCategory.Qh (C := C))
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _
        (filteredQuasiIso_gr_piece C f p hf))
    (filteredLocalizationFunctor C)

/-- The exact functor induced by forgetting the filtration. -/
noncomputable def filteredDerivedForgetfulFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    FilteredDerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift
    (filteredForgetfulHomotopyFunctor C ⋙ DerivedCategory.Qh (C := C))
    (by
      intro K L f hf
      exact Localization.inverts (DerivedCategory.Qh (C := C))
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _
        (filteredQuasiIso_forgetful C f hf))
    (filteredLocalizationFunctor C)

theorem filteredDerivedGradedFunctor_fac
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    filteredLocalizationFunctor C ⋙ filteredDerivedGradedFunctor C =
      filteredAssociatedGradedHomotopyFunctor C ⋙
        DerivedCategory.Qh (C := GradedObject ℤ C) := by
  sorry

theorem filteredDerivedGradedPieceFunctor_fac
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ)
    [HasDerivedCategory.{w} C] :
    filteredLocalizationFunctor C ⋙ filteredDerivedGradedPieceFunctor C p =
      filteredGradedPieceHomotopyFunctor C p ⋙
        DerivedCategory.Qh (C := C) := by
  sorry

theorem filteredDerivedForgetfulFunctor_fac
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    filteredLocalizationFunctor C ⋙ filteredDerivedForgetfulFunctor C =
      filteredForgetfulHomotopyFunctor C ⋙ DerivedCategory.Qh (C := C) := by
  sorry

noncomputable instance filteredDerivedGradedFunctor_commShift
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredDerivedGradedFunctor C).CommShift ℤ := by
  sorry

noncomputable instance filteredDerivedGradedPieceFunctor_commShift
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ)
    [HasDerivedCategory.{w} C] :
    (filteredDerivedGradedPieceFunctor C p).CommShift ℤ := by
  sorry

noncomputable instance filteredDerivedForgetfulFunctor_commShift
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    (filteredDerivedForgetfulFunctor C).CommShift ℤ := by
  sorry

theorem filteredDerivedGradedFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredDerivedGradedFunctor C).IsTriangulated := by
  sorry

theorem filteredDerivedGradedPieceFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ)
    [HasDerivedCategory.{w} C] :
    (filteredDerivedGradedPieceFunctor C p).IsTriangulated := by
  sorry

theorem filteredDerivedForgetfulFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    (filteredDerivedForgetfulFunctor C).IsTriangulated := by
  sorry

theorem filteredDerivedGradedCohomologyZero_fac
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    filteredLocalizationFunctor C ⋙ filteredDerivedGradedFunctor C ⋙
        derivedCohomologyFunctor (GradedObject ℤ C) 0 =
      filteredGradedHomologyZeroFunctor C := by
  sorry

/-! ## Bounded filtered derived categories -/

def filteredDerivedPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    ObjectProperty (FilteredDerivedCategory C) :=
  (derivedPlusProperty (GradedObject ℤ C)).inverseImage
    (filteredDerivedGradedFunctor C)

def filteredDerivedMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    ObjectProperty (FilteredDerivedCategory C) :=
  (derivedMinusProperty (GradedObject ℤ C)).inverseImage
    (filteredDerivedGradedFunctor C)

def filteredDerivedBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    ObjectProperty (FilteredDerivedCategory C) :=
  (derivedBoundedProperty (GradedObject ℤ C)).inverseImage
    (filteredDerivedGradedFunctor C)

/-- The bounded-below filtered derived category. -/
abbrev FilteredDerivedPlus
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :=
  (filteredDerivedPlusProperty C).FullSubcategory

/-- The bounded-above filtered derived category. -/
abbrev FilteredDerivedMinus
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :=
  (filteredDerivedMinusProperty C).FullSubcategory

/-- The bounded filtered derived category. -/
abbrev FilteredDerivedBounded
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :=
  (filteredDerivedBoundedProperty C).FullSubcategory

/-! ## Boundedness replacements in the filtered homotopy category -/

def filteredComplexGradedHomologyVanishesBelow
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) : Prop :=
  ∃ a : ℤ, ∀ n : ℤ, n < a →
    IsZero ((filteredGradedHomologyFunctor C n).obj K)

def filteredComplexGradedHomologyVanishesAbove
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) : Prop :=
  ∃ b : ℤ, ∀ n : ℤ, b < n →
    IsZero ((filteredGradedHomologyFunctor C n).obj K)

def filteredComplexGradedHomologyVanishesBounded
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) : Prop :=
  filteredComplexGradedHomologyVanishesBelow C K ∧
    filteredComplexGradedHomologyVanishesAbove C K

def filteredComplexIsZeroBelow
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) (a : ℤ) : Prop :=
  ∀ n : ℤ, n < a → IsZero (K.as.X n)

def filteredComplexIsZeroAbove
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) (b : ℤ) : Prop :=
  ∀ n : ℤ, b < n → IsZero (K.as.X n)

def filteredComplexIsBounded
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) : Prop :=
  ∃ a b : ℤ, filteredComplexIsZeroBelow C K a ∧
    filteredComplexIsZeroAbove C K b

theorem filteredComplex_cohomology_bounded_below
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) (a : ℤ)
    (hK : ∀ n : ℤ, n < a →
      IsZero ((filteredGradedHomologyFunctor C n).obj K)) :
    ∃ (L : FilteredHomotopyCategory C) (f : K ⟶ L),
      filteredQuasiIso C f ∧ filteredComplexIsZeroBelow C L a := by
  sorry

theorem filteredComplex_cohomology_bounded_above
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) (b : ℤ)
    (hK : ∀ n : ℤ, b < n →
      IsZero ((filteredGradedHomologyFunctor C n).obj K)) :
    ∃ (M : FilteredHomotopyCategory C) (f : M ⟶ K),
      filteredQuasiIso C f ∧ filteredComplexIsZeroAbove C M b := by
  sorry

theorem filteredComplex_cohomology_bounded
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C)
    (hK : filteredComplexGradedHomologyVanishesBounded C K) :
    ∃ (L M N : FilteredHomotopyCategory C)
      (f : K ⟶ L) (g : M ⟶ K) (u : M ⟶ N) (v : N ⟶ L),
      g ≫ f = u ≫ v ∧
      filteredQuasiIso C f ∧ filteredQuasiIso C g ∧
      filteredQuasiIso C u ∧ filteredQuasiIso C v ∧
      (∃ a : ℤ, filteredComplexIsZeroBelow C L a) ∧
      (∃ b : ℤ, filteredComplexIsZeroAbove C M b) ∧
      filteredComplexIsBounded C N := by
  sorry

/-! ## Bounded filtered homotopy localizations -/

abbrev FilteredKPlus
    (C : Type u) [Category.{v} C] [Abelian C] :=
  KPlus (FiniteFilteredObject C)

abbrev FilteredKMinus
    (C : Type u) [Category.{v} C] [Abelian C] :=
  KMinus (FiniteFilteredObject C)

abbrev FilteredKBounded
    (C : Type u) [Category.{v} C] [Abelian C] :=
  KBounded (FiniteFilteredObject C)

theorem filteredKPlus_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredKPlus C)) := by
  sorry

noncomputable instance filteredKPlus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredKPlus C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := by sorry }

theorem filteredKMinus_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredKMinus C)) := by
  sorry

noncomputable instance filteredKMinus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredKMinus C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := by sorry }

theorem filteredKBounded_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredKBounded C)) := by
  sorry

noncomputable instance filteredKBounded_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredKBounded C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := by sorry }

noncomputable instance filteredKPlus_shift_additive
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    (shiftFunctor (FilteredKPlus C) n).Additive := by
  sorry

noncomputable instance filteredKMinus_shift_additive
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    (shiftFunctor (FilteredKMinus C) n).Additive := by
  sorry

noncomputable instance filteredKBounded_shift_additive
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    (shiftFunctor (FilteredKBounded C) n).Additive := by
  sorry

abbrev filteredKPlusInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredKPlus C ⥤
      HomotopyCategory (FiniteFilteredObject C) (ComplexShape.up ℤ) :=
  (boundedBelowHomotopyProperty (FiniteFilteredObject C)).ι

abbrev filteredKMinusInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredKMinus C ⥤
      HomotopyCategory (FiniteFilteredObject C) (ComplexShape.up ℤ) :=
  (boundedAboveHomotopyProperty (FiniteFilteredObject C)).ι

abbrev filteredKBoundedInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredKBounded C ⥤
      HomotopyCategory (FiniteFilteredObject C) (ComplexShape.up ℤ) :=
  (boundedHomotopyProperty (FiniteFilteredObject C)).ι

def filteredAcyclicPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredKPlus C) :=
  (filteredAcyclic C).inverseImage (filteredKPlusInclusion C)

def filteredAcyclicMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredKMinus C) :=
  (filteredAcyclic C).inverseImage (filteredKMinusInclusion C)

def filteredAcyclicBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredKBounded C) :=
  (filteredAcyclic C).inverseImage (filteredKBoundedInclusion C)

abbrev filteredQuasiIsoPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (FilteredKPlus C) :=
  restrictedMorphismProperty (filteredQuasiIso C)
    (boundedBelowHomotopyProperty (FiniteFilteredObject C))

abbrev filteredQuasiIsoMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (FilteredKMinus C) :=
  restrictedMorphismProperty (filteredQuasiIso C)
    (boundedAboveHomotopyProperty (FiniteFilteredObject C))

abbrev filteredQuasiIsoBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (FilteredKBounded C) :=
  restrictedMorphismProperty (filteredQuasiIso C)
    (boundedHomotopyProperty (FiniteFilteredObject C))

theorem filteredBoundedAcyclic_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    IsStrictlyFullSaturatedPretriangulated (filteredAcyclicPlusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (filteredAcyclicMinusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (filteredAcyclicBoundedProperty C) := by
  sorry

theorem filteredBoundedQuasiIso_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (filteredQuasiIsoPlusProperty C) ∧
      SaturatedMultiplicativeSystem (filteredQuasiIsoMinusProperty C) ∧
      SaturatedMultiplicativeSystem (filteredQuasiIsoBoundedProperty C) := by
  sorry

theorem filteredDerived_maps_KPlus_to_DPlus
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    (X : FilteredKPlus C) :
    filteredDerivedPlusProperty C
      ((filteredKPlusInclusion C ⋙ filteredLocalizationFunctor C).obj X) := by
  sorry

theorem filteredDerived_maps_KMinus_to_DMinus
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    (X : FilteredKMinus C) :
    filteredDerivedMinusProperty C
      ((filteredKMinusInclusion C ⋙ filteredLocalizationFunctor C).obj X) := by
  sorry

theorem filteredDerived_maps_KBounded_to_DBounded
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    (X : FilteredKBounded C) :
    filteredDerivedBoundedProperty C
      ((filteredKBoundedInclusion C ⋙ filteredLocalizationFunctor C).obj X) := by
  sorry

noncomputable def filteredPlusDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredKPlus C ⥤ FilteredDerivedPlus C :=
  (filteredDerivedPlusProperty C).lift
    (filteredKPlusInclusion C ⋙ filteredLocalizationFunctor C)
    (filteredDerived_maps_KPlus_to_DPlus C)

noncomputable def filteredMinusDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredKMinus C ⥤ FilteredDerivedMinus C :=
  (filteredDerivedMinusProperty C).lift
    (filteredKMinusInclusion C ⋙ filteredLocalizationFunctor C)
    (filteredDerived_maps_KMinus_to_DMinus C)

noncomputable def filteredBoundedDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredKBounded C ⥤ FilteredDerivedBounded C :=
  (filteredDerivedBoundedProperty C).lift
    (filteredKBoundedInclusion C ⋙ filteredLocalizationFunctor C)
    (filteredDerived_maps_KBounded_to_DBounded C)

theorem filteredPlusDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredPlusDerivedLocalizationFunctor C).IsLocalization
      (filteredQuasiIsoPlusProperty C) := by
  sorry

theorem filteredMinusDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredMinusDerivedLocalizationFunctor C).IsLocalization
      (filteredQuasiIsoMinusProperty C) := by
  sorry

theorem filteredBoundedDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredBoundedDerivedLocalizationFunctor C).IsLocalization
      (filteredQuasiIsoBoundedProperty C) := by
  sorry

noncomputable def filteredPlusLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredQuasiIsoPlusProperty C).Localization ⥤ FilteredDerivedPlus C :=
  Localization.Construction.lift (filteredPlusDerivedLocalizationFunctor C)
    (by exact (filteredPlusDerivedLocalizationFunctor_is_localization C).inverts)

noncomputable def filteredMinusLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredQuasiIsoMinusProperty C).Localization ⥤ FilteredDerivedMinus C :=
  Localization.Construction.lift (filteredMinusDerivedLocalizationFunctor C)
    (by exact (filteredMinusDerivedLocalizationFunctor_is_localization C).inverts)

noncomputable def filteredBoundedLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredQuasiIsoBoundedProperty C).Localization ⥤ FilteredDerivedBounded C :=
  Localization.Construction.lift (filteredBoundedDerivedLocalizationFunctor C)
    (by exact (filteredBoundedDerivedLocalizationFunctor_is_localization C).inverts)

theorem filteredPlusLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Functor.IsEquivalence (filteredPlusLocalizationComparison C) := by
  sorry

theorem filteredMinusLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Functor.IsEquivalence (filteredMinusLocalizationComparison C) := by
  sorry

theorem filteredBoundedLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Functor.IsEquivalence (filteredBoundedLocalizationComparison C) := by
  sorry

theorem filteredPlusDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    functorKernel (filteredPlusDerivedLocalizationFunctor C) =
      filteredAcyclicPlusProperty C := by
  sorry

theorem filteredMinusDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    functorKernel (filteredMinusDerivedLocalizationFunctor C) =
      filteredAcyclicMinusProperty C := by
  sorry

theorem filteredBoundedDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    functorKernel (filteredBoundedDerivedLocalizationFunctor C) =
      filteredAcyclicBoundedProperty C := by
  sorry

end Formalization.Books.Derived.Unit13
