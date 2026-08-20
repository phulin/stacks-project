import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Formalization.Books.Trace.Unit06.DerivedCategories
import Formalization.Books.Homology.Unit19.Filtrations

/-!
# The Trace Formula, Chapter 7: filtered derived category

The filtered-object and associated-graded constructions are the canonical
ones from Homology, Chapter 19.  This chapter adds the finite filtered
subcategory, the filtered homotopy categories, and the localization
interfaces for the filtered derived categories appearing in the source.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit19
open Formalization.Books.Trace.Unit06
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Trace.Unit07

/-! ## Filtered objects and finite filtrations -/

/- The source's `Fil(𝒜)` is Homology 19's category of filtered objects. -/
abbrev Fil (A : Type u) [Category.{v} A] := FilteredObject A

/- A finite filtration is the canonical `FilteredObject.IsFinite` predicate.
   Its two extremal steps express the displayed finite decreasing chain. -/
def finiteFilteredProperty
    (A : Type u) [Category.{v} A] [Abelian A] :
    ObjectProperty (Fil A) :=
  fun F => F.IsFinite

/- `Fil^f(𝒜)` is a full subcategory, so its morphisms remain the canonical
   filtered morphisms with no duplicated hom-set definition. -/
abbrev FiniteFiltered
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (finiteFilteredProperty A).FullSubcategory

abbrev finiteFilteredInclusion
    (A : Type u) [Category.{v} A] [Abelian A] :
    FiniteFiltered A ⥤ Fil A :=
  (finiteFilteredProperty A).ι

/- The finite full subcategory is additive, as asserted in the definition.
   The existence interface is left as a theorem-stage obligation. -/
theorem finiteFiltered_additiveCategory_exists
    (A : Type u) [Category.{v} A] [Abelian A] :
    Nonempty (AdditiveCategory (FiniteFiltered A)) := by
  sorry

noncomputable instance finiteFiltered_additiveCategory
    (A : Type u) [Category.{v} A] [Abelian A] :
    AdditiveCategory (FiniteFiltered A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (finiteFiltered_additiveCategory_exists A)).toHasFiniteProducts }

/-! ## Filtered injective and projective objects -/

/- The ambient finite-filtered type supplies finiteness; the source's object
   predicate is exactly injectivity of every associated graded piece. -/
def IsFilteredInjective
    (A : Type u) [Category.{v} A] [Abelian A] (I : Fil A) : Prop :=
  ∀ p : ℤ, Injective (gradedPiece I p)

def IsFilteredProjective
    (A : Type u) [Category.{v} A] [Abelian A] (P : Fil A) : Prop :=
  ∀ p : ℤ, Projective (gradedPiece P p)

def filteredInjectiveProperty
  (A : Type u) [Category.{v} A] [Abelian A] :
    ObjectProperty (FiniteFiltered A) :=
  fun I => IsFilteredInjective A I.obj

def filteredProjectiveProperty
  (A : Type u) [Category.{v} A] [Abelian A] :
    ObjectProperty (FiniteFiltered A) :=
  fun P => IsFilteredProjective A P.obj

/- The full subcategories `𝓘` and `𝓟` in the source lemma. -/
abbrev FilteredInjectiveSubcategory
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (filteredInjectiveProperty A).FullSubcategory

abbrev FilteredProjectiveSubcategory
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (filteredProjectiveProperty A).FullSubcategory

theorem filteredInjectiveSubcategory_additiveCategory_exists
    (A : Type u) [Category.{v} A] [Abelian A] :
    Nonempty (AdditiveCategory (FilteredInjectiveSubcategory A)) := by
  sorry

noncomputable instance filteredInjectiveSubcategory_additiveCategory
    (A : Type u) [Category.{v} A] [Abelian A] :
    AdditiveCategory (FilteredInjectiveSubcategory A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice
        (filteredInjectiveSubcategory_additiveCategory_exists A)).toHasFiniteProducts }

theorem filteredProjectiveSubcategory_additiveCategory_exists
    (A : Type u) [Category.{v} A] [Abelian A] :
    Nonempty (AdditiveCategory (FilteredProjectiveSubcategory A)) := by
  sorry

noncomputable instance filteredProjectiveSubcategory_additiveCategory
    (A : Type u) [Category.{v} A] [Abelian A] :
    AdditiveCategory (FilteredProjectiveSubcategory A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice
        (filteredProjectiveSubcategory_additiveCategory_exists A)).toHasFiniteProducts }

/-! ## Complexes and homotopy categories of finite filtered objects -/

abbrev FilteredComplex
    (A : Type u) [Category.{v} A] [Abelian A] :=
  Comp (FiniteFiltered A)

abbrev FilteredComplexPlus
    (A : Type u) [Category.{v} A] [Abelian A] :=
  CompPlus (FiniteFiltered A)

abbrev FilteredComplexMinus
    (A : Type u) [Category.{v} A] [Abelian A] :=
  CompMinus (FiniteFiltered A)

abbrev FilteredHomotopyCategory
    (A : Type u) [Category.{v} A] [Abelian A] :=
  K (FiniteFiltered A)

abbrev FilteredHomotopyCategoryPlus
    (A : Type u) [Category.{v} A] [Abelian A] :=
  KPlus (FiniteFiltered A)

abbrev FilteredHomotopyCategoryMinus
    (A : Type u) [Category.{v} A] [Abelian A] :=
  KMinus (FiniteFiltered A)

/-! ## Graded-piece functors and filtered quasi-isomorphisms -/

abbrev finiteGradedPieceFunctor
    (A : Type u) [Category.{v} A] [Abelian A] (p : ℤ) :
    FiniteFiltered A ⥤ A :=
  finiteFilteredInclusion A ⋙ gradedPieceFunctor (C := A) p

noncomputable instance finiteGradedPieceFunctor_additive
    (A : Type u) [Category.{v} A] [Abelian A] (p : ℤ) :
    (finiteGradedPieceFunctor A p).Additive := by
  let _ : (gradedPieceFunctor (C := A) p).Additive :=
    gradedPieceFunctor_is_additive (C := A) p
  infer_instance

noncomputable abbrev filteredGradedPieceHomotopyFunctor
    (A : Type u) [Category.{v} A] [Abelian A] (p : ℤ) :
    FilteredHomotopyCategory A ⥤ K A :=
  (finiteGradedPieceFunctor A p).mapHomotopyCategory (ComplexShape.up ℤ)

/- A filtered quasi-isomorphism is a quasi-isomorphism after taking every
   associated graded piece. -/
def filteredGradedPieceQuasiIso
    (A : Type u) [Category.{v} A] [Abelian A] (p : ℤ) :
    MorphismProperty (FilteredHomotopyCategory A) :=
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
    (filteredGradedPieceHomotopyFunctor A p)

def filteredQuasiIso
    (A : Type u) [Category.{v} A] [Abelian A] :
    MorphismProperty (FilteredHomotopyCategory A) :=
  fun {_K _L} f => ∀ p : ℤ, filteredGradedPieceQuasiIso A p f

theorem filteredQuasiIso_iff_gradedPiece
    (A : Type u) [Category.{v} A] [Abelian A]
    {K L : FilteredHomotopyCategory A} (f : K ⟶ L) :
    filteredQuasiIso A f ↔
      ∀ p : ℤ,
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
          ((filteredGradedPieceHomotopyFunctor A p).map f) :=
  Iff.rfl

/- Restrict a morphism property along the inclusion of a full subcategory.
   This is the categorical operation used to define the bounded localizations. -/
def restrictMorphismProperty
    {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    (P : ObjectProperty C) : MorphismProperty P.FullSubcategory :=
  fun {_X _Y} f => W ((P.ι).map f)

/- The restrictions of the filtered quasi-isomorphism property to bounded
   homotopy subcategories are the source's `DF⁺` and `DF⁻` inputs. -/
def filteredQuasiIsoPlus
    (A : Type u) [Category.{v} A] [Abelian A] :
    MorphismProperty (FilteredHomotopyCategoryPlus A) :=
  restrictMorphismProperty (filteredQuasiIso A)
    (boundedBelowHomotopyProperty (FiniteFiltered A))

def filteredQuasiIsoMinus
    (A : Type u) [Category.{v} A] [Abelian A] :
    MorphismProperty (FilteredHomotopyCategoryMinus A) :=
  restrictMorphismProperty (filteredQuasiIso A)
    (boundedAboveHomotopyProperty (FiniteFiltered A))

/-! ## Filtered derived categories -/

/- Inverting the filtered quasi-isomorphisms is Mathlib's canonical
   localization construction. -/
abbrev DF
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (filteredQuasiIso A).Localization

abbrev DFPlus
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (filteredQuasiIsoPlus A).Localization

abbrev DFMinus
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (filteredQuasiIsoMinus A).Localization

abbrev filteredLocalizationFunctor
    (A : Type u) [Category.{v} A] [Abelian A] :
    FilteredHomotopyCategory A ⥤ DF A :=
  (filteredQuasiIso A).Q

/-! ## The filtered-derived localization lemma -/

/- The source's omitted proof is retained as a theorem interface.  Its
   hypotheses record exactly the two resolution assumptions, while the
   codomains are the full additive subcategories defined above. -/
noncomputable def filteredDerivedCategory_plus_equiv_filteredInjectiveHomotopy
    (A : Type u) [Category.{v} A] [Abelian A] [EnoughInjectives A] :
    DFPlus A ≌ KPlus (FilteredInjectiveSubcategory A) := by
  sorry

noncomputable def filteredDerivedCategory_minus_equiv_filteredProjectiveHomotopy
    (A : Type u) [Category.{v} A] [Abelian A] [EnoughProjectives A] :
    DFMinus A ≌ KMinus (FilteredProjectiveSubcategory A) := by
  sorry

end Formalization.Books.Trace.Unit07
