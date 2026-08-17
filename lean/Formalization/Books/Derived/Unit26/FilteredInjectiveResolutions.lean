import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Formalization.Books.Derived.Unit09.ConesAndTermwiseSplitSequences
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit13.FilteredDerivedCategories
import Formalization.Books.Derived.Unit20.HigherDerivedFunctors
import Formalization.Books.Derived.Unit21.CartanEilenbergResolutions
import Formalization.Books.Derived.Unit23.ResolutionFunctors
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Sets.Unit12.AbelianCategoriesAndInjectives

/-!
# Derived Categories, Chapter 26: filtered derived category and injective resolutions

This file records the filtered-injective resolutions and filtered-derived-functor
interfaces in the source section.  The finite filtered objects, filtered
quasi-isomorphisms, filtered localization, and filtered-complex spectral
sequences are the canonical interfaces from the preceding chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit09
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit13
open Formalization.Books.Derived.Unit23
open Formalization.Books.Derived.Unit20
open Formalization.Books.Derived.Unit21
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit24
open Formalization.Books.Homology.Unit27
open Formalization.Books.Homology.Unit25
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u w' v' u'

namespace Formalization.Books.Derived.Unit26

/-! ## Exact filtered sequences and filtered injectives -/

/- The source calls a sequence in `Fil^f(𝒜)` exact when its associated
   graded sequence is exact.  `gradedPieceComplex` is the Homology 19
   short-complex API for that sequence. -/
def FilteredExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) : Prop :=
  ∀ p : ℤ, (gradedPieceComplex f g hfg p).Exact

theorem filteredExact_strict
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FiniteFilteredObject C}
    (f : A.obj ⟶ B.obj) (g : B.obj ⟶ D.obj) (hfg : f ≫ g = 0)
    (h : FilteredExact f g hfg) : Strict f ∧ Strict g := by
  sorry

/- A filtered-injective object is exactly an object whose graded pieces are
   injective.  Finiteness is supplied by the ambient `FiniteFilteredObject`
   category, as in the source's `Fil^f(𝒜)`. -/
def IsFilteredInjective
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FilteredObject C) : Prop :=
  ∀ p : ℤ, Injective (gradedPiece I p)

/-! ### The finite graded direct sum used in the splitting statement -/

abbrev filteredInjectiveIndex (a b : ℤ) := {n : ℤ // n ∈ Finset.Icc a b}

noncomputable def filteredInjectiveDirectSum
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : filteredInjectiveIndex a b → C) : C := by
  classical
  letI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  letI : Finite (filteredInjectiveIndex a b) := Finite.of_fintype _
  exact ⨁ I

noncomputable def filteredInjectiveDirectSumStep
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : filteredInjectiveIndex a b → C) (p : ℤ) :
    Subobject (filteredInjectiveDirectSum I (a := a) (b := b)) := by
  classical
  letI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  letI : Finite (filteredInjectiveIndex a b) := Finite.of_fintype _
  let f := biproduct.fromSubtype I (fun n => p ≤ n.1)
  let hf : SplitMono f := {
    retraction := biproduct.toSubtype I (fun n => p ≤ n.1)
    id := biproduct.fromSubtype_toSubtype _ _ }
  have hfmono : Mono f := by
    constructor
    intro Z g h w
    simpa [Category.assoc, hf.id] using
      congrArg (fun z => z ≫ hf.retraction) w
  exact @Subobject.mk _ _ _ _ f hfmono

theorem filteredInjectiveDirectSumStep_antitone
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : filteredInjectiveIndex a b → C) {p q : ℤ} (hpq : p ≤ q) :
    filteredInjectiveDirectSumStep I (a := a) (b := b) q ≤
      filteredInjectiveDirectSumStep I (a := a) (b := b) p := by
  sorry

noncomputable def filteredInjectiveDirectSumObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : filteredInjectiveIndex a b → C) : FilteredObject C where
  carrier := filteredInjectiveDirectSum I (a := a) (b := b)
  filtration :=
    { obj := filteredInjectiveDirectSumStep I (a := a) (b := b)
      antitone := by
        intro p q hpq
        exact filteredInjectiveDirectSumStep_antitone I hpq }

theorem filteredInjectiveDirectSumObject_isFinite
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : filteredInjectiveIndex a b → C) :
    (filteredInjectiveDirectSumObject I (a := a) (b := b)).IsFinite := by
  sorry

structure FilteredInjectiveDecomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FiniteFilteredObject C) where
  lower : ℤ
  upper : ℤ
  lower_le_upper : lower ≤ upper
  piece : filteredInjectiveIndex lower upper → C
  piece_injective : ∀ n, Injective (piece n)
  iso : I.obj.carrier ≅ filteredInjectiveDirectSum piece
  filtration : ∀ p : ℤ,
    (Subobject.«exists» iso.hom).obj (I.obj.filtration.obj p) =
      filteredInjectiveDirectSumStep piece p

theorem filteredInjective_decomposition_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FiniteFilteredObject C) (hI : IsFilteredInjective I.obj) :
    Nonempty (FilteredInjectiveDecomposition I) := by
  sorry

/- The source's splitting lemma, with the finite interval and filtration
   equality made explicit in the decomposition structure. -/
theorem filteredInjective_iff_decomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FiniteFilteredObject C) :
    IsFilteredInjective I.obj ↔
      Nonempty (FilteredInjectiveDecomposition I) := by
  sorry

/- A strict monomorphism from a filtered-injective object splits. -/
def StrictMonomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (u : A ⟶ B) : Prop :=
  Mono u ∧ Strict u

def StrictMonomorphismFinite
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FiniteFilteredObject C} (u : A ⟶ B) : Prop :=
  Mono u ∧ Strict u.hom

theorem strict_monomorphism_from_filtered_injective_splits
    {C : Type u} [Category.{v} C] [Abelian C]
    {I A : FiniteFilteredObject C} (u : I.obj ⟶ A.obj)
    (hI : IsFilteredInjective I.obj) (hu : StrictMonomorphism u) :
    ∃ r : A.obj ⟶ I.obj, u ≫ r = 𝟙 I.obj := by
  sorry

/- The lifting property is the exact-category form of the preceding split
   monomorphism statement. -/
theorem filtered_injective_lifting
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B I : FiniteFilteredObject C} (u : A.obj ⟶ B.obj)
    (hu : StrictMonomorphism u) (hI : IsFilteredInjective I.obj)
    (f : A.obj ⟶ I.obj) :
    ∃ g : B.obj ⟶ I.obj, u ≫ g = f := by
  sorry

/-! ## Strict embeddings and resolutions -/

theorem strict_mono_into_filtered_injective
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (A : FiniteFilteredObject C) :
    ∃ I : FiniteFilteredObject C, ∃ u : A.obj ⟶ I.obj,
      StrictMonomorphism u ∧ IsFilteredInjective I.obj := by
  sorry

def filteredInjectiveProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FiniteFilteredObject C) :=
  fun I => IsFilteredInjective I.obj

abbrev FilteredInjectiveSubcategory
    (C : Type u) [Category.{v} C] [Abelian C] :=
  (filteredInjectiveProperty C).FullSubcategory

abbrev filteredInjectiveInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredInjectiveSubcategory C ⥤ FiniteFilteredObject C :=
  (filteredInjectiveProperty C).ι

theorem filteredInjectiveSubcategory_additive_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredInjectiveSubcategory C)) := by
  sorry

noncomputable instance filteredInjectiveSubcategory_additive
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredInjectiveSubcategory C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (filteredInjectiveSubcategory_additive_exists C)).toHasFiniteProducts }

abbrev FilteredComplex
    (C : Type u) [Category.{v} C] [Abelian C] :=
  Comp (FiniteFilteredObject C)

abbrev FilteredComplexPlus
    (C : Type u) [Category.{v} C] [Abelian C] :=
  CompPlus (FiniteFilteredObject C)

noncomputable def filteredSingleFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FiniteFilteredObject C ⥤ FilteredComplexPlus C :=
  ObjectProperty.lift (boundedBelowProperty (FiniteFilteredObject C))
    (CochainComplex.singleFunctor (FiniteFilteredObject C) 0)
    (fun _ ↦ ⟨0, inferInstance⟩)

def filteredQuasiIsoComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (f : K ⟶ L) : Prop :=
  filteredQuasiIso C
    ((HomotopyCategory.quotient (FiniteFilteredObject C)
      (ComplexShape.up ℤ)).map f)

def filteredQuasiIsoComplexPlus
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplexPlus C} (f : K ⟶ L) : Prop :=
  filteredQuasiIsoPlusProperty C
    ((HomotopyCategory.Plus.quotient (FiniteFilteredObject C)).map f)

def IsTermwiseFilteredInjective
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplexPlus C) : Prop :=
  ∀ n : ℤ, IsFilteredInjective (K.obj.X n).obj

structure FilteredInjectiveResolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FiniteFilteredObject C) where
  complex : CompPlus (FilteredInjectiveSubcategory C)
  augmentation : (filteredSingleFunctor C).obj A ⟶
    (filteredInjectiveInclusion C).mapCochainComplexPlus.obj complex
  termwise_filtered_injective : ∀ n : ℤ,
    IsFilteredInjective (complex.obj.X n).obj.obj
  quasi_isomorphism : filteredQuasiIsoComplexPlus augmentation

theorem filtered_injective_right_resolution_single_object
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (A : FiniteFilteredObject C) :
    Nonempty (FilteredInjectiveResolution A) := by
  sorry

theorem filtered_injective_right_resolution_map
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FiniteFilteredObject C} (f : A ⟶ B)
    (I : FilteredInjectiveResolution A)
    (J : FilteredInjectiveResolution B) :
    ∃ φ : (filteredInjectiveInclusion C).mapCochainComplexPlus.obj I.complex ⟶
      (filteredInjectiveInclusion C).mapCochainComplexPlus.obj J.complex,
      (filteredSingleFunctor C).map f ≫ J.augmentation =
        I.augmentation ≫ φ := by
  sorry

structure FilteredInjectiveResolutionSES
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (FiniteFilteredObject C))
    (I : FilteredInjectiveResolution S.X₁)
    (J : FilteredInjectiveResolution S.X₃) where
  middle : CompPlus (FilteredInjectiveSubcategory C)
  middle_augmentation : (filteredSingleFunctor C).obj S.X₂ ⟶
    (filteredInjectiveInclusion C).mapCochainComplexPlus.obj middle
  lower : TermwiseSplitExactSequence
    ((filteredInjectiveInclusion C).mapCochainComplexPlus.obj I.complex).obj
    ((filteredInjectiveInclusion C).mapCochainComplexPlus.obj middle).obj
    ((filteredInjectiveInclusion C).mapCochainComplexPlus.obj J.complex).obj
  left_square :
    ((filteredSingleFunctor C).map S.f).hom ≫ middle_augmentation.hom =
      I.augmentation.hom ≫ lower.f
  right_square :
    middle_augmentation.hom ≫ lower.g =
      ((filteredSingleFunctor C).map S.g).hom ≫ J.augmentation.hom

theorem filtered_injective_right_resolution_ses
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (S : ShortComplex (FiniteFilteredObject C))
    (hSshort : S.ShortExact)
    (I : FilteredInjectiveResolution S.X₁)
    (J : FilteredInjectiveResolution S.X₃) :
    Nonempty (FilteredInjectiveResolutionSES S I J) := by
  sorry

/- The bounded-below resolution of a complex.  The raw complex and its map
   are retained so the source's degreewise strict-monomorphism assertion is
   visible rather than hidden in a homotopy-category object. -/
structure FilteredComplexInjectiveResolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplexPlus C) where
  complex : CompPlus (FilteredInjectiveSubcategory C)
  augmentation : K ⟶
    (filteredInjectiveInclusion C).mapCochainComplexPlus.obj complex
  termwise_filtered_injective : ∀ n : ℤ,
    IsFilteredInjective (complex.obj.X n).obj.obj
  quasi_isomorphism : filteredQuasiIsoComplexPlus augmentation
  degreewise_strict_mono : ∀ n : ℤ,
    StrictMonomorphismFinite (augmentation.hom.f n)

theorem right_resolution_by_filtered_injectives
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (K : FilteredComplexPlus C) :
    Nonempty (FilteredComplexInjectiveResolution K) := by
  sorry

theorem filtered_acyclic_to_filtered_injective_homotopic_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplexPlus C}
    {I : CompPlus (FilteredInjectiveSubcategory C)}
    (hK : filteredAcyclicPlusProperty C
      ((HomotopyCategory.Plus.quotient (FiniteFilteredObject C)).obj K))
    (hI : ∀ n : ℤ, IsFilteredInjective (I.obj.X n).obj.obj)
    (hIbelow : ∃ n : ℤ, I.obj.IsStrictlyGE n)
    (f : K ⟶ (filteredInjectiveInclusion C).mapCochainComplexPlus.obj I) :
    Nonempty (Homotopy f.hom 0) := by
  sorry

/-! ## The filtered localization by filtered injectives -/

noncomputable def filteredInjectiveHomotopyInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    KPlus (FilteredInjectiveSubcategory C) ⥤ FilteredKPlus C :=
  additiveHomotopyPlusFunctor (filteredInjectiveInclusion C)

noncomputable def filteredInjectiveToDerivedFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
  KPlus (FilteredInjectiveSubcategory C) ⥤ FilteredDerivedPlus C :=
  filteredInjectiveHomotopyInclusion C ⋙
    filteredPlusDerivedLocalizationFunctor C

theorem filteredDerivedPlus_hasZeroObject_exists
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Nonempty (HasZeroObject (FilteredDerivedPlus C)) := by
  sorry

noncomputable instance filteredDerivedPlus_hasZeroObject
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    HasZeroObject (FilteredDerivedPlus C) :=
  Classical.choice (filteredDerivedPlus_hasZeroObject_exists C)

theorem filteredDerivedPlus_hasShift_exists
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Nonempty (HasShift (FilteredDerivedPlus C) ℤ) := by
  sorry

noncomputable instance filteredDerivedPlus_hasShift
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    HasShift (FilteredDerivedPlus C) ℤ :=
  Classical.choice (filteredDerivedPlus_hasShift_exists C)

theorem filteredDerivedPlus_shift_additive_exists
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    ∀ n : ℤ, (shiftFunctor (FilteredDerivedPlus C) n).Additive := by
  sorry

noncomputable instance filteredDerivedPlus_shift_additive
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] (n : ℤ) :
    (shiftFunctor (FilteredDerivedPlus C) n).Additive :=
  filteredDerivedPlus_shift_additive_exists C n

theorem filteredDerivedPlus_pretriangulated_exists
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Nonempty (Pretriangulated (FilteredDerivedPlus C)) := by
  sorry

noncomputable instance filteredDerivedPlus_pretriangulated
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Pretriangulated (FilteredDerivedPlus C) :=
  Classical.choice (filteredDerivedPlus_pretriangulated_exists C)

theorem filtered_localization_functor
    (C : Type u) [Category.{v} C] [Abelian C]
    [EnoughInjectives C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Nonempty (ExactTriangulatedFunctorData (filteredInjectiveToDerivedFunctor C)) ∧
      Functor.IsEquivalence (filteredInjectiveToDerivedFunctor C) := by
  sorry

/- The size qualification in the source is the standard small abelian
   injective-subcategory construction.  We expose it through the existing
   Sets chapter interface rather than introducing a parallel notion here. -/
theorem filtered_localization_small_scope
    {A : Type (u + 1)} [LargeCategory A] [Abelian A] [EnoughInjectives A]
    (S : Type u) (A₀ : S → A) :
    Nonempty
      (Formalization.Books.Sets.Unit12.AbelianInjectiveSubcategory A S A₀) :=
  Formalization.Books.Sets.Unit12.exists_abelian_injective_subcategory S A₀

/- The two commutative squares in the localization lemma are recorded as
   functor equalities.  Their component proofs are deferred with the main
   localization proof, while the functors and directions are fixed here. -/
theorem filtered_localization_graded_diagram
    (C : Type u) [Category.{v} C] [Abelian C]
    [EnoughInjectives C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    filteredInjectiveToDerivedFunctor C ⋙
        (filteredDerivedPlusProperty C).ι ⋙ filteredDerivedGradedFunctor C =
      filteredInjectiveHomotopyInclusion C ⋙ filteredKPlusInclusion C ⋙
        filteredAssociatedGradedHomotopyFunctor C ⋙
          DerivedCategory.Qh (C := GradedObject ℤ C) := by
  sorry

theorem filtered_localization_forgetful_diagram
    (C : Type u) [Category.{v} C] [Abelian C]
    [EnoughInjectives C]
    [HasDerivedCategory.{w} C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    filteredInjectiveToDerivedFunctor C ⋙
        (filteredDerivedPlusProperty C).ι ⋙ filteredDerivedForgetfulFunctor C =
      filteredInjectiveHomotopyInclusion C ⋙ filteredKPlusInclusion C ⋙
        filteredForgetfulHomotopyFunctor C ⋙ DerivedCategory.Qh (C := C) := by
  sorry

structure FilteredLocalizationQuasiInverseData
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] where
  quasiInverse : FilteredDerivedPlus C ⥤
    KPlus (FilteredInjectiveSubcategory C)
  quasiInverseOf :
    QuasiInverseOf (filteredInjectiveToDerivedFunctor C) quasiInverse

theorem filtered_localization_quasi_inverse_exists
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Nonempty (FilteredLocalizationQuasiInverseData C) := by
  sorry

noncomputable def filteredLocalizationQuasiInverse
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredDerivedPlus C ⥤ KPlus (FilteredInjectiveSubcategory C) :=
  (Classical.choice (filtered_localization_quasi_inverse_exists C)).quasiInverse

theorem filtered_acyclic_complex_map_to_filtered_injective_is_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredKPlus C} (I : KPlus (FilteredInjectiveSubcategory C))
    (hK : filteredAcyclicPlusProperty C K)
    (f : K ⟶ (filteredInjectiveHomotopyInclusion C).obj I) :
    f = 0 := by
  sorry

theorem morphisms_into_filtered_injective_complex_bijective
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C}
    (I : KPlus (FilteredInjectiveSubcategory C))
    (α : K ⟶ L) (hα : filteredQuasiIso C α) :
    Nonempty ((L ⟶
        (filteredKPlusInclusion C).obj
          ((filteredInjectiveHomotopyInclusion C).obj I)) ≃+
      (K ⟶
        (filteredKPlusInclusion C).obj
          ((filteredInjectiveHomotopyInclusion C).obj I))) := by
  sorry

/- The second part of the source lemma identifies the same morphism group
   after passing to the filtered derived localization. -/
theorem morphisms_into_filtered_injective_complex_localized
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredHomotopyCategory C}
    (I : KPlus (FilteredInjectiveSubcategory C)) :
    Nonempty ((K ⟶
        (filteredKPlusInclusion C).obj
          ((filteredInjectiveHomotopyInclusion C).obj I)) ≃+
      ((filteredLocalizationFunctor C).obj K ⟶
        (filteredLocalizationFunctor C).obj
          ((filteredKPlusInclusion C).obj
            ((filteredInjectiveHomotopyInclusion C).obj I)))) := by
  sorry

/-! ## Left exact functors on finite filtered objects -/

/- The objectwise rule in the source sends each filtration subobject along
   the image of its monomorphism.  The antitone proof is categorical and does
   not require a second filtration API.  We intentionally do not assert a
   graded comparison here: the source warns that `gr (T(A))` need not be
   `T (gr A)` for this left-exact construction. -/
noncomputable def leftExactFilteredObject
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) (A : FilteredObject C) :
    FilteredObject D := by
  letI : PreservesFiniteLimits T := hT
  exact
    { carrier := T.obj A.carrier
      filtration :=
        { obj := fun p => Subobject.mk (T.map (A.filtration.obj p).arrow)
          antitone := by
            intro p q hpq
            apply Subobject.mk_le_mk_of_comm
              (T.map (Subobject.ofLE _ _ (A.filtration.antitone hpq)))
            rw [← T.map_comp, Subobject.ofLE_arrow] } }

structure LeftExactFilteredFunctorData
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) where
  functor : FiniteFilteredObject C ⥤ FiniteFilteredObject D
  additive : functor.Additive
  objectwise : ∀ A : FiniteFilteredObject C,
    (finiteFilteredInclusion D).obj (functor.obj A) =
      leftExactFilteredObject T hT
        ((finiteFilteredInclusion C).obj A)

theorem left_exact_filtered_functor_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    Nonempty (LeftExactFilteredFunctorData T hT) := by
  sorry

noncomputable def leftExactFilteredFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    FiniteFilteredObject C ⥤ FiniteFilteredObject D :=
  (Classical.choice (left_exact_filtered_functor_exists T hT)).functor

noncomputable instance leftExactFilteredFunctor_additive
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    (leftExactFilteredFunctor T hT).Additive :=
  (Classical.choice (left_exact_filtered_functor_exists T hT)).additive

theorem leftExactFilteredFunctor_objectwise
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) (A : FiniteFilteredObject C) :
    (finiteFilteredInclusion D).obj ((leftExactFilteredFunctor T hT).obj A) =
      leftExactFilteredObject T hT ((finiteFilteredInclusion C).obj A) :=
  (Classical.choice (left_exact_filtered_functor_exists T hT)).objectwise A

noncomputable def leftExactFilteredComplexFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    FilteredComplex C ⥤ FilteredComplex D :=
  (leftExactFilteredFunctor T hT).mapHomologicalComplex (ComplexShape.up ℤ)

noncomputable def leftExactFilteredComplexPlusFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    FilteredComplexPlus C ⥤ FilteredComplexPlus D :=
  (leftExactFilteredFunctor T hT).mapCochainComplexPlus

noncomputable def leftExactFilteredHomotopyFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    FilteredHomotopyCategory C ⥤ FilteredHomotopyCategory D :=
  additiveHomotopyFunctor (leftExactFilteredFunctor T hT)

noncomputable def leftExactFilteredHomotopyPlusFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    FilteredKPlus C ⥤ FilteredKPlus D :=
  additiveHomotopyPlusFunctor (leftExactFilteredFunctor T hT)

theorem left_exact_filtered_homotopy_functors_are_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    Nonempty (ExactTriangulatedFunctorData
      (leftExactFilteredHomotopyFunctor T hT)) ∧
      Nonempty (ExactTriangulatedFunctorData
        (leftExactFilteredHomotopyPlusFunctor T hT)) := by
  sorry

/-! ## Filtered additive extensions and filtered right derived functors -/

def mapGradedObject
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (T : C ⥤ D) : GradedObject ℤ C ⥤ GradedObject ℤ D where
  obj X p := T.obj (X p)
  map f p := T.map (f p)
  map_id X := by
    ext p
    exact T.map_id (X p)
  map_comp f g := by
    ext p
    exact T.map_comp (f p) (g p)

instance mapGradedObject_additive
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (T : C ⥤ D) [T.Additive] :
    (mapGradedObject T).Additive := by
  let eC : GradedObject ℤ C ≌ (Discrete ℤ ⥤ C) :=
    piEquivalenceFunctorDiscrete ℤ C
  let eD : GradedObject ℤ D ≌ (Discrete ℤ ⥤ D) :=
    piEquivalenceFunctorDiscrete ℤ D
  have hC : eC.functor.Additive :=
    eC.fullyFaithfulFunctor.additive_ofFullyFaithful
  have hD : eD.functor.Additive :=
    eD.fullyFaithfulFunctor.additive_ofFullyFaithful
  refine ⟨?_⟩
  intro X Y f g
  have h_source : ∀ p : ℤ, (f + g) p = f p + g p := by
    intro p
    have h := congrArg (fun a => a.app (Discrete.mk p))
      (hC.map_add (f := f) (g := g))
    exact h
  apply eD.fullyFaithfulFunctor.map_injective
  ext ⟨p⟩
  rw [hD.map_add]
  change T.map ((f + g) p) = T.map (f p) + T.map (g p)
  rw [h_source p, T.map_add]

noncomputable def filteredFunctorExtensionObject
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (I : FilteredInjectiveSubcategory C)
    (d : FilteredInjectiveDecomposition I.obj) :
    FiniteFilteredObject D := by
  let J : filteredInjectiveIndex d.lower d.upper → D :=
    fun n => T.obj (d.piece n)
  refine ⟨filteredInjectiveDirectSumObject J, ?_⟩
  exact filteredInjectiveDirectSumObject_isFinite J

structure FilteredFunctorExtensionData
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] where
  functor : FilteredInjectiveSubcategory C ⥤ FiniteFilteredObject D
  additive : functor.Additive
  decomposition_object : ∀ I,
    ∃ d : FilteredInjectiveDecomposition I.obj,
      Nonempty (functor.obj I ≅ filteredFunctorExtensionObject T I d)
  graded_iso : ∀ I,
    Nonempty ((finiteAssociatedGraded D).obj (functor.obj I) ≅
      (mapGradedObject T).obj ((associatedGraded (C := C)).obj I.obj.obj))
  underlying_iso : ∀ I,
    Nonempty ((finiteForgetful D).obj (functor.obj I) ≅
      T.obj ((finiteForgetful C).obj I.obj))

theorem filtered_functor_extension_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] :
    Nonempty (FilteredFunctorExtensionData T) := by
  sorry

noncomputable def filteredFunctorExtension
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] :
    FilteredInjectiveSubcategory C ⥤ FiniteFilteredObject D :=
  (Classical.choice (filtered_functor_extension_exists T)).functor

noncomputable instance filteredFunctorExtension_additive
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] :
    (filteredFunctorExtension T).Additive :=
  (Classical.choice (filtered_functor_extension_exists T)).additive

theorem filteredFunctorExtension_graded_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] (I : FilteredInjectiveSubcategory C) :
    Nonempty ((finiteAssociatedGraded D).obj ((filteredFunctorExtension T).obj I) ≅
      (mapGradedObject T).obj ((associatedGraded (C := C)).obj I.obj.obj)) := by
  exact (Classical.choice (filtered_functor_extension_exists T)).graded_iso I

noncomputable def filteredFunctorExtensionComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] :
    KPlus (FilteredInjectiveSubcategory C) ⥤ FilteredKPlus D :=
  additiveHomotopyPlusFunctor (filteredFunctorExtension T)

theorem filteredFunctorExtensionComplex_commutes_with_graded
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] :
    Nonempty
      (filteredFunctorExtensionComplex T ⋙ filteredKPlusInclusion D ⋙
          filteredAssociatedGradedHomotopyFunctor D ≅
        filteredInjectiveHomotopyInclusion C ⋙ filteredKPlusInclusion C ⋙
          filteredAssociatedGradedHomotopyFunctor C ⋙
            (mapGradedObject T).mapHomotopyCategory (ComplexShape.up ℤ)) := by
  sorry

theorem filteredFunctorExtensionComplex_commutes_with_forgetful
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] :
    Nonempty
      (filteredFunctorExtensionComplex T ⋙ filteredKPlusInclusion D ⋙
          filteredForgetfulHomotopyFunctor D ≅
        filteredInjectiveHomotopyInclusion C ⋙ filteredKPlusInclusion C ⋙
          filteredForgetfulHomotopyFunctor C ⋙
            T.mapHomotopyCategory (ComplexShape.up ℤ)) := by
  sorry

noncomputable def filteredRightDerivedFunctor
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) [T.Additive] :
    FilteredDerivedPlus C ⥤ FilteredDerivedPlus D :=
  filteredLocalizationQuasiInverse C ⋙
    filteredFunctorExtensionComplex T ⋙
    filteredPlusDerivedLocalizationFunctor D

/- The same filtered right-derived functor on the three source categories
   listed in the text. -/
noncomputable def filteredRightDerivedOnFilteredObjects
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) [T.Additive] :
    FiniteFilteredObject C ⥤ FilteredDerivedPlus D :=
  filteredSingleFunctor C ⋙
    HomotopyCategory.Plus.quotient (FiniteFilteredObject C) ⋙
    filteredPlusDerivedLocalizationFunctor C ⋙ filteredRightDerivedFunctor T

noncomputable def filteredRightDerivedOnFilteredComplexes
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) [T.Additive] :
    FilteredComplexPlus C ⥤ FilteredDerivedPlus D :=
  HomotopyCategory.Plus.quotient (FiniteFilteredObject C) ⋙
    filteredPlusDerivedLocalizationFunctor C ⋙ filteredRightDerivedFunctor T

noncomputable def filteredRightDerivedOnFilteredHomotopy
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) [T.Additive] :
    FilteredKPlus C ⥤ FilteredDerivedPlus D :=
  filteredPlusDerivedLocalizationFunctor C ⋙ filteredRightDerivedFunctor T

theorem filteredRightDerivedOnFilteredHomotopy_is_exact
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) [T.Additive] :
    Nonempty (ExactTriangulatedFunctorData
      (filteredRightDerivedOnFilteredHomotopy T)) := by
  sorry

theorem filteredRightDerivedFunctor_is_exact
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) [T.Additive] :
    Nonempty (ExactTriangulatedFunctorData (filteredRightDerivedFunctor T)) := by
  sorry

noncomputable def leftExactFilteredRightDerivedFunctor
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    FilteredDerivedPlus C ⥤ FilteredDerivedPlus D := by
  letI : T.Additive := left_or_right_exact_additive T (Or.inl hT)
  exact filteredRightDerivedFunctor T

theorem left_exact_filtered_right_derived_is_exact
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) (hT : IsLeftExact T) :
    Nonempty (ExactTriangulatedFunctorData
      (leftExactFilteredRightDerivedFunctor T hT)) := by
  sorry

theorem filtered_right_derived_restrictions_not_delta_objects :
    ∃ (C : Type u) (_ : Category.{u} C) (_ : Abelian C),
      ¬ Nonempty (Abelian (FiniteFilteredObject C)) :=
  finiteFilteredCategory_not_abelian

theorem filtered_right_derived_restrictions_not_delta_complexes
    (C : Type u) [Category.{v} C] [Abelian C] :
    ¬ Nonempty (Abelian (FilteredComplexPlus C)) := by
  sorry

structure FilteredRightDerivedFunctorComparisonData
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) [T.Additive] where
  graded : ∀ I : FilteredInjectiveSubcategory C,
    Nonempty ((finiteAssociatedGraded D).obj ((filteredFunctorExtension T).obj I) ≅
      (mapGradedObject T).obj
        ((associatedGraded (C := C)).obj I.obj.obj))
  underlying : ∀ I : FilteredInjectiveSubcategory C,
    Nonempty ((finiteForgetful D).obj ((filteredFunctorExtension T).obj I) ≅
      T.obj ((finiteForgetful C).obj I.obj))

theorem filteredRightDerivedFunctor_graded_and_forget_comparison
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) [T.Additive] :
    Nonempty (FilteredRightDerivedFunctorComparisonData T) := by
  sorry

/-! ## The filtered spectral sequence -/

noncomputable def filteredGradedComplexFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredComplexPlus C ⥤ CompPlus C :=
  (finiteGradedPieceFunctor C p).mapCochainComplexPlus

noncomputable def filteredDerivedE₁Term
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (T : C ⥤ D) (hT : IsLeftExact T)
    (K : FilteredComplexPlus C) (p q : ℤ) : D := by
  letI : T.Additive := left_or_right_exact_additive T (Or.inl hT)
  exact
    (DerivedCategory.Plus.homologyFunctor D (p + q)).obj
      ((leftExactRightDerivedComplexFunctor T hT).obj
        ((filteredGradedComplexFunctor C p).obj K))

structure FilteredSpectralPageChoiceIso
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {K K' : Formalization.Books.Homology.Unit24.FilteredComplex D}
    (S : FilteredComplexSpectralSequence K)
    (S' : FilteredComplexSpectralSequence K') (r : ℕ) where
  iso : S.page r ≅ S'.page r
  differential_commutes :
      iso.hom ≫ S'.differential r =
      S.differential r ≫ (bigradedShift r (-r + 1)).map iso.hom

noncomputable def filteredDerivedSpectralInput
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (T : C ⥤ D) (hT : IsLeftExact T)
    {K : FilteredComplexPlus C}
    (R : FilteredComplexInjectiveResolution K) :
    Formalization.Books.Homology.Unit24.FilteredComplex D := by
  letI : T.Additive := left_or_right_exact_additive T (Or.inl hT)
  exact
    (((finiteFilteredInclusion D).mapCochainComplexPlus).obj
      ((filteredFunctorExtension T).mapCochainComplexPlus.obj R.complex)).obj

noncomputable def filteredDerivedAbutment
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) (hT : IsLeftExact T)
    (K : FilteredComplexPlus C) (n : ℤ) : D := by
  letI : T.Additive := left_or_right_exact_additive T (Or.inl hT)
  exact
    (derivedCohomologyFunctor D n).obj
      ((filteredDerivedForgetfulFunctor D).obj
        (((filteredDerivedPlusProperty D).ι).obj
          ((filteredRightDerivedFunctor T).obj
            ((filteredPlusDerivedLocalizationFunctor C).obj
              ((HomotopyCategory.Plus.quotient (FiniteFilteredObject C)).obj K)))))

structure FilteredDerivedSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
  (T : C ⥤ D) (hT : IsLeftExact T)
    (K : FilteredComplexPlus C) where
  resolution : FilteredComplexInjectiveResolution K
  spectral_sequence :
    FilteredComplexSpectralSequence
      (filteredDerivedSpectralInput T hT resolution)
  first_page : ∀ p q : ℤ,
    Nonempty (spectral_sequence.page 1 (p, q) ≅ filteredDerivedE₁Term T hT K p q)
  bounded : filteredComplexBounded spectral_sequence
  converges :
    filteredComplexRegular spectral_sequence ∧
      filteredComplexAbuts (filteredDerivedSpectralInput T hT resolution) ∧
      FilteredComplexCohomologyComplete
        (filteredDerivedSpectralInput T hT resolution)
  finite_filtration : FilteredComplexCohomologyFiniteFiltration
      (filteredDerivedSpectralInput T hT resolution)
  abutment : ∀ n : ℤ,
    Nonempty ((filteredForgetful D).obj
      (filteredComplexCohomologyFilteredObject
        (filteredDerivedSpectralInput T hT resolution) n) ≅
      filteredDerivedAbutment T hT K n)

theorem filtered_derived_spectral_sequence_exists
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) (hT : IsLeftExact T)
    (K : FilteredComplexPlus C) :
    Nonempty (FilteredDerivedSpectralSequenceData T hT K) := by
  sorry

theorem filtered_derived_spectral_sequence_functorial
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) (hT : IsLeftExact T)
    {K L : FilteredComplexPlus C} (f : K ⟶ L)
    (Sₖ : FilteredDerivedSpectralSequenceData T hT K)
    (Sₗ : FilteredDerivedSpectralSequenceData T hT L) :
    Nonempty (FilteredComplexSpectralSequenceHom
      Sₖ.spectral_sequence Sₗ.spectral_sequence) := by
  sorry

theorem filtered_derived_spectral_sequence_choice_independent
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    [HasDerivedCategory.{w'} (GradedObject ℤ D)]
    (T : C ⥤ D) (hT : IsLeftExact T)
    {K : FilteredComplexPlus C}
    (S₁ S₂ : FilteredDerivedSpectralSequenceData T hT K)
    (r : ℕ) (hr : 1 ≤ r) :
    Nonempty (FilteredSpectralPageChoiceIso
      S₁.spectral_sequence S₂.spectral_sequence r) := by
  sorry

/-! ## The final filtration comparison remark -/

noncomputable def stupidFiltrationGradedModel
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : Formalization.Books.Derived.Unit11.BookComplex C) (p : ℤ) : Comp C :=
  (shiftFunctor (Comp C) (-p)).obj
    ((CochainComplex.singleFunctor C 0).obj (K.X p))

/- The displayed equality `R^(p+q)T(K^p[-p]) = R^qT(K^p)` is exposed as a
   source-facing term, using the established higher-derived-functor API. -/
noncomputable def stupidFiltrationDerivedE₁Term
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (T : C ⥤ D) (hT : IsLeftExact T)
    (K : Formalization.Books.Derived.Unit11.BookComplex C) (p q : ℤ) : D :=
  (higherRightDerivedFunctor T hT q).obj (K.X p)

structure StupidFiltrationComparison
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasCountableCoproducts D]
    (T : C ⥤ D) (hT : IsLeftExact T)
    {K : Formalization.Books.Derived.Unit11.BookComplex C} (hK : IsBoundedBelow K)
    (R : CartanEilenbergResolution K hK) where
  first_page : ∀ p q : ℤ,
    Nonempty
      ((cartanEilenbergFirstSpectralSequence T hT R).page 1 (p, q) ≅
        stupidFiltrationDerivedE₁Term T hT K p q)
  first_differential : ∀ p q : ℤ,
    ∃ e₀ :
        (cartanEilenbergFirstSpectralSequence T hT R).page 1 (p, q) ≅
          stupidFiltrationDerivedE₁Term T hT K p q,
    ∃ e₁ :
        (cartanEilenbergFirstSpectralSequence T hT R).page 1 (p + 1, q) ≅
          stupidFiltrationDerivedE₁Term T hT K (p + 1) q,
      e₀.inv ≫
          doubleComplexPageDifferential
            (cartanEilenbergFirstSpectralSequence T hT R) 1 p q ≫
          eqToHom (by congr 1; ring_nf) ≫ e₁.hom =
        (higherRightDerivedFunctor T hT q).map (K.d p (p + 1))

theorem stupid_filtration_comparison
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasCountableCoproducts D]
    (T : C ⥤ D) (hT : IsLeftExact T)
    {K : Formalization.Books.Derived.Unit11.BookComplex C} (hK : IsBoundedBelow K)
    (R : CartanEilenbergResolution K hK) :
    Nonempty (StupidFiltrationComparison T hT hK R) := by
  sorry

noncomputable def canonicalTruncationGradedModel
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : Formalization.Books.Derived.Unit11.BookComplex C) (p : ℤ) : Comp C :=
  (shiftFunctor (Comp C) p).obj
    ((CochainComplex.singleFunctor C 0).obj
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-p)).obj K))

/- The source's second-filtration index convention, with the derived term
   written in the `(p,q)` coordinates used by the filtered spectral sequence. -/
noncomputable def canonicalTruncationDerivedE₁Term
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (T : C ⥤ D) (hT : IsLeftExact T)
    (K : Formalization.Books.Derived.Unit11.BookComplex C) (p q : ℤ) : D :=
  (higherRightDerivedFunctor T hT (2 * p + q)).obj
    ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-p)).obj K)

theorem canonical_truncation_index_change (p q : ℤ) :
    (p + (p + q), -p) = (2 * p + q, -p) := by
  congr 1; ring

structure CanonicalTruncationFiltrationComparison
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasCountableCoproducts D]
    (T : C ⥤ D) (hT : IsLeftExact T)
    {K : Formalization.Books.Derived.Unit11.BookComplex C} (hK : IsBoundedBelow K)
    (R : CartanEilenbergResolution K hK) where
  second_page : ∀ p q : ℤ,
    Nonempty
      ((cartanEilenbergSecondSpectralSequence T hT R).page 2
          (2 * p + q, -p) ≅
        canonicalTruncationDerivedE₁Term T hT K p q)
  index_change : ∀ p q : ℤ,
    (p + (p + q), -p) = (2 * p + q, -p)
  canonical_differential : ∀ p q : ℤ,
    canonicalTruncationDerivedE₁Term T hT K p q ⟶
      canonicalTruncationDerivedE₁Term T hT K (p + 1) q
  differential_comparison : ∀ p q : ℤ,
    ∃ e₀ :
        (cartanEilenbergSecondSpectralSequence T hT R).page 2
            (2 * p + q, -p) ≅
          canonicalTruncationDerivedE₁Term T hT K p q,
    ∃ e₁ :
        (cartanEilenbergSecondSpectralSequence T hT R).page 2
            (2 * (p + 1) + q, -(p + 1)) ≅
          canonicalTruncationDerivedE₁Term T hT K (p + 1) q,
      e₀.inv ≫
          doubleComplexPageDifferential
            (cartanEilenbergSecondSpectralSequence T hT R) 2
            (2 * p + q) (-p) ≫
          eqToHom (by congr 1; ring_nf) ≫ e₁.hom =
        canonical_differential p q

theorem canonical_truncation_filtration_comparison
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [HasCountableCoproducts D]
    (T : C ⥤ D) (hT : IsLeftExact T)
    {K : Formalization.Books.Derived.Unit11.BookComplex C} (hK : IsBoundedBelow K)
    (R : CartanEilenbergResolution K hK) :
    Nonempty (CanonicalTruncationFiltrationComparison T hT hK R) := by
  sorry

structure CartanEilenbergFilteredResolutionComparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : CompPlus C) where
  resolution : CartanEilenbergResolution K.obj K.2
  first_filtration_resolution :
    Formalization.Books.Homology.Unit24.FilteredComplex C
  second_filtration_resolution :
    Formalization.Books.Homology.Unit24.FilteredComplex C
  first_filtration_is_total :
    first_filtration_resolution =
      doubleComplexFirstFilteredTotal resolution.doubleComplex
  second_filtration_is_total :
    second_filtration_resolution =
      doubleComplexSecondFilteredTotal resolution.doubleComplex

theorem cartan_eilenberg_filtered_resolution_comparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    [EnoughInjectives C] (K : CompPlus C) :
    Nonempty (CartanEilenbergFilteredResolutionComparison K) := by
  sorry

end Formalization.Books.Derived.Unit26
