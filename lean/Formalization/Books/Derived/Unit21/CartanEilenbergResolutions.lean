import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Derived.Unit18.InjectiveResolutions
import Formalization.Books.Derived.Unit20.HigherDerivedFunctors
import Formalization.Books.Homology.Unit18.DoubleComplexes
import Formalization.Books.Homology.Unit25.DoubleComplexes

/-!
# Derived Categories, Chapter 21: Cartan–Eilenberg resolutions

The source's Cartan–Eilenberg resolution is expressed using the canonical
double-complex, homology, injective-complex-resolution, and filtered-complex
spectral-sequence interfaces developed in the preceding chapters.

The source also notes that non-injective resolutions and some unbounded cases
can be treated in broader settings; this file formalizes the bounded-below
injective case stated by its definition and existence lemma.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit18
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit18
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit24
open Formalization.Books.Homology.Unit25
open scoped ZeroObject

universe v u v' u' w w'

namespace Formalization.Books.Derived.Unit21

/-! ## The complexes occurring in a Cartan–Eilenberg resolution -/

/-- The cohomology object of a cochain complex in a specified degree. -/
abbrev cohomologyObject
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : BookComplex A) (p : ℤ) : A :=
  K.homology p

/-- The complex `H_I^p(I^{\bullet,\bullet})`, obtained by taking horizontal
cohomology of the rows of a double complex. -/
abbrev horizontalCohomologyComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : DoubleComplex A) (p : ℤ) : BookComplex A :=
  (HomologicalComplex.homologyFunctor (CochainComplex A ℤ)
      (ComplexShape.up ℤ) p).obj (columnsAsComplex I)

/-! ## Maps of double complexes -/

/-- The map of rows induced by a map of double complexes. -/
def doubleComplexMapRow
    {A : Type u} [Category.{v} A] [Preadditive A]
    {I J : DoubleComplex A} (f : DoubleComplexMap I J) (q : ℤ) :
    row I q ⟶ row J q where
  f p := f.f p q
  comm' p r hpr := by
    have hpr' : p + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hpr
    subst r
    simpa [row] using (f.comm1 p q).symm

/-- The map of columns induced by a map of double complexes. -/
def doubleComplexMapColumn
    {A : Type u} [Category.{v} A] [Preadditive A]
    {I J : DoubleComplex A} (f : DoubleComplexMap I J) (p : ℤ) :
    column I p ⟶ column J p where
  f q := f.f p q
  comm' q r hqr := by
    have hqr' : q + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hqr
    subst r
    simpa [column] using (f.comm2 p q).symm

/-- Applying an additive functor termwise to a double complex. -/
def mapDoubleComplex
    {A : Type u} [Category.{v} A] [Preadditive A]
    {B : Type u'} [Category.{v'} B] [Preadditive B]
    (F : A ⥤ B) (hF : F.Additive) (I : DoubleComplex A) : DoubleComplex B := by
  letI : F.Additive := hF
  exact
    { obj := fun p q => F.obj (I.obj p q)
      d1 := fun p q => F.map (I.d1 p q)
      d2 := fun p q => F.map (I.d2 p q)
      d1_sq := fun p q => by
        simpa only [Functor.map_comp, Functor.map_zero] using
          congrArg F.map (I.d1_sq p q)
      d2_sq := fun p q => by
        simpa only [Functor.map_comp, Functor.map_zero] using
          congrArg F.map (I.d2_sq p q)
      comm := fun p q => by
        simpa only [Functor.map_comp] using congrArg F.map (I.comm p q) }

/-! ## The Cartan–Eilenberg resolution -/

/-- A Cartan–Eilenberg resolution of a bounded-below cochain complex.

The maps out of the degree-zero complexes make the augmentations implicit in
the phrase “is an injective resolution” explicit.  Their degree-zero terms
are required to be the components of the source augmentation.  Kernels,
images, and horizontal cohomology are the canonical complexes in the abelian
category of cochain complexes.
-/
structure CartanEilenbergResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : BookComplex A) (hK : IsBoundedBelow K) where
  /-- The underlying double complex `I^{p,q}`. -/
  doubleComplex : DoubleComplex A
  /-- The augmentation `K^\bullet → I^{\bullet,0}`. -/
  augmentation : K ⟶ row doubleComplex 0
  /-- The double complex is bounded below in its first index. -/
  horizontal_support :
    ∃ i : ℤ, ∀ p : ℤ, p < i → ∀ q : ℤ, IsZero (doubleComplex.obj p q)
  /-- The double complex is zero in negative vertical degrees. -/
  vertical_support :
    ∀ p q : ℤ, q < 0 → IsZero (doubleComplex.obj p q)
  /-- Every column resolves the corresponding term of `K`. -/
  vertical_resolution :
    ∀ p : ℤ, ∃ ι : (CochainComplex.singleFunctor A 0).obj (K.X p) ⟶
        column doubleComplex p,
      ι.f 0 = augmentation.f p ∧
        IsComplexInjectiveResolution
          ((CochainComplex.singleFunctor A 0).obj (K.X p))
          (column doubleComplex p) ι
  /-- The kernel of each horizontal differential resolves the corresponding
  kernel in `K`. -/
  kernel_resolution :
    ∀ p : ℤ, ∃ ι :
        (CochainComplex.singleFunctor A 0).obj
          (kernel (K.d p (p + 1))) ⟶
        kernel (columnMap doubleComplex p),
      IsComplexInjectiveResolution
        ((CochainComplex.singleFunctor A 0).obj
          (kernel (K.d p (p + 1))))
        (kernel (columnMap doubleComplex p)) ι
  /-- The image of each horizontal differential resolves the corresponding
  image in `K`. -/
  image_resolution :
    ∀ p : ℤ, ∃ ι :
        (CochainComplex.singleFunctor A 0).obj
          (Abelian.image (K.d p (p + 1))) ⟶
        Abelian.image (columnMap doubleComplex p),
      IsComplexInjectiveResolution
        ((CochainComplex.singleFunctor A 0).obj
          (Abelian.image (K.d p (p + 1))))
        (Abelian.image (columnMap doubleComplex p)) ι
  /-- The horizontal cohomology complex resolves the corresponding
  cohomology object of `K`. -/
  horizontal_cohomology_resolution :
    ∀ p : ℤ, ∃ ι :
        (CochainComplex.singleFunctor A 0).obj (cohomologyObject K p) ⟶
        horizontalCohomologyComplex doubleComplex p,
      IsComplexInjectiveResolution
        ((CochainComplex.singleFunctor A 0).obj (cohomologyObject K p))
        (horizontalCohomologyComplex doubleComplex p) ι

/-- A Cartan–Eilenberg resolution exists in an abelian category with enough
injectives. -/
theorem cartanEilenbergResolution_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {K : BookComplex A} (hK : IsBoundedBelow K) :
    Nonempty (CartanEilenbergResolution K hK) := by
  sorry

/-- The support conditions of a Cartan–Eilenberg resolution give finite
support on every diagonal of its double complex. -/
theorem cartanEilenbergResolution_hasFiniteDiagonalSupport
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : BookComplex A} {hK : IsBoundedBelow K}
    (R : CartanEilenbergResolution K hK) :
    HasFiniteDiagonalSupport R.doubleComplex := by
  sorry

/-! ## The two spectral sequences after applying a functor -/

/-- The first spectral sequence associated to `F(I^{\bullet,\bullet})`.
The local additivity instance is the canonical consequence of left exactness.
-/
noncomputable def cartanEilenbergFirstSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasCountableCoproducts B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {K : BookComplex A} {hK : IsBoundedBelow K}
    (R : CartanEilenbergResolution K hK) :
    FilteredComplexSpectralSequence
      (doubleComplexFirstFilteredTotal
        (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
          R.doubleComplex)) := by
  exact doubleComplexFirstSpectralSequence
    (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
      R.doubleComplex)

/-- The second spectral sequence associated to `F(I^{\bullet,\bullet})`.
The local additivity instance is the canonical consequence of left exactness.
-/
noncomputable def cartanEilenbergSecondSpectralSequence
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasCountableCoproducts B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {K : BookComplex A} {hK : IsBoundedBelow K}
    (R : CartanEilenbergResolution K hK) :
    FilteredComplexSpectralSequence
      (doubleComplexSecondFilteredTotal
        (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
          R.doubleComplex)) := by
  exact doubleComplexSecondSpectralSequence
    (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
      R.doubleComplex)

/-- The general double-complex page formulas, including the `d₁` maps and the
sign convention for the second spectral sequence, applied to a
Cartan–Eilenberg resolution after `F`. -/
theorem cartanEilenberg_spectral_sequence_terms
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasCountableCoproducts B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {K : BookComplex A} {hK : IsBoundedBelow K}
    (R : CartanEilenbergResolution K hK) :
    DoubleComplexFirstSpectralSequenceTerms
        (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
          R.doubleComplex)
        (cartanEilenbergFirstSpectralSequence F hF R) ∧
      DoubleComplexSecondSpectralSequenceTerms
        (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
          R.doubleComplex)
        (cartanEilenbergSecondSpectralSequence F hF R) := by
  simpa [cartanEilenbergFirstSpectralSequence,
    cartanEilenbergSecondSpectralSequence] using
    (doubleComplex_spectral_sequence_terms
      (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
        R.doubleComplex))

/-- The cohomology object `H^n(RF(K))`, using the canonical bounded-below
right-derived functor from Chapter 20. -/
noncomputable def cartanEilenbergRightDerivedCohomology
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {K : BookComplex A} (hK : IsBoundedBelow K) (n : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B n).obj
    ((leftExactRightDerivedComplexFunctor F hF).obj ⟨K, hK⟩)

/-- The page formulas, boundedness, convergence, finite filtrations, and
abutment identification asserted for the two spectral sequences of a
Cartan–Eilenberg resolution. -/
structure CartanEilenbergSpectralSequenceData
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [HasCountableCoproducts B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {K : BookComplex A} (hK : IsBoundedBelow K)
    (R : CartanEilenbergResolution K hK) : Prop where
  /-- `{}'E_1^{p,q} = R^qF(K^p)`. -/
  first_page :
    ∀ p q : ℤ,
      Nonempty
        ((cartanEilenbergFirstSpectralSequence F hF R).page 1 (p, q) ≅
          (higherRightDerivedFunctor F hF q).obj (K.X p))
  /-- The first `d₁` is induced by the differential of `K`. -/
  first_differential :
    ∀ p q : ℤ,
      ∃ e₀ :
          (cartanEilenbergFirstSpectralSequence F hF R).page 1 (p, q) ≅
            (higherRightDerivedFunctor F hF q).obj (K.X p),
      ∃ e₁ :
          (cartanEilenbergFirstSpectralSequence F hF R).page 1 (p + 1, q) ≅
            (higherRightDerivedFunctor F hF q).obj (K.X (p + 1)),
        e₀.inv ≫
            doubleComplexPageDifferential
              (cartanEilenbergFirstSpectralSequence F hF R) 1 p q ≫
            eqToHom (by congr 1; ring_nf) ≫ e₁.hom =
          (higherRightDerivedFunctor F hF q).map (K.d p (p + 1))
  /-- `{}''E_2^{p,q} = R^pF(H^q(K^\bullet))`. -/
  second_page :
    ∀ p q : ℤ,
      Nonempty
        ((cartanEilenbergSecondSpectralSequence F hF R).page 2 (p, q) ≅
          (higherRightDerivedFunctor F hF p).obj (cohomologyObject K q))
  /-- The first page of the second sequence is the functor applied to the
  horizontal cohomology complex. -/
  second_first_page :
    ∀ p q : ℤ,
      Nonempty
        ((cartanEilenbergSecondSpectralSequence F hF R).page 1 (p, q) ≅
          F.obj ((horizontalCohomologyComplex R.doubleComplex q).X p))
  /-- The second-sequence `d₁` has the standard `(-1)^q` sign. -/
  second_differential :
    ∀ p q : ℤ,
      ∃ e₀ :
          (cartanEilenbergSecondSpectralSequence F hF R).page 1 (p, q) ≅
            F.obj ((horizontalCohomologyComplex R.doubleComplex q).X p),
      ∃ e₁ :
          (cartanEilenbergSecondSpectralSequence F hF R).page 1 (p + 1, q) ≅
            F.obj ((horizontalCohomologyComplex R.doubleComplex q).X (p + 1)),
        e₀.inv ≫
            doubleComplexPageDifferential
              (cartanEilenbergSecondSpectralSequence F hF R) 1 p q ≫
            eqToHom (by congr 1; ring_nf) ≫ e₁.hom =
          q.negOnePow • F.map
            ((horizontalCohomologyComplex R.doubleComplex q).d p (p + 1))
  /-- Both spectral sequences are bounded. -/
  bounded :
    filteredComplexBounded (cartanEilenbergFirstSpectralSequence F hF R) ∧
      filteredComplexBounded (cartanEilenbergSecondSpectralSequence F hF R)
  /-- Both spectral sequences converge in the filtered-complex sense. -/
  converges :
    filteredComplexConverges
        (doubleComplexFirstFilteredTotal
          (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
            R.doubleComplex)) ∧
      filteredComplexConverges
        (doubleComplexSecondFilteredTotal
          (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
            R.doubleComplex))
  /-- The induced filtrations on every abutment cohomology object are finite. -/
  finite_filtration :
    FilteredComplexCohomologyFiniteFiltration
        (doubleComplexFirstFilteredTotal
          (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
            R.doubleComplex)) ∧
      FilteredComplexCohomologyFiniteFiltration
        (doubleComplexSecondFilteredTotal
          (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
            R.doubleComplex))
  /-- Both filtered total cohomologies identify with `H^n(RF(K))`. -/
  abutment :
    ∀ n : ℤ,
      Nonempty
          (doubleComplexFirstTotalCohomology
              (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
                R.doubleComplex) n ≅
            cartanEilenbergRightDerivedCohomology F hF hK n) ∧
        Nonempty
          (doubleComplexSecondTotalCohomology
              (mapDoubleComplex F (left_or_right_exact_additive F (Or.inl hF))
                R.doubleComplex) n ≅
            cartanEilenbergRightDerivedCohomology F hF hK n)

/-- The two spectral sequences of a Cartan–Eilenberg resolution have the page
formulas and convergence properties in the source lemma. -/
theorem cartanEilenberg_two_spectral_sequences
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [HasCountableCoproducts B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {K : BookComplex A} (hK : IsBoundedBelow K)
    (R : CartanEilenbergResolution K hK) :
    CartanEilenbergSpectralSequenceData F hF hK R := by
  sorry

/-! ## Functoriality -/

/-- A morphism of Cartan–Eilenberg resolutions over a map of complexes. -/
structure CartanEilenbergResolutionMap
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} {hK : IsBoundedBelow K} {hL : IsBoundedBelow L}
    (R : CartanEilenbergResolution K hK)
    (S : CartanEilenbergResolution L hL) (f : K ⟶ L) where
  doubleComplexMap : DoubleComplexMap R.doubleComplex S.doubleComplex
  augmentation_naturality :
    f ≫ S.augmentation = R.augmentation ≫
      doubleComplexMapRow doubleComplexMap 0

/-- The two spectral sequences are functorial in the complex, once the usual
map of Cartan–Eilenberg resolutions has been chosen. -/
theorem cartanEilenberg_spectral_sequences_functorial
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasCountableCoproducts B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {K L : BookComplex A} {hK : IsBoundedBelow K} {hL : IsBoundedBelow L}
    (R : CartanEilenbergResolution K hK)
    (S : CartanEilenbergResolution L hL) (f : K ⟶ L)
    (h : CartanEilenbergResolutionMap R S f) :
    Nonempty
        (FilteredComplexSpectralSequenceHom
          (cartanEilenbergFirstSpectralSequence F hF R)
          (cartanEilenbergFirstSpectralSequence F hF S)) ∧
      Nonempty
        (FilteredComplexSpectralSequenceHom
          (cartanEilenbergSecondSpectralSequence F hF R)
          (cartanEilenbergSecondSpectralSequence F hF S)) := by
  sorry

end Formalization.Books.Derived.Unit21
