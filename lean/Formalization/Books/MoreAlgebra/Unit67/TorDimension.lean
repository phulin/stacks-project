import Formalization.Books.MoreAlgebra.Unit56.DerivedCategoriesOfModules
import Formalization.Books.MoreAlgebra.Unit59.DerivedTensorProduct
import Formalization.Books.MoreAlgebra.Unit63.ProductsAndTor
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Order.Interval.Set.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# More on Algebra, Chapter 67: Tor dimension

The source's tor-amplitude and tor-dimension predicates are stated using the
canonical derived category, cohomology, K-flat, and derived-tensor interfaces
from the preceding chapters.  This file also records the localization and
change-of-rings interfaces used by the later lemmas in the section.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit57
open Formalization.Books.MoreAlgebra.Unit58
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit63

universe w u

namespace Formalization.Books.MoreAlgebra.Unit67

/-! ## Tor amplitude and tor dimension -/

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := CochainComplex (Mod R) ℤ

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := DerivedCategory (Mod R)

noncomputable abbrev derivedCohomology
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (i : ℤ) : D R ⥤ Mod R :=
  derivedCohomologyFunctor (Mod R) i

/- The degree-zero stalk of a module in the derived category. -/
noncomputable abbrev moduleInDerived
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) : D R :=
  (DerivedCategory.singleFunctor (Mod R) 0).obj M

/- The source's interval convention is represented by `Set.Icc` in `ℤ`. -/
def TorAmplitude
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a b : ℤ) : Prop :=
  ∀ (M : Mod R) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((derivedCohomology R i).obj (derivedTensor K (moduleInDerived R M)))

def TorAmplitudeBelow
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a : ℤ) : Prop :=
  ∀ (M : Mod R) (i : ℤ), i < a →
    IsZero ((derivedCohomology R i).obj (derivedTensor K (moduleInDerived R M)))

def HasFiniteTorDimension
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : Prop :=
  ∃ a b : ℤ, TorAmplitude R K a b

def ModuleTorAmplitude
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) (a b : ℤ) : Prop :=
  TorAmplitude R (moduleInDerived R M) a b

def ModuleTorDimensionLE
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) (d : ℕ) : Prop :=
  TorAmplitude R (moduleInDerived R M) (-((d : ℤ))) 0

def ModuleHasFiniteTorDimension
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) : Prop :=
  HasFiniteTorDimension R (moduleInDerived R M)

theorem finite_tor_dimension_bounded
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {K : D R}
    (hK : HasFiniteTorDimension R K) :
    derivedBoundedProperty (Mod R) K := by
  sorry

/-! ## Flat representatives -/

def IsSupportedIn
    {R : Type u} [CommRing R] (K : Comp R) (a b : ℤ) : Prop :=
  ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)

def IsSupportedBelow
    {R : Type u} [CommRing R] (K : Comp R) (a : ℤ) : Prop :=
  ∀ i : ℤ, i < a → IsZero (K.X i)

/- A finite flat resolution is a flat cochain complex supported in
   `[-d, 0]`, together with its quasi-isomorphic augmentation to the stalk. -/
structure FlatResolution
    {R : Type u} [CommRing R] (M : Mod R) (d : ℕ) where
  complex : Comp R
  flat : TermwiseFlat complex
  support : IsSupportedIn complex (-((d : ℤ))) 0
  augmentation : complex ⟶
    (CochainComplex.singleFunctor (Mod R) 0).obj M
  quasiIso : QuasiIso augmentation

noncomputable def CokerDifferential
    {R : Type u} [CommRing R] (K : Comp R) (i : ℤ) : Mod R :=
  CategoryTheory.Limits.cokernel (K.d i (i + 1))

theorem coker_d_flat_of_tor_amplitude
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : Comp R) (a b : ℤ) (hK : IsBoundedAbove K)
    (hflat : TermwiseFlat K) (hamp : TorAmplitude R
      ((derivedComplexQuotient R).obj K) a b) :
    Module.Flat R (CokerDifferential K (a - 1) : Type u) := by
  sorry

theorem tor_amplitude_iff_bounded_flat_complex
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a b : ℤ) :
    TorAmplitude R K a b ↔
      ∃ E : Comp R, TermwiseFlat E ∧ IsSupportedIn E a b ∧
        Nonempty ((derivedComplexQuotient R).obj E ≅ K) := by
  sorry

theorem tor_amplitude_below_iff_bounded_below_flat_kFlat_complex
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a : ℤ) :
    TorAmplitudeBelow R K a ↔
      ∃ E : Comp R, IsKFlat E ∧ TermwiseFlat E ∧
        IsSupportedBelow E a ∧
        Nonempty ((derivedComplexQuotient R).obj E ≅ K) := by
  sorry

/-! ## Triangles, resolutions, summands, and finite complexes -/

theorem tor_amplitude_of_distinguished_triangle₁₂
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (T : Triangle (D R)) (hT : T ∈ distTriang (D R))
    (a b : ℤ) (h₁ : TorAmplitude R T.obj₁ (a + 1) (b + 1))
    (h₂ : TorAmplitude R T.obj₂ a b) :
    TorAmplitude R T.obj₃ a b := by
  sorry

theorem tor_amplitude_of_distinguished_triangle₁₃
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (T : Triangle (D R)) (hT : T ∈ distTriang (D R))
    (a b : ℤ) (h₁ : TorAmplitude R T.obj₁ a b)
    (h₃ : TorAmplitude R T.obj₃ a b) :
    TorAmplitude R T.obj₂ a b := by
  sorry

theorem tor_amplitude_of_distinguished_triangle₂₃
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (T : Triangle (D R)) (hT : T ∈ distTriang (D R))
    (a b : ℤ) (h₂ : TorAmplitude R T.obj₂ (a + 1) (b + 1))
    (h₃ : TorAmplitude R T.obj₃ a b) :
    TorAmplitude R T.obj₁ (a + 1) (b + 1) := by
  sorry

theorem module_tor_dimension_le_iff_flat_resolution
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) (d : ℕ) :
    ModuleTorDimensionLE R M d ↔ Nonempty (FlatResolution M d) := by
  sorry

theorem module_tor_dimension_zero_iff_flat
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) :
    ModuleTorDimensionLE R M 0 ↔ Module.Flat R (M : Type u) := by
  sorry

theorem tor_amplitude_of_biprod
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {K L : D R} (a b : ℤ)
    (hKL : TorAmplitude R (K ⊞ L) a b) :
    TorAmplitude R K a b ∧ TorAmplitude R L a b := by
  sorry

theorem tor_amplitude_of_bounded_complex
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : Comp R) (a b : ℤ)
    (hK : IsBounded K)
    (hterms : ∀ i : ℤ, ModuleTorAmplitude R (K.X i) (a - i) (b - i)) :
    TorAmplitude R ((derivedComplexQuotient R).obj K) a b := by
  sorry

theorem finite_tor_dimension_of_bounded_complex
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : Comp R) (hK : IsBounded K)
    (hterms : ∀ i : ℤ, ModuleHasFiniteTorDimension R (K.X i)) :
    HasFiniteTorDimension R ((derivedComplexQuotient R).obj K) := by
  sorry

theorem tor_amplitude_of_bounded_derived_object
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a b : ℤ)
    (hK : derivedBoundedProperty (Mod R) K)
    (hcoh : ∀ i : ℤ,
      ModuleTorAmplitude R ((derivedCohomology R i).obj K) (a - i) (b - i)) :
    TorAmplitude R K a b := by
  sorry

theorem finite_tor_dimension_of_bounded_derived_object
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R)
    (hK : derivedBoundedProperty (Mod R) K)
    (hcoh : ∀ i : ℤ,
      ModuleHasFiniteTorDimension R ((derivedCohomology R i).obj K)) :
    HasFiniteTorDimension R K := by
  sorry

/-! ## Base rings and derived tensor products -/

structure DerivedTensorOverBaseData
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B) where
  functor : (D B × D B) ⥤ D A
  represented : ∀ X Y : D B, ∃ K L : Comp B,
    Nonempty ((derivedComplexQuotient B).obj K ≅ X) ∧
    Nonempty ((derivedComplexQuotient B).obj L ≅ Y) ∧
    IsKFlat K ∧ IsKFlat L ∧
    Nonempty (functor.obj (X, Y) ≅
      (derivedComplexQuotient A).obj
        (restrictScalarsComplex f (tensorProductComplex B K L)))

theorem exists_derivedTensorOverBaseData
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B) :
    Nonempty (DerivedTensorOverBaseData f) := by
  sorry

noncomputable def derivedTensorOverBaseData
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B) :
    DerivedTensorOverBaseData f :=
  Classical.choice (exists_derivedTensorOverBaseData f)

noncomputable abbrev derivedTensorOverBase
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B)
    (X Y : D B) : D A :=
  (derivedTensorOverBaseData f).functor.obj (X, Y)

def TorAmplitudeAsBase
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] (f : A →+* B)
    (K : Comp B) (a b : ℤ) : Prop :=
  TorAmplitude A
    ((derivedComplexQuotient A).obj (restrictScalarsComplex f K)) a b

theorem tor_amplitude_push
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B)
    (K L : Comp B) (a b c d : ℤ)
    (hK : TorAmplitude B ((derivedComplexQuotient B).obj K) a b)
    (hL : TorAmplitudeAsBase f L c d) :
    TorAmplitude A (derivedTensorOverBase f
      ((derivedComplexQuotient B).obj K)
      ((derivedComplexQuotient B).obj L)) (a + c) (b + d) := by
  sorry

theorem tor_amplitude_push_of_flat
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B)
    (hflat : RingHom.Flat f) (K : Comp B) (a b : ℤ)
    (hK : TorAmplitude B ((derivedComplexQuotient B).obj K) a b) :
    TorAmplitudeAsBase f K a b := by
  sorry

theorem tor_amplitude_push_of_finite_tor_dimension
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B) (d : ℕ)
    (hB : ModuleTorDimensionLE A
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) d)
    (K : Comp B) (a b : ℤ)
    (hK : TorAmplitude B ((derivedComplexQuotient B).obj K) a b) :
    TorAmplitudeAsBase f K (a - (d : ℤ)) b := by
  sorry

theorem tor_amplitude_pull
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B)
    (K : Comp A) (a b : ℤ)
    (hK : TorAmplitude A ((derivedComplexQuotient A).obj K) a b) :
    TorAmplitude B
      ((derivedBaseChange f).obj ((derivedComplexQuotient A).obj K)) a b := by
  sorry

theorem flat_base_change_module_tor_dimension
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)]
    [HasDerivedCategory.{w} (Mod B)] (f : A →+* B)
    (hflat : RingHom.Flat f) (d : ℕ) (M : Mod A)
    (hM : ModuleTorDimensionLE A M d) :
    ModuleTorDimensionLE B ((ModuleCat.extendScalars f).obj M) d := by
  sorry

/-! ## Localization -/

structure LocalizedRingMapData
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (q : PrimeSpectrum B) where
  map : Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal →+*
    Localization.AtPrime q.asIdeal
  commutes : ∀ a : A,
    map (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal) a) =
      algebraMap B (Localization.AtPrime q.asIdeal) (f a)

theorem exists_localizedRingMapData
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (q : PrimeSpectrum B) :
    Nonempty (LocalizedRingMapData f q) := by
  sorry

noncomputable def localizedRingMapData
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (q : PrimeSpectrum B) :
    LocalizedRingMapData f q :=
  Classical.choice (exists_localizedRingMapData f q)

noncomputable def localizedComplexAtPrime
    {B : Type u} [CommRing B] (K : Comp B) (q : PrimeSpectrum B) :
    CochainComplex (ModuleCat.{u} (Localization.AtPrime q.asIdeal)) ℤ :=
  ((ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl).mapHomologicalComplex
    (.up ℤ)).obj K

noncomputable def localizedComplexAtPrimeAsBase
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (K : Comp B) (q : PrimeSpectrum B) :
    CochainComplex
      (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal)) ℤ :=
  ((ModuleCat.restrictScalars (localizedRingMapData f q).map).mapHomologicalComplex
    (.up ℤ)).obj (localizedComplexAtPrime K q)

def TorAmplitudeAtPrime
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (K : Comp B) (q : PrimeSpectrum B)
    [HasDerivedCategory.{w} (ModuleCat.{u}
      (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal))]
    (a b : ℤ) : Prop :=
  TorAmplitude (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal)
    ((derivedComplexQuotient _).obj (localizedComplexAtPrimeAsBase f K q)) a b

def TorAmplitudeAtMaximal
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (K : Comp B) (q : MaximalSpectrum B)
    [HasDerivedCategory.{w} (ModuleCat.{u}
      (Localization.AtPrime
        (PrimeSpectrum.comap f (MaximalSpectrum.toPrimeSpectrum q)).asIdeal))]
    (a b : ℤ) : Prop :=
  TorAmplitudeAtPrime f K (MaximalSpectrum.toPrimeSpectrum q) a b

theorem tor_amplitude_localization_iff
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] (f : A →+* B) (K : Comp B)
    (hprime : ∀ q : PrimeSpectrum B,
      HasDerivedCategory.{w} (ModuleCat.{u}
        (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal)))
    (hmax : ∀ q : MaximalSpectrum B,
      HasDerivedCategory.{w} (ModuleCat.{u}
        (Localization.AtPrime
          (PrimeSpectrum.comap f (MaximalSpectrum.toPrimeSpectrum q)).asIdeal)))
    (a b : ℤ) :
    List.TFAE [
      TorAmplitudeAsBase f K a b,
      ∀ q : PrimeSpectrum B,
        letI := hprime q
        TorAmplitudeAtPrime f K q a b,
      ∀ q : MaximalSpectrum B,
        letI := hmax q
        TorAmplitudeAtMaximal f K q a b] := by
  sorry

noncomputable def localizedComplexAway
    {R : Type u} [CommRing R] (K : Comp R) (f : R) :
    CochainComplex (ModuleCat.{u} (Localization.Away f)) ℤ :=
  ((ModuleCat.localizedModuleFunctor (Submonoid.powers f)).mapHomologicalComplex
    (.up ℤ)).obj K

def TorAmplitudeAway
    {R : Type u} [CommRing R] (K : Comp R) (f : R)
    [HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away f))]
    (a b : ℤ) : Prop :=
  TorAmplitude (Localization.Away f)
    ((derivedComplexQuotient _).obj (localizedComplexAway K f)) a b

theorem tor_amplitude_glue
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : Comp R) (f : Fin n → R)
    (hunit : Ideal.span (Set.range f) = ⊤)
    (hlocalDC : ∀ i : Fin n,
      HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away (f i))))
    (a b : ℤ)
    (hlocal : ∀ i : Fin n,
      letI := hlocalDC i
      TorAmplitudeAway K (f i) a b) :
    TorAmplitude R ((derivedComplexQuotient R).obj K) a b := by
  sorry

theorem tor_amplitude_flat_descent
    {R R' : Type u} [CommRing R] [CommRing R']
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod R')] (f : R →+* R')
    (hfaithful : RingHom.FaithfullyFlat f) (K : Comp R) (a b : ℤ)
    (hK : TorAmplitude R'
      ((derivedComplexQuotient R').obj (baseChangeComplex f K)) a b) :
    TorAmplitude R ((derivedComplexQuotient R).obj K) a b := by
  sorry

theorem tor_amplitude_no_change_under_faithfully_flat_extension
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (f : R →+* A) (g : A →+* B) (hfaithful : RingHom.FaithfullyFlat g)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    TorAmplitudeAsBase f K a b ↔
      TorAmplitudeAsBase (g.comp f)
        (baseChangeComplex g K) a b := by
  sorry

/-! ## Finite global dimension and nilpotent reduction -/

/- The earlier Mathlib projective-dimension API supplies the canonical
   meaning of a finite global-dimension bound. -/
def HasGlobalDimensionLE (R : Type u) [Ring R] (d : ℕ) : Prop :=
  ∀ M : ModuleCat.{u} R, CategoryTheory.HasProjectiveDimensionLE M d

theorem finite_global_dimension_tor_dimension
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (d : ℕ)
    (hR : HasGlobalDimensionLE R d) :
    ∀ M : Mod R, ModuleTorDimensionLE R M d := by
  sorry

theorem finite_global_dimension_tor_amplitude
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (d : ℕ)
    (hR : HasGlobalDimensionLE R d)
    (K : Comp R) (a b : ℤ)
    (hK : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((derivedCohomology R i).obj ((derivedComplexQuotient R).obj K))) :
    TorAmplitude R ((derivedComplexQuotient R).obj K)
      (a - (d : ℤ)) b := by
  sorry

theorem finite_global_dimension_finite_tor_iff_bounded
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (d : ℕ)
    (hR : HasGlobalDimensionLE R d)
    (K : D R) :
    HasFiniteTorDimension R K ↔ derivedBoundedProperty (Mod R) K := by
  sorry

def NilpotentKernel {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) : Prop :=
  ∃ n : ℕ, (RingHom.ker f) ^ n = ⊥

noncomputable abbrev nilpotentDerivedBaseChange
    {R' R : Type u} [CommRing R'] [CommRing R]
    [HasDerivedCategory.{w} (Mod R')]
    [HasDerivedCategory.{w} (Mod R)] (f : R' →+* R) (K : D R') : D R :=
  (derivedBaseChange f).obj K

theorem tor_amplitude_nilpotent_quotient_iff
    {R' R : Type u} [CommRing R'] [CommRing R]
    [HasDerivedCategory.{w} (Mod R')]
    [HasDerivedCategory.{w} (Mod R)] (f : R' →+* R)
    (hsurj : Function.Surjective f) (hker : NilpotentKernel f)
    (K : D R') (a b : ℤ) :
    TorAmplitude R (nilpotentDerivedBaseChange f K) a b ↔
      TorAmplitude R' K a b := by
  sorry

end Formalization.Books.MoreAlgebra.Unit67
