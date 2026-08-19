import Formalization.Books.MoreAlgebra.Unit53.AbelianCategoriesOfModules
import Formalization.Books.MoreAlgebra.Unit60.DerivedBaseChange
import Formalization.Books.MoreAlgebra.Unit71.NearProjective
import Formalization.Books.Derived.Unit27.ExtGroups
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# More on Algebra, Chapter 85: Two term complexes

This file records the chapter's two-term-complex criteria in the canonical
module-complex and derived-category language used by the preceding chapters.
The source's `H^i(K) = 0` conditions are expressed with the derived-category
homology functors, and its factorization conditions use morphisms in
`ModuleCat`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit27
open Formalization.Books.MoreAlgebra.Unit53
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit60
open Formalization.Books.MoreAlgebra.Unit71

universe w u v

namespace Formalization.Books.MoreAlgebra.Unit85

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := Unit59.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit59.D R

/-! ## Two-term representatives and cohomology support -/

/-- A cochain complex supported in degrees `-1` and `0`. -/
structure TwoTermComplex (R : Type u) [CommRing R] where
  complex : Comp R
  supported : ∀ i : ℤ, i < -1 ∨ 0 < i → IsZero (complex.X i)

abbrev TwoTermComplex.neg {R : Type u} [CommRing R]
    (T : TwoTermComplex R) : Mod R := T.complex.X (-1)

abbrev TwoTermComplex.zero {R : Type u} [CommRing R]
    (T : TwoTermComplex R) : Mod R := T.complex.X 0

/-- The differential of a two-term complex. -/
abbrev TwoTermComplex.differential {R : Type u} [CommRing R]
    (T : TwoTermComplex R) : T.neg ⟶ T.zero := T.complex.d (-1) 0

/-- A two-term complex represents a derived object. -/
def RepresentsTwoTerm {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (T : TwoTermComplex R) (K : D R) : Prop :=
  Nonempty ((derivedComplexQuotient R).obj T.complex ≅ K)

def TwoTermZeroFree {R : Type u} [CommRing R]
    (T : TwoTermComplex R) : Prop :=
  Module.Free R (T.zero : Type u)

def TwoTermZeroProjective {R : Type u} [CommRing R]
    (T : TwoTermComplex R) : Prop :=
  Module.Projective R (T.zero : Type u)

def TwoTermZeroFiniteFree {R : Type u} [CommRing R]
    (T : TwoTermComplex R) : Prop :=
  Module.Free R (T.zero : Type u) ∧ Module.Finite R (T.zero : Type u)

def TwoTermNegFinite {R : Type u} [CommRing R]
    (T : TwoTermComplex R) : Prop :=
  Module.Finite R (T.neg : Type u)

noncomputable abbrev derivedCohomologyFunctor
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)] (i : ℤ) :
    D R ⥤ Mod R :=
  DerivedCategory.homologyFunctor (Mod R) i

noncomputable abbrev H
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (i : ℤ) (K : D R) : Mod R :=
  (derivedCohomologyFunctor R i).obj K

abbrev HMinusOne
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) : Mod R := H R (-1) K

abbrev HZero
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) : Mod R := H R 0 K

/-- The source hypothesis that a derived object has cohomology only in the
two displayed degrees. -/
def CohomologySupportedInTwoTerms
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) : Prop :=
  ∀ i : ℤ, i < -1 ∨ 0 < i → IsZero (H R i K)

def ExtOne
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (N : Mod R) : Type _ :=
  DerivedExt K (DerivedObject N) 1

def ExtOneVanishes
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) : Prop :=
  ∀ N : Mod R, ∀ ξ : ExtOne K N, ξ = 0

def ExtOneVanishesOnFiniteModules
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) : Prop :=
  ∀ (N : Mod R), Module.Finite R (N : Type u) →
    ∀ ξ : ExtOne K N, ξ = 0

def ExtOneAnnihilatedByIdeal
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) (K : D R) : Prop :=
  ∀ (N : Mod R) (a : R), a ∈ I → ∀ ξ : ExtOne K N, a • ξ = 0

def IdealAnnihilatesModule
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) : Prop :=
  ∀ a : R, a ∈ I → ∀ x : M, a • x = 0

/-- A map factors through the differential of a two-term complex. -/
def FactorsThroughDifferential {R : Type u} [CommRing R]
    (T : TwoTermComplex R) (a : T.neg ⟶ T.neg) : Prop :=
  ∃ h : T.zero ⟶ T.neg, T.differential ≫ h = a

/-! ## The first Ext criterion and the smoothness remark -/

theorem ext_one_zero_characterization
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (hK : CohomologySupportedInTwoTerms K) :
    List.TFAE [
      IsZero (HMinusOne R K) ∧ Module.Projective R (HZero R K : Type u),
      ExtOneVanishes K] := by
  sorry

theorem ext_one_zero_characterization_on_finite_modules
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R)
    (hK : CohomologySupportedInTwoTerms K)
    (hfinite : Module.Finite R (HMinusOne R K : Type u) ∧
      Module.Finite R (HZero R K : Type u)) :
    List.TFAE [
      IsZero (HMinusOne R K) ∧ Module.Projective R (HZero R K : Type u),
      ExtOneVanishes K,
      ExtOneVanishesOnFiniteModules K] := by
  sorry

/- The earlier algebra chapters do not yet package the naive cotangent
complex as an object of the derived category.  This small chapter-local
interface names the chosen object needed by the source's two smoothness
remarks, without changing the mathematical criterion. -/
class NaiveCotangentComplexData
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] where
  object : D S

noncomputable abbrev naiveCotangentObject
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    [NaiveCotangentComplexData f] : D S :=
  NaiveCotangentComplexData.object (f := f)

/-- The source's condition `(*)` for a finitely presented ring map and an
ideal in the target. -/
def NaiveCotangentExtOneAnnihilatedByIdeal
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (f : R →+* S) (hf : f.FinitePresentation) (I : Ideal S)
    [NaiveCotangentComplexData f] : Prop :=
  ExtOneAnnihilatedByIdeal I (naiveCotangentObject f)

theorem smooth_iff_ext_one_zero
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] (f : R →+* S)
    [NaiveCotangentComplexData f] :
    f.Smooth ↔ f.FinitePresentation ∧
      ExtOneVanishes (naiveCotangentObject f) := by
  sorry

theorem formallySmooth_iff_ext_one_zero
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] (f : R →+* S)
    [NaiveCotangentComplexData f] :
    f.FormallySmooth ↔ ExtOneVanishes (naiveCotangentObject f) := by
  sorry

/-! ## Representation and maps out of almost-free complexes -/

def IsZeroAbove {R : Type u} [CommRing R] (M : Comp R) : Prop :=
  ∀ i : ℤ, 0 < i → IsZero (M.X i)

def IsZeroAtOrBelow {R : Type u} [CommRing R] (M : Comp R) (n : ℤ) : Prop :=
  ∀ i : ℤ, i ≤ n → IsZero (M.X i)

def IsZeroOutsideMinusOneZero {R : Type u} [CommRing R]
    (K : Comp R) : Prop :=
  ∀ i : ℤ, i < -1 ∨ 0 < i → IsZero (K.X i)

def IsProjectiveAt {R : Type u} [CommRing R]
    (M : Comp R) (i : ℤ) : Prop :=
  Module.Projective R (M.X i : Type u)

def ComplexExtOneMapZero
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {M K : Comp R} (a : M ⟶ K) : Prop :=
  ∀ (N : Mod R) (ξ : ExtOne ((derivedComplexQuotient R).obj K) N),
    derivedExtPrecomp ((derivedComplexQuotient R).map a) 1 ξ = 0

theorem represent_two_term_complex
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (hK : CohomologySupportedInTwoTerms K) :
    (∃ T : TwoTermComplex R, RepresentsTwoTerm T K ∧ TwoTermZeroFree T) ∧
      (IsNoetherianRing R →
        (Module.Finite R (HMinusOne R K : Type u) ∧
          Module.Finite R (HZero R K : Type u) →
          ∃ T : TwoTermComplex R,
            RepresentsTwoTerm T K ∧ TwoTermZeroFiniteFree T ∧
              TwoTermNegFinite T)) := by
  sorry

theorem maps_out_of_almost_free_part_one
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {M K : Comp R} (hM : IsZeroAbove M ∧ IsProjectiveAt M 0)
    (hK : IsZeroAtOrBelow K (-2)) :
    Nonempty (((homotopyQuotient R).obj M ⟶ (homotopyQuotient R).obj K)
      ≃+ ((derivedComplexQuotient R).obj M ⟶
        (derivedComplexQuotient R).obj K)) := by
  sorry

theorem maps_out_of_almost_free_part_two
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {M K : Comp R} (hM : IsZeroAbove M ∧ IsProjectiveAt M 0)
    (hK : IsZeroOutsideMinusOneZero K ∧ IsProjectiveAt K 0)
    (a : M ⟶ K) :
    ComplexExtOneMapZero a ↔
      ∃ h : M.X 0 ⟶ K.X (-1),
        a.f (-1) + M.d (-1) 0 ≫ h = 0 := by
  sorry

structure DegreeMinusTwoComponent
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {M K : Comp R}
    (α : (derivedComplexQuotient R).obj M ⟶
      (derivedComplexQuotient R).obj K)
    (a : M.X (-2) ⟶ K.X (-2)) where
  targetProjection : (derivedComplexQuotient R).obj K ⟶
    (shiftFunctor (D R) (2 : ℤ)).obj
      (DerivedObject (K.X (-2)))
  sourceProjection : (derivedComplexQuotient R).obj M ⟶
    (shiftFunctor (D R) (2 : ℤ)).obj
      (DerivedObject (M.X (-2)))
  projection_compatibility :
    α ≫ targetProjection = sourceProjection ≫
      (shiftFunctor (D R) (2 : ℤ)).map
        ((DerivedCategory.singleFunctor (Mod R) 0).map a)

theorem maps_out_of_almost_free_part_three
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {M K : Comp R} (hM : IsZeroAbove M ∧ IsProjectiveAt M 0)
    (hK : ∀ i : ℤ, i ≤ -3 → IsZero (K.X i))
    (α : (derivedComplexQuotient R).obj M ⟶
      (derivedComplexQuotient R).obj K)
    (a : M.X (-2) ⟶ K.X (-2))
    (ha : M.d (-3) (-2) ≫ a = 0)
    (hα : DegreeMinusTwoComponent α a) :
    ∃ b : M ⟶ K,
      (derivedComplexQuotient R).map b = α ∧ b.f (-2) = a := by
  sorry

theorem maps_out_of_almost_free_part_four
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {M K : Comp R} (hM : IsZeroAbove M ∧ IsProjectiveAt M 0)
    (hK : ∀ i : ℤ, i ≤ -3 → IsZero (K.X i))
    (α : (derivedComplexQuotient R).obj M ⟶
      (derivedComplexQuotient R).obj K)
    (a a' : M ⟶ K) (ha : (derivedComplexQuotient R).map a = α)
    (ha' : (derivedComplexQuotient R).map a' = α)
    (hdegree : a.f (-2) = a'.f (-2)) :
    ∃ h₋₁ : M.X (-1) ⟶ K.X (-2), ∃ h₀ : M.X 0 ⟶ K.X (-1),
      M.d (-2) (-1) ≫ h₋₁ = 0 ∧
      a'.f (-1) = a.f (-1) + h₋₁ ≫ K.d (-2) (-1) +
        M.d (-1) 0 ≫ h₀ ∧
      a'.f 0 = a.f 0 + h₀ ≫ K.d (-1) 0 := by
  sorry

/-! ## Annihilation by an ideal -/

def ExtOneAnnihilatedByIdealForTwoTermRepresentation
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) (K : D R) : Prop :=
  ∃ T : TwoTermComplex R, RepresentsTwoTerm T K ∧ TwoTermZeroFree T ∧
    ∀ a : R, a ∈ I →
      FactorsThroughDifferential T (a • 𝟙 T.neg)

def ExtOneAnnihilatedByIdealForEveryProjectiveRepresentation
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) (K : D R) : Prop :=
  ∀ T : TwoTermComplex R, RepresentsTwoTerm T K →
    TwoTermZeroProjective T →
      ∀ a : R, a ∈ I → FactorsThroughDifferential T (a • 𝟙 T.neg)

def ExtOneAnnihilatedByIdealForFiniteRepresentation
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) (K : D R) : Prop :=
  ∃ T : TwoTermComplex R, RepresentsTwoTerm T K ∧
    TwoTermZeroFiniteFree T ∧ TwoTermNegFinite T ∧
    ∀ a : R, a ∈ I → FactorsThroughDifferential T (a • 𝟙 T.neg)

def ExtOneAnnihilatedByIdealOnFiniteModules
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) (K : D R) : Prop :=
  ∀ (N : Mod R), Module.Finite R (N : Type u) →
    ∀ a : R, a ∈ I → ∀ ξ : ExtOne K N, a • ξ = 0

theorem ext_one_annihilated_definite
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) (K : D R) (hK : CohomologySupportedInTwoTerms K) :
    List.TFAE [
      ExtOneAnnihilatedByIdeal I K,
      ExtOneAnnihilatedByIdealForTwoTermRepresentation I K,
      ExtOneAnnihilatedByIdealForEveryProjectiveRepresentation I K] := by
  sorry

theorem ext_one_annihilated_definite_on_finite_modules
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (I : Ideal R) (K : D R)
    (hK : CohomologySupportedInTwoTerms K)
    (hfinite : Module.Finite R (HMinusOne R K : Type u) ∧
      Module.Finite R (HZero R K : Type u)) :
    List.TFAE [
      ExtOneAnnihilatedByIdeal I K,
      ExtOneAnnihilatedByIdealForTwoTermRepresentation I K,
      ExtOneAnnihilatedByIdealForEveryProjectiveRepresentation I K,
      ExtOneAnnihilatedByIdealOnFiniteModules I K,
      ExtOneAnnihilatedByIdealForFiniteRepresentation I K] := by
  sorry

/-! ## Base change and the surjection criterion -/

noncomputable abbrev derivedTruncGEAtMinusOne
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) : D R :=
  ((DerivedCategory.TStructure.t (C := Mod R)).truncGE (-1 : ℤ)).obj K

def RepresentsTruncatedBaseChange
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (E : Comp R) (K : D R) : Prop :=
  Nonempty ((derivedComplexQuotient S).obj (baseChangeComplex f E) ≅
    derivedTruncGEAtMinusOne ((derivedBaseChangeFunctor f).obj K))

theorem two_term_base_change
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (T : TwoTermComplex R)
    (hflat : Module.Flat R (T.zero : Type u))
    (K : D R) (hK : RepresentsTwoTerm T K) :
    RepresentsTruncatedBaseChange f T.complex K := by
  sorry

theorem base_change_preserves_ext_one_annihilated
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (I : Ideal R) (f : R →+* S) (K : D R)
    (hK : CohomologySupportedInTwoTerms K)
    (hI : ExtOneAnnihilatedByIdeal I K) :
    ExtOneAnnihilatedByIdeal (I.map f)
      (derivedTruncGEAtMinusOne ((derivedBaseChangeFunctor f).obj K)) := by
  sorry

theorem two_term_surjection_map_zero
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {K K' : D R} (α : K ⟶ K')
    (hK : CohomologySupportedInTwoTerms K ∧
      CohomologySupportedInTwoTerms K')
    (hα : IsIso ((derivedCohomologyFunctor R 0).map α) ∧
      Epi ((derivedCohomologyFunctor R (-1)).map α))
    (f : R) (hf : f • 𝟙 K = 0) :
    f • 𝟙 K' = 0 := by
  sorry

theorem surjection_preserves_ext_one_annihilated
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) {K K' : D R} (α : K ⟶ K')
    (hK : CohomologySupportedInTwoTerms K ∧
      CohomologySupportedInTwoTerms K')
    (hα : IsIso ((derivedCohomologyFunctor R 0).map α) ∧
      Epi ((derivedCohomologyFunctor R (-1)).map α))
    (hI : ExtOneAnnihilatedByIdeal I K) :
    ExtOneAnnihilatedByIdeal I K' := by
  sorry

/-! ## The power, localization, and projectivity criterion -/

def IsIPowerProjective
    {R : Type u} [CommRing R] (I : Ideal R) (M : Mod R) : Prop :=
  IsIdealProjective I M

def LocalizedModule
    {R : Type u} [CommRing R] (f : R) (M : Mod R) :
    ModuleCat.{u} (Localization.Away f) :=
  (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M

def LocalizedProjective
    {R : Type u} [CommRing R] (f : R) (M : Mod R) : Prop :=
  Module.Projective (Localization.Away f)
    (LocalizedModule f M : Type u)

def ZeroLocusOfFinset {R : Type u} [CommRing R] (s : Finset R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus (s : Set R)

def ZeroLocusOfIdeal {R : Type u} [CommRing R] (I : Ideal R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus (I : Set R)

def HasProjectiveLocalizationCover
    {R : Type u} [CommRing R] (I : Ideal R) (M : Mod R) : Prop :=
  ∃ s : Finset R,
    ZeroLocusOfFinset s ⊆ ZeroLocusOfIdeal I ∧
      ∀ f ∈ s, LocalizedProjective f M

def HasProjectiveLocalizationCoverInIdeal
    {R : Type u} [CommRing R] (I : Ideal R) (M : Mod R) : Prop :=
  ∃ s : Finset R,
    (∀ f ∈ s, f ∈ I) ∧
      ZeroLocusOfFinset s = ZeroLocusOfIdeal I ∧
      ∀ f ∈ s, LocalizedProjective f M

def EveryProjectiveLocalizationCoverInIdeal
    {R : Type u} [CommRing R] (I : Ideal R) (M : Mod R) : Prop :=
  ∀ s : Finset R,
    (∀ f ∈ s, f ∈ I) →
      ZeroLocusOfFinset s = ZeroLocusOfIdeal I →
      ∀ f ∈ s, LocalizedProjective f M

theorem ext_one_annihilated_power_characterization
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (I : Ideal R) (K : D R) (hK : CohomologySupportedInTwoTerms K) :
    List.TFAE [
      ∃ c : ℕ, ExtOneAnnihilatedByIdeal (I ^ c) K,
      ∃ c : ℕ,
        IdealAnnihilatesModule (I ^ c) (HMinusOne R K : Type u) ∧
          IsIPowerProjective (I ^ c) (HZero R K)] := by
  sorry

theorem ext_one_annihilated_power_characterization_on_finite_modules
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (I : Ideal R) (K : D R)
    (hK : CohomologySupportedInTwoTerms K)
    (hfinite : Module.Finite R (HMinusOne R K : Type u) ∧
      Module.Finite R (HZero R K : Type u)) :
    List.TFAE [
      ∃ c : ℕ, ExtOneAnnihilatedByIdeal (I ^ c) K,
      ∃ c : ℕ,
        IdealAnnihilatesModule (I ^ c) (HMinusOne R K : Type u) ∧
          IsIPowerProjective (I ^ c) (HZero R K),
      ∃ c : ℕ, ExtOneAnnihilatedByIdealOnFiniteModules (I ^ c) K,
      IsIPowerTorsion I (HMinusOne R K : Type u) ∧
        HasProjectiveLocalizationCover I (HZero R K),
      IsIPowerTorsion I (HMinusOne R K : Type u) ∧
        HasProjectiveLocalizationCoverInIdeal I (HZero R K),
      IsIPowerTorsion I (HMinusOne R K : Type u) ∧
        EveryProjectiveLocalizationCoverInIdeal I (HZero R K)] := by
  sorry

/-! ## Two final consequences -/

theorem zero_in_derived
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {K₁ K₂ K₃ : D R} (φ : K₁ ⟶ K₂) (ψ : K₂ ⟶ K₃)
    (hK : CohomologySupportedInTwoTerms K₁ ∧
      CohomologySupportedInTwoTerms K₂ ∧
      CohomologySupportedInTwoTerms K₃)
    (hφ : (derivedCohomologyFunctor R 0).map φ = 0)
    (hψ : (derivedCohomologyFunctor R (-1)).map ψ = 0) :
    φ ≫ ψ = 0 := by
  sorry

structure SquareTwoTermComplex
    (R : Type u) [CommRing R] (n : ℕ) where
  complex : TwoTermComplex R
  negIso : complex.neg ≅ ModuleCat.of R (Fin n → R)
  zeroIso : complex.zero ≅ ModuleCat.of R (Fin n → R)

noncomputable def squareDifferentialMatrix
    {R : Type u} [CommRing R] {n : ℕ}
    (T : SquareTwoTermComplex R n) : Matrix (Fin n) (Fin n) R :=
  LinearMap.toMatrix (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n))
    (T.negIso.inv.hom ≫ T.complex.differential ≫ T.zeroIso.hom).hom

theorem determinant_scalar_zero
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    {n : ℕ} (T : SquareTwoTermComplex R n) :
    (squareDifferentialMatrix T).det •
      𝟙 ((derivedComplexQuotient R).obj T.complex.complex) = 0 := by
  sorry

end Formalization.Books.MoreAlgebra.Unit85
