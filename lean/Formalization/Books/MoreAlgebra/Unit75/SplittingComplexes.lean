import Formalization.Books.MoreAlgebra.Unit75.LiftingComplexes
import Formalization.Books.MoreAlgebra.Unit69.ProjectiveDimension
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# More on Algebra, Chapter 75: splitting complexes

The canonical truncation triangle is packaged explicitly so the splitting
interfaces retain its three objects, distinguishedness, and cohomological
support.  This avoids introducing a second derived-category model.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit27
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit69
open Formalization.Books.MoreAlgebra.Unit75
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w u

namespace Formalization.Books.MoreAlgebra.Unit75

noncomputable def residueFieldMap
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    R →+* p.asIdeal.ResidueField :=
  (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField).comp
    (Ideal.Quotient.mk p.asIdeal)

structure CanonicalTruncation
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (i : ℤ) where
  lower : D R
  upper : D R
  triangle : Triangle (D R)
  distinguished : triangle ∈ distTriang (D R)
  lowerIso : triangle.obj₁ ≅ lower
  middleIso : triangle.obj₂ ≅ K
  upperIso : triangle.obj₃ ≅ upper
  lowerVanishing : ∀ n : ℤ, i < n →
    IsZero ((derivedCohomologyFunctor (Mod R) n).obj lower)
  upperVanishing : ∀ n : ℤ, n ≤ i →
    IsZero ((derivedCohomologyFunctor (Mod R) n).obj upper)

def CohomologyVanishesAtOrAbove
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a : ℤ) : Prop :=
  ∀ i : ℤ, a ≤ i →
    IsZero ((derivedCohomologyFunctor (Mod R) i).obj K)

def CohomologyVanishesAbove
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a : ℤ) : Prop :=
  ∀ i : ℤ, a < i →
    IsZero ((derivedCohomologyFunctor (Mod R) i).obj K)

def FiberCohomologySurjective
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D R) (i : ℤ) : Prop :=
  ∃ φ : (ModuleCat.extendScalars (residueFieldMap p)).obj
      ((derivedCohomologyFunctor (Mod R) i).obj K) ⟶
      (derivedCohomologyFunctor (Mod p.asIdeal.ResidueField) i).obj
        ((derivedBaseChange (residueFieldMap p)).obj K),
    Epi φ

noncomputable def moduleShift
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) (i : ℤ) : D R :=
  (shiftFunctor (D R) (-i)).obj (moduleInDerived R M)

theorem splitting_unique
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : D R) (a b : ℤ)
    (hL : HasProjectiveAmplitude L a b) :
    (CohomologyVanishesAtOrAbove R K a →
      ∀ T : Triangle (D R), IsDistinguishedTriangle R T →
        T.obj₁ = K → T.obj₃ = L →
        Nonempty (T.obj₂ ≅ K ⊞ L)) ∧
    (CohomologyVanishesAtOrAbove R K (a + 1) →
      ∀ T : Triangle (D R), IsDistinguishedTriangle R T →
        T.obj₁ = K → T.obj₃ = L →
        Nonempty (T.obj₂ ≅ K ⊞ L)) ∧
    (CohomologyVanishesAtOrAbove R K a →
      ∀ T : Triangle (D R), IsDistinguishedTriangle R T →
        T.obj₁ = K → T.obj₃ = L →
        Subsingleton (T.obj₂ ≅ K ⊞ L)) := by
  sorry

theorem better_cut_complex_in_two
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (i : ℤ)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (hlocalDC : ∀ f : R, HasDerivedCategory.{w}
      (Mod (Localization.Away f)))
    (K : D R) (hK : IsPseudoCoherent R K)
    (hsurj : FiberCohomologySurjective R p K i) :
    ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
      ∃ T : CanonicalTruncation (Localization.Away f)
          ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K) i,
        Perfect (Localization.Away f) T.upper ∧
        TorAmplitudeBelow (Localization.Away f) T.upper (i + 1) ∧
        Nonempty (T.middleIso.hom ≠ 0) := by
  sorry

theorem isolate_a_cohomology_group
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (i : ℤ)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (hlocalDC : ∀ f : R, HasDerivedCategory.{w}
      (Mod (Localization.Away f)))
    (K : D R) (hK : IsPseudoCoherent R K)
    (hᵢ : FiberCohomologySurjective R p K i)
    (hprev : FiberCohomologySurjective R p K (i - 1)) :
    ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
      ∃ T : CanonicalTruncation (Localization.Away f)
          ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K) i,
        FiniteFreeModule (Localization.Away f)
          ((derivedCohomologyFunctor
            (Mod (Localization.Away f)) i).obj
            ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)) ∧
        Nonempty (T.middleIso.hom ≠ 0) := by
  sorry

theorem cut_complex_in_two
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (i : ℤ)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (hlocalDC : ∀ f : R, HasDerivedCategory.{w}
      (Mod (Localization.Away f)))
    (K : D R) (hK : IsPseudoCoherent R K)
    (hvanish : IsZero ((derivedCohomologyFunctor (Mod p.asIdeal.ResidueField) i).obj
      ((derivedBaseChange (residueFieldMap p)).obj K))) :
    ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
      ∃ T : CanonicalTruncation (Localization.Away f)
          ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K) i,
        Perfect (Localization.Away f) T.upper ∧
        TorAmplitudeBelow (Localization.Away f) T.upper (i + 1) ∧
        Nonempty (T.middleIso.hom ≠ 0) := by
  sorry

def ExtInjectiveOnInjectiveMaps
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a : ℤ) : Prop :=
  ∀ (M M' : Mod R) (f : M ⟶ M'), Mono f →
    Function.Injective
      (derivedExtPostcomp (X := K)
        ((DerivedCategory.singleFunctor (Mod R) 0).map f) (-a))

theorem split_using_ext_injective
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a : ℤ)
    (hK : IsInDMinus R K)
    (hExt : ExtInjectiveOnInjectiveMaps R K a) :
    ∃ T : CanonicalTruncation R K a,
      Nonempty (K ≅ T.lower ⊞ T.upper) ∧
      ∃ b : ℤ, HasProjectiveAmplitude T.upper (a + 1) b := by
  sorry

theorem split_using_ext_zero
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a : ℤ)
    (hK : IsInDMinus R K)
    (hExt : ∀ M : Mod R,
      DerivedExtVanishes K (DerivedObject M) (-a)) :
    ∃ T : CanonicalTruncation R K a,
      Nonempty (K ≅ T.lower ⊞ T.upper) ∧
      ∃ b : ℤ, HasProjectiveAmplitude T.upper (a + 1) b ∧
        IsZero ((derivedCohomologyFunctor (Mod R) a).obj K) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit75
