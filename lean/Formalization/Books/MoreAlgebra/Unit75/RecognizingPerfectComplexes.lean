import Formalization.Books.MoreAlgebra.Unit75.SplittingComplexes
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More on Algebra, Chapter 75: recognizing perfect complexes

This file records the local and fiberwise criteria used to recognize perfect
complexes.  The boundedness and fiber-rank hypotheses are explicit so that the
interfaces can be used independently of a particular model of `D(R)`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit27
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit69
open Formalization.Books.MoreAlgebra.Unit60
open Formalization.Books.MoreAlgebra.Unit75
open scoped CategoryTheory.Preadditive TensorProduct

universe w u

namespace Formalization.Books.MoreAlgebra.Unit75

def IsBoundedBelowDerived
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : Prop :=
  ∃ E : Comp R, IsBoundedBelow E ∧
    Nonempty ((derivedQuotient R).obj E ≅ K)

def FiberCohomologyRank
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D p.asIdeal.ResidueField) (i : ℤ) : ℕ :=
  Module.finrank p.asIdeal.ResidueField
    (((derivedCohomologyFunctor (Mod p.asIdeal.ResidueField) i).obj K :
      Mod p.asIdeal.ResidueField) : Type u)

def FiberCohomologyVanishesOutside
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D R) (a b : ℤ) : Prop :=
  ∀ i : ℤ, i < a ∨ b < i →
    IsZero ((derivedCohomologyFunctor (Mod p.asIdeal.ResidueField) i).obj
      ((derivedBaseChange (residueFieldMap p)).obj K))

def FiberCohomologyVanishesBelow
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D R) (a : ℤ) : Prop :=
  ∀ i : ℤ, i < a →
    IsZero ((derivedCohomologyFunctor (Mod p.asIdeal.ResidueField) i).obj
      ((derivedBaseChange (residueFieldMap p)).obj K))

def PerfectAtPrime
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (p : PrimeSpectrum R)
    (hlocalDC : HasDerivedCategory.{w} (Mod (Localization.AtPrime p.asIdeal))) : Prop :=
  letI := hlocalDC
  Perfect (Localization.AtPrime p.asIdeal)
    ((derivedBaseChange (algebraMap R (Localization.AtPrime p.asIdeal))).obj K)

def PerfectAtMaximal
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (m : MaximalSpectrum R)
    (hlocalDC : HasDerivedCategory.{w} (Mod (Localization.AtPrime m.asIdeal))) : Prop :=
  letI := hlocalDC
  Perfect (Localization.AtPrime m.asIdeal)
    ((derivedBaseChange (algebraMap R (Localization.AtPrime m.asIdeal))).obj K)

theorem lift_bounded_pseudoCoherent_to_perfect
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (K : D R) (a : ℤ) (d : ℤ → ℕ)
    (hK : IsPseudoCoherent R K ∧ IsBoundedBelowDerived R K)
    (hdim : ∀ i : ℤ, d i = FiberCohomologyRank R p
      (((derivedBaseChange (residueFieldMap p)).obj K)) i)
    (hvanish : ∀ i : ℤ, i < a → d i = 0)
    (hlocalDC : ∀ f : R, HasDerivedCategory.{w}
      (Mod (Localization.Away f))) :
    ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
      ∃ E : Comp (Localization.Away f),
        FiberRankedComplex (Localization.Away f) E d ∧
          Nonempty ((derivedQuotient (Localization.Away f)).obj E ≅
            (derivedBaseChange (algebraMap R (Localization.Away f))).obj K) ∧
          Perfect (Localization.Away f)
            ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K) := by
  sorry

theorem check_perfect_pointwise
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a b : ℤ)
    (hprimeDC : ∀ p : PrimeSpectrum R,
      HasDerivedCategory.{w} (Mod (p.asIdeal.ResidueField)))
    (hmaxDC : ∀ m : MaximalSpectrum R,
      HasDerivedCategory.{w} (Mod (m.asIdeal.ResidueField))) :
    List.TFAE [
      Perfect R K ∧ TorAmplitude R K a b,
      ∀ p : PrimeSpectrum R, letI := hprimeDC p;
        FiberCohomologyVanishesOutside R p K a b,
      ∀ m : MaximalSpectrum R, letI := hmaxDC m;
        FiberCohomologyVanishesOutside R (MaximalSpectrum.toPrimeSpectrum m) K a b] := by
  sorry

theorem check_perfect_stalks
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R)
    (hK : IsPseudoCoherent R K)
    (hprimeLocalDC : ∀ p : PrimeSpectrum R,
      HasDerivedCategory.{w} (Mod (Localization.AtPrime p.asIdeal)))
    (hmaxLocalDC : ∀ m : MaximalSpectrum R,
      HasDerivedCategory.{w} (Mod (Localization.AtPrime m.asIdeal)))
    (hprimeFiberDC : ∀ p : PrimeSpectrum R,
      HasDerivedCategory.{w} (Mod (p.asIdeal.ResidueField)))
    (hmaxFiberDC : ∀ m : MaximalSpectrum R,
      HasDerivedCategory.{w} (Mod (m.asIdeal.ResidueField))) :
    (Perfect R K →
      (∀ p : PrimeSpectrum R, PerfectAtPrime R K p (hprimeLocalDC p))) ∧
    ((∀ p : PrimeSpectrum R, PerfectAtPrime R K p (hprimeLocalDC p)) ↔
      (∀ m : MaximalSpectrum R, PerfectAtMaximal R K m (hmaxLocalDC m))) ∧
    ((∀ m : MaximalSpectrum R, PerfectAtMaximal R K m (hmaxLocalDC m)) ↔
      (∀ p : PrimeSpectrum R, letI := hprimeFiberDC p;
        FiberCohomologyVanishesBelow R p K 0)) ∧
    ((∀ p : PrimeSpectrum R, letI := hprimeFiberDC p;
        FiberCohomologyVanishesBelow R p K 0) ↔
      (∀ m : MaximalSpectrum R, letI := hmaxFiberDC m;
        FiberCohomologyVanishesBelow R (MaximalSpectrum.toPrimeSpectrum m) K 0)) ∧
    (IsBoundedBelowDerived R K → List.TFAE [
      Perfect R K,
      ∀ p : PrimeSpectrum R, PerfectAtPrime R K p (hprimeLocalDC p),
      ∀ m : MaximalSpectrum R, PerfectAtMaximal R K m (hmaxLocalDC m),
      ∀ p : PrimeSpectrum R, letI := hprimeFiberDC p;
        FiberCohomologyVanishesBelow R p K 0,
      ∀ m : MaximalSpectrum R, letI := hmaxFiberDC m;
        FiberCohomologyVanishesBelow R (MaximalSpectrum.toPrimeSpectrum m) K 0]) := by
  sorry

theorem projective_amplitude_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (a b : ℤ)
    (hK : IsPseudoCoherent R K) :
    List.TFAE [
      HasProjectiveAmplitude K a b,
      Perfect R K ∧ TorAmplitude R K a b,
      ∀ (N : Mod R) (i : ℤ), FinitelyPresented R N →
        i ∉ Set.Icc (-b) (-a) → DerivedExtVanishes K (DerivedObject N) i,
      (∀ n : ℤ, b < n →
          IsZero ((derivedCohomologyFunctor (Mod R) n).obj K)) ∧
        (∀ (N : Mod R) (i : ℤ), FinitelyPresented R N → -a < i →
          DerivedExtVanishes K (DerivedObject N) i),
      (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
          IsZero ((derivedCohomologyFunctor (Mod R) n).obj K)) ∧
        (∀ (N : Mod R), FinitelyPresented R N →
          DerivedExtVanishes K (DerivedObject N) (-a + 1))] := by
  sorry

def RegularFiberOfDimension
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A]
    (d : ℕ) : Prop :=
  IsRegularLocalRing (B ⧸ Ideal.map (algebraMap A B)
    (IsLocalRing.maximalIdeal A)) ∧
    ringKrullDim (B ⧸ Ideal.map (algebraMap A B)
      (IsLocalRing.maximalIdeal A)) = d

theorem perfect_over_polynomial_ring
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (K : D B) (a b : ℤ) (d : ℕ)
    (hflat : RingHom.Flat (algebraMap A B))
    (hfiber : ∀ p : PrimeSpectrum A,
      HasGlobalDimensionLE (B ⊗[A] p.asIdeal.ResidueField) d)
    (hK : IsPseudoCoherent B K)
    (hA : TorAmplitude A
      ((derivedRestrictionFunctor (algebraMap A B)).obj K) a b) :
    Perfect B K ∧
      TorAmplitude B K (a - (d : ℤ)) b := by
  sorry

theorem perfect_over_regular_local_ring
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (K : D B) (a b : ℤ) (d : ℕ)
    (hlocal : IsLocalHom (algebraMap A B))
    (hflat : RingHom.Flat (algebraMap A B))
    (hfiber : RegularFiberOfDimension A B d)
    (hK : IsPseudoCoherent B K)
    (hA : TorAmplitude A
      ((derivedRestrictionFunctor (algebraMap A B)).obj K) a b) :
    Perfect B K ∧
      TorAmplitude B K (a - (d : ℤ)) b := by
  sorry

end Formalization.Books.MoreAlgebra.Unit75
