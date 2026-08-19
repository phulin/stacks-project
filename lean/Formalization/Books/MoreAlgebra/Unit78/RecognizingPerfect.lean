import Formalization.Books.MoreAlgebra.Unit65.PseudoCoherentModules
import Formalization.Books.MoreAlgebra.Unit67.TorDimension
import Formalization.Books.MoreAlgebra.Unit69.ProjectiveDimension
import Formalization.Books.Derived.Unit27.ExtGroups
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Interval.Set.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# More on Algebra, Chapter 78: recognizing perfect complexes

This file records the source-facing interfaces for the six recognition
lemmas in the chapter.  The derived categories, pseudo-coherence, tor
amplitude, projective amplitude, and base-change operations are the canonical
interfaces from the preceding chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit27
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit69
open Formalization.Books.MoreAlgebra.Unit63
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject
open scoped TensorProduct

universe u

namespace Formalization.Books.MoreAlgebra.Unit78

/-! ## Canonical objects and perfectness -/

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := CochainComplex (Mod R) ℤ

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)] := DerivedCategory (Mod R)

/- The project intentionally keeps the choice of derived category explicit for
module categories.  These are the standard choices for the residue fields and
localizations used throughout this chapter. -/
noncomputable instance residueField_hasDerivedCategory
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    HasDerivedCategory.{u + 1} (Mod p.asIdeal.ResidueField) :=
  HasDerivedCategory.standard _

noncomputable instance localizationAtPrime_hasDerivedCategory
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    HasDerivedCategory.{u + 1} (Mod (Localization.AtPrime p.asIdeal)) :=
  HasDerivedCategory.standard _

noncomputable instance localizationAway_hasDerivedCategory
    {R : Type u} [CommRing R] (f : R) :
    HasDerivedCategory.{u + 1} (Mod (Localization.Away f)) :=
  HasDerivedCategory.standard _

noncomputable instance localizationAtMaximal_hasDerivedCategory
    {R : Type u} [CommRing R] (m : MaximalSpectrum R) :
    HasDerivedCategory.{u + 1} (Mod (Localization.AtPrime m.asIdeal)) :=
  HasDerivedCategory.standard _

/- The source's perfect objects are represented by bounded complexes of finite
projective modules.  This is the module-category version of the usual
definition, and reuses the finite-projective predicate from Chapter 65. -/
def FiniteProjectiveComplex (R : Type u) [CommRing R] (E : Comp R) : Prop :=
  IsBounded E ∧
    ∀ i : ℤ, Formalization.Books.MoreAlgebra.Unit65.FiniteProjectiveModule
      R (E.X i)

def IsPerfect {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)] (K : D R) : Prop :=
  ∃ E : Comp R, FiniteProjectiveComplex R E ∧
    Nonempty ((DerivedCategory.Q (C := Mod R)).obj E ≅ K)

abbrev IsPerfectComplex {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)] (E : Comp R) : Prop :=
  IsPerfect ((DerivedCategory.Q (C := Mod R)).obj E)

def IsPerfectWithTorAmplitude {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)] (K : D R) (a b : ℤ) : Prop :=
  IsPerfect K ∧ TorAmplitude R K a b

/-! ## Residue fields and localizations -/

noncomputable def residueCohomology
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
  (K : D R) (p : PrimeSpectrum R) (i : ℤ) :
    ModuleCat.{u} p.asIdeal.ResidueField :=
  (Formalization.Books.MoreAlgebra.Unit65.derivedCohomologyFunctor
      p.asIdeal.ResidueField i).obj
    ((derivedBaseChange (algebraMap R p.asIdeal.ResidueField)).obj K)

noncomputable def residueDimension
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (p : PrimeSpectrum R) (i : ℤ) : ℕ :=
  Module.finrank p.asIdeal.ResidueField
    (residueCohomology K p i : Type u)

def ResidueCohomologySupportedIn
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (p : PrimeSpectrum R) (a b : ℤ) : Prop :=
    ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (residueCohomology K p i)

def ResidueCohomologyVanishesBelow
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (p : PrimeSpectrum R) : Prop :=
  ∃ N : ℤ, ∀ i : ℤ, i ≤ N → IsZero (residueCohomology K p i)

noncomputable def localizationAtPrime
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (p : PrimeSpectrum R) :
    D (Localization.AtPrime p.asIdeal) :=
  (derivedBaseChange
      (algebraMap R (Localization.AtPrime p.asIdeal))).obj K

noncomputable def localizationAtMaximal
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (m : MaximalSpectrum R) :
    D (Localization.AtPrime m.asIdeal) :=
  localizationAtPrime K (MaximalSpectrum.toPrimeSpectrum m)

/-! ## Finite free complexes with prescribed residue ranks -/

def FiniteFreeOfRank (R : Type u) [CommRing R]
    (M : Mod R) (n : ℕ) : Prop :=
  Nonempty (M ≅ ModuleCat.of R (Fin n → R))

structure FiniteFreeComplexOfRank
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (a b : ℤ) (d : ℤ → ℕ) where
  complex : Comp R
  interval_nonempty : a ≤ b
  zero_below : ∀ i : ℤ, i < a → IsZero (complex.X i)
  zero_above : ∀ i : ℤ, b < i → IsZero (complex.X i)
  term_rank : ∀ i : ℤ, a ≤ i → i ≤ b →
    FiniteFreeOfRank R (complex.X i) (d i)
  represents : Nonempty ((DerivedCategory.Q (C := Mod R)).obj complex ≅ K)

theorem isPerfect_of_finiteFreeComplexOfRank
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    {K : D R} {a b : ℤ} {d : ℤ → ℕ}
    (E : FiniteFreeComplexOfRank K a b d) :
    IsPerfect K := by
  sorry

/-! ## The first recognition lemma -/

theorem lift_bounded_pseudoCoherent_to_perfect
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (p : PrimeSpectrum R) (K : D R)
    (hK : IsPseudoCoherent R K)
    (hbounded : derivedPlusProperty (Mod R) K)
    (ha : ∃ a : ℤ, ∀ i : ℤ, i < a → residueDimension K p i = 0) :
    ∃ a : ℤ, (∀ i : ℤ, i < a → residueDimension K p i = 0) ∧
      ∃ f : R, f ∉ p.asIdeal ∧
        ∃ b : ℤ,
          Nonempty (FiniteFreeComplexOfRank
            ((derivedBaseChange
              (algebraMap R (Localization.Away f))).obj K)
            a b (residueDimension K p)) ∧
          IsPerfect ((derivedBaseChange
            (algebraMap R (Localization.Away f))).obj K) := by
  sorry

/-! ## Pointwise and stalk criteria -/

theorem check_perfect_pointwise
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (a b : ℤ) (hK : IsPseudoCoherent R K) :
    List.TFAE [
      IsPerfectWithTorAmplitude K a b,
      ∀ p : PrimeSpectrum R, ResidueCohomologySupportedIn K p a b,
      ∀ m : MaximalSpectrum R,
        ResidueCohomologySupportedIn K
          (MaximalSpectrum.toPrimeSpectrum m) a b] := by
  sorry

theorem check_perfect_stalks
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (hK : IsPseudoCoherent R K) :
    (IsPerfect K →
      ∀ p : PrimeSpectrum R, IsPerfect (localizationAtPrime K p)) ∧
    ((∀ p : PrimeSpectrum R, IsPerfect (localizationAtPrime K p)) ↔
      (∀ m : MaximalSpectrum R,
        IsPerfect (localizationAtMaximal K m))) ∧
    ((∀ m : MaximalSpectrum R,
        IsPerfect (localizationAtMaximal K m)) ↔
      (∀ p : PrimeSpectrum R, ResidueCohomologyVanishesBelow K p)) ∧
    ((∀ p : PrimeSpectrum R, ResidueCohomologyVanishesBelow K p) ↔
      (∀ m : MaximalSpectrum R,
        ResidueCohomologyVanishesBelow K
          (MaximalSpectrum.toPrimeSpectrum m))) ∧
    (derivedPlusProperty (Mod R) K →
      List.TFAE [
        IsPerfect K,
        ∀ p : PrimeSpectrum R, IsPerfect (localizationAtPrime K p),
        ∀ m : MaximalSpectrum R,
          IsPerfect (localizationAtMaximal K m),
        ∀ p : PrimeSpectrum R, ResidueCohomologyVanishesBelow K p,
        ∀ m : MaximalSpectrum R,
          ResidueCohomologyVanishesBelow K
            (MaximalSpectrum.toPrimeSpectrum m)]) := by
  sorry

/-! ## Projective amplitude and Ext -/

def ExtVanishesForFinitelyPresented
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (i : ℤ) : Prop :=
  ∀ N : Mod R, FinitelyPresented R N →
    DerivedExtVanishes K (DerivedObject N) i

theorem projective_amplitude_pseudoCoherent_criteria
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{u + 1} (Mod R)]
    (K : D R) (a b : ℤ) (hK : IsPseudoCoherent R K) :
    List.TFAE [
      HasProjectiveAmplitude K a b,
      IsPerfectWithTorAmplitude K a b,
      ∀ i : ℤ, i ∉ Set.Icc (-b) (-a) →
        ExtVanishesForFinitelyPresented K i,
      (∀ n : ℤ, b < n →
          IsZero ((Formalization.Books.MoreAlgebra.Unit65.derivedCohomologyFunctor
            R n).obj K)) ∧
        (∀ i : ℤ, -a < i → ExtVanishesForFinitelyPresented K i),
      (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
          IsZero ((Formalization.Books.MoreAlgebra.Unit65.derivedCohomologyFunctor
            R n).obj K)) ∧
        ExtVanishesForFinitelyPresented K (-a + 1)] := by
  sorry

/-! ## Polynomial and regular-local recognition -/

def IsRegularLocalRingOfDimension
    (S : Type u) [CommRing S] (d : ℕ) : Prop :=
  ∃ (_ : IsRegularLocalRing S),
    ringKrullDim S = (d : WithBot ℕ∞)

def BaseResidueCohomologySupportedIn
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A]
    [HasDerivedCategory.{u + 1} (Mod A)]
    (f : A →+* B) (K : Comp B) (a b : ℤ) : Prop :=
  ResidueCohomologySupportedIn
    ((DerivedCategory.Q (C := Mod A)).obj
      (Formalization.Books.MoreAlgebra.Unit56.restrictScalarsComplex f K))
    (MaximalSpectrum.toPrimeSpectrum
      (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : MaximalSpectrum A)) a b

theorem perfect_over_polynomial_ring
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{u + 1} (Mod A)]
    [HasDerivedCategory.{u + 1} (Mod B)]
    (f : A →+* B) (a b : ℤ) (d : ℕ) (K : Comp B)
    (hflat : RingHom.Flat f)
    (hfiber : ∀ p : PrimeSpectrum A,
      letI : Algebra A B := f.toAlgebra
      HasGlobalDimensionLE (B ⊗[A] p.asIdeal.ResidueField) d)
    (hK : IsPseudoCoherent B
      ((DerivedCategory.Q (C := Mod B)).obj K))
    (hamp : TorAmplitudeAsBase f K a b) :
    IsPerfectComplex (R := B) K ∧
      TorAmplitude B ((DerivedCategory.Q (C := Mod B)).obj K)
        (a - (d : ℤ)) b := by
  sorry

theorem perfect_over_regular_local_ring
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [HasDerivedCategory.{u + 1} (Mod A)]
    [HasDerivedCategory.{u + 1} (Mod B)]
    (f : A →+* B) [IsLocalHom f]
    (a b : ℤ) (d : ℕ) (K : Comp B)
    (hflat : RingHom.Flat f)
    (hregular : IsRegularLocalRingOfDimension
      (B ⧸ Ideal.map f (IsLocalRing.maximalIdeal A)) d)
    (hK : IsPseudoCoherent B
      ((DerivedCategory.Q (C := Mod B)).obj K))
    (hamp : TorAmplitudeAsBase f K a b ∨
      BaseResidueCohomologySupportedIn f K a b) :
    IsPerfectComplex (R := B) K ∧
      TorAmplitude B ((DerivedCategory.Q (C := Mod B)).obj K)
        (a - (d : ℤ)) b := by
  sorry

end Formalization.Books.MoreAlgebra.Unit78
