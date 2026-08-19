import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Formalization.Books.MoreAlgebra.Unit67.TorDimension
import Formalization.Books.MoreAlgebra.Unit69.ProjectiveDimension
import Formalization.Books.Derived.Unit12.CanonicalDeltaFunctor
import Formalization.Books.Derived.Unit27.ExtGroups
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# More on Algebra, Chapter 77: splitting complexes

This file records the six splitting-complex interfaces in source order.  The
truncations are Mathlib's canonical t-structure truncations, and the derived
base-change and amplitude predicates are reused from earlier chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit12
open Formalization.Books.Derived.Unit27
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit69
open Formalization.Books.MoreAlgebra.Unit75
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w u

namespace Formalization.Books.MoreAlgebra.Unit77

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := CochainComplex (Mod R) ℤ

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := DerivedCategory (Mod R)

noncomputable abbrev derivedBaseChange
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) : D A ⥤ D B :=
  Unit75.derivedBaseChange f

noncomputable abbrev moduleInDerived
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (M : Mod R) : D R :=
  (DerivedCategory.singleFunctor (Mod R) 0).obj M

noncomputable def moduleShift
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (M : Mod R) (i : ℤ) : D R :=
  (shiftFunctor (D R) (-i)).obj (moduleInDerived R M)

def CohomologyVanishesAtOrAbove
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) : Prop :=
  ∀ i : ℤ, a ≤ i →
    IsZero ((derivedCohomologyFunctor (Mod R) i).obj K)

def CohomologyVanishesAbove
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) : Prop :=
  ∀ i : ℤ, a < i →
    IsZero ((derivedCohomologyFunctor (Mod R) i).obj K)

noncomputable abbrev truncLE
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) : D R :=
  ((canonicalTStructure (Mod R)).truncLE a).obj K

noncomputable abbrev truncGE
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) : D R :=
  ((canonicalTStructure (Mod R)).truncGE a).obj K

noncomputable abbrev canonicalTruncationTriangle
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) : Triangle (D R) :=
  ((canonicalTStructure (Mod R)).triangleLEGE a (a + 1) (by omega)).obj K

def IsCompatibleTriangleIso
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (T : Triangle (D R)) (K L : D R)
    (e₁ : T.obj₁ ≅ K) (e₃ : T.obj₃ ≅ L)
    (e : T.obj₂ ≅ K ⊞ L) : Prop :=
  e₁.inv ≫ T.mor₁ ≫ e.hom = biprod.inl ∧
    e.hom ≫ biprod.snd = T.mor₂ ≫ e₃.hom

def IsCompatibleWithCanonicalTruncationPieces
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) (A B : D R)
    (e : K ≅ A ⊞ B) : Prop :=
  let T := canonicalTruncationTriangle R K a
  ∃ e₁ : T.obj₁ ≅ A,
    ∃ e₂ : T.obj₂ ≅ K,
      ∃ e₃ : T.obj₃ ≅ B,
        e₁.inv ≫ T.mor₁ ≫ e₂.hom ≫ e.hom = biprod.inl ∧
          e.hom ≫ biprod.snd = e₂.inv ≫ T.mor₂ ≫ e₃.hom

def IsCompatibleWithCanonicalTruncation
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ)
    (e : K ≅ truncLE R K a ⊞ truncGE R K (a + 1)) : Prop :=
  IsCompatibleWithCanonicalTruncationPieces R K a
    (truncLE R K a) (truncGE R K (a + 1)) e

/-! ## The splitting-uniqueness lemma -/

theorem splitting_unique
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K L : D R) (a b : ℤ) (hL : HasProjectiveAmplitude L a b) :
    (CohomologyVanishesAtOrAbove R K a →
      ∀ f : L ⟶ K, f = 0) ∧
    (CohomologyVanishesAtOrAbove R K (a + 1) →
      ∀ (T : Triangle (D R)), T ∈ distTriang (D R) →
        ∀ (h₁ : T.obj₁ = K) (h₃ : T.obj₃ = L),
        Nonempty
          {e : T.obj₂ ≅ K ⊞ L //
            IsCompatibleTriangleIso R T K L (eqToIso h₁) (eqToIso h₃) e}) ∧
    (CohomologyVanishesAtOrAbove R K a →
      ∀ (T : Triangle (D R)), T ∈ distTriang (D R) →
        ∀ (h₁ : T.obj₁ = K) (h₃ : T.obj₃ = L),
        ∃! e : T.obj₂ ≅ K ⊞ L,
          IsCompatibleTriangleIso R T K L (eqToIso h₁) (eqToIso h₃) e) := by
  sorry

/-! ## Localization and residue-field interfaces -/

noncomputable def residueFieldMap
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) :
    R →+* p.asIdeal.ResidueField :=
  (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField).comp
    (Ideal.Quotient.mk p.asIdeal)

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

def LocalizedCohomology
    (R : Type u) [CommRing R] (f : R)
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (i : ℤ) :
    ModuleCat.{u} (Localization.Away f) :=
  (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj
    ((derivedCohomologyFunctor (Mod R) i).obj K)

/-! ## Cutting a pseudo-coherent complex in two -/

theorem better_cut_complex_in_two
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (i : ℤ)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (hlocalDC : ∀ f : R,
      HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away f)))
    (K : D R) (hK : IsPseudoCoherent R K)
    (hsurj : FiberCohomologySurjective R p K i) :
    ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
      Perfect (Localization.Away f) (truncGE (Localization.Away f)
        ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
        (i + 1)) ∧
      TorAmplitudeBelow (Localization.Away f)
        (truncGE (Localization.Away f)
          ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
          (i + 1)) (i + 1) ∧
      Nonempty
        (((derivedBaseChange (algebraMap R (Localization.Away f))).obj K) ≅
          truncLE (Localization.Away f)
            ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K) i ⊞
          truncGE (Localization.Away f)
            ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
            (i + 1)) := by
  sorry

theorem isolate_a_cohomology_group
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (i : ℤ)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (hlocalDC : ∀ f : R,
      HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away f)))
    (K : D R) (hK : IsPseudoCoherent R K)
    (hᵢ : FiberCohomologySurjective R p K i)
    (hprev : FiberCohomologySurjective R p K (i - 1)) :
    ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
      Perfect (Localization.Away f) (truncGE (Localization.Away f)
        ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
        (i + 1)) ∧
      FiniteFreeModule (Localization.Away f)
        (LocalizedCohomology R f K i) ∧
      Nonempty
        (((derivedBaseChange (algebraMap R (Localization.Away f))).obj K) ≅
          (truncLE (Localization.Away f)
              ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
              (i - 1) ⊞
            moduleShift (Localization.Away f)
              (LocalizedCohomology R f K i) i) ⊞
          truncGE (Localization.Away f)
            ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
            (i + 1)) := by
  sorry

theorem cut_complex_in_two
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (i : ℤ)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod p.asIdeal.ResidueField)]
    (hlocalDC : ∀ f : R,
      HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away f)))
    (K : D R) (hK : IsPseudoCoherent R K)
    (hvanish : IsZero
      ((derivedCohomologyFunctor (Mod p.asIdeal.ResidueField) i).obj
        ((derivedBaseChange (residueFieldMap p)).obj K))) :
    ∃ f : R, f ∉ p.asIdeal ∧ letI := hlocalDC f
      Perfect (Localization.Away f) (truncGE (Localization.Away f)
        ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
        (i + 1)) ∧
      TorAmplitudeBelow (Localization.Away f)
        (truncGE (Localization.Away f)
          ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
          (i + 1)) (i + 1) ∧
      Nonempty
        (((derivedBaseChange (algebraMap R (Localization.Away f))).obj K) ≅
          truncGE (Localization.Away f)
            ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
            (i + 1) ⊞
          truncLE (Localization.Away f)
            ((derivedBaseChange (algebraMap R (Localization.Away f))).obj K)
            (i - 1)) := by
  sorry

/-! ## Splitting from Ext hypotheses -/

def ExtInjectiveOnInjectiveMaps
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) : Prop :=
  ∀ (M M' : Mod R) (f : M ⟶ M'), Mono f →
    Function.Injective
      (derivedExtPostcomp (X := K)
        ((DerivedCategory.singleFunctor (Mod R) 0).map f) (-a))

theorem split_using_ext_injective
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) (hK : IsInDMinus R K)
    (hExt : ExtInjectiveOnInjectiveMaps R K a) :
    (∃! e : K ≅ truncLE R K a ⊞ truncGE R K (a + 1),
      IsCompatibleWithCanonicalTruncation R K a e) ∧
      ∃ b : ℤ, HasProjectiveAmplitude (truncGE R K (a + 1)) (a + 1) b := by
  sorry

theorem split_using_ext_zero
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (a : ℤ) (hK : IsInDMinus R K)
    (hExt : ∀ M : Mod R,
      DerivedExtVanishes K (DerivedObject M) (-a)) :
    (∃! e : K ≅ truncLE R K (a - 1) ⊞ truncGE R K (a + 1),
      IsCompatibleWithCanonicalTruncationPieces R K a
        (truncLE R K (a - 1)) (truncGE R K (a + 1)) e) ∧
      (∃ b : ℤ, HasProjectiveAmplitude (truncGE R K (a + 1)) (a + 1) b) ∧
      IsZero ((derivedCohomologyFunctor (Mod R) a).obj K) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit77
