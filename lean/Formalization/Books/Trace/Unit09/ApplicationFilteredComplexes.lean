import Formalization.Books.Trace.Unit08.FilteredDerivedFunctors
import Formalization.Books.Homology.Unit20.DifferentialObjects
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Data.ZMod.Basic

/-!
# The Trace Formula, Chapter 9: application of filtered complexes

This file records the two-step filtration attached to a short exact sequence,
the derived and spectral-sequence consequences used in the source, the
resulting long exact sequence, and the final Frobenius-trace application.
The geometric étale/cohomology constructions used by the last application
are not present in the preceding Trace chapters, so they are exposed as an
explicit data interface rather than replaced by unrelated objects.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit19
open Formalization.Books.Trace.Unit06
open Formalization.Books.Trace.Unit07
open Formalization.Books.Trace.Unit08
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u v w u' v' w'

namespace Formalization.Books.Trace.Unit09

/-! ## The two-step filtered object -/

/- The source's short exact sequence `0 → L → M → N → 0` is Mathlib's
   `ShortComplex` together with its canonical `ShortExact` predicate. -/

def twoStepFiltration
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    DecreasingFiltration A S.X₂ := by
  letI : Mono S.f := hS.mono_f
  exact
    { obj := fun n =>
        if n ≤ 0 then ⊤
        else if n = 1 then Subobject.mk S.f
        else ⊥
      antitone := by
        intro i j hij
        by_cases hi : i ≤ 0
        · simp [hi]
        · have hiPos : 1 ≤ i := by omega
          by_cases hiOne : i = 1
          · by_cases hjOne : j = 1
            · simp [hi, hiOne, hjOne]
            · have hjTwo : 2 ≤ j := by omega
              have hjNotZero : ¬j ≤ 0 := by omega
              simp [hi, hiOne, hjOne, hjTwo, hjNotZero]
          · have hiTwo : 2 ≤ i := by omega
            have hjTwo : 2 ≤ j := le_trans hiTwo hij
            have hjNotZero : ¬j ≤ 0 := by omega
            have hjNotOne : ¬j = 1 := by omega
            simp [hi, hiOne, hiTwo, hjTwo, hjNotZero, hjNotOne] }

noncomputable def twoStepFilteredObject
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) : FilteredObject A where
  carrier := S.X₂
  filtration := twoStepFiltration S hS

def filteredForgetfulObject
    {A : Type u} [Category.{v} A] (F : FilteredObject A) : A :=
  F.carrier

noncomputable def twoStepFilteredObjectFinite
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    FiniteFiltered A :=
  ⟨twoStepFilteredObject S hS, by
    refine ⟨0, 2, ?_, ?_⟩
    · simp [twoStepFilteredObject, twoStepFiltration] <;> rfl
    · simp [twoStepFilteredObject, twoStepFiltration] <;> rfl⟩

theorem twoStepFilteredObject_carrier
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    filteredForgetfulObject (twoStepFilteredObject S hS) = S.X₂ := rfl

/- The graded identifications are stated as isomorphisms, which is the
   source-faithful formulation in an arbitrary abelian category. -/
theorem twoStepFilteredObject_gradedPieces
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    Nonempty (gradedPiece (twoStepFilteredObject S hS) 0 ≅ S.X₃) ∧
      Nonempty (gradedPiece (twoStepFilteredObject S hS) 1 ≅ S.X₁) ∧
      ∀ p : ℤ, p ≠ 0 → p ≠ 1 → IsZero (gradedPiece (twoStepFilteredObject S hS) p) := by
  sorry

theorem twoStepFilteredObject_gradedPiece_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    Nonempty (gradedPiece (twoStepFilteredObject S hS) 0 ≅ S.X₃) :=
  (twoStepFilteredObject_gradedPieces S hS).1

theorem twoStepFilteredObject_gradedPiece_one
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    Nonempty (gradedPiece (twoStepFilteredObject S hS) 1 ≅ S.X₁) :=
  (twoStepFilteredObject_gradedPieces S hS).2.1

theorem twoStepFilteredObject_gradedPiece_other
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) (p : ℤ)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    IsZero (gradedPiece (twoStepFilteredObject S hS) p) :=
  (twoStepFilteredObject_gradedPieces S hS).2.2 p hp0 hp1

/-! ## Concentrated filtered objects and derived objects -/

noncomputable def filteredObjectAsDerivedPlus
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : FilteredObject A) (hF : F.IsFinite) : DFPlus A :=
  filteredPlusLocalizationFunctor A |>.obj
    ((HomotopyCategory.Plus.singleFunctor (FiniteFiltered A) 0).obj
      ⟨F, hF⟩)

noncomputable abbrev twoStepFilteredDerivedInput
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) : DFPlus A :=
  filteredObjectAsDerivedPlus (twoStepFilteredObject S hS)
    (twoStepFilteredObjectFinite S hS).property

noncomputable abbrev totalRightDerivedObject
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) (X : A) : DPlus B :=
  (totalRightDerivedFunctor A B T hT).obj
    ((DerivedCategory.Plus.singleFunctor A 0).obj X)

noncomputable abbrev rightDerivedCohomology
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) (X : A) (n : ℕ) : B :=
  if n = 0 then T.obj X
  else (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj
    (totalRightDerivedObject T hT X)

noncomputable abbrev filteredRightDerivedApplicationObject
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (hS : S.ShortExact) : DFPlus B :=
  (filteredRightDerivedFunctor T hT).obj (twoStepFilteredDerivedInput S hS)

/-! ## The derived graded pieces and the spectral sequence -/

theorem filteredRightDerivedApplication_gradedPieces
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (hS : S.ShortExact) :
    (∀ p : ℤ, p ≠ 0 → p ≠ 1 →
      IsZero ((filteredDerivedGradedFunctor B p).obj
        (filteredRightDerivedApplicationObject T hT S hS))) ∧
      Nonempty ((filteredDerivedGradedFunctor B 0).obj
        (filteredRightDerivedApplicationObject T hT S hS) ≅
          totalRightDerivedObject T hT S.X₃) ∧
      Nonempty ((filteredDerivedGradedFunctor B 1).obj
        (filteredRightDerivedApplicationObject T hT S hS) ≅
          totalRightDerivedObject T hT S.X₁) ∧
      Nonempty ((filteredDerivedForgetfulFunctor B).obj
        (filteredRightDerivedApplicationObject T hT S hS) ≅
          totalRightDerivedObject T hT S.X₂) := by
  sorry

theorem filteredRightDerivedApplication_spectralSequence
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (hS : S.ShortExact) :
    Nonempty (FilteredDerivedSpectralSequence
      (filteredRightDerivedApplicationObject T hT S hS)) := by
  exact filteredDerivedSpectralSequence_exists _

noncomputable def filteredRightDerivedApplication_spectralSequenceData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (hS : S.ShortExact) :
    FilteredDerivedSpectralSequence
      (filteredRightDerivedApplicationObject T hT S hS) :=
  Classical.choice (filteredRightDerivedApplication_spectralSequence T hT S hS)

theorem filteredRightDerivedApplication_first_page
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (hS : S.ShortExact) (p q : ℤ) :
    Nonempty
      (((filteredRightDerivedApplication_spectralSequenceData T hT S hS).spectral_sequence.page 1).X
          (p, q) ≅
        (DerivedCategory.Plus.homologyFunctor B (p + q)).obj
          ((filteredDerivedGradedFunctor B p).obj
            (filteredRightDerivedApplicationObject T hT S hS))) :=
  (filteredRightDerivedApplication_spectralSequenceData T hT S hS).first_page p q

theorem filteredRightDerivedApplication_abutment
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (hS : S.ShortExact) (m : ℤ) :
    Nonempty
      ((filteredRightDerivedApplication_spectralSequenceData T hT S hS).abutment m ≅
        (DerivedCategory.Plus.homologyFunctor B m).obj
          ((filteredDerivedForgetfulFunctor B).obj
            (filteredRightDerivedApplicationObject T hT S hS))) :=
  (filteredRightDerivedApplication_spectralSequenceData T hT S hS).abutment_iso m

/-! ## The long exact sequence -/

def derivedLongTermNat
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (n : ℕ) : B :=
  if n % 3 = 0 then rightDerivedCohomology T hT S.X₁ (n / 3)
  else if n % 3 = 1 then rightDerivedCohomology T hT S.X₂ (n / 3)
  else rightDerivedCohomology T hT S.X₃ (n / 3)

def derivedLongTerm
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (n : ℤ) : B :=
  if h : n < 0 then 0 else derivedLongTermNat T hT S n.toNat

theorem derivedLongTerm_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) (S : ShortComplex A) :
    derivedLongTerm T hT S 0 = T.obj S.X₁ := by
  simp [derivedLongTerm, derivedLongTermNat, rightDerivedCohomology]

theorem derivedLongTerm_one
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) (S : ShortComplex A) :
    derivedLongTerm T hT S 1 = T.obj S.X₂ := by
  simp [derivedLongTerm, derivedLongTermNat, rightDerivedCohomology]

theorem derivedLongTerm_two
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T) (S : ShortComplex A) :
    derivedLongTerm T hT S 2 = T.obj S.X₃ := by
  simp [derivedLongTerm, derivedLongTermNat, rightDerivedCohomology]

theorem filteredDerived_longExactSequence
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A]
    (T : A ⥤ B) (hT : IsLeftExact T)
    (S : ShortComplex A) (hS : S.ShortExact) :
    Nonempty (Formalization.Books.Homology.Unit20.LongExactSequence
      (derivedLongTerm T hT S)) := by
  sorry

/-! ## Frobenius trace application -/

structure FiniteTypeSchemeOver (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k))
  locallyOfFiniteType : LocallyOfFiniteType structureMap
  quasiCompact : QuasiCompact structureMap

abbrev traceCoefficientRing (ell n : ℕ) := ZMod (ell ^ n)

/- The preceding Trace chapters do not yet contain the étale coefficient
   category or compactly supported cohomology.  This interface keeps the
   source's objects and the geometric Frobenius pullback explicit. -/
structure FrobeniusTraceTheory
    {k : Type u} [Field k]
    (X : FiniteTypeSchemeOver k) (ell n : ℕ)
    (C : Type v) [Category.{w} C] [Abelian C] where
  isFlatConstructible : C → Prop
  compactlySupportedCohomology :
    C ⥤ CochainComplex (ModuleCat.{u} (traceCoefficientRing ell n)) ℤ
  geometricFrobeniusPullback : ∀ F : C,
    (compactlySupportedCohomology.obj F ⟶ compactlySupportedCohomology.obj F)
  cohomologicalTrace :
    ∀ (K : CochainComplex (ModuleCat.{u} (traceCoefficientRing ell n)) ℤ),
      (K ⟶ K) → traceCoefficientRing ell n

def frobeniusTrace
    {k : Type u} [Field k]
    {X : FiniteTypeSchemeOver k} {ell n : ℕ}
    {C : Type v} [Category.{w} C] [Abelian C]
    (D : FrobeniusTraceTheory X ell n C) (F : C) :
    traceCoefficientRing ell n :=
  D.cohomologicalTrace _ (D.geometricFrobeniusPullback F)

def FrobeniusTraceAdditive
    {k : Type u} [Field k]
    {X : FiniteTypeSchemeOver k} {ell n : ℕ}
    {C : Type v} [Category.{w} C] [Abelian C]
    (D : FrobeniusTraceTheory X ell n C) : Prop :=
  ∀ (S : ShortComplex C) (hS : S.ShortExact),
    (D.isFlatConstructible S.X₁ ∧
      D.isFlatConstructible S.X₂ ∧
      D.isFlatConstructible S.X₃) →
      frobeniusTrace D S.X₂ =
        frobeniusTrace D S.X₁ + frobeniusTrace D S.X₃

theorem frobeniusTrace_additive_on_shortExact
    {k : Type u} [Field k]
    {X : FiniteTypeSchemeOver k} {ell n : ℕ}
    {C : Type v} [Category.{w} C] [Abelian C]
    (D : FrobeniusTraceTheory X ell n C) :
    FrobeniusTraceAdditive D := by
  sorry

end Formalization.Books.Trace.Unit09
