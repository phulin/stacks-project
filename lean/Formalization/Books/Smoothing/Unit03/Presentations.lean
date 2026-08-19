import Formalization.Books.Smoothing.Unit02
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.MoreAlgebra.Unit03.StablyFree
import Formalization.Books.MoreAlgebra.Unit33.Core
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Smoothing Ring Maps, Chapter 3: presentations of algebras

This file records the presentation-improvement, lifting, standard-smooth, and
standard-element interfaces in the chapter.  The canonical Mathlib predicates
for smooth and standard-smooth maps, and the earlier chapter's syntomic and
relative-global-complete-intersection predicates, are used throughout.
-/

namespace Formalization.Books.Smoothing.Unit03

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit127
open Formalization.Books.Algebra.Unit131
open Formalization.Books.Algebra.Unit136
open Formalization.Books.Smoothing.Unit02

open scoped TensorProduct

noncomputable section

universe u v

/-! ## The improved presentation -/

/-- The symmetric algebra appearing in the improved-presentation construction.
This is Mathlib's concrete symmetric algebra, applied to the conormal module of
a chosen finite polynomial presentation. -/
abbrev symmetricAlgebraOfPresentation
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m)) : Type u :=
  SymmetricAlgebra A P.toExtension.Cotangent

/- The canonical map between the two principal localizations induced by a
ring homomorphism. -/
noncomputable def localizedAwayAlgebraMap
    {A C : Type u} [CommRing A] [CommRing C]
    (f : A →+* C) (a : A) :
    Localization.Away a →+* Localization.Away (f a) := by
  exact Localization.awayLift
    ((algebraMap C (Localization.Away (f a))).comp f) a (by
      change IsUnit (algebraMap C (Localization.Away (f a)) (f a))
      exact IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (f a)) (f a))

/-- The kernel module `K` in the proof of the improved-presentation lemma. -/
def presentationRelationKernel
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    Submodule A (Fin m → A) :=
  LinearMap.ker (presentationRelationMap P
    ⟨id, fun _ _ h => h⟩)

/-- The exact sequence displayed in the proof of the improved-presentation
lemma, with the two conormal modules represented by Mathlib presentations. -/
def HasImprovedPresentationExactSequence
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    {n m n' m' : ℕ}
    (P : Algebra.Presentation R A (Fin n) (Fin m))
    (Q : Algebra.Presentation R C (Fin n') (Fin m')) : Prop :=
    ∃ α : TensorProduct A C P.toExtension.Cotangent →ₗ[C]
      Q.toExtension.Cotangent,
    ∃ β : Q.toExtension.Cotangent →ₗ[C]
      TensorProduct A C (presentationRelationKernel P),
      Function.Exact α β ∧ Function.Surjective β

/-- The localized exact sequence displayed in the proof of the improved-
presentation lemma.  The direct-summand copies of the localized base ring are
represented by products of modules. -/
def HasLocalizedImprovedPresentationExactSequence
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    {n m n' m' : ℕ}
    (P : Algebra.Presentation R A (Fin n) (Fin m))
    (Q : Algebra.Presentation R C (Fin n') (Fin m')) (a : A) : Prop :=
  let Cₐ := Localization.Away (algebraMap A C a)
  ∃ α : (Cₐ × TensorProduct A Cₐ P.toExtension.Cotangent) →ₗ[Cₐ]
      (Cₐ × TensorProduct C Cₐ Q.toExtension.Cotangent),
    ∃ β : (Cₐ × TensorProduct C Cₐ Q.toExtension.Cotangent) →ₗ[Cₐ]
      TensorProduct A Cₐ (presentationRelationKernel P),
      Function.Exact α β ∧ Function.Surjective β

/-- The precise assertion behind the first lemma of the section: a finite
presentation admits the symmetric-algebra retraction with the two local
properties in the source.  The proof-level exact sequences are exposed
separately by `HasImprovedPresentationExactSequence` and
`HasLocalizedImprovedPresentationExactSequence`. -/
theorem exists_improved_presentation
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ (n m : ℕ) (P : Algebra.Presentation R A (Fin n) (Fin m)),
      let C := symmetricAlgebraOfPresentation P
      RingHom.FiniteType (algebraMap A C) ∧
        RingHom.FiniteType (algebraMap R C) ∧
        Function.LeftInverse
          (SymmetricAlgebra.algebraMapInv (R := A)
            (M := P.toExtension.Cotangent))
          (algebraMap A C) ∧
        (∀ a : A,
            Formalization.Books.MoreAlgebra.Unit33.IsLocalCompleteIntersection
              R (Localization.Away a) →
            (RingHom.Smooth
              (localizedAwayAlgebraMap (algebraMap A C) a) ∧
              Formalization.Books.Algebra.Unit136.HasFreeConormalPresentation
                (algebraMap R (Localization.Away (algebraMap A C a))))) ∧
        (∀ a : A,
          RingHom.Smooth (algebraMap R (Localization.Away a)) →
            Module.Free (Localization.Away (algebraMap A C a))
              (ModuleOfDifferentials R (Localization.Away (algebraMap A C a)))) := by
  sorry

/-- Over a Noetherian base, the symmetric algebra in the construction is of
finite presentation over the base. -/
theorem symmetricAlgebraOfPresentation_finitePresentation
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [Algebra.FinitePresentation R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    Algebra.FinitePresentation R
      (symmetricAlgebraOfPresentation P) := by
  sorry

/-- The exact sequence in the proof of the improved-presentation lemma is
available for the selected presentations. -/
theorem exists_improvedPresentation_exactSequences
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ (n m n' m' : ℕ) (P : Algebra.Presentation R A (Fin n) (Fin m)),
      ∃ Q : Algebra.Presentation R (symmetricAlgebraOfPresentation P)
          (Fin n') (Fin m'),
        HasImprovedPresentationExactSequence P Q ∧
          ∀ a : A, HasLocalizedImprovedPresentationExactSequence P Q a := by
  sorry

/-! ## Lifting syntomic and smooth maps along a surjection -/

/-- A lift of a map across a quotient, including the reduction isomorphism
used in the source's lifting proposition. -/
structure QuotientLiftData
    {R R₀ A₀ : Type u} [CommRing R] [CommRing R₀] [CommRing A₀]
    (q : R →+* R₀) (f₀ : R₀ →+* A₀) where
  A : Type u
  [commRingA : CommRing A]
  lift : R →+* A
  reduction : A →+* A₀
  reduction_comm : reduction.comp lift = f₀.comp q
  reductionIso : A ⧸ Ideal.map lift (RingHom.ker q) ≃+* A₀
  reductionIso_comp_quotientMk :
    reductionIso.toRingHom.comp (Ideal.Quotient.mk (Ideal.map lift (RingHom.ker q))) =
      reduction

/-- Syntomic algebras lift across surjective base maps. -/
theorem exists_syntomic_quotient_lift
    {R R₀ A₀ : Type u} [CommRing R] [CommRing R₀] [CommRing A₀]
    (q : R →+* R₀) (hq : Function.Surjective q)
    (f₀ : R₀ →+* A₀)
    (hf₀ : IsSyntomic f₀) :
    ∃ d : QuotientLiftData q f₀,
      (let _ : CommRing d.A := d.commRingA
       IsSyntomic d.lift) := by
  sorry

/-- Smooth algebras lift across surjective base maps. -/
theorem exists_smooth_quotient_lift
    {R R₀ A₀ : Type u} [CommRing R] [CommRing R₀] [CommRing A₀]
    (q : R →+* R₀) (hq : Function.Surjective q)
    (f₀ : R₀ →+* A₀)
    (hf₀ : RingHom.Smooth f₀) :
    ∃ d : QuotientLiftData q f₀,
      (let _ : CommRing d.A := d.commRingA
       RingHom.Smooth d.lift) := by
  sorry

/-! ## Relative complete intersections and standard smoothness -/

/-- A smooth retraction of the sort used in the chapter's complete-
intersection lemma. -/
structure SmoothRetractionData
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (f : R →+* A) where
  C : Type u
  [commRingC : CommRing C]
  lift : A →+* C
  retract : C →+* A
  lift_smooth : RingHom.Smooth lift
  retract_lift : retract.comp lift = RingHom.id A
  base_compatibility : retract.comp (lift.comp f) = f

/- The source's “global relative complete intersection” includes the flatness
of the map to the displayed polynomial quotient. -/
def IsFlatRelativeGlobalCompleteIntersection
    {R C : Type u} [CommRing R] [CommRing C]
    (f : R →+* C) : Prop :=
  RingHom.Flat f ∧ IsRelativeGlobalCompleteIntersection f

/-- A smooth algebra admits a smooth retraction into a relative global
complete intersection over the base. -/
theorem exists_smooth_retraction_relativeGlobalCompleteIntersection
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (f : R →+* A)
    (hf : IsSyntomic f) :
    ∃ d : SmoothRetractionData f,
      (let _ : CommRing d.C := d.commRingC
       IsFlatRelativeGlobalCompleteIntersection (d.lift.comp f)) := by
  sorry

/-- The differential exact sequence for a finite relative complete
intersection presentation.  The last conjunct identifies the first map with
the Jacobian matrix of the named relations. -/
def HasRelativeCompleteIntersectionDifferentialSequence
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    {n c : ℕ} (P : Algebra.Presentation R C (Fin n) (Fin c)) : Prop :=
  ∃ d : (Fin c → C) →ₗ[C] (Fin n → C),
    ∃ π : (Fin n → C) →ₗ[C] ModuleOfDifferentials R C,
      Function.Exact d π ∧ Function.Surjective π ∧
        ∀ j, d (Pi.single j 1) =
          fun i => MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation j))

/-- The exact sequence used in the standard-smooth construction is available
for the relative complete-intersection stage. -/
theorem exists_relativeCompleteIntersection_differentialSequence
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    (hsmooth : RingHom.Smooth (algebraMap R C))
    (hci : IsFlatRelativeGlobalCompleteIntersection (algebraMap R C)) :
    ∃ (n c : ℕ) (P : Algebra.Presentation R C (Fin n) (Fin c)),
      HasRelativeCompleteIntersectionDifferentialSequence P := by
  sorry

/-- A smooth algebra admits a smooth retraction into a standard-smooth
algebra over the base. -/
theorem exists_smooth_retraction_standardSmooth
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (f : R →+* A) (hf : RingHom.Smooth f) :
    ∃ d : SmoothRetractionData f,
      (let _ : CommRing d.C := d.commRingC
       RingHom.IsStandardSmooth (d.lift.comp f)) := by
  sorry

/-- The polynomial-coordinate map used in the proof of the standard-smooth
lemma is étale. -/
def HasEtalePolynomialFactorization
    {R B : Type u} [CommRing R] [CommRing B]
    (f : R →+* B) : Prop :=
  ∃ n : ℕ, ∃ φ : MvPolynomial (Fin n) R →+* B,
    RingHom.Etale φ ∧
      φ.comp (algebraMap R (MvPolynomial (Fin n) R)) = f

/-- Standard smoothness supplies the étale polynomial factorization used in
the coordinate-change argument. -/
theorem standardSmooth_hasEtalePolynomialFactorization
    {R B : Type u} [CommRing R] [CommRing B]
    (f : R →+* B) (hf : RingHom.IsStandardSmooth f) :
    HasEtalePolynomialFactorization f := by
  sorry

/-! ## Filtered colimits and standard-smooth stages -/

/-- The source's phrase “filtered colimit of smooth `R`-algebras”, expressed
using the canonical filtered-algebra-colimit package from Chapter 127. -/
def IsFilteredColimitOfSmooth
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : Prop :=
  Nonempty (FilteredAlgebraColimitIn f
    {B | RingHom.Smooth B.hom.hom})

/-- A filtered colimit of smooth algebras is a filtered colimit of
standard-smooth algebras. -/
theorem filteredColimitOfSmooth_isFilteredColimitOfStandardSmooth
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (h : IsFilteredColimitOfSmooth f) :
    Nonempty (FilteredAlgebraColimitIn f
      {B | RingHom.IsStandardSmooth B.hom.hom}) := by
  sorry

/-! ## Prescribed generators -/

/-- A submersive presentation whose first variables represent a prescribed
finite set of elements.  The equality of `P.map` with the first-coordinate
embedding is the source's displayed Jacobian minor. -/
def HasInitialGeneratorPresentation
    {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (E : Finset A) : Prop :=
    ∃ (m c : ℕ) (hcm : c ≤ E.card + m)
    (P : Algebra.SubmersivePresentation R A (Fin (E.card + m)) (Fin c)),
    E.card ≤ c ∧
      P.map = Fin.castLE hcm ∧
      ∃ e : Fin E.card → A,
        (E : Set A) = Set.range e ∧
          ∀ i, P.val (Fin.castAdd m i) = e i

/-- A standard-smooth map admits a standard presentation containing any finite
set of target generators. -/
theorem standardSmooth_hasInitialGeneratorPresentation
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hf : Algebra.IsStandardSmooth R A) (E : Finset A) :
    HasInitialGeneratorPresentation (R := R) (A := A) E := by
  sorry

/-! ## Comparison of standardness conditions -/

def SmoothAtElement
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (a : A) : Prop :=
  Algebra.Smooth R (Localization.Away a)

def SmoothAtElementWithStablyFreeDifferentials
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (a : A) : Prop :=
  SmoothAtElement R A a ∧
    Module.IsStablyFree (Localization.Away a)
      (ModuleOfDifferentials R (Localization.Away a))

def SmoothAtElementWithFreeDifferentials
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (a : A) : Prop :=
  SmoothAtElement R A a ∧
    Module.Free (Localization.Away a)
      (ModuleOfDifferentials R (Localization.Away a))

def StandardSmoothAtElement
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (a : A) : Prop :=
  Algebra.IsStandardSmooth R (Localization.Away a)

theorem standardSmoothAtElement_implies_freeDifferentials
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A) :
    StandardSmoothAtElement R A a →
      SmoothAtElementWithFreeDifferentials R A a := by
  sorry

theorem freeDifferentials_implies_stablyFreeDifferentials
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A) :
    SmoothAtElementWithFreeDifferentials R A a →
      SmoothAtElementWithStablyFreeDifferentials R A a := by
  sorry

theorem stablyFreeDifferentials_implies_smoothAtElement
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A) :
    SmoothAtElementWithStablyFreeDifferentials R A a →
      SmoothAtElement R A a := by
  intro h
  exact h.1

/-- Elementary standardness implies strict standardness; this is the earlier
chapter's canonical bridge. -/
theorem elementaryStandardAtElement_implies_strictlyStandardAtElement
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (a : A) :
    IsElementaryStandard R A a → IsStrictlyStandard R A a := by
  intro h
  exact elementaryStandard_isStrictlyStandard h

theorem elementaryStandardAtElement_implies_standardSmoothAtElement
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A) :
    IsElementaryStandard R A a → StandardSmoothAtElement R A a := by
  sorry

theorem strictlyStandardAtElement_implies_stablyFreeDifferentials
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A) :
    IsStrictlyStandard R A a →
      SmoothAtElementWithStablyFreeDifferentials R A a := by
  sorry

theorem eventually_strictlyStandard_of_stablyFreeDifferentials
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A)
    (h : SmoothAtElementWithStablyFreeDifferentials R A a) :
    ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → IsStrictlyStandard R A (a ^ e) := by
  sorry

theorem eventually_elementaryStandard_of_standardSmooth
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (a : A)
    (h : StandardSmoothAtElement R A a) :
    ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → IsElementaryStandard R A (a ^ e) := by
  sorry

end

end Formalization.Books.Smoothing.Unit03
