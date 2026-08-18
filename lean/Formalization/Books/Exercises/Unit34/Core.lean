import Formalization.Books.Exercises.Unit33.Core
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Exercises, Chapter 34: Morphisms

This file contains the concrete affine schemes, projective spaces, and
source-facing predicates used by the exercises.  Scheme-theoretic properties
such as finite and closed immersion are Mathlib's canonical properties.
-/

namespace Formalization.Books.Exercises.Unit34

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Opposite TopologicalSpace

universe u

noncomputable section

/-! ## Sections of a scheme morphism -/

/-- A section of a morphism `X ⟶ S`. -/
def HasSection {X S : Scheme.{u}} (π : X ⟶ S) : Prop :=
  ∃ σ : S ⟶ X, σ ≫ π = 𝟙 S

abbrev openSubscheme (S : Scheme.{u}) (U : Opens S) : Scheme.{u} :=
  Formalization.Books.Exercises.Unit33.openSubscheme S U

abbrev openSubschemeInclusion (S : Scheme.{u}) (U : Opens S) :
    openSubscheme S U ⟶ S :=
  Formalization.Books.Exercises.Unit33.openSubschemeInclusion S U

abbrev IsIntegralScheme :=
  Formalization.Books.Exercises.Unit33.IsIntegralScheme

abbrev IsFiniteTypeMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Formalization.Books.Exercises.Unit33.IsFiniteTypeMorphism f

/-- A section after restriction to a nonempty open of the target. -/
def HasOpenSection {X S : Scheme.{u}} (π : X ⟶ S) : Prop :=
  ∃ U : Opens S, (U : Set S).Nonempty ∧
    ∃ σ : openSubscheme S U ⟶ X,
      σ ≫ π = openSubschemeInclusion S U

/-- The combination of the two properties used in the number-theoretic
exercises. -/
def IsFiniteSurjective {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Function.Surjective f.base

/-- The base-change conclusion discussed in the source's Skolem--Noether
remark. -/
def HasFiniteSurjectiveBaseChangeSection {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
    IsFiniteSurjective g ∧ HasSection (pullback.snd f g)

/-! ## Affine schemes and polynomial presentations -/

/-- The affine scheme associated to a commutative ring. -/
abbrev affineScheme (R : Type u) [CommRing R] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of R)

/-- The scheme map contravariantly induced by a ring homomorphism. -/
def affineSchemeMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : affineScheme S ⟶ affineScheme R :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)

/-- The standard inclusion of a one-variable polynomial ring into a polynomial
ring on finitely many variables. -/
def polynomialBaseMap {K : Type u} [CommRing K] {n : ℕ} (i : Fin n) :
    MvPolynomial (Fin 1) K →+* MvPolynomial (Fin n) K :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    (fun _ ↦ MvPolynomial.X i)

def quotientMap {R : Type u} [CommRing R] (I : Ideal R) :
    R →+* (R ⧸ I) :=
  Ideal.Quotient.mk I

/-! ## The first five affine examples -/

abbrev complexPolynomialRing (n : ℕ) := MvPolynomial (Fin n) ℂ

abbrev noSectionBaseRing := complexPolynomialRing 1
abbrev noSectionPolynomialRing := complexPolynomialRing 2

def noSectionX : noSectionPolynomialRing := MvPolynomial.X 1
def noSectionT : noSectionPolynomialRing := MvPolynomial.X 0
def noSectionInvertingElement : noSectionPolynomialRing :=
  noSectionX * noSectionT

abbrev noSectionLocalizationRing :=
  Localization.Away noSectionInvertingElement

def noSectionBaseToSource : noSectionBaseRing →+* noSectionLocalizationRing :=
  (algebraMap noSectionPolynomialRing noSectionLocalizationRing).comp
    (polynomialBaseMap (K := ℂ) (n := 2) 0)

abbrev noSectionBase : Scheme.{0} := affineScheme noSectionBaseRing
abbrev noSectionSource : Scheme.{0} := affineScheme noSectionLocalizationRing

def noSectionMorphism : noSectionSource ⟶ noSectionBase :=
  affineSchemeMap noSectionBaseToSource

abbrev noRationalSectionBaseRing := complexPolynomialRing 1
abbrev noRationalSectionPolynomialRing := complexPolynomialRing 2

def noRationalSectionRelation : noRationalSectionPolynomialRing :=
  (MvPolynomial.X 0) ^ 2 + MvPolynomial.X 1

abbrev noRationalSectionIdeal :=
  Ideal.span ({noRationalSectionRelation} :
    Set noRationalSectionPolynomialRing)
abbrev noRationalSectionRing :=
  noRationalSectionPolynomialRing ⧸ noRationalSectionIdeal

def noRationalSectionBaseToSource : noRationalSectionBaseRing →+*
    noRationalSectionRing :=
  (quotientMap noRationalSectionIdeal).comp
    (polynomialBaseMap (K := ℂ) (n := 2) 1)

abbrev noRationalSectionBase : Scheme.{0} :=
  affineScheme noRationalSectionBaseRing
abbrev noRationalSectionSource : Scheme.{0} :=
  affineScheme noRationalSectionRing

def noRationalSectionMorphism : noRationalSectionSource ⟶
    noRationalSectionBase :=
  affineSchemeMap noRationalSectionBaseToSource

def rationalSectionPolynomialRing (A B C : noRationalSectionBaseRing) :
    complexPolynomialRing 3 :=
  polynomialBaseMap (K := ℂ) (n := 3) 2 A +
    polynomialBaseMap (K := ℂ) (n := 3) 2 B * (MvPolynomial.X 0) ^ 2 +
    polynomialBaseMap (K := ℂ) (n := 3) 2 C * (MvPolynomial.X 1) ^ 2

abbrev rationalSectionIdeal (A B C : noRationalSectionBaseRing) :=
  Ideal.span ({rationalSectionPolynomialRing A B C} :
    Set (complexPolynomialRing 3))
abbrev rationalSectionRing (A B C : noRationalSectionBaseRing) :=
  complexPolynomialRing 3 ⧸ rationalSectionIdeal A B C

def rationalSectionBaseToSource (A B C : noRationalSectionBaseRing) :
    noRationalSectionBaseRing →+* rationalSectionRing A B C :=
  (quotientMap (rationalSectionIdeal A B C)).comp
    (polynomialBaseMap (K := ℂ) (n := 3) 2)

abbrev rationalSectionSource (A B C : noRationalSectionBaseRing) : Scheme.{0} :=
  affineScheme (rationalSectionRing A B C)

def rationalSectionMorphism (A B C : noRationalSectionBaseRing) :
    rationalSectionSource A B C ⟶ noSectionBase :=
  affineSchemeMap (rationalSectionBaseToSource A B C)

abbrev noSectionCurvePolynomialRing := complexPolynomialRing 3
def noSectionCurveRelation : noSectionCurvePolynomialRing :=
  1 + MvPolynomial.X 2 * (MvPolynomial.X 0) ^ 3 +
    (MvPolynomial.X 2) ^ 2 * (MvPolynomial.X 1) ^ 3
abbrev noSectionCurveIdeal :=
  Ideal.span ({noSectionCurveRelation} : Set noSectionCurvePolynomialRing)
abbrev noSectionCurveRing := noSectionCurvePolynomialRing ⧸ noSectionCurveIdeal
def noSectionCurveBaseToSource : noSectionBaseRing →+* noSectionCurveRing :=
  (quotientMap noSectionCurveIdeal).comp
    (polynomialBaseMap (K := ℂ) (n := 3) 2)
abbrev noSectionCurveSource : Scheme.{0} := affineScheme noSectionCurveRing
def noSectionCurveMorphism : noSectionCurveSource ⟶ noSectionBase :=
  affineSchemeMap noSectionCurveBaseToSource

abbrev noSectionSurfaceBaseRing := complexPolynomialRing 2
abbrev noSectionSurfacePolynomialRing := complexPolynomialRing 10

def noSectionSurfaceBaseMap : noSectionSurfaceBaseRing →+*
    noSectionSurfacePolynomialRing :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℂ →+* noSectionSurfacePolynomialRing)
    (Fin.cases (MvPolynomial.X 8) (fun _ ↦ MvPolynomial.X 9))

def noSectionSurfaceRelation : noSectionSurfacePolynomialRing :=
  1 + MvPolynomial.X 8 * (MvPolynomial.X 0) ^ 3 +
    (MvPolynomial.X 8) ^ 2 * (MvPolynomial.X 1) ^ 3 +
    MvPolynomial.X 9 * (MvPolynomial.X 2) ^ 3 +
    MvPolynomial.X 8 * MvPolynomial.X 9 * (MvPolynomial.X 3) ^ 3 +
    (MvPolynomial.X 8) ^ 2 * MvPolynomial.X 9 * (MvPolynomial.X 4) ^ 3 +
    (MvPolynomial.X 9) ^ 2 * (MvPolynomial.X 5) ^ 3 +
    MvPolynomial.X 8 * (MvPolynomial.X 9) ^ 2 * (MvPolynomial.X 6) ^ 3 +
    (MvPolynomial.X 8) ^ 2 * (MvPolynomial.X 9) ^ 2 * (MvPolynomial.X 7) ^ 3

abbrev noSectionSurfaceIdeal :=
  Ideal.span ({noSectionSurfaceRelation} :
    Set noSectionSurfacePolynomialRing)
abbrev noSectionSurfaceRing :=
  noSectionSurfacePolynomialRing ⧸ noSectionSurfaceIdeal
def noSectionSurfaceBaseToSource : noSectionSurfaceBaseRing →+*
    noSectionSurfaceRing :=
  (quotientMap noSectionSurfaceIdeal).comp noSectionSurfaceBaseMap
abbrev noSectionSurfaceBase : Scheme.{0} := affineScheme noSectionSurfaceBaseRing
abbrev noSectionSurfaceSource : Scheme.{0} := affineScheme noSectionSurfaceRing
def noSectionSurfaceMorphism : noSectionSurfaceSource ⟶ noSectionSurfaceBase :=
  affineSchemeMap noSectionSurfaceBaseToSource

/-! ## Finite-surjective closed subschemes -/

abbrev numberTheoryPolynomialRing := MvPolynomial (Fin 1) ℤ
def numberTheoryX : numberTheoryPolynomialRing := MvPolynomial.X 0
def numberTheoryInvertingElement : numberTheoryPolynomialRing :=
  numberTheoryX * (numberTheoryX - 1) * (2 * numberTheoryX - 1)
abbrev numberTheoryLocalizationRing :=
  Localization.Away numberTheoryInvertingElement
abbrev numberTheoryScheme : Scheme.{0} :=
  affineScheme numberTheoryLocalizationRing
abbrev numberTheoryBase : Scheme.{0} := affineScheme ℤ
def numberTheoryBaseToSource : ℤ →+* numberTheoryLocalizationRing :=
  algebraMap ℤ numberTheoryLocalizationRing
def numberTheoryMorphism : numberTheoryScheme ⟶ numberTheoryBase :=
  affineSchemeMap numberTheoryBaseToSource

abbrev finiteFieldPolynomialRing (p : ℕ) := MvPolynomial (Fin 1) (ZMod p)
abbrev finiteFieldTwoVariableRing (p : ℕ) := MvPolynomial (Fin 2) (ZMod p)

def finiteFieldX (p : ℕ) : finiteFieldTwoVariableRing p := MvPolynomial.X 0
def finiteFieldT (p : ℕ) : finiteFieldTwoVariableRing p := MvPolynomial.X 1
def finiteFieldInvertingElement (p : ℕ) : finiteFieldTwoVariableRing p :=
  finiteFieldX p * (finiteFieldX p - finiteFieldT p) *
    (finiteFieldT p * finiteFieldX p - 1)
abbrev finiteFieldLocalizationRing (p : ℕ) :=
  Localization.Away (finiteFieldInvertingElement p)
def finiteFieldBaseToSource (p : ℕ) [Fact p.Prime] :
    finiteFieldPolynomialRing p →+* finiteFieldLocalizationRing p :=
  (algebraMap (finiteFieldTwoVariableRing p)
      (finiteFieldLocalizationRing p)).comp
    (polynomialBaseMap (K := ZMod p) (n := 2) 1)
abbrev finiteFieldBase (p : ℕ) := affineScheme (finiteFieldPolynomialRing p)
abbrev finiteFieldScheme (p : ℕ) := affineScheme (finiteFieldLocalizationRing p)
def finiteFieldMorphism (p : ℕ) [Fact p.Prime] :
    finiteFieldScheme p ⟶ finiteFieldBase p :=
  affineSchemeMap (finiteFieldBaseToSource p)

/-! ## The non-quasi-section example -/

abbrev noQuasiSectionPolynomialRing := complexPolynomialRing 2
def noQuasiSectionX : noQuasiSectionPolynomialRing := MvPolynomial.X 0
def noQuasiSectionT : noQuasiSectionPolynomialRing := MvPolynomial.X 1
def noQuasiSectionLinearFactor (α : ℂ) : noQuasiSectionPolynomialRing :=
  noQuasiSectionT - MvPolynomial.C α
abbrev noQuasiSectionLocalizationRing (f : noQuasiSectionPolynomialRing) :=
  Localization.Away f
abbrev noQuasiSectionBase : Scheme.{0} := affineScheme noSectionBaseRing
abbrev noQuasiSectionSource (f : noQuasiSectionPolynomialRing) : Scheme.{0} :=
  affineScheme (noQuasiSectionLocalizationRing f)
def noQuasiSectionBaseToSource (f : noQuasiSectionPolynomialRing) :
    noSectionBaseRing →+* noQuasiSectionLocalizationRing f :=
  (algebraMap noQuasiSectionPolynomialRing _).comp
    (polynomialBaseMap (K := ℂ) (n := 2) 1)
def noQuasiSectionMorphism (f : noQuasiSectionPolynomialRing) :
    noQuasiSectionSource f ⟶ noQuasiSectionBase :=
  affineSchemeMap (noQuasiSectionBaseToSource f)

def noQuasiSectionCandidate : noQuasiSectionPolynomialRing :=
  (noQuasiSectionX * noQuasiSectionT - 2) *
    (noQuasiSectionX - noQuasiSectionT + 3)

/-! ## Projective spaces and projectivity -/

abbrev projectiveSpaceGrading {R : Type u} [CommRing R] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

noncomputable def projectiveSpace (R : Type u) [CommRing R] (n : ℕ) : Scheme.{u} :=
  letI : GradedAlgebra (projectiveSpaceGrading (R := R) n) :=
    MvPolynomial.gradedAlgebra
  AlgebraicGeometry.«Proj» (projectiveSpaceGrading (R := R) n)

noncomputable def projectiveSpaceStructureMap
    (R : Type u) [CommRing R] (n : ℕ) :
    projectiveSpace R n ⟶ affineScheme R :=
  by
    letI : GradedAlgebra (projectiveSpaceGrading (R := R) n) :=
      MvPolynomial.gradedAlgebra
    change AlgebraicGeometry.«Proj» (projectiveSpaceGrading (R := R) n) ⟶
      affineScheme R
    exact AlgebraicGeometry.Proj.toSpecZero
        (projectiveSpaceGrading (R := R) n) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (algebraMap R (projectiveSpaceGrading (R := R) n 0)))

/-- A projective scheme over `Spec R`, in the standard closed-immersion
presentation used by the textbook. -/
def IsProjectiveOver (R : Type u) [CommRing R]
    (X : Scheme.{u}) (p : X ⟶ affineScheme R) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ projectiveSpace R n,
    IsClosedImmersion i ∧ i ≫ projectiveSpaceStructureMap R n = p

/-- The source's “projective variety over a field” package: integral, finite
type, and projective over the field. -/
def IsProjectiveVarietyOver (k : Type u) [Field k]
    (X : Scheme.{u}) (p : X ⟶ affineScheme k) : Prop :=
  IsIntegralScheme X ∧ IsFiniteTypeMorphism p ∧ IsProjectiveOver k X p

end

end Formalization.Books.Exercises.Unit34
