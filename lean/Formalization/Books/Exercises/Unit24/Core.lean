import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Topology

import Formalization.Books.Exercises.Unit16.Core

/-!
# Exercises, Chapter 24: Going up and going down

The source's spectra are represented by Mathlib's `PrimeSpectrum`, and the
polynomial rings in several variables use the canonical `MvPolynomial`
presentation exposed by Chapter 16.  The ring-map predicates below adapt
Mathlib's canonical going-up and going-down classes to the source's explicit
`RingHom` formulation.
-/

noncomputable section

universe u

open Set

namespace Formalization.Books.Exercises.Unit24

/-! ## Definition `GU-GD` -/

/-- The source's going-up predicate for a ring homomorphism.

The body is Mathlib's canonical `Algebra.HasGoingUp`, with the algebra
structure induced by the given ring homomorphism. -/
def GoingUpProperty {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) : Prop :=
  @Algebra.HasGoingUp A B _ _ φ.toAlgebra

/-- The source's going-down predicate for a ring homomorphism. -/
def GoingDownProperty {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) : Prop :=
  @Algebra.HasGoingDown A B _ _ φ.toAlgebra

/-- A prime of the target lies over a prime of the source when its contraction
is the given source prime. -/
def LiesOver {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : PrimeSpectrum A) (P : PrimeSpectrum B) : Prop :=
  PrimeSpectrum.comap φ P = p

/-! ## Ring maps occurring in `exercise-GU-GD` -/

/-- The structure map from a field to its one-variable polynomial ring. -/
def fieldToPolynomialMap (k : Type u) [Field k] : k →+* Polynomial k :=
  Polynomial.C

/-- The inclusion of the `x`-polynomial ring into the `x,y`-polynomial ring. -/
def polynomialToBivariateMap (k : Type u) [Field k] :
    Polynomial k →+* Formalization.Books.Exercises.Unit16.polynomialRing k 2 :=
  Polynomial.eval₂RingHom
    (MvPolynomial.C : k →+* Formalization.Books.Exercises.Unit16.polynomialRing k 2)
    (MvPolynomial.X (0 : Fin 2))

/-- The localization map `ℤ → ℤ[1/11]`. -/
abbrev integerLocalizationAt11 : Type := Localization.Away (11 : ℤ)

def integerToLocalizationAt11 : ℤ →+* integerLocalizationAt11 :=
  algebraMap ℤ integerLocalizationAt11

/-! ### The integral polynomial tower in case (4) -/

/-- The ideal `(x²-y, z²-x)` in `k[x,y,z]`. -/
def algebraicTowerIdeal (k : Type u) [Field k] :
    Ideal (Formalization.Books.Exercises.Unit16.polynomialRing k 3) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 3) ^ 2 - MvPolynomial.X (1 : Fin 3),
      MvPolynomial.X (2 : Fin 3) ^ 2 - MvPolynomial.X (0 : Fin 3)} :
      Set (Formalization.Books.Exercises.Unit16.polynomialRing k 3))

abbrev algebraicTowerRing (k : Type u) [Field k] : Type u :=
  Formalization.Books.Exercises.Unit16.polynomialRing k 3 ⧸ algebraicTowerIdeal k

/-- The map `k[x,y] → k[x,y,z]/(x²-y,z²-x)`. -/
def algebraicTowerMap (k : Type u) [Field k] :
    Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+* algebraicTowerRing k :=
  MvPolynomial.eval₂Hom
    ((Ideal.Quotient.mk (algebraicTowerIdeal k)).comp
      (MvPolynomial.C : k →+*
        Formalization.Books.Exercises.Unit16.polynomialRing k 3))
    (fun i : Fin 2 =>
      Ideal.Quotient.mk (algebraicTowerIdeal k)
        (MvPolynomial.X (Fin.castSucc i)))

/-! ### Gaussian-integer localizations in cases (5) and (6) -/

/-- A canonical quotient model for `ℤ[i]`. -/
abbrev gaussianPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 2 + Polynomial.C 1

abbrev gaussianIntegerModel : Type := AdjoinRoot gaussianPolynomial

/-- The class of `i` in the quotient model of `ℤ[i]`. -/
def gaussianImaginaryUnit : gaussianIntegerModel :=
  AdjoinRoot.root gaussianPolynomial

/-- The element `2+i`. -/
def gaussianTwoPlusI : gaussianIntegerModel :=
  algebraMap ℤ gaussianIntegerModel 2 + gaussianImaginaryUnit

/-- The element `14+7i`. -/
def gaussianFourteenPlusSevenI : gaussianIntegerModel :=
  algebraMap ℤ gaussianIntegerModel 14 +
    algebraMap ℤ gaussianIntegerModel 7 * gaussianImaginaryUnit

abbrev gaussianLocalizationAtTwoPlusI : Type :=
  Localization.Away gaussianTwoPlusI

abbrev gaussianLocalizationAtFourteenPlusSevenI : Type :=
  Localization.Away gaussianFourteenPlusSevenI

/-- The map from `ℤ` into a localization of the Gaussian-integer model. -/
def integerToGaussianLocalization (a : gaussianIntegerModel) :
    ℤ →+* Localization.Away a :=
  (algebraMap gaussianIntegerModel (Localization.Away a)).comp
    (algebraMap ℤ gaussianIntegerModel)

def integerToGaussianLocalizationAtTwoPlusI :
    ℤ →+* gaussianLocalizationAtTwoPlusI :=
  integerToGaussianLocalization gaussianTwoPlusI

def integerToGaussianLocalizationAtFourteenPlusSevenI :
    ℤ →+* gaussianLocalizationAtFourteenPlusSevenI :=
  integerToGaussianLocalization gaussianFourteenPlusSevenI

/-! ### Case (7), the idempotent quotient and localization -/

/-- The ideal `(y²-y)` in `k[x,y]`. -/
def idempotentPolynomialIdeal (k : Type u) [Field k] :
    Ideal (Formalization.Books.Exercises.Unit16.polynomialRing k 2) :=
  Ideal.span
    ({MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (1 : Fin 2)} :
      Set (Formalization.Books.Exercises.Unit16.polynomialRing k 2))

abbrev idempotentQuotientRing (k : Type u) [Field k] : Type u :=
  Formalization.Books.Exercises.Unit16.polynomialRing k 2 ⧸
    idempotentPolynomialIdeal k

/-- The image of `xy-1` in the idempotent quotient. -/
def idempotentLocalizationElement (k : Type u) [Field k] :
    idempotentQuotientRing k :=
  Ideal.Quotient.mk (idempotentPolynomialIdeal k)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1)

abbrev idempotentLocalizationRing (k : Type u) [Field k] : Type u :=
  Localization.Away (idempotentLocalizationElement k)

def idempotentLocalizationCoefficientMap (k : Type u) [Field k] :
    k →+* idempotentLocalizationRing k :=
  (algebraMap (idempotentQuotientRing k) (idempotentLocalizationRing k)).comp
    ((Ideal.Quotient.mk (idempotentPolynomialIdeal k)).comp
      (MvPolynomial.C : k →+*
        Formalization.Books.Exercises.Unit16.polynomialRing k 2))

/-- The map `k[x] → k[x,y,1/(xy-1)]/(y²-y)`. -/
def idempotentLocalizationMap (k : Type u) [Field k] :
    Polynomial k →+* idempotentLocalizationRing k :=
  Polynomial.eval₂RingHom
    (idempotentLocalizationCoefficientMap k)
    ((algebraMap (idempotentQuotientRing k) (idempotentLocalizationRing k))
      (Ideal.Quotient.mk (idempotentPolynomialIdeal k)
        (MvPolynomial.X (0 : Fin 2))))

/-! ## Ring maps occurring in `exercise-images` -/

/-- The map `k[x,y] → k[x,yx⁻¹]`, with the second target variable renamed to
`yx⁻¹`. -/
def reciprocalImageMap (k : Type u) [Field k] :
    Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+*
      Formalization.Books.Exercises.Unit16.polynomialRing k 2 :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : k →+*
      Formalization.Books.Exercises.Unit16.polynomialRing k 2)
    (fun i : Fin 2 =>
      if i = 0 then MvPolynomial.X (0 : Fin 2)
      else MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))

/-- The ideal `(ax-by-1)` in `k[x,y,a,b]`. -/
def unitEquationIdeal (k : Type u) [Field k] :
    Ideal (Formalization.Books.Exercises.Unit16.polynomialRing k 4) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4) -
          MvPolynomial.X (1 : Fin 4) * MvPolynomial.X (3 : Fin 4) - 1} :
      Set (Formalization.Books.Exercises.Unit16.polynomialRing k 4))

abbrev unitEquationRing (k : Type u) [Field k] : Type u :=
  Formalization.Books.Exercises.Unit16.polynomialRing k 4 ⧸ unitEquationIdeal k

/-- The projection map from the ring in the second image computation. -/
def unitEquationMap (k : Type u) [Field k] :
    Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+* unitEquationRing k :=
  MvPolynomial.eval₂Hom
    ((Ideal.Quotient.mk (unitEquationIdeal k)).comp
      (MvPolynomial.C : k →+*
        Formalization.Books.Exercises.Unit16.polynomialRing k 4))
    (fun i : Fin 2 =>
      Ideal.Quotient.mk (unitEquationIdeal k)
        (MvPolynomial.X (Fin.castAdd 2 i)))

/-! ### The cusp parameterization in image computation (3) -/

def cuspParameterPolynomial (k : Type u) [Field k] : Polynomial k :=
  Polynomial.X - Polynomial.C 1

abbrev cuspParameterRing (k : Type u) [Field k] : Type u :=
  Localization.Away (cuspParameterPolynomial k)

def cuspParameterCoefficientMap (k : Type u) [Field k] :
    k →+* cuspParameterRing k :=
  (algebraMap (Polynomial k) (cuspParameterRing k)).comp
    (Polynomial.C : k →+* Polynomial k)

/-- The map `k[x,y] → k[t,1/(t-1)]`, with `x ↦ t²` and `y ↦ t³`. -/
def cuspParameterMap (k : Type u) [Field k] :
    Formalization.Books.Exercises.Unit16.polynomialRing k 2 →+* cuspParameterRing k :=
  MvPolynomial.eval₂Hom
    (cuspParameterCoefficientMap k)
    (fun i : Fin 2 =>
      if i = 0 then
        (algebraMap (Polynomial k) (cuspParameterRing k)) (Polynomial.X ^ 2)
      else
        (algebraMap (Polynomial k) (cuspParameterRing k)) (Polynomial.X ^ 3))

/-! ### The cubic curve in image computation (4) -/

/-- The ideal `(s³+t³-1)` in the source curve ring. -/
def cubicCurveIdeal : Ideal (Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2) ^ 3 + MvPolynomial.X (1 : Fin 2) ^ 3 - 1} :
      Set (Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2))

abbrev cubicCurveRing : Type :=
  Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2 ⧸ cubicCurveIdeal

/-- The map `ℂ[x,y] → ℂ[s,t]/(s³+t³-1)`, with `x ↦ s²` and `y ↦ t²`. -/
def cubicSquareMap :
    Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2 →+* cubicCurveRing :=
  MvPolynomial.eval₂Hom
    ((Ideal.Quotient.mk cubicCurveIdeal).comp
      (MvPolynomial.C : ℂ →+*
        Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2))
    (fun i : Fin 2 =>
      (Ideal.Quotient.mk cubicCurveIdeal (MvPolynomial.X i)) ^ 2)

/-! ## Source-facing answers for the four image computations -/

/-- The image answer for `k[x,yx⁻¹]`. -/
def reciprocalImageAnswer (k : Type u) [Field k] :
    Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2)) :=
  (PrimeSpectrum.basicOpen (MvPolynomial.X (R := k) (0 : Fin 2)) :
      Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2))) ∪
    PrimeSpectrum.zeroLocus
      ({MvPolynomial.X (R := k) (0 : Fin 2), MvPolynomial.X (R := k) (1 : Fin 2)} :
        Set (Formalization.Books.Exercises.Unit16.polynomialRing k 2))

/-- The image answer for `k[x,y,a,b]/(ax-by-1)`. -/
def unitEquationImageAnswer (k : Type u) [Field k] :
    Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2)) :=
  (PrimeSpectrum.basicOpen (MvPolynomial.X (R := k) (0 : Fin 2)) :
      Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2))) ∪
    (PrimeSpectrum.basicOpen (MvPolynomial.X (R := k) (1 : Fin 2)) :
      Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2)))

/-- The equation of the cusp `y²=x³`. -/
def cuspEquation (k : Type u) [Field k] :
    Formalization.Books.Exercises.Unit16.polynomialRing k 2 :=
  MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ 3

/-- The image answer for the localized cusp parameterization. -/
def cuspImageAnswer (k : Type u) [Field k] :
    Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing k 2)) :=
  PrimeSpectrum.zeroLocus ({cuspEquation k} :
      Set (Formalization.Books.Exercises.Unit16.polynomialRing k 2)) \
    PrimeSpectrum.zeroLocus
      ({MvPolynomial.X (0 : Fin 2) - 1, MvPolynomial.X (1 : Fin 2) - 1} :
        Set (Formalization.Books.Exercises.Unit16.polynomialRing k 2))

/-- The eliminated equation for the last image computation. -/
def cubicImageEquation :
    Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2 :=
  ((1 : Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2) +
      MvPolynomial.X (0 : Fin 2) ^ 3 - MvPolynomial.X (1 : Fin 2) ^ 3) ^ 2 -
    4 * MvPolynomial.X (0 : Fin 2) ^ 3

/-- The image answer for `ℂ[s,t]/(s³+t³-1)`. -/
def cubicImageAnswer :
    Set (PrimeSpectrum (Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2)) :=
  PrimeSpectrum.zeroLocus ({cubicImageEquation} :
    Set (Formalization.Books.Exercises.Unit16.polynomialRing ℂ 2))

end Formalization.Books.Exercises.Unit24

end
