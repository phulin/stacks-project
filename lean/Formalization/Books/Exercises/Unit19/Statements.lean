import Formalization.Books.Exercises.Unit19.Core

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Data.Rat.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# Exercises, Chapter 19: Fraction fields

This file records the domain assertion and the fraction-field identification
requested by the chapter's single exercise.  The proofs are deferred to the
proving stage.
-/

namespace Formalization.Books.Exercises.Unit19

noncomputable section

private lemma quadratic_plus_twenty_four_irreducible :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)) := by sorry
private lemma no_rat_square_24 (z : ℚ) : z ^ 2 ≠ 24 := by sorry
private lemma monic_quadratic_eq {p : Polynomial ℚ} (hm : p.Monic)
    (hnd : p.natDegree = 2) :
    p = Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X +
      Polynomial.C (p.coeff 0) := by sorry
private lemma quartic_plus_144_irreducible :
    Irreducible (Polynomial.X ^ 4 + Polynomial.C (144 : ℚ)) := by sorry
private def planeFirstPolynomial : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C (1 : ℚ)) *
    (Polynomial.X - Polynomial.C (2 : ℚ)) *
    (Polynomial.X - Polynomial.C (3 : ℚ))

private def planeSecondPolynomial : Polynomial ℚ :=
  (Polynomial.X + Polynomial.C (1 : ℚ)) *
    (Polynomial.X + Polynomial.C (2 : ℚ)) *
    (Polynomial.X + Polynomial.C (3 : ℚ))

private def planeYPolynomial : Polynomial (Polynomial ℚ) :=
  (Polynomial.X ^ 2 - Polynomial.C planeFirstPolynomial -
      Polynomial.C planeSecondPolynomial) ^ 2 -
    Polynomial.C (Polynomial.C (4 : ℚ)) * Polynomial.C planeFirstPolynomial *
      Polynomial.C planeSecondPolynomial

private lemma planeYPolynomial_irreducible : Irreducible planeYPolynomial := by sorry
private def sourceBaseRelation : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C (1 : ℚ)) *
    (Polynomial.X - Polynomial.C (2 : ℚ)) *
    (Polynomial.X - Polynomial.C (3 : ℚ))

private def sourceSPolynomial : Polynomial (Polynomial ℚ) :=
  Polynomial.X ^ 2 - Polynomial.C sourceBaseRelation

private lemma sourceSPolynomial_isEisenstein :
    sourceSPolynomial.IsEisensteinAt
      (Ideal.span ({Polynomial.X - Polynomial.C (1 : ℚ)} : Set (Polynomial ℚ))) := by sorry
private def sourceBaseRelationMv : MvPolynomial (Fin 2) ℚ :=
  (MvPolynomial.X (1 : Fin 2)) ^ 2 -
    (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (1 : ℚ)) *
      (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (2 : ℚ)) *
      (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (3 : ℚ))

private def sourceBaseReindex : MvPolynomial (Fin 2) ℚ ≃+* Polynomial (Polynomial ℚ) :=
  ((MvPolynomial.renameEquiv ℚ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv ℚ 1).toRingEquiv).trans
      (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingEquiv)

private lemma sourceBaseReindex_relation :
    sourceBaseReindex sourceBaseRelationMv = sourceSPolynomial := by sorry
private def sourceBaseIdeal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {sourceBaseRelationMv}

private lemma sourceBaseIdeal_isPrime : sourceBaseIdeal.IsPrime := by sorry
private lemma monic_span_isPrime_of_map_isPrime
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (g : Polynomial R) (hg : g.Monic)
    (hprime : (Ideal.span {g.map f} : Ideal (Polynomial S)).IsPrime) :
    (Ideal.span {g} : Ideal (Polynomial R)).IsPrime := by sorry
private def planeReindex : planePolynomialRing ≃+* Polynomial (Polynomial ℚ) :=
  ((MvPolynomial.renameEquiv ℚ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv ℚ 1).toRingEquiv).trans
      (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingEquiv)

private lemma planeReindex_relation :
    planeReindex planeRelation = planeYPolynomial := by sorry
private lemma planeYPolynomial_span_isPrime :
    (Ideal.span {planeYPolynomial} : Ideal (Polynomial (Polynomial ℚ))).IsPrime := by sorry
private lemma planeIdeal_isPrime :
    (Ideal.span {planeRelation} : Ideal planePolynomialRing).IsPrime := by sorry
private def sourceFullReindexAux : MvPolynomial (Fin 2) ℚ →+*
    Polynomial (Polynomial ℚ) :=
  (Polynomial.mapRingHom
      (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) :
        MvPolynomial (Fin 1) ℚ →+* Polynomial ℚ)).comp
    (MvPolynomial.finSuccEquiv ℚ 1)

private def sourceFullReindex : sourcePolynomialRing →+*
    Polynomial (Polynomial (Polynomial ℚ)) :=
  (Polynomial.mapRingHom sourceFullReindexAux).comp
    (((MvPolynomial.renameEquiv ℚ (Equiv.swap (0 : Fin 3) 2)).toRingEquiv.trans
      (MvPolynomial.finSuccEquiv ℚ 2).toRingEquiv).toRingHom)

private def sourceTPolynomial : Polynomial (Polynomial (Polynomial ℚ)) :=
  Polynomial.X ^ 2 -
    Polynomial.C (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C (1 : ℚ))) *
      Polynomial.C (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C (2 : ℚ))) *
      Polynomial.C (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C (3 : ℚ)))

private lemma sourceFullReindex_tRelation :
    sourceFullReindex sourceTRelation = sourceTPolynomial := by sorry
private lemma sourceSPolynomial_span_isPrime :
    (Ideal.span {sourceSPolynomial} :
      Ideal (Polynomial (Polynomial ℚ))).IsPrime := by sorry
private abbrev sourceInnerPrime : Ideal (Polynomial ℚ) :=
  Ideal.span {Polynomial.X - Polynomial.C (-1 : ℚ)}

private abbrev sourceCoefficientPrime : Ideal (Polynomial (Polynomial ℚ)) :=
  Ideal.map (Polynomial.C : Polynomial ℚ →+* Polynomial (Polynomial ℚ)) sourceInnerPrime

private lemma sourceInnerPrime_isPrime : sourceInnerPrime.IsPrime := by sorry
private lemma sourceCoefficientPrime_isPrime : sourceCoefficientPrime.IsPrime := by sorry
private noncomputable def sourceInnerQuotientEquiv :
    (Polynomial ℚ ⧸ sourceInnerPrime) ≃+* ℚ :=
  Polynomial.quotientSpanXSubCAlgEquiv (-1 : ℚ)

private noncomputable def sourceCoefficientQuotientEquiv :
    Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) ≃+* Polynomial ℚ :=
  Polynomial.mapEquiv sourceInnerQuotientEquiv

private noncomputable def sourcePolynomialQuotientEquiv :
    Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) ≃+*
      Polynomial (Polynomial ℚ) ⧸ sourceCoefficientPrime :=
  Ideal.polynomialQuotientEquivQuotientPolynomial sourceInnerPrime

private lemma sourceSPolynomial_mod_inner_map :
    sourceCoefficientQuotientEquiv
        (sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)) =
      Polynomial.X ^ 2 + Polynomial.C (24 : ℚ) := by sorry
private lemma sourceBasePlusCoefficientPrime_isPrime :
    (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))) ⊔
        sourceCoefficientPrime |>.IsPrime := by sorry
private lemma sourceT_quotient_isEisenstein :
    (sourceTPolynomial.map
      (Ideal.Quotient.mk (Ideal.span {sourceSPolynomial}))).IsEisensteinAt
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {sourceSPolynomial})
        (Polynomial.C (Polynomial.X - Polynomial.C (-1 : ℚ)))}) := by sorry
instance sourceRing_isDomain : IsDomain sourceRing := by sorry
instance planeCurveRing_isDomain : IsDomain planeCurveRing := by sorry
theorem source_fraction_field_equiv_plane_curve :
    Nonempty (FractionRing sourceRing ≃+* FractionRing planeCurveRing) := by sorry
