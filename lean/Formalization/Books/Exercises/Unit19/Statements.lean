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
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Exercises, Chapter 19: Fraction fields

This file records the domain assertion and the fraction-field identification
requested by the chapter's single exercise.  The proofs are deferred to the
proving stage.
-/

namespace Formalization.Books.Exercises.Unit19

noncomputable section

private lemma quadratic_plus_twenty_four_irreducible :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)) := by
  convert X_pow_sub_C_irreducible_of_prime (K := ℚ) Nat.prime_two (a := (-24 : ℚ)) ?_ using 1
  · simp
  intro z hz
  exact not_isSquare_of_neg (x := (-24 : ℚ)) (by norm_num)
    ⟨z, by simpa [pow_two] using hz.symm⟩
private lemma no_rat_square_24 (z : ℚ) : z ^ 2 ≠ 24 := by
  intro h
  have hs : IsSquare (24 : ℚ) := ⟨z, by simpa [pow_two] using h.symm⟩
  exact (by norm_num : ¬ IsSquare (24 : ℚ)) hs
private lemma monic_quadratic_eq {p : Polynomial ℚ} (hm : p.Monic)
    (hnd : p.natDegree = 2) :
    p = Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X +
      Polynomial.C (p.coeff 0) := by
  ext n
  rcases n with (_ | _ | _ | n)
  · simp
  · simp
  · have hp2 : p.coeff 2 = 1 := by
      simpa [hnd] using hm.coeff_natDegree
    simp [hp2]
  · have hp : p.coeff (n + 3) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    simp [hp]
private lemma quartic_plus_144_irreducible :
    Irreducible (Polynomial.X ^ 4 + Polynomial.C (144 : ℚ)) := by
  have hm : (Polynomial.X ^ 4 + Polynomial.C (144 : ℚ)).Monic := by
    exact Polynomial.monic_X_pow_add_C (a := (144 : ℚ)) (by norm_num)
  have hnd : (Polynomial.X ^ 4 + Polynomial.C (144 : ℚ)).natDegree = 4 := by
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X_pow]
  have hone : Polynomial.X ^ 4 + Polynomial.C (144 : ℚ) ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [hnd] at this
    norm_num at this
  rw [hm.irreducible_iff_lt_natDegree_lt hone]
  intro q hq hqdeg hqdiv
  simp only [Finset.mem_Ioc] at hqdeg
  have hqpos : 0 < q.natDegree := hqdeg.1
  have hqle : q.natDegree ≤ 2 := by
    rw [hnd] at hqdeg
    omega
  rcases (show q.natDegree = 1 ∨ q.natDegree = 2 by omega) with hq1 | hq2
  · have hqform : q = Polynomial.X + Polynomial.C (q.coeff 0) :=
      hq.eq_X_add_C (by omega)
    rw [hqform, ← sub_neg_eq_add, ← Polynomial.C_neg] at hqdiv
    rw [Polynomial.dvd_iff_isRoot] at hqdiv
    simp [Polynomial.IsRoot] at hqdiv
    nlinarith [sq_nonneg ((q.coeff 0) ^ 2)]
  · obtain ⟨r, hqr⟩ := hqdiv
    have hprod : (q * r).Monic := by rw [← hqr]; exact hm
    have hr : r.Monic := hq.of_mul_monic_left hprod
    have hrd : r.natDegree = 2 := by
      have hdeg := congrArg Polynomial.natDegree hqr
      rw [hnd, Polynomial.natDegree_mul hq.ne_zero hr.ne_zero] at hdeg
      omega
    rw [monic_quadratic_eq hq hq2, monic_quadratic_eq hr hrd] at hqr
    have h0 := congrArg (fun f : Polynomial ℚ => f.coeff 0) hqr
    have h1 := congrArg (fun f : Polynomial ℚ => f.coeff 1) hqr
    have h2 := congrArg (fun f : Polynomial ℚ => f.coeff 2) hqr
    have h3 := congrArg (fun f : Polynomial ℚ => f.coeff 3) hqr
    rw [Polynomial.mul_coeff_zero] at h0
    rw [Polynomial.mul_coeff_one] at h1
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h2 h3
    simp at h0 h1
    norm_num [Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_C] at h2 h3
    have h0' : (144 : ℚ) = q.coeff 0 * r.coeff 0 := h0
    have h1' : (0 : ℚ) = q.coeff 0 * r.coeff 1 + q.coeff 1 * r.coeff 0 := h1
    have h2' : (0 : ℚ) = q.coeff 0 + q.coeff 1 * r.coeff 1 + r.coeff 0 := h2
    have h3' : (0 : ℚ) = q.coeff 1 + r.coeff 1 := h3
    have hr1 : r.coeff 1 = -q.coeff 1 := by linarith [h3']
    have hfac : q.coeff 1 * (r.coeff 0 - q.coeff 0) = 0 := by
      calc
        q.coeff 1 * (r.coeff 0 - q.coeff 0) =
            q.coeff 0 * (-q.coeff 1) + q.coeff 1 * r.coeff 0 := by ring
        _ = 0 := by rw [← hr1]; exact h1'.symm
    rcases mul_eq_zero.mp hfac with hqa | hdiff
    · have hrd0 : r.coeff 0 = -q.coeff 0 := by
        nlinarith [h2', hr1, hqa]
      rw [hrd0] at h0'
      nlinarith [h0', sq_nonneg (q.coeff 0)]
    · have hrd0 : r.coeff 0 = q.coeff 0 := sub_eq_zero.mp hdiff
      rw [hrd0] at h0'
      have hpm : (q.coeff 0 - 12) * (q.coeff 0 + 12) = 0 := by
        nlinarith [h0']
      rcases mul_eq_zero.mp hpm with hplus | hminus
      · have hq0 : q.coeff 0 = 12 := by linarith
        have h2'' := h2'
        rw [hr1, hq0, hrd0] at h2''
        apply no_rat_square_24 (q.coeff 1)
        nlinarith [h2'']
      · have hq0 : q.coeff 0 = -12 := by linarith
        have h2'' := h2'
        rw [hr1, hq0, hrd0] at h2''
        nlinarith [h2'', sq_nonneg (q.coeff 1)]
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
