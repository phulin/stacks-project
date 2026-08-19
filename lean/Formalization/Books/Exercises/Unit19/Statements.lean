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

private lemma planeYPolynomial_irreducible : Irreducible planeYPolynomial := by
  have hm : planeYPolynomial.Monic := by
    have hdeg :
        (Polynomial.C planeSecondPolynomial : Polynomial (Polynomial ℚ)).degree <
          (Polynomial.X ^ 2 - Polynomial.C planeFirstPolynomial).degree := by
      rw [Polynomial.degree_X_pow_sub_C (by norm_num)]
      exact Polynomial.degree_C_lt.trans (by norm_num)
    have hinner :
        (Polynomial.X ^ 2 - Polynomial.C planeFirstPolynomial -
          Polynomial.C planeSecondPolynomial : Polynomial (Polynomial ℚ)).Monic := by
      exact (Polynomial.monic_X_pow_sub_C planeFirstPolynomial (by norm_num)).sub_of_left hdeg
    have hinnerdeg :
      (Polynomial.X ^ 2 - Polynomial.C planeFirstPolynomial -
          Polynomial.C planeSecondPolynomial : Polynomial (Polynomial ℚ)).degree = 2 := by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt hdeg,
        Polynomial.degree_X_pow_sub_C (by norm_num)]
      norm_num
    have hsqdeg :
        ((Polynomial.X ^ 2 - Polynomial.C planeFirstPolynomial -
          Polynomial.C planeSecondPolynomial : Polynomial (Polynomial ℚ)) ^ 2).degree = 4 := by
      rw [Polynomial.degree_pow, hinnerdeg]
      norm_num
    apply (hinner.pow 2).sub_of_left
    rw [hsqdeg, ← Polynomial.C_mul, ← Polynomial.C_mul]
    exact Polynomial.degree_C_lt.trans (by norm_num)
  apply hm.irreducible_of_irreducible_map (Polynomial.evalRingHom (0 : ℚ))
  convert quartic_plus_144_irreducible using 1
  simp [planeYPolynomial, planeFirstPolynomial, planeSecondPolynomial,
    Polynomial.coe_evalRingHom, pow_two]
  ring_nf
  norm_num [← map_pow, ← Polynomial.C_mul]
private def sourceBaseRelation : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C (1 : ℚ)) *
    (Polynomial.X - Polynomial.C (2 : ℚ)) *
    (Polynomial.X - Polynomial.C (3 : ℚ))

private def sourceSPolynomial : Polynomial (Polynomial ℚ) :=
  Polynomial.X ^ 2 - Polynomial.C sourceBaseRelation

private lemma sourceSPolynomial_isEisenstein :
    sourceSPolynomial.IsEisensteinAt
      (Ideal.span ({Polynomial.X - Polynomial.C (1 : ℚ)} : Set (Polynomial ℚ))) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sourceSPolynomial]
    intro h
    rw [Ideal.mem_span_singleton] at h
    exact (Polynomial.monic_X_sub_C (1 : ℚ)).not_dvd_of_natDegree_lt one_ne_zero
      (by
        rw [Polynomial.natDegree_X_sub_C]
        norm_num) h
  · intro n hn
    have hn' : n ≤ 1 := by
      simpa [sourceSPolynomial] using hn
    replace hn := hn'
    interval_cases n
    · simp [sourceSPolynomial, sourceBaseRelation, Ideal.mem_span_singleton]
      exact ⟨(Polynomial.X - Polynomial.C (2 : ℚ)) *
          (Polynomial.X - Polynomial.C (3 : ℚ)), by ring⟩
    · simp [sourceSPolynomial]
  · intro h
    have h' : sourceBaseRelation ∈
        Ideal.span ({Polynomial.X - Polynomial.C (1 : ℚ)} : Set (Polynomial ℚ)) ^ 2 := by
      simpa [sourceSPolynomial] using h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h'
    obtain ⟨q, hq⟩ := h'
    have hcancel :
        (Polynomial.X - Polynomial.C (2 : ℚ)) *
            (Polynomial.X - Polynomial.C (3 : ℚ)) =
          (Polynomial.X - Polynomial.C (1 : ℚ)) * q := by
      apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (1 : ℚ))
      calc
        (Polynomial.X - Polynomial.C (1 : ℚ)) *
              ((Polynomial.X - Polynomial.C (2 : ℚ)) *
                (Polynomial.X - Polynomial.C (3 : ℚ))) = sourceBaseRelation := by
          simp [sourceBaseRelation]
          ring
        _ = (Polynomial.X - Polynomial.C (1 : ℚ)) ^ 2 * q := hq
        _ = (Polynomial.X - Polynomial.C (1 : ℚ)) *
              ((Polynomial.X - Polynomial.C (1 : ℚ)) * q) := by ring
    have hroot :
        Polynomial.IsRoot
          ((Polynomial.X - Polynomial.C (2 : ℚ)) *
            (Polynomial.X - Polynomial.C (3 : ℚ))) 1 := by
      rw [← Polynomial.dvd_iff_isRoot]
      exact ⟨q, hcancel⟩
    norm_num [Polynomial.IsRoot] at hroot
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
    sourceBaseReindex sourceBaseRelationMv = sourceSPolynomial := by
  have hfin :
      (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ))
        (fun k : Fin 1 => Polynomial.C (MvPolynomial.X k)) (1 : Fin 2)) =
        Polynomial.C (MvPolynomial.X 0) := by
    rfl
  simp [sourceBaseReindex, sourceBaseRelationMv, sourceSPolynomial,
    RingEquiv.trans_apply, Polynomial.mapEquiv_apply, MvPolynomial.renameEquiv_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right, MvPolynomial.finSuccEquiv_apply,
    hfin, Polynomial.map_C, Polynomial.map_X]
  rw [← Polynomial.C_1, ← Polynomial.C_sub, ← Polynomial.C_sub, ← Polynomial.C_sub]
  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
  simp [sourceBaseRelation]
private def sourceBaseIdeal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {sourceBaseRelationMv}

private lemma sourceBaseIdeal_isPrime : sourceBaseIdeal.IsPrime := by
  have hspan :
      (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))).IsPrime := by
    have hbase :
        (Ideal.span ({Polynomial.X - Polynomial.C (1 : ℚ)} : Set (Polynomial ℚ))).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime (Polynomial.prime_X_sub_C (1 : ℚ))
    have hmonic : sourceSPolynomial.Monic := by
      simpa [sourceSPolynomial] using
        (Polynomial.monic_X_pow_sub_C sourceBaseRelation (by norm_num))
    have hirr : Irreducible sourceSPolynomial :=
      sourceSPolynomial_isEisenstein.irreducible hbase hmonic.isPrimitive (by
        simp [sourceSPolynomial])
    exact Ideal.isPrime_span_singleton_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  have hcomap :
      (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))).comap
          (sourceBaseReindex : MvPolynomial (Fin 2) ℚ →+* Polynomial (Polynomial ℚ)) =
        sourceBaseIdeal := by
    have heinv : sourceBaseReindex.symm sourceSPolynomial = sourceBaseRelationMv := by
      rw [← sourceBaseReindex_relation]
      simp
    ext z
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, sourceBaseIdeal,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨sourceBaseReindex.symm q, ?_⟩
      calc
        z = sourceBaseReindex.symm (sourceBaseReindex z) := by simp
        _ = sourceBaseReindex.symm (sourceSPolynomial * q) :=
          congrArg (fun p => sourceBaseReindex.symm p) hq
        _ = sourceBaseReindex.symm sourceSPolynomial * sourceBaseReindex.symm q := by
          rw [map_mul]
        _ = sourceBaseRelationMv * sourceBaseReindex.symm q := by rw [heinv]
    · rintro ⟨q, hq⟩
      refine ⟨sourceBaseReindex q, ?_⟩
      calc
        sourceBaseReindex z = sourceBaseReindex (sourceBaseRelationMv * q) := by rw [hq]
        _ = sourceBaseReindex sourceBaseRelationMv * sourceBaseReindex q := by rw [map_mul]
        _ = sourceSPolynomial * sourceBaseReindex q := by rw [sourceBaseReindex_relation]
  have hprime :
      ((Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))).comap
        (sourceBaseReindex : MvPolynomial (Fin 2) ℚ →+* Polynomial (Polynomial ℚ))).IsPrime :=
    Ideal.comap_isPrime
      (f := (sourceBaseReindex : MvPolynomial (Fin 2) ℚ →+* Polynomial (Polynomial ℚ)))
      (K := Ideal.span {sourceSPolynomial}) (H := hspan)
  rw [hcomap] at hprime
  exact hprime
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
