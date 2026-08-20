import Formalization.Books.Exercises.Unit19.Core

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Data.Rat.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.QuadraticAlgebra.Basic
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
    (Ideal.span {g} : Ideal (Polynomial R)).IsPrime := by
  have hcomap :
      (Ideal.span {g.map f} : Ideal (Polynomial S)).comap
          (Polynomial.mapRingHom f) =
        (Ideal.span {g} : Ideal (Polynomial R)) := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    exact Polynomial.map_dvd_map f hf hg
  have hprime' :
      ((Ideal.span {g.map f} : Ideal (Polynomial S)).comap
        (Polynomial.mapRingHom f)).IsPrime :=
    Ideal.comap_isPrime (Polynomial.mapRingHom f) (Ideal.span {g.map f})
  rw [hcomap] at hprime'
  exact hprime'
private def planeReindex : planePolynomialRing ≃+* Polynomial (Polynomial ℚ) :=
  ((MvPolynomial.renameEquiv ℚ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv ℚ 1).toRingEquiv).trans
      (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingEquiv)

private lemma planeReindex_relation :
    planeReindex planeRelation = planeYPolynomial := by
  have hfin :
      (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ))
        (fun k : Fin 1 => Polynomial.C (MvPolynomial.X k)) (1 : Fin 2)) =
        Polynomial.C (MvPolynomial.X 0) := by
    rfl
  have hx :
      planeReindex (MvPolynomial.X (0 : Fin 2)) = Polynomial.C Polynomial.X := by
    simp [planeReindex, RingEquiv.trans_apply, Polynomial.mapEquiv_apply,
      MvPolynomial.renameEquiv_apply, Equiv.swap_apply_left,
      MvPolynomial.finSuccEquiv_apply, hfin]
  have hy :
      planeReindex (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
    simp [planeReindex, RingEquiv.trans_apply, Polynomial.mapEquiv_apply,
      MvPolynomial.renameEquiv_apply, Equiv.swap_apply_right,
      MvPolynomial.finSuccEquiv_apply]
  have hC (q : ℚ) :
      planeReindex (MvPolynomial.C q) = Polynomial.C (Polynomial.C q) := by
    simp [planeReindex, MvPolynomial.finSuccEquiv_apply]
  have hfirst :
      planeReindex planeFirstCubic = Polynomial.C planeFirstPolynomial := by
    simp only [planeFirstCubic, map_mul, map_sub, hx, hC]
    rw [← Polynomial.C_sub, ← Polynomial.C_sub, ← Polynomial.C_sub,
      ← Polynomial.C_mul, ← Polynomial.C_mul]
    simp [planeFirstPolynomial]
  have hsecond :
      planeReindex planeSecondCubic = Polynomial.C planeSecondPolynomial := by
    simp only [planeSecondCubic, map_mul, map_add, hx, hC]
    rw [← Polynomial.C_add, ← Polynomial.C_add, ← Polynomial.C_add,
      ← Polynomial.C_mul, ← Polynomial.C_mul]
    simp [planeSecondPolynomial]
  have hfour :
      planeReindex (4 : planePolynomialRing) =
        Polynomial.C (Polynomial.C (4 : ℚ)) := by
    rw [← map_ofNat (MvPolynomial.C : ℚ →+* planePolynomialRing) 4]
    exact hC 4
  rw [planeRelation, planeYPolynomial]
  simp only [map_sub, map_pow, map_mul]
  rw [hy, hfirst, hsecond, hfour]
private lemma planeYPolynomial_span_isPrime :
    (Ideal.span {planeYPolynomial} : Ideal (Polynomial (Polynomial ℚ))).IsPrime := by
  exact Ideal.isPrime_span_singleton_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp planeYPolynomial_irreducible)
private lemma planeIdeal_isPrime :
    (Ideal.span {planeRelation} : Ideal planePolynomialRing).IsPrime := by
  have hcomap :
      (Ideal.span {planeYPolynomial} : Ideal (Polynomial (Polynomial ℚ))).comap
          (planeReindex : planePolynomialRing →+* Polynomial (Polynomial ℚ)) =
        (Ideal.span {planeRelation} : Ideal planePolynomialRing) := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨planeReindex.symm q, ?_⟩
      calc
        z = planeReindex.symm (planeReindex z) := by simp
        _ = planeReindex.symm (planeYPolynomial * q) :=
          congrArg (fun p => planeReindex.symm p) hq
        _ = planeReindex.symm planeYPolynomial * planeReindex.symm q := by
          rw [map_mul]
        _ = planeRelation * planeReindex.symm q := by
          rw [← planeReindex_relation]
          simp
    · rintro ⟨q, hq⟩
      refine ⟨planeReindex q, ?_⟩
      calc
        planeReindex z = planeReindex (planeRelation * q) := by rw [hq]
        _ = planeReindex planeRelation * planeReindex q := by rw [map_mul]
        _ = planeYPolynomial * planeReindex q := by rw [planeReindex_relation]
  have hprime :
      ((Ideal.span {planeYPolynomial} : Ideal (Polynomial (Polynomial ℚ))).comap
        (planeReindex : planePolynomialRing →+* Polynomial (Polynomial ℚ))).IsPrime :=
    Ideal.comap_isPrime
      (f := (planeReindex : planePolynomialRing →+* Polynomial (Polynomial ℚ)))
      (K := Ideal.span {planeYPolynomial}) (H := planeYPolynomial_span_isPrime)
  rw [hcomap] at hprime
  exact hprime
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
    sourceFullReindex sourceTRelation = sourceTPolynomial := by
  have hfin :
      (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 2) ℚ))
        (fun k : Fin 2 => Polynomial.C (MvPolynomial.X k)) (2 : Fin 3)) =
        Polynomial.C (MvPolynomial.X 1) := by
    rfl
  have hfin' :
      (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ))
        (fun k : Fin 1 => Polynomial.C (MvPolynomial.X k)) (1 : Fin 2)) =
        Polynomial.C (MvPolynomial.X 0) := by
    rfl
  simp [sourceFullReindex, sourceTRelation, sourceTPolynomial, sourceFullReindexAux,
    MvPolynomial.renameEquiv_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right, MvPolynomial.finSuccEquiv_apply,
    hfin, hfin', Polynomial.map_C, Polynomial.map_X]
private lemma sourceSPolynomial_span_isPrime :
    (Ideal.span {sourceSPolynomial} :
      Ideal (Polynomial (Polynomial ℚ))).IsPrime := by
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
private abbrev sourceInnerPrime : Ideal (Polynomial ℚ) :=
  Ideal.span {Polynomial.X - Polynomial.C (-1 : ℚ)}

private abbrev sourceCoefficientPrime : Ideal (Polynomial (Polynomial ℚ)) :=
  Ideal.map (Polynomial.C : Polynomial ℚ →+* Polynomial (Polynomial ℚ)) sourceInnerPrime

private lemma sourceInnerPrime_isPrime : sourceInnerPrime.IsPrime := by
  change (Ideal.span {Polynomial.X - Polynomial.C (-1 : ℚ)} : Ideal (Polynomial ℚ)).IsPrime
  exact Ideal.isPrime_span_singleton_of_prime (Polynomial.prime_X_sub_C (-1 : ℚ))
private lemma sourceCoefficientPrime_isPrime : sourceCoefficientPrime.IsPrime := by
  change (Ideal.map (Polynomial.C : Polynomial ℚ →+* Polynomial (Polynomial ℚ))
    sourceInnerPrime).IsPrime
  exact (Ideal.isPrime_map_C_iff_isPrime sourceInnerPrime).mpr sourceInnerPrime_isPrime
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
      Polynomial.X ^ 2 + Polynomial.C (24 : ℚ) := by
  simp [sourceSPolynomial, sourceCoefficientQuotientEquiv, sourceInnerQuotientEquiv]
  norm_num [sourceBaseRelation]
private lemma sourceBasePlusCoefficientPrime_isPrime :
    (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))) ⊔
        sourceCoefficientPrime |>.IsPrime := by
  have hquad :
      (Ideal.span {Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)} :
        Ideal (Polynomial ℚ)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        quadratic_plus_twenty_four_irreducible)
  have hmapA :
      (Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :
        Ideal (Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))).map
          (sourceCoefficientQuotientEquiv :
            Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) →+*
              Polynomial ℚ) =
        Ideal.span {Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    exact congrArg (Ideal.span : Set (Polynomial ℚ) → Ideal (Polynomial ℚ))
      (congrArg (fun p : Polynomial ℚ => ({p} : Set (Polynomial ℚ)))
        sourceSPolynomial_mod_inner_map)
  have hprimeA :
      (Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :
        Ideal (Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))).IsPrime := by
    have h :=
      Ideal.comap_isPrime
        (sourceCoefficientQuotientEquiv :
          Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) →+* Polynomial ℚ)
        (K := Ideal.span {Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)})
        (H := hquad)
    have hcancel :
        Ideal.comap (sourceCoefficientQuotientEquiv :
          Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) →+* Polynomial ℚ)
          (Ideal.comap (sourceCoefficientQuotientEquiv.symm :
            Polynomial ℚ →+* Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))
            (Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)})) =
        Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :=
      Ideal.comap_of_equiv sourceCoefficientQuotientEquiv
    rw [← hmapA, Ideal.map_comap_of_equiv] at h
    change (Ideal.comap (sourceCoefficientQuotientEquiv :
      Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) →+* Polynomial ℚ)
      (Ideal.comap (sourceCoefficientQuotientEquiv.symm :
        Polynomial ℚ →+* Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))
        (Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)}))).IsPrime at h
    exact hcancel ▸ h
  have hprimeQ :
      ((Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :
        Ideal (Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))).map
          (sourcePolynomialQuotientEquiv :
            Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) →+*
              Polynomial (Polynomial ℚ) ⧸ sourceCoefficientPrime)).IsPrime := by
    exact @Ideal.map_isPrime_of_equiv _ _ _ _ _ _ _ sourcePolynomialQuotientEquiv _ hprimeA
  have hrel :
      sourcePolynomialQuotientEquiv
          (sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)) =
        Ideal.Quotient.mk sourceCoefficientPrime sourceSPolynomial := by
    exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk
      sourceInnerPrime sourceSPolynomial
  have heq :
      (Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :
        Ideal (Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))).map
          (sourcePolynomialQuotientEquiv :
            Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) →+*
              Polynomial (Polynomial ℚ) ⧸ sourceCoefficientPrime) =
        (Ideal.span {sourceSPolynomial} :
          Ideal (Polynomial (Polynomial ℚ))).map
            (Ideal.Quotient.mk sourceCoefficientPrime) := by
    rw [Ideal.map_span, Ideal.map_span]
    simp only [Set.image_singleton]
    exact congrArg (Ideal.span : Set _ → Ideal _)
      (congrArg (fun p => ({p} : Set _)) hrel)
  have hprimeMapped :
      ((Ideal.span {sourceSPolynomial} :
        Ideal (Polynomial (Polynomial ℚ))).map
          (Ideal.Quotient.mk sourceCoefficientPrime)).IsPrime := by
    rw [← heq]
    exact hprimeQ
  have hprimeSup :
      ((Ideal.span {sourceSPolynomial} :
        Ideal (Polynomial (Polynomial ℚ))).map
          (Ideal.Quotient.mk sourceCoefficientPrime)).comap
            (Ideal.Quotient.mk sourceCoefficientPrime) |>.IsPrime :=
    Ideal.comap_isPrime (Ideal.Quotient.mk sourceCoefficientPrime)
      (K := (Ideal.span {sourceSPolynomial} :
        Ideal (Polynomial (Polynomial ℚ))).map
          (Ideal.Quotient.mk sourceCoefficientPrime))
      (H := hprimeMapped)
  rw [Ideal.comap_map_quotientMk] at hprimeSup
  simpa [sup_comm] using hprimeSup
attribute [local instance] sourceSPolynomial_span_isPrime

private lemma sourceT_quotient_isEisenstein :
    (sourceTPolynomial.map
      (Ideal.Quotient.mk (Ideal.span {sourceSPolynomial}))).IsEisensteinAt
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {sourceSPolynomial})
        (Polynomial.C (Polynomial.X - Polynomial.C (-1 : ℚ)))}) := by
  have hcoeff :
      sourceCoefficientPrime =
        Ideal.span {Polynomial.C (Polynomial.X - Polynomial.C (-1 : ℚ))} := by
    change Ideal.map (Polynomial.C : Polynomial ℚ →+* Polynomial (Polynomial ℚ))
      (Ideal.span {Polynomial.X - Polynomial.C (-1 : ℚ)}) = _
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
  have hPprime :
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {sourceSPolynomial})
        (Polynomial.C (Polynomial.X - Polynomial.C (-1 : ℚ)))} :
        Ideal (Polynomial (Polynomial ℚ) ⧸ Ideal.span {sourceSPolynomial})).IsPrime := by
    have hprimeSup :
        (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))) ⊔
          sourceCoefficientPrime |>.IsPrime :=
      sourceBasePlusCoefficientPrime_isPrime
    have hp :=
      @Ideal.isPrime_map_quotientMk_of_isPrime _ _ _ _ _ hprimeSup
        le_sup_left
    simpa [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, hcoeff,
      Ideal.map_span] using hp
  have hTmonic : sourceTPolynomial.Monic := by
    rw [sourceTPolynomial, ← Polynomial.C_mul, ← Polynomial.C_mul]
    exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have hmonic :
        (sourceTPolynomial.map
          (Ideal.Quotient.mk (Ideal.span {sourceSPolynomial}))).Monic := by
      exact hTmonic.map _
    exact hmonic.leadingCoeff_notMem hPprime.1
  · intro n hn
    have hdeg :
        (sourceTPolynomial.map
          (Ideal.Quotient.mk (Ideal.span {sourceSPolynomial}))).natDegree = 2 := by
      rw [hTmonic.natDegree_map, sourceTPolynomial,
        ← Polynomial.C_mul, ← Polynomial.C_mul,
        Polynomial.natDegree_X_pow_sub_C]
    have hn' : n < 2 := by simpa [hdeg] using hn
    interval_cases n
    · rw [Polynomial.coeff_map]
      simp [sourceTPolynomial, Ideal.mem_span_singleton]
      refine ⟨-(((Ideal.Quotient.mk (Ideal.span {sourceSPolynomial}))
          (Polynomial.C Polynomial.X) +
            (Ideal.Quotient.mk (Ideal.span {sourceSPolynomial}))
              (Polynomial.C (Polynomial.C 2))) *
        ((Ideal.Quotient.mk (Ideal.span {sourceSPolynomial}))
          (Polynomial.C Polynomial.X) +
            (Ideal.Quotient.mk (Ideal.span {sourceSPolynomial}))
              (Polynomial.C (Polynomial.C 3)))), ?_⟩
      ring
    · rw [Polynomial.coeff_map]
      have hcoeff1 : sourceTPolynomial.coeff 1 = 0 := by
        rw [sourceTPolynomial, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          ← Polynomial.C_mul, ← Polynomial.C_mul, Polynomial.coeff_C]
        simp
      rw [hcoeff1]
      simp
  · let q : Polynomial (Polynomial ℚ) →+*
        Polynomial (Polynomial ℚ) ⧸ Ideal.span {sourceSPolynomial} :=
      Ideal.Quotient.mk _
    let qI : Polynomial (Polynomial ℚ) →+*
        Polynomial (Polynomial ℚ) ⧸ sourceCoefficientPrime :=
      Ideal.Quotient.mk _
    let q0 : Polynomial (Polynomial ℚ) ⧸ Ideal.span {sourceSPolynomial} :=
      q (Polynomial.C (Polynomial.X - Polynomial.C (-1 : ℚ)))
    let braw : Polynomial (Polynomial ℚ) :=
      Polynomial.C (Polynomial.X + Polynomial.C (2 : ℚ)) *
        Polynomial.C (Polynomial.X + Polynomial.C (3 : ℚ))
    let bS : Polynomial (Polynomial ℚ) ⧸ Ideal.span {sourceSPolynomial} := q braw
    have hsourceMonic : sourceSPolynomial.Monic := by
      simpa [sourceSPolynomial] using
        (Polynomial.monic_X_pow_sub_C sourceBaseRelation (by norm_num))
    have hq0 : q0 ≠ 0 := by
      intro hzero
      have hzero' :
          q (Polynomial.C (Polynomial.X + Polynomial.C (1 : ℚ))) = 0 := by
        simpa [q0, q, sub_neg_eq_add] using hzero
      rw [Ideal.Quotient.eq_zero_iff_mem] at hzero'
      rw [Ideal.mem_span_singleton] at hzero'
      obtain ⟨u, hu⟩ := hzero'
      have hdvd : sourceSPolynomial ∣
          Polynomial.C (Polynomial.X + Polynomial.C (1 : ℚ)) :=
        ⟨u, hu⟩
      have hnonzero :
          Polynomial.C (Polynomial.X + Polynomial.C (1 : ℚ)) ≠ 0 := by
        exact Polynomial.C_ne_zero.mpr (Polynomial.X_add_C_ne_zero 1)
      exact hsourceMonic.not_dvd_of_natDegree_lt hnonzero
        (by simp [sourceSPolynomial]) hdvd
    have hquad :
        (Ideal.span {Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)} :
          Ideal (Polynomial ℚ)).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp
          quadratic_plus_twenty_four_irreducible)
    have hmapA :
        (Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :
          Ideal (Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))).map
            (sourceCoefficientQuotientEquiv :
              Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) →+* Polynomial ℚ) =
          Ideal.span {Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)} := by
      rw [Ideal.map_span]
      simp only [Set.image_singleton]
      exact congrArg (Ideal.span : Set (Polynomial ℚ) → Ideal (Polynomial ℚ))
        (congrArg (fun p : Polynomial ℚ => ({p} : Set (Polynomial ℚ)))
          sourceSPolynomial_mod_inner_map)
    have hrelJ :
        sourcePolynomialQuotientEquiv
            (sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)) =
          qI sourceSPolynomial := by
      exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk
        sourceInnerPrime sourceSPolynomial
    have hmapJ :
        (Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :
          Ideal (Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))).map
            (sourcePolynomialQuotientEquiv :
              Polynomial (Polynomial ℚ ⧸ sourceInnerPrime) →+*
                Polynomial (Polynomial ℚ) ⧸ sourceCoefficientPrime) =
          (Ideal.span {sourceSPolynomial} :
            Ideal (Polynomial (Polynomial ℚ))).map qI := by
      rw [Ideal.map_span, Ideal.map_span]
      simp only [Set.image_singleton]
      exact congrArg (Ideal.span : Set _ → Ideal _)
        (congrArg (fun p => ({p} : Set _)) hrelJ)
    have hbnot : bS ∉ Ideal.span {q0} := by
      intro hb
      have hbmap : q braw ∈
          (Ideal.span {Polynomial.C (Polynomial.X - Polynomial.C (-1 : ℚ))} :
            Ideal (Polynomial (Polynomial ℚ))).map q := by
        rw [Ideal.map_span]
        simpa [q0, bS, braw, q, sub_neg_eq_add] using hb
      have hsup : braw ∈
          (Ideal.span {Polynomial.C (Polynomial.X - Polynomial.C (-1 : ℚ))} :
            Ideal (Polynomial (Polynomial ℚ))) ⊔
            (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))) :=
        (Ideal.mem_quotient_iff_mem_sup
          (I := Ideal.span {sourceSPolynomial})
          (J := Ideal.span {Polynomial.C (Polynomial.X - Polynomial.C (-1 : ℚ))})).mp hbmap
      have hsup' : braw ∈ sourceCoefficientPrime ⊔
          (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))) := by
        rw [hcoeff]
        exact hsup
      have hbI : qI braw ∈
          (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))).map qI := by
        apply (Ideal.mem_quotient_iff_mem_sup
          (I := sourceCoefficientPrime)
          (J := Ideal.span {sourceSPolynomial})).mpr
        simpa [sup_comm] using hsup'
      have hbA' : qI braw ∈
          (Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :
              Ideal (Polynomial (Polynomial ℚ ⧸ sourceInnerPrime))).map
                sourcePolynomialQuotientEquiv := by
        exact hmapJ.symm ▸ hbI
      have hbA :
          sourcePolynomialQuotientEquiv.symm (qI braw) ∈
            Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} :=
        (Ideal.symm_apply_mem_of_equiv_iff).2 hbA'
      have hbA' : braw.map (Ideal.Quotient.mk sourceInnerPrime) ∈
          Ideal.span {sourceSPolynomial.map (Ideal.Quotient.mk sourceInnerPrime)} := by
        have hmap_mk' :
            sourcePolynomialQuotientEquiv
                (braw.map (Ideal.Quotient.mk sourceInnerPrime)) = qI braw := by
          exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk
            sourceInnerPrime braw
        have hsymm :
            sourcePolynomialQuotientEquiv.symm (qI braw) =
              braw.map (Ideal.Quotient.mk sourceInnerPrime) := by
          rw [← hmap_mk']
          simp
        rw [← hsymm]
        exact hbA
      have hbquad :
          sourceCoefficientQuotientEquiv
              (braw.map (Ideal.Quotient.mk sourceInnerPrime)) ∈
            Ideal.span {Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)} := by
        rw [← hmapA]
        exact Ideal.mem_map_of_mem _ hbA'
      have hval :
          sourceCoefficientQuotientEquiv
              (braw.map (Ideal.Quotient.mk sourceInnerPrime)) =
            Polynomial.C (2 : ℚ) := by
        simp [sourceCoefficientQuotientEquiv, sourceInnerQuotientEquiv, braw]
        have h2 : (-1 : Polynomial ℚ) + Polynomial.C 2 = Polynomial.C 1 := by
          rw [show (-1 : Polynomial ℚ) = Polynomial.C (-1 : ℚ) by simp,
            ← Polynomial.C_add]
          norm_num
        have h3 : (-1 : Polynomial ℚ) + Polynomial.C 3 = Polynomial.C 2 := by
          rw [show (-1 : Polynomial ℚ) = Polynomial.C (-1 : ℚ) by simp,
            ← Polynomial.C_add]
          norm_num
        rw [h2, h3, ← Polynomial.C_mul]
        norm_num
      rw [hval] at hbquad
      rw [Ideal.mem_span_singleton] at hbquad
      obtain ⟨u, hu⟩ := hbquad
      have hdvd : Polynomial.X ^ 2 + Polynomial.C (24 : ℚ) ∣
          Polynomial.C (2 : ℚ) := ⟨u, hu⟩
      exact (Polynomial.monic_X_pow_add_C (a := (24 : ℚ)) (by norm_num)).not_dvd_of_natDegree_lt
        (by norm_num) (by norm_num) hdvd
    have hf0 :
        (sourceTPolynomial.map q).coeff 0 = -q0 * bS := by
      rw [Polynomial.coeff_map]
      simp [sourceTPolynomial, q0, bS, braw, q, sub_neg_eq_add]
      ring
    intro ha
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨u, hu⟩ := ha
    have hcancel : -bS = q0 * u := by
      apply mul_left_cancel₀ hq0
      calc
        q0 * (-bS) = -q0 * bS := by ring
        _ = (sourceTPolynomial.map q).coeff 0 := hf0.symm
        _ = q0 ^ 2 * u := hu
        _ = q0 * (q0 * u) := by ring
    have hbdiv : q0 ∣ bS := by
      refine ⟨-u, ?_⟩
      calc
        bS = -(-bS) := by ring
        _ = -(q0 * u) := by rw [hcancel]
        _ = q0 * (-u) := by ring
    apply hbnot
    exact (Ideal.mem_span_singleton (x := bS) (y := q0)).mpr hbdiv

/-
Proof roadmap for `sourceRing_isDomain` (the statement is sound).

Do not try to finish from `sourceT_quotient_isEisenstein.irreducible` by turning
that irreducible polynomial into a prime element.  Its coefficient ring

  A := Polynomial (Polynomial ℚ) ⧸ Ideal.span {sourceSPolynomial}

is currently known only to be a domain (via the local instance
`sourceSPolynomial_span_isPrime`).  There is no `UniqueFactorizationMonoid A`
or `IsIntegrallyClosed A` instance, so irreducible does not imply prime here.
Instead embed `A` in the quadratic function field and test the second
quadratic there, as follows.

1. Put `R := Polynomial ℚ`, `K := FractionRing R`,
   `P := sourceBaseRelation`, and `Q := planeSecondPolynomial`.  Prove the
   following three facts in `K`:

     `∀ z : K, z ^ 2 ≠ algebraMap R K P`,
     `∀ z : K, z ^ 2 ≠ algebraMap R K Q`, and
     `∀ z : K, z ^ 2 ≠ algebraMap R K (P * Q)`.

   For the first, reuse `sourceSPolynomial_isEisenstein` and the monicity of
   `sourceSPolynomial`; apply
   `Polynomial.IsEisensteinAt.irreducible` from
   `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean`, then transport the
   result to `K[X]` with
   `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` from
   `Mathlib/RingTheory/Polynomial/GaussLemma.lean`.  Convert the resulting
   irreducibility of `X ^ 2 - C (algebraMap R K P)` to the displayed
   nonsquare statement with `X_pow_sub_C_irreducible_iff_of_prime
   Nat.prime_two` from `Mathlib/FieldTheory/KummerPolynomial.lean`.

   Establish the other two facts by the same sequence.  Over `R`, use the
   monic polynomials `X ^ 2 - C Q` and `X ^ 2 - C (P * Q)`.  They are
   Eisenstein respectively at
   `Ideal.span {X - C (-1 : ℚ)}` and
   `Ideal.span {X - C (1 : ℚ)}`.  The constant-coefficient checks are the
   same cancellation/root-evaluation argument already used in
   `sourceSPolynomial_isEisenstein`: after removing the indicated linear
   factor, evaluate the remaining factors at `-1` or `1` to show that a
   second copy cannot divide.  Use `Polynomial.prime_X_sub_C` and
   `Ideal.isPrime_span_singleton_of_prime` for the prime ideals.

2. Let

     `L := QuadraticAlgebra K (algebraMap R K P) 0`.

   Install the first nonsquare fact as the required
   `Fact (∀ z : K, z ^ 2 ≠ algebraMap R K P + 0 * z)`; the field instance for
   `L` is in `Mathlib/Algebra/QuadraticAlgebra/Basic.lean`.  Prove

     `∀ z : L, z ^ 2 ≠ algebraMap K L (algebraMap R K Q)`.

   Apply `congrArg QuadraticAlgebra.re` and `.im` to a hypothetical square
   equality and simplify with `QuadraticAlgebra.re_mul`,
   `QuadraticAlgebra.im_mul`, and `pow_two`.  The imaginary equation is
   `2 * z.re * z.im = 0`, hence `z.re = 0 ∨ z.im = 0`.  If `z.im = 0`, the
   second nonsquare fact gives a contradiction.  If `z.re = 0`, the real
   equation gives `P * z.im ^ 2 = Q`; after multiplying by `P`, it makes
   `P * Q` the square `(P * z.im) ^ 2`, contradicting the third fact.  The
   first nonsquare fact also supplies `algebraMap R K P ≠ 0` for cancellation.

3. Regard `A` definitionally as `AdjoinRoot sourceSPolynomial`.  Construct an
   injective ring hom `iA : A →+* L` in two small steps.  First use
   `AdjoinRoot.map (algebraMap R K)` to map into
   `AdjoinRoot (sourceSPolynomial.map (algebraMap R K))`.  Its injectivity
   follows from `AdjoinRoot.mk_eq_zero` and
   `Polynomial.map_dvd_map`: the latter applies because
   `sourceSPolynomial` is monic and `algebraMap R K` is injective.  Then make
   the explicit `K`-algebra equivalence from that adjoin-root to `L`: send
   `AdjoinRoot.root` to `QuadraticAlgebra.omega` using
   `AdjoinRoot.liftAlgHom`, and send `omega` back to the root using
   `QuadraticAlgebra.lift`; prove the two composites by
   `AdjoinRoot.algHom_ext` and `QuadraticAlgebra.algHom_ext`.  The defining
   root equations reduce to `QuadraticAlgebra.omega_mul_omega_eq_algebraMap`
   and `AdjoinRoot.eval₂_root`.

4. Write `qA := Ideal.Quotient.mk (Ideal.span {sourceSPolynomial})` and
   `g := sourceTPolynomial.map qA : Polynomial A`.  It is monic because
   `sourceTPolynomial` is monic.  Show

     `g.map iA = X ^ 2 - C (algebraMap K L (algebraMap R K Q))`

   by unfolding `sourceTPolynomial`, `planeSecondPolynomial`, and the
   construction of `iA`.  Step 2 and
   `X_pow_sub_C_irreducible_of_prime Nat.prime_two` make the right side
   irreducible in `L[X]`, hence prime by
   `UniqueFactorizationMonoid.irreducible_iff_prime`.  Therefore its
   singleton span is prime.  Apply the existing local helper
   `monic_span_isPrime_of_map_isPrime` with `R := A`, `S := L`, `f := iA`,
   and `g := g` to obtain `(Ideal.span {g}).IsPrime` in `Polynomial A`.

5. Lift that prime ideal back through the first relation.  Use
   `Ideal.polynomialQuotientEquivQuotientPolynomial
   (Ideal.span {sourceSPolynomial})` and its theorem
   `Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk` (both in
   `Mathlib/RingTheory/Polynomial/Quotient.lean`) to identify the image of
   `Ideal.span {g}` with the image of `Ideal.span {sourceTPolynomial}` under
   the quotient by
   `Ideal.map Polynomial.C (Ideal.span {sourceSPolynomial})`.  Transport
   primeness across the equivalence with `Ideal.map_isPrime_of_equiv`, then
   comap along the quotient map.  Rewrite the comap with
   `Ideal.comap_map_quotientMk` from
   `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, and rewrite
   `Ideal.map_span`, to conclude

     `(Ideal.span {Polynomial.C sourceSPolynomial, sourceTPolynomial}).IsPrime`.

6. Package the existing three-variable reindexing as an actual `RingEquiv`:
   use `MvPolynomial.renameEquiv`, `MvPolynomial.finSuccEquiv`, and twice
   `Polynomial.mapEquiv` (the inner equivalence is
   `MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)`).  Its coerced hom is the existing
   `sourceFullReindex`.  Add the companion computation

     `sourceFullReindex sourceSRelation = Polynomial.C sourceSPolynomial`

   alongside `sourceFullReindex_tRelation`.  By `Ideal.map_span`, the
   equivalence sends `sourceRelationsIdeal` to the prime ideal from step 5.
   Equivalently, comap that prime with `Ideal.comap_isPrime` and identify the
   comap generator-by-generator, following the already checked pattern in
   `planeIdeal_isPrime`.  This proves `sourceRelationsIdeal.IsPrime`.

7. Finish exactly as for the adjacent plane curve:

     `(Ideal.Quotient.isDomain_iff_prime
       (I := sourceRelationsIdeal)).mpr sourceRelationsIdeal_isPrime`.
-/
instance sourceRing_isDomain : IsDomain sourceRing := by sorry
instance planeCurveRing_isDomain : IsDomain planeCurveRing := by
  exact (Ideal.Quotient.isDomain_iff_prime (I := Ideal.span {planeRelation})).mpr
    planeIdeal_isPrime

private abbrev quadraticAuxiliaryRing :=
  Polynomial ℚ ⧸ Ideal.span {Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)}

private lemma quadraticAuxiliary_X_ne_zero :
    (Ideal.Quotient.mk (Ideal.span {Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)})
      Polynomial.X : quadraticAuxiliaryRing) ≠ 0 := by
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem] at h
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have hm : (Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)).Monic :=
    Polynomial.monic_X_pow_add_C (a := (24 : ℚ)) (by norm_num)
  exact hm.not_dvd_of_natDegree_lt (by simp) (by simp) ⟨u, hu⟩

private lemma source_sum_ne_zero :
    (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (1 : Fin 3)) +
      Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (2 : Fin 3)) :
        sourceRing) ≠ 0 := by
  let q : Polynomial ℚ →+* quadraticAuxiliaryRing := Ideal.Quotient.mk _
  let f : sourcePolynomialRing →+* quadraticAuxiliaryRing :=
    MvPolynomial.eval₂Hom (algebraMap ℚ quadraticAuxiliaryRing)
      ![-1, q Polynomial.X, 0]
  have hquad : q Polynomial.X ^ 2 + (24 : quadraticAuxiliaryRing) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self (Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)))
    change q (Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)) = 0 at h
    rw [map_add, map_pow] at h
    norm_num at h
    exact h
  have hS : sourceRelationsIdeal ≤ RingHom.ker f := by
    rw [sourceRelationsIdeal, Ideal.span_le]
    intro p hp
    change f p = 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · rw [sourceSRelation]
      simp [f, MvPolynomial.eval₂Hom_X']
      convert hquad using 1 <;> norm_num [map_ofNat]
    · rw [sourceTRelation]
      simp [f, MvPolynomial.eval₂Hom_X']
  let F : sourceRing →+* quadraticAuxiliaryRing :=
    Ideal.Quotient.lift sourceRelationsIdeal f (by
      intro a ha
      simpa only [RingHom.mem_ker] using hS ha)
  intro h
  have h' := congrArg F h
  dsimp [F] at h'
  simp only [map_add, map_zero, Ideal.Quotient.lift_mk] at h'
  have h'' : q Polynomial.X = 0 := by
    simpa [f] using h'
  exact quadraticAuxiliary_X_ne_zero h''

private lemma plane_y_ne_zero :
    (Ideal.Quotient.mk (Ideal.span {planeRelation})
      (MvPolynomial.X (1 : Fin 2)) : planeCurveRing) ≠ 0 := by
  let q : Polynomial ℚ →+* quadraticAuxiliaryRing := Ideal.Quotient.mk _
  let f : planePolynomialRing →+* quadraticAuxiliaryRing :=
    MvPolynomial.eval₂Hom (algebraMap ℚ quadraticAuxiliaryRing)
      ![-1, q Polynomial.X]
  have hquad : q Polynomial.X ^ 2 + (24 : quadraticAuxiliaryRing) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self (Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)))
    change q (Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)) = 0 at h
    rw [map_add, map_pow] at h
    norm_num at h
    exact h
  have hP : Ideal.span {planeRelation} ≤ RingHom.ker f := by
    rw [Ideal.span_le]
    intro p hp
    change f p = 0
    simp only [Set.mem_singleton_iff] at hp
    subst p
    rw [planeRelation]
    simp [f, planeFirstCubic, planeSecondCubic, MvPolynomial.eval₂Hom_X']
    convert congrArg (fun z : quadraticAuxiliaryRing => z ^ 2) hquad using 1 <;>
      norm_num [map_ofNat]
  let F : planeCurveRing →+* quadraticAuxiliaryRing :=
    Ideal.Quotient.lift (Ideal.span {planeRelation}) f (by
      intro a ha
      simpa only [RingHom.mem_ker] using hP ha)
  intro h
  have h' := congrArg F h
  dsimp [F] at h'
  simp only [map_zero, Ideal.Quotient.lift_mk] at h'
  have h'' : q Polynomial.X = 0 := by
    simpa [f] using h'
  exact quadraticAuxiliary_X_ne_zero h''

private lemma primitive_element_quadratic_identities {R : Type*} [CommRing R]
    {y p q v c : R} (hy : y * v = 1) (hc : 2 * c = 1)
    (hrel : (y ^ 2 - p - q) ^ 2 = 4 * p * q) :
    (c * (y + (p - q) * v)) ^ 2 = p ∧
      (c * (y - (p - q) * v)) ^ 2 = q := by
  have hy2 : y ^ 2 * v ^ 2 = 1 := by
    rw [← mul_pow, hy, one_pow]
  have hfirst : v ^ 2 * y ^ 4 = y ^ 2 := by
    calc
      v ^ 2 * y ^ 4 = y ^ 2 * (y ^ 2 * v ^ 2) := by ring
      _ = y ^ 2 := by rw [hy2, mul_one]
  have hsecond : v ^ 2 * (y ^ 2 * (p + q)) = p + q := by
    calc
      v ^ 2 * (y ^ 2 * (p + q)) = (y ^ 2 * v ^ 2) * (p + q) := by ring
      _ = p + q := by rw [hy2, one_mul]
  have hrel' : y ^ 2 - 2 * (p + q) + (p - q) ^ 2 * v ^ 2 = 0 := by
    calc
      y ^ 2 - 2 * (p + q) + (p - q) ^ 2 * v ^ 2 =
          v ^ 2 * y ^ 4 - 2 * (v ^ 2 * (y ^ 2 * (p + q))) +
            (p - q) ^ 2 * v ^ 2 := by rw [hfirst, hsecond]
      _ = v ^ 2 * ((y ^ 2 - p - q) ^ 2 - 4 * p * q) := by ring
      _ = 0 := by rw [hrel]; ring
  have hplus : (y + (p - q) * v) ^ 2 = 4 * p := by
    calc
      (y + (p - q) * v) ^ 2 =
          y ^ 2 + 2 * (p - q) + (p - q) ^ 2 * v ^ 2 := by
            calc
              (y + (p - q) * v) ^ 2 =
                  y ^ 2 + 2 * (p - q) * (y * v) + (p - q) ^ 2 * v ^ 2 := by ring
              _ = y ^ 2 + 2 * (p - q) + (p - q) ^ 2 * v ^ 2 := by rw [hy, mul_one]
      _ = 4 * p := by linear_combination hrel'
  have hminus : (y - (p - q) * v) ^ 2 = 4 * q := by
    calc
      (y - (p - q) * v) ^ 2 =
          y ^ 2 - 2 * (p - q) + (p - q) ^ 2 * v ^ 2 := by
            calc
              (y - (p - q) * v) ^ 2 =
                  y ^ 2 - 2 * (p - q) * (y * v) + (p - q) ^ 2 * v ^ 2 := by ring
              _ = y ^ 2 - 2 * (p - q) + (p - q) ^ 2 * v ^ 2 := by rw [hy, mul_one]
      _ = 4 * q := by linear_combination hrel'
  constructor
  · calc
      (c * (y + (p - q) * v)) ^ 2 = c ^ 2 * (y + (p - q) * v) ^ 2 := by ring
      _ = c ^ 2 * (4 * p) := by rw [hplus]
      _ = p := by calc
        c ^ 2 * (4 * p) = (2 * c) ^ 2 * p := by ring
        _ = p := by rw [hc, one_pow, one_mul]
  · calc
      (c * (y - (p - q) * v)) ^ 2 = c ^ 2 * (y - (p - q) * v) ^ 2 := by ring
      _ = c ^ 2 * (4 * q) := by rw [hminus]
      _ = q := by calc
        c ^ 2 * (4 * q) = (2 * c) ^ 2 * q := by ring
        _ = q := by rw [hc, one_pow, one_mul]

private lemma source_plane_localization_comp_simple
    {yA : sourceRing} {yB : planeCurveRing}
    (gA : sourceRing →+* Localization.Away yB)
    (gB : planeCurveRing →+* Localization.Away yA)
    (FA : Localization.Away yA →+* Localization.Away yB)
    (hFA_comp : FA.comp (algebraMap sourceRing (Localization.Away yA)) = gA)
    (hconstA : ∀ r : ℚ, algebraMap ℚ (Localization.Away yA) r =
      algebraMap sourceRing (Localization.Away yA)
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C r)))
    (hconstB : ∀ r : ℚ, algebraMap ℚ (Localization.Away yB) r =
      algebraMap planeCurveRing (Localization.Away yB)
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C r)))
    (hgA_C : ∀ r : ℚ, gA (Ideal.Quotient.mk sourceRelationsIdeal
        (MvPolynomial.C r)) = algebraMap ℚ (Localization.Away yB) r)
    (hgB_C : ∀ r : ℚ, gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
        (MvPolynomial.C r)) = algebraMap ℚ (Localization.Away yA) r)
    (hFA_x : FA (algebraMap sourceRing (Localization.Away yA)
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3)))) =
      algebraMap planeCurveRing (Localization.Away yB)
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.X (0 : Fin 2))))
    (hFA_y : FA (algebraMap sourceRing (Localization.Away yA)
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (1 : Fin 3)) +
          Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (2 : Fin 3)))) =
      algebraMap planeCurveRing (Localization.Away yB)
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.X (1 : Fin 2))))
    (hgB_x : gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
        (MvPolynomial.X (0 : Fin 2))) =
      algebraMap sourceRing (Localization.Away yA)
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3))))
    (hgB_y : gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
        (MvPolynomial.X (1 : Fin 2))) =
      algebraMap sourceRing (Localization.Away yA)
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (1 : Fin 3)) +
          Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (2 : Fin 3)))) :
    FA.comp gB = algebraMap planeCurveRing (Localization.Away yB) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change FA (gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
      (MvPolynomial.C r))) =
      algebraMap planeCurveRing (Localization.Away yB)
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C r))
    calc
      FA (gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
          (MvPolynomial.C r))) = FA (algebraMap ℚ (Localization.Away yA) r) := by
        rw [hgB_C r]
      _ = FA (algebraMap sourceRing (Localization.Away yA)
          (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C r))) := by
        rw [hconstA r]
      _ = gA (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C r)) :=
        RingHom.congr_fun hFA_comp _
      _ = algebraMap ℚ (Localization.Away yB) r := hgA_C r
      _ = algebraMap planeCurveRing (Localization.Away yB)
          (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C r)) :=
        hconstB r
  · intro i
    fin_cases i
    · have hx : FA (gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
          (MvPolynomial.X (0 : Fin 2)))) =
        algebraMap planeCurveRing (Localization.Away yB)
          (Ideal.Quotient.mk (Ideal.span {planeRelation})
            (MvPolynomial.X (0 : Fin 2))) := by
        rw [hgB_x, hFA_x]
      convert hx using 1 <;> rfl
    · have hy : FA (gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
          (MvPolynomial.X (1 : Fin 2)))) =
        algebraMap planeCurveRing (Localization.Away yB)
          (Ideal.Quotient.mk (Ideal.span {planeRelation})
            (MvPolynomial.X (1 : Fin 2))) := by
        rw [hgB_y, hFA_y]
      convert hy using 1 <;> rfl

private lemma source_plane_localization_comp_coordinates
    {yA : sourceRing} {yB : planeCurveRing}
    (xA' yA' : Localization.Away yA)
    (xB' yB' : Localization.Away yB)
    (gA : sourceRing →+* Localization.Away yB)
    (gB : planeCurveRing →+* Localization.Away yA)
    (FA : Localization.Away yA →+* Localization.Away yB)
    (hFA_comp : FA.comp (algebraMap sourceRing (Localization.Away yA)) = gA)
    (hconstA : ∀ r : ℚ, algebraMap ℚ (Localization.Away yA) r =
      algebraMap sourceRing (Localization.Away yA)
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C r)))
    (hconstB : ∀ r : ℚ, algebraMap ℚ (Localization.Away yB) r =
      algebraMap planeCurveRing (Localization.Away yB)
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C r)))
    (hgA_C : ∀ r : ℚ, gA (Ideal.Quotient.mk sourceRelationsIdeal
        (MvPolynomial.C r)) = algebraMap ℚ (Localization.Away yB) r)
    (hgB_C : ∀ r : ℚ, gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
        (MvPolynomial.C r)) = algebraMap ℚ (Localization.Away yA) r)
    (hFA_x : FA xA' = xB')
    (hFA_y : FA yA' = yB')
    (hgB_x : gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
        (MvPolynomial.X (0 : Fin 2))) = xA')
    (hgB_y : gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
        (MvPolynomial.X (1 : Fin 2))) = yA')
    (hxA : xA' = algebraMap sourceRing (Localization.Away yA)
      (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3))))
    (hyA : yA' = algebraMap sourceRing (Localization.Away yA)
      (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (1 : Fin 3)) +
        Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (2 : Fin 3))))
    (hxB : xB' = algebraMap planeCurveRing (Localization.Away yB)
      (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.X (0 : Fin 2))))
    (hyB : yB' = algebraMap planeCurveRing (Localization.Away yB)
      (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.X (1 : Fin 2)))) :
    FA.comp gB = algebraMap planeCurveRing (Localization.Away yB) := by
  refine source_plane_localization_comp_simple (yA := yA) (yB := yB)
    gA gB FA hFA_comp hconstA hconstB hgA_C hgB_C ?_ ?_ ?_ ?_
  · rw [← hxA, ← hxB]
    exact hFA_x
  · rw [← hyA, ← hyB]
    exact hFA_y
  · rw [hgB_x, hxA]
  · rw [hgB_y, hyA]

private lemma source_away_hom_compositions
    {yA : sourceRing} {yB : planeCurveRing}
    (gA : sourceRing →+* Localization.Away yB)
    (gB : planeCurveRing →+* Localization.Away yA)
    (FA : Localization.Away yA →+* Localization.Away yB)
    (FB : Localization.Away yB →+* Localization.Away yA)
    (hFA_comp : FA.comp (algebraMap sourceRing (Localization.Away yA)) = gA)
    (hFB_comp : FB.comp (algebraMap planeCurveRing (Localization.Away yB)) = gB)
    (hcompA : FB.comp gA = algebraMap sourceRing (Localization.Away yA))
    (hcompB : FA.comp gB = algebraMap planeCurveRing (Localization.Away yB)) :
    FB.comp FA = RingHom.id (Localization.Away yA) ∧
      FA.comp FB = RingHom.id (Localization.Away yB) := by
  constructor
  · apply IsLocalization.ringHom_ext (Submonoid.powers yA)
    apply RingHom.ext
    intro z
    change FB (FA (algebraMap sourceRing (Localization.Away yA) z)) =
      algebraMap sourceRing (Localization.Away yA) z
    calc
      FB (FA (algebraMap sourceRing (Localization.Away yA) z)) = FB (gA z) := by
        change FB ((FA.comp (algebraMap sourceRing (Localization.Away yA))) z) = FB (gA z)
        rw [RingHom.congr_fun hFA_comp z]
      _ = algebraMap sourceRing (Localization.Away yA) z :=
        RingHom.congr_fun hcompA z
  · apply IsLocalization.ringHom_ext (Submonoid.powers yB)
    apply RingHom.ext
    intro z
    change FA (FB (algebraMap planeCurveRing (Localization.Away yB) z)) =
      algebraMap planeCurveRing (Localization.Away yB) z
    calc
      FA (FB (algebraMap planeCurveRing (Localization.Away yB) z)) = FA (gB z) := by
        change FA ((FB.comp (algebraMap planeCurveRing (Localization.Away yB))) z) = FA (gB z)
        rw [RingHom.congr_fun hFB_comp z]
      _ = algebraMap planeCurveRing (Localization.Away yB) z :=
        RingHom.congr_fun hcompB z

private lemma fractionRing_equiv_of_away_equiv
    {yA : sourceRing} {yB : planeCurveRing}
    (hyA : yA ≠ 0) (hyB : yB ≠ 0)
    (e : Localization.Away yA ≃+* Localization.Away yB) :
    Nonempty (FractionRing sourceRing ≃+* FractionRing planeCurveRing) := by
  let algA : Localization.Away yA →ₐ[sourceRing] FractionRing sourceRing :=
    IsLocalization.Away.liftAlgHom (R := sourceRing) (S := Localization.Away yA)
      (P := FractionRing sourceRing)
      (f := Algebra.ofId sourceRing (FractionRing sourceRing)) yA
      (isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _
          (IsFractionRing.injective sourceRing (FractionRing sourceRing))).mpr hyA))
  let _ : Algebra (Localization.Away yA) (FractionRing sourceRing) := algA.toAlgebra
  let algB : Localization.Away yB →ₐ[planeCurveRing] FractionRing planeCurveRing :=
    IsLocalization.Away.liftAlgHom (R := planeCurveRing) (S := Localization.Away yB)
      (P := FractionRing planeCurveRing)
      (f := Algebra.ofId planeCurveRing (FractionRing planeCurveRing)) yB
      (isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _
          (IsFractionRing.injective planeCurveRing (FractionRing planeCurveRing))).mpr hyB))
  let _ : Algebra (Localization.Away yB) (FractionRing planeCurveRing) := algB.toAlgebra
  letI : IsFractionRing (Localization.Away yA) (FractionRing sourceRing) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers yA) (Localization.Away yA) (FractionRing sourceRing)
  letI : IsFractionRing (Localization.Away yB) (FractionRing planeCurveRing) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers yB) (Localization.Away yB) (FractionRing planeCurveRing)
  exact ⟨(IsFractionRing.ringEquivOfRingEquiv e :
    FractionRing sourceRing ≃+* FractionRing planeCurveRing)⟩

private lemma source_square_relations
    (xA sA tA : sourceRing)
    (hxA : xA = Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3)))
    (hsA : sA = Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (1 : Fin 3)))
    (htA : tA = Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (2 : Fin 3))) :
    sA ^ 2 = (xA - 1) * (xA - 2) * (xA - 3) ∧
      tA ^ 2 = (xA + 1) * (xA + 2) * (xA + 3) := by
  subst xA
  subst sA
  subst tA
  have hC2 :
      (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C (2 : ℚ)) : sourceRing) = 2 := by
    change Ideal.Quotient.mk sourceRelationsIdeal (algebraMap ℚ sourcePolynomialRing 2) = 2
    rw [Ideal.Quotient.mk_algebraMap]
    exact map_ofNat (algebraMap ℚ sourceRing) 2
  have hC3 :
      (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C (3 : ℚ)) : sourceRing) = 3 := by
    change Ideal.Quotient.mk sourceRelationsIdeal (algebraMap ℚ sourcePolynomialRing 3) = 3
    rw [Ideal.Quotient.mk_algebraMap]
    exact map_ofNat (algebraMap ℚ sourceRing) 3
  constructor
  · have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (show sourceSRelation ∈ sourceRelationsIdeal from
        Ideal.subset_span (by simp))
    rw [sourceSRelation] at h
    simp only [map_sub, map_mul, map_pow, map_add] at h
    rw [hC2, hC3] at h
    have h0 :
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (1 : Fin 3))) ^ 2 -
          (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3)) - 1) *
            (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3)) - 2) *
              (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3)) - 3) = 0 := by
      simpa using h
    exact sub_eq_zero.mp h0
  · have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (show sourceTRelation ∈ sourceRelationsIdeal from
        Ideal.subset_span (by simp))
    rw [sourceTRelation] at h
    simp only [map_sub, map_mul, map_pow, map_add] at h
    rw [hC2, hC3] at h
    have h0 :
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (2 : Fin 3))) ^ 2 -
          (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3)) + 1) *
            (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3)) + 2) *
              (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3)) + 3) = 0 := by
      simpa using h
    exact sub_eq_zero.mp h0

theorem source_fraction_field_equiv_plane_curve :
    Nonempty (FractionRing sourceRing ≃+* FractionRing planeCurveRing) := by
  let xA : sourceRing :=
    Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (0 : Fin 3))
  let sA : sourceRing :=
    Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (1 : Fin 3))
  let tA : sourceRing :=
    Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.X (2 : Fin 3))
  let yA : sourceRing := sA + tA
  let pA : sourceRing :=
    (xA - 1) * (xA - 2) * (xA - 3)
  let qA : sourceRing :=
    (xA + 1) * (xA + 2) * (xA + 3)
  let xB : planeCurveRing :=
    Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.X (0 : Fin 2))
  let yB : planeCurveRing :=
    Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.X (1 : Fin 2))
  let pB : planeCurveRing :=
    (xB - 1) * (xB - 2) * (xB - 3)
  let qB : planeCurveRing :=
    (xB + 1) * (xB + 2) * (xB + 3)
  have hyA : yA ≠ 0 := by
    simpa [yA, sA, tA] using source_sum_ne_zero
  have hyB : yB ≠ 0 := by
    simpa [yB] using plane_y_ne_zero
  have hsource := source_square_relations xA sA tA rfl rfl rfl
  have hsA : sA ^ 2 = pA := by simpa [pA] using hsource.1
  have htA : tA ^ 2 = qA := by simpa [qA] using hsource.2
  let A' := Localization.Away yA
  let B' := Localization.Away yB
  let xA' : A' := algebraMap sourceRing A' xA
  let sA' : A' := algebraMap sourceRing A' sA
  let tA' : A' := algebraMap sourceRing A' tA
  let yA' : A' := algebraMap sourceRing A' yA
  let xB' : B' := algebraMap planeCurveRing B' xB
  let yB' : B' := algebraMap planeCurveRing B' yB
  let pB' : B' := algebraMap planeCurveRing B' pB
  let qB' : B' := algebraMap planeCurveRing B' qB
  have hsA' : sA' ^ 2 = algebraMap sourceRing A' pA := by
    simpa [sA', pA] using congrArg (algebraMap sourceRing A') hsA
  have htA' : tA' ^ 2 = algebraMap sourceRing A' qA := by
    simpa [tA', qA] using congrArg (algebraMap sourceRing A') htA
  have hC2A : algebraMap ℚ A' (2 : ℚ) = algebraMap sourceRing A' (2 : sourceRing) := by
    simpa only [map_ofNat] using IsScalarTower.algebraMap_apply ℚ sourceRing A' (2 : ℚ)
  have hC3A : algebraMap ℚ A' (3 : ℚ) = algebraMap sourceRing A' (3 : sourceRing) := by
    simpa only [map_ofNat] using IsScalarTower.algebraMap_apply ℚ sourceRing A' (3 : ℚ)
  have hpA' :
      (xA' - 1) * (xA' - algebraMap ℚ A' 2) * (xA' - algebraMap ℚ A' 3) =
        algebraMap sourceRing A' pA := by
    simp [pA, xA']
    rw [hC2A, hC3A]
  have hqA' :
      (xA' + 1) * (xA' + algebraMap ℚ A' 2) * (xA' + algebraMap ℚ A' 3) =
        algebraMap sourceRing A' qA := by
    simp [qA, xA']
    rw [hC2A, hC3A]
  let fB : planePolynomialRing →+* A' :=
    MvPolynomial.eval₂Hom (algebraMap ℚ A') ![xA', sA' + tA']
  have hfB_rel : fB planeRelation = 0 := by
    simp [fB, planeRelation, planeFirstCubic, planeSecondCubic,
      MvPolynomial.eval₂Hom_X']
    rw [hpA', hqA']
    rw [← hsA', ← htA']
    ring
  have hfB_ker : ∀ a ∈ Ideal.span {planeRelation}, fB a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨u, rfl⟩ := ha
    simp [map_mul, hfB_rel]
  let gB : planeCurveRing →+* A' :=
    Ideal.Quotient.lift (Ideal.span {planeRelation})
      (MvPolynomial.eval₂Hom (algebraMap ℚ A') ![xA', sA' + tA']) hfB_ker
  have hgB_C : ∀ r : ℚ, gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
      (MvPolynomial.C r)) = algebraMap ℚ A' r := by
    intro r
    dsimp only [gB]
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]
  let invYB : B' := IsLocalization.Away.invSelf yB
  have hYB : yB' * invYB = 1 := by
    simpa [yB'] using IsLocalization.Away.mul_invSelf yB
  let cB : B' := algebraMap ℚ B' (1 / 2 : ℚ)
  let sB' : B' := cB * (yB' + (pB' - qB') * invYB)
  let tB' : B' := cB * (yB' - (pB' - qB') * invYB)
  have hcB : 2 * cB = 1 := by
    dsimp [cB]
    rw [← map_ofNat (algebraMap ℚ B') 2, ← map_mul]
    norm_num
  have hB_rel : (yB' ^ 2 - pB' - qB') ^ 2 = 4 * pB' * qB' := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (show planeRelation ∈ Ideal.span {planeRelation} from Ideal.subset_span (by simp))
    have h0 := h
    change (Ideal.Quotient.mk (Ideal.span {planeRelation}))
      (((MvPolynomial.X (1 : Fin 2)) ^ 2 - planeFirstCubic - planeSecondCubic) ^ 2 -
        4 * planeFirstCubic * planeSecondCubic) = 0 at h0
    simp only [map_sub, map_mul, map_pow, map_add] at h0
    have hC2 :
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C (2 : ℚ)) :
          planeCurveRing) = 2 := by
      change Ideal.Quotient.mk (Ideal.span {planeRelation})
        (algebraMap ℚ planePolynomialRing 2) = 2
      rw [Ideal.Quotient.mk_algebraMap]
      exact map_ofNat (algebraMap ℚ planeCurveRing) 2
    have hC3 :
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C (3 : ℚ)) :
          planeCurveRing) = 3 := by
      change Ideal.Quotient.mk (Ideal.span {planeRelation})
        (algebraMap ℚ planePolynomialRing 3) = 3
      rw [Ideal.Quotient.mk_algebraMap]
      exact map_ofNat (algebraMap ℚ planeCurveRing) 3
    have hFirst :
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) planeFirstCubic :
          planeCurveRing) = pB := by
      simp [planeFirstCubic, pB, xB]
      rw [hC2, hC3]
    have hSecond :
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) planeSecondCubic :
          planeCurveRing) = qB := by
      simp [planeSecondCubic, qB, xB]
      rw [hC2, hC3]
    rw [hFirst, hSecond] at h0
    simp only [map_ofNat] at h0
    have h0' : (yB ^ 2 - pB - qB) ^ 2 - 4 * pB * qB = 0 := by
      simpa [pB, qB, xB] using h0
    have h' := congrArg (algebraMap planeCurveRing B') h0'
    simp only [map_sub, map_mul, map_pow, map_add] at h'
    have hC4 : algebraMap planeCurveRing B' (4 : planeCurveRing) = 4 :=
      map_ofNat (algebraMap planeCurveRing B') 4
    rw [hC4] at h'
    have h0'' :
        (yB' ^ 2 - pB' - qB') ^ 2 - 4 * pB' * qB' = 0 := by
      simpa [pB', qB', yB'] using h'
    exact sub_eq_zero.mp h0''
  have hsB : sB' ^ 2 = pB' := by
    exact (primitive_element_quadratic_identities hYB hcB hB_rel).1
  have htB : tB' ^ 2 = qB' := by
    exact (primitive_element_quadratic_identities hYB hcB hB_rel).2
  let fA : sourcePolynomialRing →+* B' :=
    MvPolynomial.eval₂Hom (algebraMap ℚ B') ![xB', sB', tB']
  have hfA_s : fA (MvPolynomial.X (1 : Fin 3)) = sB' := by
    simp [fA]
  have hfA_t : fA (MvPolynomial.X (2 : Fin 3)) = tB' := by
    simp [fA]
  have hfA_rel : fA sourceSRelation = 0 ∧ fA sourceTRelation = 0 := by
    have hC2B : algebraMap ℚ B' (2 : ℚ) =
        algebraMap planeCurveRing B' (2 : planeCurveRing) := by
      simpa only [map_ofNat] using
        IsScalarTower.algebraMap_apply ℚ planeCurveRing B' (2 : ℚ)
    have hC3B : algebraMap ℚ B' (3 : ℚ) =
        algebraMap planeCurveRing B' (3 : planeCurveRing) := by
      simpa only [map_ofNat] using
        IsScalarTower.algebraMap_apply ℚ planeCurveRing B' (3 : ℚ)
    have hpB' :
        pB' = (xB' - 1) * (xB' - algebraMap ℚ B' 2) *
          (xB' - algebraMap ℚ B' 3) := by
      dsimp [pB', pB, xB', xB]
      simp only [map_mul, map_sub, map_add, map_one]
      rw [hC2B, hC3B]
    have hqB' :
        qB' = (xB' + 1) * (xB' + algebraMap ℚ B' 2) *
          (xB' + algebraMap ℚ B' 3) := by
      dsimp [qB', qB, xB', xB]
      simp only [map_mul, map_add, map_one]
      rw [hC2B, hC3B]
    constructor
    · simp [fA, sourceSRelation, MvPolynomial.eval₂Hom_X', hsB, hpB']
    · simp [fA, sourceTRelation, MvPolynomial.eval₂Hom_X', htB, hqB']
  have hFA : sourceRelationsIdeal ≤ RingHom.ker fA := by
    rw [sourceRelationsIdeal, Ideal.span_le]
    intro p hp
    change fA p = 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact hfA_rel.1
    · exact hfA_rel.2
  have hFA_ker : ∀ a ∈ sourceRelationsIdeal, fA a = 0 := by
    intro a ha
    simpa only [RingHom.mem_ker] using hFA ha
  let gA : sourceRing →+* B' :=
    Ideal.Quotient.lift sourceRelationsIdeal
      (MvPolynomial.eval₂Hom (algebraMap ℚ B') ![xB', sB', tB']) hFA_ker
  have hgA_C : ∀ r : ℚ, gA (Ideal.Quotient.mk sourceRelationsIdeal
      (MvPolynomial.C r)) = algebraMap ℚ B' r := by
    intro r
    dsimp only [gA]
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]
  have hgA_y : gA yA = yB' := by
    simp [gA, yA, sA, tA]
    dsimp [sB', tB']
    calc
      cB * (yB' + (pB' - qB') * invYB) +
          cB * (yB' - (pB' - qB') * invYB) = (2 * cB) * yB' := by ring
      _ = yB' := by rw [hcB, one_mul]
  have hgA_powers : ∀ z : Submonoid.powers yA, IsUnit (gA z) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow, hgA_y]
    exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit yB)
  let FA : A' →+* B' :=
    IsLocalization.lift (M := Submonoid.powers yA) (g := gA) hgA_powers
  have hFA_comp : FA.comp (algebraMap sourceRing A') = gA := by
    simpa [FA, yA, sA', tA'] using
      (IsLocalization.lift_comp (M := Submonoid.powers yA) (g := gA) hgA_powers)
  have hFA_xA : FA xA' = xB' := by
    dsimp [xA']
    calc
      FA (algebraMap sourceRing A' xA) = gA xA :=
        RingHom.congr_fun hFA_comp xA
      _ = xB' := by simp [gA, xA, fA, xB']
  have hFA_yA : FA yA' = yB' := by
    dsimp [yA']
    exact (RingHom.congr_fun hFA_comp yA).trans hgA_y
  have hgB_y : gB yB = yA' := by
    simp [gB, yB, yA', fB]
    change sA' + tA' = algebraMap sourceRing A' (sA + tA)
    rw [map_add]
  have hgB_powers : ∀ z : Submonoid.powers yB, IsUnit (gB z) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow, hgB_y]
    exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit yA)
  let FB : B' →+* A' :=
    IsLocalization.lift (M := Submonoid.powers yB) (g := gB) hgB_powers
  have hFB_comp : FB.comp (algebraMap planeCurveRing B') = gB := by
    simpa [FB] using
      (IsLocalization.lift_comp (M := Submonoid.powers yB) (g := gB) hgB_powers)
  have hFB_yB : FB yB' = yA' := by
    dsimp [yB']
    exact (RingHom.congr_fun hFB_comp yB).trans hgB_y
  let invYA : A' := IsLocalization.Away.invSelf yA
  have hYA : yA' * invYA = 1 := by
    simpa [invYA, yA'] using IsLocalization.Away.mul_invSelf yA
  have hFB_invYB : FB invYB = invYA := by
    apply (IsLocalization.Away.algebraMap_isUnit yA).mul_left_inj.mp
    change FB invYB * yA' = invYA * yA'
    calc
      FB invYB * yA' = FB invYB * FB yB' := by rw [hFB_yB]
      _ = FB (invYB * yB') := by rw [← map_mul]
      _ = 1 := by rw [mul_comm invYB yB', hYB, map_one]
      _ = invYA * yA' := by
        calc
          1 = yA' * invYA := hYA.symm
          _ = invYA * yA' := mul_comm _ _
  have hFB_xB : FB xB' = xA' := by
    dsimp [xB']
    have h := RingHom.congr_fun hFB_comp xB
    simpa [xB', xB, gB, fB, xA'] using h
  have hgB_x : gB xB = xA' := by
    simp [gB, xB, fB, xA']
  have hFB_pB : FB pB' = algebraMap sourceRing A' pA := by
    dsimp [pB']
    calc
      FB (algebraMap planeCurveRing B' pB) = gB pB :=
        RingHom.congr_fun hFB_comp pB
      _ = algebraMap sourceRing A' pA := by
        simp only [pB, map_mul, map_sub, map_ofNat]
        rw [hgB_x]
        simp [pA, xA', xA, map_ofNat]
  have hFB_qB : FB qB' = algebraMap sourceRing A' qA := by
    dsimp [qB']
    calc
      FB (algebraMap planeCurveRing B' qB) = gB qB :=
        RingHom.congr_fun hFB_comp qB
      _ = algebraMap sourceRing A' qA := by
        simp only [qB, map_mul, map_add, map_ofNat]
        rw [hgB_x]
        simp [qA, xA', xA, map_ofNat]
  let cA : A' := algebraMap ℚ A' (1 / 2)
  have hcA : (2 : A') * cA = 1 := by
    dsimp [cA]
    rw [← map_ofNat (algebraMap ℚ A') 2, ← map_mul]
    norm_num
  have h2A : IsUnit (2 : A') := by
    rw [← map_ofNat (algebraMap ℚ A') 2]
    exact IsUnit.map _ (isUnit_iff_ne_zero.mpr (by norm_num))
  have hFB_cB : FB cB = cA := by
    apply h2A.mul_left_inj.mp
    calc
      FB cB * 2 = FB (cB * 2) := by rw [map_mul, map_ofNat]
      _ = 1 := by rw [mul_comm cB 2, hcB, map_one]
      _ = cA * 2 := by rw [mul_comm, hcA]
  have hdiffA : (algebraMap sourceRing A' pA -
      algebraMap sourceRing A' qA) = (sA' - tA') * yA' := by
    rw [← hsA', ← htA']
    have hyA' : yA' = sA' + tA' := by
      simp [yA', yA, sA', tA']
    rw [hyA']
    ring
  have hdiffA_inv : (algebraMap sourceRing A' pA -
      algebraMap sourceRing A' qA) * invYA = sA' - tA' := by
    rw [hdiffA, mul_assoc, hYA, mul_one]
  have hprimitiveA_s : cA * (yA' +
      (algebraMap sourceRing A' pA - algebraMap sourceRing A' qA) * invYA) = sA' := by
    have hyA' : yA' = sA' + tA' := by
      simp [yA', yA, sA', tA']
    rw [hyA', hdiffA_inv]
    calc
      cA * ((sA' + tA') + (sA' - tA')) = (2 * cA) * sA' := by ring
      _ = sA' := by rw [hcA, one_mul]
  have hprimitiveA_t : cA * (yA' -
      (algebraMap sourceRing A' pA - algebraMap sourceRing A' qA) * invYA) = tA' := by
    have hyA' : yA' = sA' + tA' := by
      simp [yA', yA, sA', tA']
    rw [hyA', hdiffA_inv]
    calc
      cA * ((sA' + tA') - (sA' - tA')) = (2 * cA) * tA' := by ring
      _ = tA' := by rw [hcA, one_mul]
  have hFB_sB : FB sB' = sA' := by
    dsimp [sB']
    rw [map_mul, hFB_cB, map_add, map_mul, map_sub, hFB_yB, hFB_pB,
      hFB_qB, hFB_invYB]
    exact hprimitiveA_s
  have hFB_tB : FB tB' = tA' := by
    dsimp [tB']
    rw [map_mul, hFB_cB, map_sub, map_mul, map_sub, hFB_yB, hFB_pB,
      hFB_qB, hFB_invYB]
    exact hprimitiveA_t
  have hconstA : ∀ r : ℚ, algebraMap ℚ A' r =
      algebraMap sourceRing A'
        (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C r)) := by
    intro r
    change algebraMap ℚ A' r =
      algebraMap sourceRing A'
        (Ideal.Quotient.mk sourceRelationsIdeal
          (algebraMap ℚ sourcePolynomialRing r))
    rw [Ideal.Quotient.mk_algebraMap]
    exact (IsScalarTower.algebraMap_apply ℚ sourceRing A' r).symm
  have hconstB : ∀ r : ℚ, algebraMap ℚ B' r =
      algebraMap planeCurveRing B'
        (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C r)) := by
    intro r
    change algebraMap ℚ B' r =
      algebraMap planeCurveRing B'
        (Ideal.Quotient.mk (Ideal.span {planeRelation})
          (algebraMap ℚ planePolynomialRing r))
    rw [Ideal.Quotient.mk_algebraMap]
    exact (IsScalarTower.algebraMap_apply ℚ planeCurveRing B' r).symm
  have hcompA : (FB.comp gA) = algebraMap sourceRing A' := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      change FB (fA (MvPolynomial.C r)) =
        algebraMap sourceRing A'
          (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C r))
      rw [show fA (MvPolynomial.C r) = algebraMap ℚ B' r by simp [fA]]
      have hgB_const : gB (Ideal.Quotient.mk (Ideal.span {planeRelation})
          (MvPolynomial.C r)) = algebraMap ℚ A' r := by
        simp [gB, fB]
      rw [hconstB r]
      calc
        FB (algebraMap planeCurveRing B'
            (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C r))) =
            gB (Ideal.Quotient.mk (Ideal.span {planeRelation}) (MvPolynomial.C r)) :=
          RingHom.congr_fun hFB_comp _
        _ = algebraMap ℚ A' r := hgB_const
        _ = algebraMap sourceRing A'
            (Ideal.Quotient.mk sourceRelationsIdeal (MvPolynomial.C r)) := hconstA r
    · intro i
      fin_cases i
      · simpa [RingHom.comp_apply, gA, fA, xB', xA', xB, xA] using hFB_xB
      · simpa [RingHom.comp_apply, gA, fA, sB', sA', xB', xA', xB, xA] using hFB_sB
      · simpa [RingHom.comp_apply, gA, fA, tB', tA', xB', xA', xB, xA] using hFB_tB
  have hcompB : (FA.comp gB) = algebraMap planeCurveRing B' := by
    exact source_plane_localization_comp_coordinates
      (xA' := xA') (yA' := yA') (xB' := xB') (yB' := yB')
      gA gB FA hFA_comp hconstA hconstB hgA_C hgB_C hFA_xA hFA_yA
      hgB_x hgB_y (by rfl) (by rfl) (by rfl) (by rfl)
  have hcomps := source_away_hom_compositions gA gB FA FB hFA_comp hFB_comp hcompA hcompB
  have hcompFA : FB.comp FA = RingHom.id A' := hcomps.1
  have hcompBF : FA.comp FB = RingHom.id B' := hcomps.2
  let e : A' ≃+* B' := RingEquiv.ofRingHom FA FB hcompBF hcompFA
  exact fractionRing_equiv_of_away_equiv hyA hyB e
