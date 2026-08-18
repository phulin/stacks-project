import Formalization.Books.Exercises.Unit19.Core

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IsIntegral
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
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (24 : ℚ)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · intro x hx
    rw [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]

private lemma no_rat_square_24 (z : ℚ) : z ^ 2 ≠ 24 := by
  intro hz
  have hs : IsSquare (24 : ℚ) := ⟨z, by simpa [pow_two] using hz.symm⟩
  rw [Rat.isSquare_ofNat_iff] at hs
  obtain ⟨w, hw⟩ := hs
  have hwle : w ≤ 4 := by nlinarith [Nat.zero_le w]
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 by omega) with
    rfl | rfl | rfl | rfl | rfl <;> norm_num at hw

private lemma monic_quadratic_eq {p : Polynomial ℚ} (hm : p.Monic)
    (hnd : p.natDegree = 2) :
    p = Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X +
      Polynomial.C (p.coeff 0) := by
  apply Polynomial.ext
  intro n
  by_cases h0 : n = 0
  · subst n
    simp
  by_cases h1 : n = 1
  · subst n
    simp
  by_cases h2 : n = 2
  · subst n
    have hcoeff := hm.coeff_natDegree
    rw [hnd] at hcoeff
    simpa using hcoeff
  have hn3 : 3 ≤ n := by omega
  have h0' : ¬0 = n := by omega
  have h1' : ¬1 = n := by omega
  have h2' : ¬2 = n := by omega
  have hlt : p.degree < (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hnd]
    exact_mod_cast hn3
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp only [if_neg h2, if_neg h1, if_neg h0, zero_add, add_zero]
  exact Polynomial.coeff_eq_zero_of_degree_lt hlt

private lemma quartic_plus_144_irreducible :
    Irreducible (Polynomial.X ^ 4 + Polynomial.C (144 : ℚ)) := by
  let p : Polynomial ℚ := Polynomial.X ^ 4 + Polynomial.C (144 : ℚ)
  have hp : p.Monic := by
    simpa [p] using
      (Polynomial.monic_X_pow_add_C (a := (144 : ℚ)) (n := 4) (by norm_num))
  have hp1 : p ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    simp [p] at this
  rw [hp.irreducible_iff_lt_natDegree_lt hp1]
  intro q hq hdeg hdiv
  have hdeg' : q.natDegree = 1 ∨ q.natDegree = 2 := by
    norm_num [p] at hdeg
    omega
  obtain ⟨r, hqr⟩ := hdiv
  have hprod : (q * r).Monic := by simpa [hqr] using hp
  have hr : r.Monic := hq.of_mul_monic_left hprod
  rcases hdeg' with hq1 | hq2
  · have hqform := hq.eq_X_add_C hq1
    have hev := congrArg (fun u : Polynomial ℚ => u.eval (-q.coeff 0)) hqr
    rw [hqform] at hev
    simp [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hev
    nlinarith [sq_nonneg (q.coeff 0 ^ 2)]
  · have hrdeg : r.natDegree = 2 := by
      have := congrArg Polynomial.natDegree hqr
      rw [Polynomial.natDegree_mul hq.ne_zero hr.ne_zero] at this
      simp [p, hq2] at this
      omega
    have hqform := monic_quadratic_eq hq hq2
    have hrform := monic_quadratic_eq hr hrdeg
    rw [hqform, hrform] at hqr
    ring_nf at hqr
    simp only [← mul_assoc, ← Polynomial.C_mul] at hqr
    have hcc :
        Polynomial.X ^ 2 * Polynomial.C (q.coeff 1) * Polynomial.C (r.coeff 1) =
          Polynomial.C (q.coeff 1 * r.coeff 1) * Polynomial.X ^ 2 := by
      rw [mul_assoc, ← Polynomial.C_mul]
      ring
    rw [hcc] at hqr
    have h0 := congrArg (fun u : Polynomial ℚ => u.coeff 0) hqr
    have h1 := congrArg (fun u : Polynomial ℚ => u.coeff 1) hqr
    have h2 := congrArg (fun u : Polynomial ℚ => u.coeff 2) hqr
    have h3 := congrArg (fun u : Polynomial ℚ => u.coeff 3) hqr
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_C, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_mul_X_pow, Polynomial.coeff_X_pow_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h0 h1 h2 h3
    norm_num at h0 h1 h2 h3
    by_cases ha : q.coeff 1 = 0
    · rw [ha] at h1 h2 h3
      have hr1 : r.coeff 1 = 0 := by linarith [h3]
      have hr0 : r.coeff 0 = -q.coeff 0 := by linarith [h2]
      rw [hr0] at h0
      nlinarith [h0, sq_nonneg (q.coeff 0)]
    · have hab : r.coeff 0 = q.coeff 0 := by
        have hr1 : r.coeff 1 = -q.coeff 1 := by linarith [h3]
        rw [hr1] at h1
        have h1' : 0 = q.coeff 1 * r.coeff 0 - q.coeff 1 * q.coeff 0 := by
          nlinarith [h1]
        have hzero : q.coeff 1 * (r.coeff 0 - q.coeff 0) = 0 := by
          nlinarith [h1']
        have : r.coeff 0 - q.coeff 0 = 0 :=
          (mul_eq_zero.mp hzero).resolve_left ha
        linarith
      have hsq : (q.coeff 0) ^ 2 = 12 ^ 2 := by
        rw [hab] at h0
        nlinarith [h0]
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hq0 | hq0
      · have hq1sq : (q.coeff 1) ^ 2 = 24 := by
          have hr1 : r.coeff 1 = -q.coeff 1 := by linarith [h3]
          rw [hr1, hab, hq0] at h2
          nlinarith [h2]
        exact no_rat_square_24 (q.coeff 1) hq1sq
      · have hr1 : r.coeff 1 = -q.coeff 1 := by linarith [h3]
        rw [hr1, hab, hq0] at h2
        nlinarith [h2, sq_nonneg (q.coeff 1)]

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
  have hmap :
      planeYPolynomial.map (Polynomial.evalRingHom (0 : ℚ)) =
        Polynomial.X ^ 4 + Polynomial.C (144 : ℚ) := by
    simp [planeYPolynomial, planeFirstPolynomial, planeSecondPolynomial,
      Polynomial.evalRingHom]
    ring_nf
    norm_num [← Polynomial.C_pow, ← Polynomial.C_mul]
  have hmon : planeYPolynomial.Monic := by
    let A : Polynomial (Polynomial ℚ) :=
      Polynomial.X ^ 2 - Polynomial.C planeFirstPolynomial -
        Polynomial.C planeSecondPolynomial
    let B : Polynomial (Polynomial ℚ) :=
      Polynomial.C (Polynomial.C (4 : ℚ) * planeFirstPolynomial * planeSecondPolynomial)
    have hBeq :
        Polynomial.C (Polynomial.C (4 : ℚ)) * Polynomial.C planeFirstPolynomial *
            Polynomial.C planeSecondPolynomial = B := by
      dsimp [B]
      rw [← Polynomial.C_mul, ← Polynomial.C_mul]
    have hAeq : A = Polynomial.X ^ 2 - Polynomial.C
        (planeFirstPolynomial + planeSecondPolynomial) := by
      dsimp [A]
      rw [Polynomial.C_add]
      ring
    have hA : A.Monic := by
      rw [hAeq]
      exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
    have hAdeg : A.degree = 2 := by
      rw [hAeq]
      exact Polynomial.degree_X_pow_sub_C (by norm_num) _
    have hA2deg : (A ^ 2).degree = 4 := by
      rw [Polynomial.degree_pow, hAdeg]
      norm_num
    have hBdeg : B.degree < (A ^ 2).degree := by
      have hB0 : B.degree ≤ 0 := by
        dsimp [B]
        exact Polynomial.degree_C_le
      rw [hA2deg]
      exact lt_of_le_of_lt hB0 (by norm_num)
    change (A ^ 2 -
      (Polynomial.C (Polynomial.C (4 : ℚ)) * Polynomial.C planeFirstPolynomial *
        Polynomial.C planeSecondPolynomial)).Monic
    rw [hBeq]
    exact (hA.pow 2).sub_of_left hBdeg
  exact Polynomial.Monic.irreducible_of_irreducible_map
    (Polynomial.evalRingHom (0 : ℚ)) planeYPolynomial hmon (by
      rw [hmap]
      exact quartic_plus_144_irreducible)

private def sourceBaseRelation : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C (1 : ℚ)) *
    (Polynomial.X - Polynomial.C (2 : ℚ)) *
    (Polynomial.X - Polynomial.C (3 : ℚ))

private def sourceSPolynomial : Polynomial (Polynomial ℚ) :=
  Polynomial.X ^ 2 - Polynomial.C sourceBaseRelation

private lemma sourceSPolynomial_isEisenstein :
    sourceSPolynomial.IsEisensteinAt
      (Ideal.span ({Polynomial.X - Polynomial.C (1 : ℚ)} : Set (Polynomial ℚ))) := by
  let P : Ideal (Polynomial ℚ) :=
    Ideal.span {Polynomial.X - Polynomial.C (1 : ℚ)}
  have hP : P.IsPrime := by
    exact Ideal.isPrime_span_singleton_of_prime (Polynomial.prime_X_sub_C (1 : ℚ))
  apply Polynomial.Monic.isEisensteinAt_of_mem_of_notMem
  · exact Polynomial.monic_X_pow_sub_C sourceBaseRelation (by norm_num)
  · exact hP.ne_top
  · intro n hn
    have hn' : n = 0 ∨ n = 1 := by
      have : n < 2 := by simpa [sourceSPolynomial] using hn
      omega
    rcases hn' with rfl | rfl
    · rw [Ideal.mem_span_singleton]
      refine ⟨-((Polynomial.X - Polynomial.C (2 : ℚ)) *
          (Polynomial.X - Polynomial.C (3 : ℚ))), ?_⟩
      simp [sourceSPolynomial, sourceBaseRelation]
      ring
    · simp [sourceSPolynomial, P]
  · intro h
    have h' : (Polynomial.X - Polynomial.C (1 : ℚ)) ^ 2 ∣
        -sourceBaseRelation := by
      change sourceSPolynomial.coeff 0 ∈
        (Ideal.span {Polynomial.X - Polynomial.C (1 : ℚ)}) ^ 2 at h
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
      simpa [sourceSPolynomial] using h
    rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff] at h'
    have h'' := h' 1 (by omega)
    simp only [Polynomial.neg_comp, Polynomial.mul_comp, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.C_comp] at h''
    have heq : sourceBaseRelation.comp (Polynomial.X + Polynomial.C (1 : ℚ)) =
        Polynomial.X ^ 3 - 3 * Polynomial.X ^ 2 + 2 * Polynomial.X := by
      simp [sourceBaseRelation, Polynomial.mul_comp, Polynomial.sub_comp]
      simp only [Polynomial.C_ofNat]
      ring
    rw [heq] at h''
    norm_num at h''

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
  let f : MvPolynomial (Fin 1) ℚ →+* Polynomial ℚ :=
    (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) :
      MvPolynomial (Fin 1) ℚ →+* Polynomial ℚ)
  have hfX : f (MvPolynomial.X (0 : Fin 1)) = Polynomial.X := by
    simp [f, MvPolynomial.uniqueAlgEquiv]
  have hfC (n : ℚ) : f (MvPolynomial.C n) = Polynomial.C n := by
    simp [f, MvPolynomial.uniqueAlgEquiv]
  have hrename :
      (MvPolynomial.finSuccEquiv ℚ 1)
          (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) sourceBaseRelationMv) =
        Polynomial.X ^ 2 - Polynomial.C
          ((MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (1 : ℚ)) *
            (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (2 : ℚ)) *
            (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (3 : ℚ))) := by
    have hzero :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.X (0 : Fin 2)) =
          Polynomial.X := by
      rw [MvPolynomial.finSuccEquiv_X_zero]
    have hone : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by decide
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by decide
    have hsucc :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.X (1 : Fin 2)) =
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
      rw [hone, MvPolynomial.finSuccEquiv_X_succ]
    have htwo :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (2 : ℚ)) =
          Polynomial.C (MvPolynomial.C (2 : ℚ)) := by
      rw [MvPolynomial.finSuccEquiv_apply]
      simp
    have honeC :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (1 : ℚ)) =
          Polynomial.C (MvPolynomial.C (1 : ℚ)) := by
      rw [MvPolynomial.finSuccEquiv_apply]
      simp
    have hthree :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (3 : ℚ)) =
          Polynomial.C (MvPolynomial.C (3 : ℚ)) := by
      rw [MvPolynomial.finSuccEquiv_apply]
      simp
    simp only [sourceBaseRelationMv, map_sub, map_mul, map_pow,
      MvPolynomial.rename_X, MvPolynomial.rename_C, hswap0, hswap1,
      hzero, hsucc, honeC, htwo, hthree]
  change Polynomial.map f
      ((MvPolynomial.finSuccEquiv ℚ 1)
        (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) sourceBaseRelationMv)) =
    sourceSPolynomial
  rw [hrename, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X]
  simp only [map_mul, map_sub, hfX, hfC]
  simp [sourceSPolynomial, sourceBaseRelation]

private def sourceBaseIdeal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {sourceBaseRelationMv}

private lemma sourceBaseIdeal_isPrime : sourceBaseIdeal.IsPrime := by
  have hi : Irreducible sourceSPolynomial := by
    apply Polynomial.IsEisensteinAt.irreducible
      sourceSPolynomial_isEisenstein
    · exact Ideal.isPrime_span_singleton_of_prime
        (Polynomial.prime_X_sub_C (1 : ℚ))
    · exact (Polynomial.monic_X_pow_sub_C sourceBaseRelation (by norm_num)).isPrimitive
    · simp [sourceSPolynomial]
  have hp : (Ideal.span {sourceSPolynomial} : Ideal (Polynomial (Polynomial ℚ))).IsPrime := by
    exact (Ideal.span_singleton_prime hi.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi)
  have hmap : Ideal.map (sourceBaseReindex : MvPolynomial (Fin 2) ℚ →+*
      Polynomial (Polynomial ℚ)) sourceBaseIdeal =
      Ideal.span {sourceSPolynomial} := by
    rw [sourceBaseIdeal, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({sourceBaseReindex sourceBaseRelationMv} :
      Set (Polynomial (Polynomial ℚ))) = Ideal.span {sourceSPolynomial}
    rw [sourceBaseReindex_relation]
  have hc := hp.comap (sourceBaseReindex : MvPolynomial (Fin 2) ℚ →+*
      Polynomial (Polynomial ℚ))
  have hcomap : Ideal.comap (sourceBaseReindex : MvPolynomial (Fin 2) ℚ →+*
      Polynomial (Polynomial ℚ)) (Ideal.span {sourceSPolynomial}) =
      sourceBaseIdeal := by
    rw [← hmap]
    rw [Ideal.comap_map_of_surjective (sourceBaseReindex :
      MvPolynomial (Fin 2) ℚ →+* Polynomial (Polynomial ℚ)) sourceBaseReindex.surjective]
    apply sup_eq_left.mpr
    intro x hx
    change sourceBaseReindex x = 0 at hx
    have hx' : sourceBaseReindex x = sourceBaseReindex 0 := by simpa using hx
    have : x = 0 := sourceBaseReindex.injective hx'
    simpa [this] using sourceBaseIdeal.zero_mem
  rw [hcomap] at hc
  exact hc

private lemma monic_span_isPrime_of_map_isPrime
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (g : Polynomial R) (hg : g.Monic)
    (hprime : (Ideal.span {g.map f} : Ideal (Polynomial S)).IsPrime) :
    (Ideal.span {g} : Ideal (Polynomial R)).IsPrime := by
  let F : Polynomial R →+* Polynomial S := Polynomial.mapRingHom f
  let P : Ideal (Polynomial S) := Ideal.span {g.map f}
  have hcomap : Ideal.comap F P = Ideal.span {g} := by
    apply le_antisymm
    · intro p hp
      change p.map f ∈ P at hp
      have hdiv : g.map f ∣ p.map f := (Ideal.mem_span_singleton.mp hp)
      have hmod : (p.map f) %ₘ (g.map f) = 0 :=
        (Polynomial.modByMonic_eq_zero_iff_dvd (hg.map f)).2 hdiv
      have hmapmod : (p %ₘ g).map f = 0 := by
        rw [Polynomial.map_modByMonic f hg]
        exact hmod
      have hmodzero : p %ₘ g = 0 := by
        apply Polynomial.map_injective f hf
        simpa using hmapmod
      rw [← Polynomial.modByMonic_add_div p g, hmodzero, zero_add]
      simpa [mul_comm] using
        (Ideal.span {g}).mul_mem_left (p /ₘ g)
          (Ideal.subset_span (Set.mem_singleton g))
    · apply Ideal.span_le.2
      intro p hp
      have hp' : p = g := Set.mem_singleton_iff.mp hp
      rw [hp']
      change F g ∈ P
      exact Ideal.subset_span (Set.mem_singleton (g.map f))
  rw [← hcomap]
  exact hprime.comap F

private def planeReindex : planePolynomialRing ≃+* Polynomial (Polynomial ℚ) :=
  ((MvPolynomial.renameEquiv ℚ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv ℚ 1).toRingEquiv).trans
      (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingEquiv)

private lemma planeReindex_relation :
    planeReindex planeRelation = planeYPolynomial := by
  let f : MvPolynomial (Fin 1) ℚ →+* Polynomial ℚ :=
    (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) :
      MvPolynomial (Fin 1) ℚ →+* Polynomial ℚ)
  have hfX : f (MvPolynomial.X (0 : Fin 1)) = Polynomial.X := by
    simp [f, MvPolynomial.uniqueAlgEquiv]
  have hfC (n : ℚ) : f (MvPolynomial.C n) = Polynomial.C n := by
    simp [f, MvPolynomial.uniqueAlgEquiv]
  have hrename :
      (MvPolynomial.finSuccEquiv ℚ 1)
          (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) planeRelation) =
        (Polynomial.X ^ 2 -
            Polynomial.C ((MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (1 : ℚ)) *
              (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (2 : ℚ)) *
              (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (3 : ℚ))) -
            Polynomial.C ((MvPolynomial.X (0 : Fin 1) + MvPolynomial.C (1 : ℚ)) *
              (MvPolynomial.X (0 : Fin 1) + MvPolynomial.C (2 : ℚ)) *
              (MvPolynomial.X (0 : Fin 1) + MvPolynomial.C (3 : ℚ)))) ^ 2 -
          Polynomial.C (MvPolynomial.C (4 : ℚ)) *
            Polynomial.C ((MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (1 : ℚ)) *
              (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (2 : ℚ)) *
              (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (3 : ℚ))) *
            Polynomial.C ((MvPolynomial.X (0 : Fin 1) + MvPolynomial.C (1 : ℚ)) *
              (MvPolynomial.X (0 : Fin 1) + MvPolynomial.C (2 : ℚ)) *
              (MvPolynomial.X (0 : Fin 1) + MvPolynomial.C (3 : ℚ))) := by
    have hzero :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.X (0 : Fin 2)) =
          Polynomial.X := by
      rw [MvPolynomial.finSuccEquiv_X_zero]
    have hone : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by decide
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by decide
    have hsucc :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.X (1 : Fin 2)) =
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
      rw [hone, MvPolynomial.finSuccEquiv_X_succ]
    have htwo :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (2 : ℚ)) =
          Polynomial.C (MvPolynomial.C (2 : ℚ)) := by
      rw [MvPolynomial.finSuccEquiv_apply]
      simp
    have honeC :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (1 : ℚ)) =
          Polynomial.C (MvPolynomial.C (1 : ℚ)) := by
      rw [MvPolynomial.finSuccEquiv_apply]
      simp
    have hthree :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (3 : ℚ)) =
          Polynomial.C (MvPolynomial.C (3 : ℚ)) := by
      rw [MvPolynomial.finSuccEquiv_apply]
      simp
    have hfour :
        (MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (4 : ℚ)) =
          Polynomial.C (MvPolynomial.C (4 : ℚ)) := by
      rw [MvPolynomial.finSuccEquiv_apply]
      simp
    have hfour' :
        (MvPolynomial.finSuccEquiv ℚ 1)
            (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
              (4 : MvPolynomial (Fin 2) ℚ)) =
          Polynomial.C (MvPolynomial.C (4 : ℚ)) := by
      rw [show (4 : MvPolynomial (Fin 2) ℚ) = MvPolynomial.C (4 : ℚ) by
        exact (map_natCast (MvPolynomial.C : ℚ →+* MvPolynomial (Fin 2) ℚ) 4).symm,
        MvPolynomial.rename_C, hfour]
    simp only [planeRelation, planeFirstCubic, planeSecondCubic,
      map_sub, map_add, map_mul, map_pow, MvPolynomial.rename_X,
      MvPolynomial.rename_C, hswap0, hswap1, hzero, hsucc, honeC, htwo,
      hthree, hfour, hfour']
  change Polynomial.map f
      ((MvPolynomial.finSuccEquiv ℚ 1)
        (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) planeRelation)) =
    planeYPolynomial
  rw [hrename]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X, hfX, hfC]
  simp [f, MvPolynomial.uniqueAlgEquiv, planeYPolynomial,
    planeFirstPolynomial, planeSecondPolynomial]

private lemma planeYPolynomial_span_isPrime :
    (Ideal.span {planeYPolynomial} : Ideal (Polynomial (Polynomial ℚ))).IsPrime := by
  let K := FractionRing (Polynomial ℚ)
  let f : Polynomial ℚ →+* K := algebraMap (Polynomial ℚ) K
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have hmon : planeYPolynomial.Monic := by
    let A : Polynomial (Polynomial ℚ) :=
      Polynomial.X ^ 2 - Polynomial.C planeFirstPolynomial -
        Polynomial.C planeSecondPolynomial
    let B : Polynomial (Polynomial ℚ) :=
      Polynomial.C (Polynomial.C (4 : ℚ) * planeFirstPolynomial * planeSecondPolynomial)
    have hBeq :
        Polynomial.C (Polynomial.C (4 : ℚ)) * Polynomial.C planeFirstPolynomial *
            Polynomial.C planeSecondPolynomial = B := by
      dsimp [B]
      rw [← Polynomial.C_mul, ← Polynomial.C_mul]
    have hAeq : A = Polynomial.X ^ 2 - Polynomial.C
        (planeFirstPolynomial + planeSecondPolynomial) := by
      dsimp [A]
      rw [Polynomial.C_add]
      ring
    have hA : A.Monic := by
      rw [hAeq]
      exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
    have hAdeg : A.degree = 2 := by
      rw [hAeq]
      exact Polynomial.degree_X_pow_sub_C (by norm_num) _
    have hA2deg : (A ^ 2).degree = 4 := by
      rw [Polynomial.degree_pow, hAdeg]
      norm_num
    have hBdeg : B.degree < (A ^ 2).degree := by
      have hB0 : B.degree ≤ 0 := by
        dsimp [B]
        exact Polynomial.degree_C_le
      rw [hA2deg]
      exact lt_of_le_of_lt hB0 (by norm_num)
    change (A ^ 2 -
      (Polynomial.C (Polynomial.C (4 : ℚ)) * Polynomial.C planeFirstPolynomial *
        Polynomial.C planeSecondPolynomial)).Monic
    rw [hBeq]
    exact (hA.pow 2).sub_of_left hBdeg
  have hi : Irreducible (planeYPolynomial.map f) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hmon).1
      planeYPolynomial_irreducible
  have hp : (Ideal.span {planeYPolynomial.map f} : Ideal (Polynomial K)).IsPrime := by
    exact (Ideal.span_singleton_prime hi.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi)
  exact monic_span_isPrime_of_map_isPrime f hf planeYPolynomial
    hmon hp

private lemma planeIdeal_isPrime :
    (Ideal.span {planeRelation} : Ideal planePolynomialRing).IsPrime := by
  have hp := planeYPolynomial_span_isPrime
  have hmap : Ideal.map (planeReindex : planePolynomialRing →+*
      Polynomial (Polynomial ℚ)) (Ideal.span {planeRelation}) =
      Ideal.span {planeYPolynomial} := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span ({planeReindex planeRelation} :
      Set (Polynomial (Polynomial ℚ))) = Ideal.span {planeYPolynomial}
    rw [planeReindex_relation]
  have hc := hp.comap (planeReindex : planePolynomialRing →+*
      Polynomial (Polynomial ℚ))
  have hcomap : Ideal.comap (planeReindex : planePolynomialRing →+*
      Polynomial (Polynomial ℚ)) (Ideal.span {planeYPolynomial}) =
      Ideal.span {planeRelation} := by
    rw [← hmap]
    rw [Ideal.comap_map_of_surjective (planeReindex : planePolynomialRing →+*
      Polynomial (Polynomial ℚ)) planeReindex.surjective]
    apply sup_eq_left.mpr
    intro x hx
    change planeReindex x = 0 at hx
    have hx' : planeReindex x = planeReindex 0 := by simpa using hx
    have : x = 0 := planeReindex.injective hx'
    simpa [this] using (Ideal.span {planeRelation}).zero_mem
  rw [hcomap] at hc
  exact hc

private lemma sourceFullReindex_tRelation :
    sourceFullReindex sourceTRelation = sourceTPolynomial := by
  let f : MvPolynomial (Fin 2) ℚ →+* Polynomial (Polynomial ℚ) :=
    (Polynomial.mapRingHom
      (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) :
        MvPolynomial (Fin 1) ℚ →+* Polynomial ℚ)).comp
      (MvPolynomial.finSuccEquiv ℚ 1)
  have hf0 : f (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
    change Polynomial.map (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingHom
        ((MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.X (0 : Fin 2))) = _
    rw [MvPolynomial.finSuccEquiv_X_zero]
    simp [MvPolynomial.uniqueAlgEquiv]
  have hf1 : f (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (Polynomial.X) := by
    change Polynomial.map (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingHom
        ((MvPolynomial.finSuccEquiv ℚ 1)
          (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp [MvPolynomial.uniqueAlgEquiv]
  change Polynomial.map f
      ((MvPolynomial.finSuccEquiv ℚ 2)
        (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 2) sourceTRelation)) =
    sourceTPolynomial
  have hswap0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have hswap1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have hswap2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  have hfin2 :
      Polynomial.map f (Fin.cases Polynomial.X
        (fun k => Polynomial.C (MvPolynomial.X k)) 2) =
      Polynomial.C (Polynomial.C Polynomial.X) := by
    change Polynomial.map f (Polynomial.C (MvPolynomial.X (1 : Fin 2))) = _
    rw [Polynomial.map_C, hf1]
  have hC2 : f (MvPolynomial.C (2 : ℚ)) =
      Polynomial.C (Polynomial.C (2 : ℚ)) := by
    change Polynomial.map (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingHom
        ((MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (2 : ℚ))) = _
    rw [MvPolynomial.finSuccEquiv_apply]
    simp [MvPolynomial.uniqueAlgEquiv]
  have hC3 : f (MvPolynomial.C (3 : ℚ)) =
      Polynomial.C (Polynomial.C (3 : ℚ)) := by
    change Polynomial.map (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingHom
        ((MvPolynomial.finSuccEquiv ℚ 1) (MvPolynomial.C (3 : ℚ))) = _
    rw [MvPolynomial.finSuccEquiv_apply]
    simp [MvPolynomial.uniqueAlgEquiv]
  simp only [sourceTRelation, MvPolynomial.rename_X, MvPolynomial.rename_C,
    hswap0, hswap1, hswap2, map_sub, map_mul, map_pow,
    MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ,
    MvPolynomial.finSuccEquiv_apply, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, hf0, hf1, hfin2, hC2, hC3]
  have hfin2' := hfin2
  have hC2' := hC2
  have hC3' := hC3
  dsimp [f] at hfin2' hC2' hC3'
  simp only [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, hfin2', hC2', hC3']
  simp [map_mul, map_sub, map_pow, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
    hfin2', hC2', hC3', sourceSecondRelation, sourceTPolynomial, f,
    MvPolynomial.finSuccEquiv_apply, MvPolynomial.uniqueAlgEquiv]

private lemma sourceSPolynomial_span_isPrime :
    (Ideal.span {sourceSPolynomial} :
      Ideal (Polynomial (Polynomial ℚ))).IsPrime := by
  have hmap : Ideal.map (sourceBaseReindex :
      MvPolynomial (Fin 2) ℚ →+* Polynomial (Polynomial ℚ)) sourceBaseIdeal =
      Ideal.span {sourceSPolynomial} := by
    rw [sourceBaseIdeal, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({sourceBaseReindex sourceBaseRelationMv} :
      Set (Polynomial (Polynomial ℚ))) = Ideal.span {sourceSPolynomial}
    rw [sourceBaseReindex_relation]
  rw [← hmap]
  letI : sourceBaseIdeal.IsPrime := sourceBaseIdeal_isPrime
  exact Ideal.map_isPrime_of_surjective sourceBaseReindex.surjective (by simp)

/-! ## Exercise `find-fraction-field` -/

/- The source calls the displayed quotient a domain.  Recording that fact as
   an instance makes Mathlib's canonical `FractionRing` a field here. -/
instance sourceRing_isDomain : IsDomain sourceRing := by
  sorry

/- The explicit plane curve is a domain, as required by the requested form
   `ℚ[x, y]/(f)`. -/
instance planeCurveRing_isDomain : IsDomain planeCurveRing := by
  rw [Ideal.Quotient.isDomain_iff_prime]
  exact planeIdeal_isPrime

/-- The source quotient has the same fraction field as the displayed plane
curve with `y = s + t`. -/
theorem source_fraction_field_equiv_plane_curve :
    Nonempty (FractionRing sourceRing ≃+* FractionRing planeCurveRing) := by
  sorry

end

end Formalization.Books.Exercises.Unit19
