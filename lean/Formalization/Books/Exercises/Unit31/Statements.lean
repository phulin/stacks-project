import Formalization.Books.Exercises.Unit31.Core

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Prime
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Exercises, Chapter 31: Regular functions

The declarations below follow the five numbered exercises in the source.  The
proofs are deferred to the proving stage; the named examples and polynomial
data are retained so that the theorem interfaces expose the source's actual
objects.
-/

namespace Formalization.Books.Exercises.Unit31

open Set

universe u

noncomputable section

/-! ## Exercise `extra-function` -/

/-- The equation `t² = s⁵ + 8` in the two-variable complex affine space. -/
def affineCurveEquation : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X (1 : Fin 2) ^ 2 -
    (MvPolynomial.X (0 : Fin 2) ^ 5 + MvPolynomial.C (8 : ℂ))

/-- The affine curve cut out by `affineCurveEquation`. -/
def affineCurve : Set (Fin 2 → ℂ) :=
  MvPolynomial.zeroLocus ℂ (Ideal.span {affineCurveEquation})

/-- The point `(1, 3)` on `affineCurve`. -/
def affineCurvePoint : Fin 2 → ℂ := ![(1 : ℂ), 3]

/-- The punctured curve from the first exercise. -/
def affineCurvePunctured : Set (Fin 2 → ℂ) :=
  affineCurve \ {affineCurvePoint}

/-- The polynomial `s - 1`. -/
def affineCurveSMinusOne : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (1 : ℂ)

/-- The polynomial `t + 3`. -/
def affineCurveTPlusThree : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X (1 : Fin 2) + MvPolynomial.C (3 : ℂ)

/-- The polynomial `t - 3`. -/
def affineCurveTMinusThree : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (3 : ℂ)

/-- The quotient polynomial `(s⁵ - 1)/(s - 1)`. -/
def affineCurveQuotient : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X (0 : Fin 2) ^ 4 + MvPolynomial.X (0 : Fin 2) ^ 3 +
    MvPolynomial.X (0 : Fin 2) ^ 2 + MvPolynomial.X (0 : Fin 2) + 1

/-- The extra regular function, written using the two local expressions
`(t + 3)/(s - 1)` and `affineCurveQuotient/(t - 3)`. -/
def affineCurveExtraFunction (z : ↥affineCurvePunctured) : ℂ :=
  if MvPolynomial.aeval z.1 affineCurveSMinusOne ≠ 0 then
    MvPolynomial.aeval z.1 affineCurveTPlusThree /
      MvPolynomial.aeval z.1 affineCurveSMinusOne
  else
      MvPolynomial.aeval z.1 affineCurveQuotient /
      MvPolynomial.aeval z.1 affineCurveTMinusThree

private instance affine_curve_fraction_ring_isFractionRing :
    IsFractionRing (MvPolynomial (Fin 1) ℂ)
      (FractionRing (MvPolynomial (Fin 1) ℂ)) := by
  change IsLocalization
    (nonZeroDivisors (MvPolynomial (Fin 1) ℂ))
    (Localization (nonZeroDivisors (MvPolynomial (Fin 1) ℂ)))
  exact Localization.isLocalization

private theorem affine_curve_equation_prime : Prime affineCurveEquation := by
  let A := MvPolynomial (Fin 1) ℂ
  let K := FractionRing A
  let q : A := MvPolynomial.X 0 ^ 2 - MvPolynomial.C 8
  have hqns : ∀ b : K, b ^ 5 ≠ algebraMap A K q := by
    intro b hb
    have hbint : IsIntegral A (b ^ 5) := by
      rw [hb]
      exact isIntegral_algebraMap
    obtain ⟨a, ha⟩ :=
      IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
        (R := A) (x := b) (by norm_num) hbint
    have haq : a ^ 5 = q := by
      apply (IsFractionRing.injective A K)
      rw [map_pow, ha, hb]
    let e := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
    have haq' : (e a : Polynomial ℂ) ^ 5 = e q := by
      calc
        (e a : Polynomial ℂ) ^ 5 = e (a ^ 5) := (map_pow e a 5).symm
        _ = e q := congrArg (fun x : A => (e x : Polynomial ℂ)) haq
    have hqdeg' : (e q : Polynomial ℂ).natDegree = 2 := by
      change
        ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1))
          (MvPolynomial.X 0 ^ 2 - MvPolynomial.C 8) : Polynomial ℂ).natDegree = 2
      simp [MvPolynomial.uniqueAlgEquiv]
    have hq0' : (e q : Polynomial ℂ) ≠ 0 := by
      intro hq0
      rw [hq0] at hqdeg'
      simp at hqdeg'
    have ha0' : (e a : Polynomial ℂ) ≠ 0 := by
      intro ha0
      apply hq0'
      rw [← haq', ha0]
      simp
    have hd := congrArg Polynomial.natDegree haq'
    rw [Polynomial.natDegree_pow, hqdeg'] at hd
    omega
  have hpmap : Irreducible
      ((Polynomial.X ^ 5 - Polynomial.C q).map (algebraMap A K)) := by
    simpa using
      (X_pow_sub_C_irreducible_of_prime (K := K) (p := 5) (by decide)
        (a := algebraMap A K q) hqns)
  have hp : Irreducible (Polynomial.X ^ 5 - Polynomial.C q) := by
    apply Polynomial.Monic.irreducible_of_irreducible_map (algebraMap A K)
      (Polynomial.X ^ 5 - Polynomial.C q)
        (Polynomial.monic_X_pow_sub_C q (by norm_num))
    exact hpmap
  have hp' : Prime (Polynomial.X ^ 5 - Polynomial.C q) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  have hpe : Prime (MvPolynomial.finSuccEquiv ℂ 1 affineCurveEquation) := by
    convert Prime.neg hp' using 1
    have h1 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by rfl
    simp only [affineCurveEquation, q, h1, map_sub, map_add, map_pow,
      MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquiv_X_zero]
    have hC :
        MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.C (8 : ℂ)) =
          Polynomial.C (MvPolynomial.C (8 : ℂ)) := by
      exact (MvPolynomial.finSuccEquiv ℂ 1).commutes 8
    rw [hC]
    simp
    ring
  exact (MulEquiv.prime_iff (p := affineCurveEquation)
    (MvPolynomial.finSuccEquiv ℂ 1).toMulEquiv).mp hpe

/-- The displayed point lies on the displayed curve. -/
theorem affine_curve_point_mem : affineCurvePoint ∈ affineCurve := by
  simp only [affineCurve, MvPolynomial.zeroLocus_span, affineCurveEquation, affineCurvePoint]
  norm_num

/-- The displayed equation defines an affine variety over `ℂ`. -/
theorem affine_curve_is_affine_variety :
    IsAffineVariety ℂ 2 affineCurve := by
  refine ⟨Ideal.span {affineCurveEquation}, ?_, rfl⟩
  exact (Ideal.span_singleton_prime affine_curve_equation_prime.ne_zero).mpr
    affine_curve_equation_prime

/-- The local quotient construction is a regular function on the punctured
curve. -/
theorem affine_curve_extra_function_is_regular :
    IsRegularFunction affineCurvePunctured affineCurveExtraFunction := by
  intro z
  by_cases hS : MvPolynomial.aeval z.1 affineCurveSMinusOne ≠ 0
  · let U := affineCurvePunctured \
      MvPolynomial.zeroLocus ℂ (Ideal.span {affineCurveSMinusOne})
    refine ⟨U, ?_, ?_, ?_, affineCurveTPlusThree, affineCurveSMinusOne, ?_, ?_⟩
    · refine ⟨z.2, ?_⟩
      intro hz
      apply hS
      exact (MvPolynomial.mem_zeroLocus_iff.mp hz) affineCurveSMinusOne
        (Ideal.subset_span (by simp))
    · intro u hu
      exact hu.1
    · exact ⟨Ideal.span {affineCurveSMinusOne}, rfl⟩
    · intro u hu hu0
      apply hu.2
      have hspan : Ideal.span {affineCurveSMinusOne} ≤
          RingHom.ker (MvPolynomial.aeval u).toRingHom := by
        refine Ideal.span_le.2 ?_
        intro p hp
        simpa [Set.mem_singleton_iff.mp hp] using hu0
      exact MvPolynomial.mem_zeroLocus_iff.mpr (fun p hp => hspan hp)
    · intro u hu
      have huS : MvPolynomial.aeval u affineCurveSMinusOne ≠ 0 := by
        intro huS0
        apply hu.2
        have hspan : Ideal.span {affineCurveSMinusOne} ≤
            RingHom.ker (MvPolynomial.aeval u).toRingHom := by
          refine Ideal.span_le.2 ?_
          intro p hp
          simpa [Set.mem_singleton_iff.mp hp] using huS0
        exact MvPolynomial.mem_zeroLocus_iff.mpr (fun p hp => hspan hp)
      simp only [affineCurveExtraFunction, if_pos huS]
  · let U := affineCurvePunctured \
      MvPolynomial.zeroLocus ℂ (Ideal.span {affineCurveTMinusThree})
    refine ⟨U, ?_, ?_, ?_, affineCurveQuotient, affineCurveTMinusThree, ?_, ?_⟩
    · refine ⟨z.2, ?_⟩
      intro hz
      have hzT : MvPolynomial.aeval z.1 affineCurveTMinusThree ≠ 0 := by
        intro hzT0
        have hscoord : z.1 0 = 1 := by
          exact sub_eq_zero.mp (by
            simpa [affineCurveSMinusOne] using (not_ne_iff.mp hS))
        have htcoord : z.1 1 = 3 := by
          exact sub_eq_zero.mp (by
            simpa [affineCurveTMinusThree] using hzT0)
        apply z.2.2
        simp only [Set.mem_singleton_iff]
        funext i
        fin_cases i <;> simp [affineCurvePoint, hscoord, htcoord]
      exact hzT ((MvPolynomial.mem_zeroLocus_iff.mp hz) affineCurveTMinusThree
        (Ideal.subset_span (by simp)))
    · intro u hu
      exact hu.1
    · exact ⟨Ideal.span {affineCurveTMinusThree}, rfl⟩
    · intro u hu hu0
      apply hu.2
      have hspan : Ideal.span {affineCurveTMinusThree} ≤
          RingHom.ker (MvPolynomial.aeval u).toRingHom := by
        refine Ideal.span_le.2 ?_
        intro p hp
        simpa [Set.mem_singleton_iff.mp hp] using hu0
      exact MvPolynomial.mem_zeroLocus_iff.mpr (fun p hp => hspan hp)
    · intro u hu
      have huT : MvPolynomial.aeval u affineCurveTMinusThree ≠ 0 := by
        intro huT0
        apply hu.2
        have hspan : Ideal.span {affineCurveTMinusThree} ≤
            RingHom.ker (MvPolynomial.aeval u).toRingHom := by
          refine Ideal.span_le.2 ?_
          intro p hp
          simpa [Set.mem_singleton_iff.mp hp] using huT0
        exact MvPolynomial.mem_zeroLocus_iff.mpr (fun p hp => hspan hp)
      by_cases huS : MvPolynomial.aeval u affineCurveSMinusOne ≠ 0
      · simp only [affineCurveExtraFunction, if_pos huS]
        have hcurve0 := (MvPolynomial.mem_zeroLocus_iff.mp hu.1.1)
          affineCurveEquation (Ideal.subset_span (by simp))
        have hcurve : (u 1) ^ 2 - ((u 0) ^ 5 + 8) = 0 := by
          simpa [affineCurveEquation] using hcurve0
        have hrel :
            MvPolynomial.aeval u affineCurveTPlusThree *
                MvPolynomial.aeval u affineCurveTMinusThree =
              MvPolynomial.aeval u affineCurveSMinusOne *
                MvPolynomial.aeval u affineCurveQuotient := by
          calc
            MvPolynomial.aeval u affineCurveTPlusThree *
                MvPolynomial.aeval u affineCurveTMinusThree =
                (u 1 + 3) * (u 1 - 3) := by
                  simp [affineCurveTPlusThree, affineCurveTMinusThree]
            _ = (u 1) ^ 2 - 9 := by ring
            _ = (u 0) ^ 5 - 1 := by linear_combination hcurve
            _ = (u 0 - 1) *
                ((u 0) ^ 4 + (u 0) ^ 3 + (u 0) ^ 2 + u 0 + 1) := by ring
            _ = MvPolynomial.aeval u affineCurveSMinusOne *
                MvPolynomial.aeval u affineCurveQuotient := by
                  simp [affineCurveSMinusOne, affineCurveQuotient]
        field_simp [huS, huT]
        simpa [mul_comm] using hrel
      · simp only [affineCurveExtraFunction, if_neg huS]

/-- The extra function is not induced by an ambient polynomial. -/
theorem affine_curve_extra_function_not_polynomial :
    ¬ IsPolynomialRestriction affineCurvePunctured affineCurveExtraFunction := by
  rintro ⟨f, hf⟩
  let q := affineCurveSMinusOne * f - affineCurveTPlusThree
  have hq_punct : ∀ z : affineCurvePunctured,
      MvPolynomial.aeval z.1 q = 0 := by
    intro z
    by_cases hS : MvPolynomial.aeval z.1 affineCurveSMinusOne ≠ 0
    · have hz := hf z
      simp only [affineCurveExtraFunction, if_pos hS] at hz
      simp only [q, map_sub, map_mul]
      field_simp [hS] at hz
      rw [hz]
      ring
    · have hscoord : z.1 0 = 1 := by
        exact sub_eq_zero.mp (by
          simpa [affineCurveSMinusOne] using (not_ne_iff.mp hS))
      have hcurve0 := (MvPolynomial.mem_zeroLocus_iff.mp z.2.1)
        affineCurveEquation (Ideal.subset_span (by simp))
      have hcurve : (z.1 1) ^ 2 - ((z.1 0) ^ 5 + 8) = 0 := by
        simpa [affineCurveEquation] using hcurve0
      norm_num [hscoord] at hcurve
      have hfactor : (z.1 1 - 3) * (z.1 1 + 3) = 0 := by
        calc
          (z.1 1 - 3) * (z.1 1 + 3) = (z.1 1) ^ 2 - 9 := by ring
          _ = 0 := by simpa [hscoord] using hcurve
      have htcoord : z.1 1 = -3 := by
        rcases mul_eq_zero.mp hfactor with ht | ht
        · have ht' : z.1 1 = 3 := sub_eq_zero.mp ht
          exfalso
          apply z.2.2
          simp only [Set.mem_singleton_iff]
          funext i
          obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
          · simpa [affineCurvePoint] using hscoord
          · have hj : j = 0 := Subsingleton.elim _ _
            subst j
            change z.1 1 = 3
            exact ht'
        · exact (eq_neg_iff_add_eq_zero).2 ht
      simp [q, affineCurveSMinusOne, affineCurveTPlusThree, hscoord, htcoord]
  have hprod_mem : affineCurveSMinusOne * q ∈
      MvPolynomial.vanishingIdeal ℂ affineCurve := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    by_cases hxp : x = affineCurvePoint
    · subst x
      rw [map_mul]
      simp [affineCurveSMinusOne, affineCurvePoint]
    · have hxpunct : x ∈ affineCurvePunctured := ⟨hx, hxp⟩
      have hq := hq_punct ⟨x, hxpunct⟩
      rw [map_mul, hq, mul_zero]
  let p := Ideal.span {affineCurveEquation}
  have hp : p.IsPrime := by
    dsimp [p]
    exact (Ideal.span_singleton_prime affine_curve_equation_prime.ne_zero).mpr
      affine_curve_equation_prime
  have hprod_p : affineCurveSMinusOne * q ∈ p := by
    have hprod_rad : affineCurveSMinusOne * q ∈ p.radical := by
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)
        (k := ℂ) p]
      simpa [affineCurve, p] using hprod_mem
    simpa [hp.radical] using hprod_rad
  rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hp).mp hprod_p with hS_mem | hq_mem
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (n := 2) (8 : ℂ) (by norm_num)
    let y : Fin 2 → ℂ := ![(0 : ℂ), t]
    have hy : y ∈ affineCurve := by
      simp [affineCurve, MvPolynomial.zeroLocus_span, affineCurveEquation, y, ht]
    have hyS := (MvPolynomial.mem_zeroLocus_iff.mp hy)
      affineCurveSMinusOne hS_mem
    norm_num [affineCurveSMinusOne, y] at hyS
  · have hxq := (MvPolynomial.mem_zeroLocus_iff.mp affine_curve_point_mem)
      q hq_mem
    simp [q, affineCurveSMinusOne, affineCurveTPlusThree, affineCurvePoint] at hxq

/-- There is a regular function on the punctured curve which is not the
restriction of a polynomial in the ambient coordinates. -/
theorem extra_function_on_affine_curve :
    ∃ φ : affineCurvePunctured → ℂ,
      IsRegularFunction affineCurvePunctured φ ∧
        ¬ IsPolynomialRestriction affineCurvePunctured φ := by
  exact ⟨affineCurveExtraFunction,
    affine_curve_extra_function_is_regular,
    affine_curve_extra_function_not_polynomial⟩

/-! ## Exercise `no-extra-function` -/

private lemma cofinite_aeval_eq_zero
    {n : ℕ} (hn : 0 < n) (E : Set (Fin n → ℂ)) (hE : E.Finite)
    {p : MvPolynomial (Fin n) ℂ}
    (hp : ∀ x, x ∉ E → MvPolynomial.aeval x p = 0) : p = 0 := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  let S : Fin n → Set ℂ := fun i =>
    if i = i₀ then (E.image (fun x => x i₀))ᶜ else Set.univ
  have hS : ∀ i, (S i).Infinite := by
    intro i
    by_cases hi : i = i₀
    · subst i
      simpa [S] using (hE.image (fun x => x i₀)).infinite_compl
    · simpa [S, hi] using (Set.infinite_univ : (Set.univ : Set ℂ).Infinite)
  apply MvPolynomial.funext_set S hS
  intro x hx
  have hxE : x ∉ E := by
    intro hxE
    have hxi : x i₀ ∈ E.image (fun y => y i₀) := ⟨x, hxE, rfl⟩
    have hxi' : x i₀ ∉ E.image (fun y => y i₀) := by
      simpa [S] using hx i₀
    exact hxi' hxi
  simpa [MvPolynomial.aeval_def] using hp x hxE

private lemma exists_aeval_ne_zero_of_finite_complement
    {n : ℕ} (hn : 0 < n) (E : Set (Fin n → ℂ)) (hE : E.Finite)
    {p q : MvPolynomial (Fin n) ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ x, x ∉ E ∧ MvPolynomial.aeval x p ≠ 0 ∧
      MvPolynomial.aeval x q ≠ 0 := by
  classical
  by_contra h
  apply mul_ne_zero hp hq
  apply cofinite_aeval_eq_zero hn E hE
  intro x hxE
  by_cases hpx : MvPolynomial.aeval x p = 0
  · rw [map_mul, hpx, zero_mul]
  by_cases hqx : MvPolynomial.aeval x q = 0
  · rw [map_mul, hqx, mul_zero]
  exact False.elim (h ⟨x, hxE, hpx, hqx⟩)

private lemma exists_aeval_ne_zero_of_finite_complement_single
    {n : ℕ} (hn : 0 < n) (E : Set (Fin n → ℂ)) (hE : E.Finite)
    {p : MvPolynomial (Fin n) ℂ} (hp : p ≠ 0) :
    ∃ x, x ∉ E ∧ MvPolynomial.aeval x p ≠ 0 := by
  obtain ⟨x, hxE, hpx, _⟩ :=
    exists_aeval_ne_zero_of_finite_complement hn E hE hp (one_ne_zero :
      (1 : MvPolynomial (Fin n) ℂ) ≠ 0)
  exact ⟨x, hxE, hpx⟩

private lemma exists_aeval_eq_zero_of_not_isUnit
    {n : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ≠ 0)
    (hpn : ¬IsUnit p) : ∃ x : Fin n → ℂ, MvPolynomial.aeval x p = 0 := by
  obtain ⟨M, hM, hMmax⟩ :=
    Ideal.exists_le_maximal (Ideal.span {p}) (Ideal.span_singleton_ne_top hpn)
  obtain ⟨x, hx⟩ :=
    MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x, ?_⟩
  have hpx : p ∈ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin n → ℂ)) := by
    rw [← hx]
    exact hMmax (Ideal.subset_span (by simp))
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp hpx

private lemma aeval_eval_C_eq_zero_of_isRoot_map
    {m : ℕ} {F : Polynomial (MvPolynomial (Fin m) ℂ)}
    (y : Fin m → ℂ) (r : ℂ)
    (hr : (F.map (MvPolynomial.aeval y).toRingHom).IsRoot r) :
    MvPolynomial.aeval y (Polynomial.eval (MvPolynomial.C r) F) = 0 := by
  have hrootQ : Polynomial.aeval r (F.map (MvPolynomial.aeval y).toRingHom) = 0 := by
    simpa [Polynomial.IsRoot.def] using hr
  have hrootQr : Polynomial.eval r (F.map (MvPolynomial.aeval y).toRingHom) = 0 := by
    simpa [Polynomial.aeval_def] using hrootQ
  have hrootQ' : Polynomial.eval₂ (MvPolynomial.aeval y).toRingHom r F = 0 := by
    simpa [Polynomial.eval_map] using hrootQr
  calc
    MvPolynomial.aeval y (Polynomial.eval (MvPolynomial.C r) F) =
        Polynomial.eval₂ (MvPolynomial.aeval y).toRingHom
          (MvPolynomial.aeval y (MvPolynomial.C r)) F := by
      exact (Polynomial.eval₂_at_apply
        (p := F) (MvPolynomial.aeval y).toRingHom
        (MvPolynomial.C r)).symm
    _ = Polynomial.eval₂ (MvPolynomial.aeval y).toRingHom r F := by simp
    _ = 0 := hrootQ'

private lemma aeval_finSucc_eq_zero_of_eval_C_eq_zero
    {m : ℕ} {p : MvPolynomial (Fin (m + 1)) ℂ}
    (y : Fin m → ℂ) (r : ℂ)
    (hroot : MvPolynomial.aeval y
      (Polynomial.eval (MvPolynomial.C r) (MvPolynomial.finSuccEquiv ℂ m p)) = 0) :
    MvPolynomial.aeval (Fin.cases r y) p = 0 := by
  have hroot'' := MvPolynomial.eval_polynomial_eval_finSuccEquiv
    (R := ℂ) (x := y) p (MvPolynomial.C r)
  have hcases :
      (Fin.cases (MvPolynomial.eval y (MvPolynomial.C r)) y :
        Fin (m + 1) → ℂ) = Fin.cases r y := by
    funext i
    simp
  rw [hcases] at hroot''
  have hroot'e : MvPolynomial.eval y
      (Polynomial.eval (MvPolynomial.C r) (MvPolynomial.finSuccEquiv ℂ m p)) = 0 := by
    simpa [MvPolynomial.aeval_def] using hroot
  have hroot_eval : MvPolynomial.eval (Fin.cases r y) p = 0 :=
    (hroot'e.symm.trans hroot'').symm
  simpa [MvPolynomial.aeval_def] using hroot_eval

private lemma exists_root_of_map_of_positive_degree
    {m : ℕ} {F : Polynomial (MvPolynomial (Fin m) ℂ)}
    (y : Fin m → ℂ) (hdeg : 0 < F.natDegree)
    (hly : MvPolynomial.aeval y F.leadingCoeff ≠ 0) :
    ∃ r, (F.map (MvPolynomial.aeval y).toRingHom).IsRoot r := by
  let Q := F.map (MvPolynomial.aeval y).toRingHom
  have hQdeg : Q.natDegree = F.natDegree := by
    dsimp [Q]
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
    simpa using hly
  obtain ⟨r, hr⟩ :=
    IsAlgClosed.exists_root Q
      (Polynomial.degree_ne_of_natDegree_ne (by
        have hQpos : 0 < Q.natDegree := by
          rw [hQdeg]
          exact hdeg
        exact Nat.ne_of_gt hQpos))
  exact ⟨r, by change Q.IsRoot r; exact hr⟩

private lemma exists_root_outside_finite_projection_of_positive_degree
    {m : ℕ} (hm : 0 < m) (E : Set (Fin (m + 1) → ℂ)) (hE : E.Finite)
    {p : MvPolynomial (Fin (m + 1)) ℂ}
    (hdeg : 0 < (MvPolynomial.finSuccEquiv ℂ m p).natDegree) :
    ∃ y r, y ∉ E.image (fun x : Fin (m + 1) → ℂ => fun i => x i.succ) ∧
      ((MvPolynomial.finSuccEquiv ℂ m p).map
        (MvPolynomial.aeval y).toRingHom).IsRoot r := by
  classical
  let F := MvPolynomial.finSuccEquiv ℂ m p
  have hF : F ≠ 0 := by
    intro hF
    have : F.natDegree = 0 := by simp [hF]
    have hdegF : 0 < F.natDegree := by
      change 0 < F.natDegree
      exact hdeg
    omega
  have hdegF : 0 < F.natDegree := by
    change 0 < F.natDegree
    exact hdeg
  have hlc : F.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hF
  let E' : Set (Fin m → ℂ) :=
    E.image (fun x : Fin (m + 1) → ℂ => fun i => x i.succ)
  have hE' : E'.Finite := hE.image _
  obtain ⟨y, hyE', hly⟩ :=
    exists_aeval_ne_zero_of_finite_complement_single hm E' hE' hlc
  obtain ⟨r, hr⟩ := exists_root_of_map_of_positive_degree y hdegF hly
  refine ⟨y, r, ?_, ?_⟩
  · change y ∉ E'
    exact hyE'
  · change (F.map (MvPolynomial.aeval y).toRingHom).IsRoot r
    exact hr

private lemma exists_aeval_eq_zero_outside_finite_of_positive_degree
    {m : ℕ} (hm : 0 < m) (E : Set (Fin (m + 1) → ℂ)) (hE : E.Finite)
    {p : MvPolynomial (Fin (m + 1)) ℂ}
    (hdeg : 0 < (MvPolynomial.finSuccEquiv ℂ m p).natDegree) :
    ∃ x, x ∉ E ∧ MvPolynomial.aeval x p = 0 := by
  obtain ⟨y, r, hyE', hr⟩ :=
    exists_root_outside_finite_projection_of_positive_degree
      (p := p) hm E hE hdeg
  have hxE : Fin.cases r y ∉ E := by
    intro hx
    apply hyE'
    exact ⟨Fin.cases r y, hx, by funext i; simp⟩
  have hroot' : MvPolynomial.aeval y
      (Polynomial.eval (MvPolynomial.C r)
        (MvPolynomial.finSuccEquiv ℂ m p)) = 0 :=
    aeval_eval_C_eq_zero_of_isRoot_map
      (F := MvPolynomial.finSuccEquiv ℂ m p) y r hr
  have hroot : MvPolynomial.aeval (Fin.cases r y) p = 0 :=
    aeval_finSucc_eq_zero_of_eval_C_eq_zero (p := p) y r hroot'
  refine ⟨Fin.cases r y, ?_, ?_⟩
  · exact hxE
  · exact hroot

private lemma exists_fin_cases_not_mem_finite
    {m : ℕ} (E : Set (Fin (m + 1) → ℂ)) (hE : E.Finite)
    (y : Fin m → ℂ) : ∃ r : ℂ, Fin.cases r y ∉ E := by
  classical
  let S : Set ℂ := {r | Fin.cases r y ∈ E}
  have hS : S.Finite := by
    apply (hE.image (fun x : Fin (m + 1) → ℂ => x 0)).subset
    intro r hr
    change Fin.cases r y ∈ E at hr
    exact ⟨Fin.cases r y, hr, by simp⟩
  have hSnot : ∃ r : ℂ, r ∉ S := by
    by_contra hnot
    push_neg at hnot
    apply (Set.infinite_univ : (Set.univ : Set ℂ).Infinite)
    apply hS.subset
    intro r hr
    exact hnot r
  obtain ⟨r, hrS⟩ := hSnot
  exact ⟨r, by intro hx; exact hrS hx⟩

private lemma exists_aeval_eq_zero_outside_finite_of_constant_value
    {m : ℕ} (E : Set (Fin (m + 1) → ℂ)) (hE : E.Finite)
    {p : MvPolynomial (Fin (m + 1)) ℂ} {q : MvPolynomial (Fin m) ℂ}
    (hFC : MvPolynomial.finSuccEquiv ℂ m p = Polynomial.C q)
    (y : Fin m → ℂ) (hqy : MvPolynomial.aeval y q = 0) :
    ∃ x, x ∉ E ∧ MvPolynomial.aeval x p = 0 := by
  classical
  obtain ⟨r, hxE⟩ := exists_fin_cases_not_mem_finite E hE y
  have hroot' : MvPolynomial.aeval y
      (Polynomial.eval (MvPolynomial.C r)
        (MvPolynomial.finSuccEquiv ℂ m p)) = 0 := by
    rw [hFC]
    simp [hqy]
  have hroot : MvPolynomial.aeval (Fin.cases r y) p = 0 :=
    aeval_finSucc_eq_zero_of_eval_C_eq_zero (p := p) y r hroot'
  refine ⟨Fin.cases r y, ?_, ?_⟩
  · exact hxE
  · exact hroot

private lemma exists_aeval_eq_zero_outside_finite_of_constant_coefficient
    {m : ℕ} (hm : 0 < m) (E : Set (Fin (m + 1) → ℂ)) (hE : E.Finite)
    {p : MvPolynomial (Fin (m + 1)) ℂ} {q : MvPolynomial (Fin m) ℂ}
    (hFC : MvPolynomial.finSuccEquiv ℂ m p = Polynomial.C q)
    (hqne : q ≠ 0) (hqnonunit : ¬IsUnit q) :
    ∃ x, x ∉ E ∧ MvPolynomial.aeval x p = 0 := by
  classical
  obtain ⟨y, hqy⟩ := exists_aeval_eq_zero_of_not_isUnit hqne hqnonunit
  exact exists_aeval_eq_zero_outside_finite_of_constant_value
    E hE hFC y hqy

private lemma exists_aeval_eq_zero_outside_finite_of_degree_zero
    {m : ℕ} (hm : 0 < m) (E : Set (Fin (m + 1) → ℂ)) (hE : E.Finite)
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp0 : p ≠ 0)
    (hunit : ¬IsUnit p)
    (hdeg : ¬0 < (MvPolynomial.finSuccEquiv ℂ m p).natDegree) :
    ∃ x, x ∉ E ∧ MvPolynomial.aeval x p = 0 := by
  classical
  let F := MvPolynomial.finSuccEquiv ℂ m p
  have hFdeg : F.natDegree = 0 := by
    have hdegF : ¬0 < F.natDegree := by
      change ¬0 < F.natDegree
      exact hdeg
    omega
  have hFC : F = Polynomial.C (F.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hFdeg
  have hFne : F ≠ 0 := by
    intro hFzero
    apply hp0
    have hFzero' := congrArg (MvPolynomial.finSuccEquiv ℂ m).symm hFzero
    have heq : (MvPolynomial.finSuccEquiv ℂ m).symm F = p := by
      change (MvPolynomial.finSuccEquiv ℂ m).symm
          ((MvPolynomial.finSuccEquiv ℂ m) p) = p
      exact (MvPolynomial.finSuccEquiv ℂ m).symm_apply_apply p
    exact heq.symm.trans (hFzero'.trans (by simp))
  have hqne : F.coeff 0 ≠ 0 := by
    intro hqzero
    apply hFne
    rw [hFC, hqzero]
    simp
  have hqnonunit : ¬IsUnit (F.coeff 0) := by
    intro hqunit
    apply hunit
    have hFunit : IsUnit F := by
      rw [hFC]
      exact IsUnit.map (Polynomial.C :
        MvPolynomial (Fin m) ℂ →+* Polynomial (MvPolynomial (Fin m) ℂ)) hqunit
    have hpunit :=
      IsUnit.map (MvPolynomial.finSuccEquiv ℂ m).symm.toRingHom hFunit
    have heq : (MvPolynomial.finSuccEquiv ℂ m).symm.toRingHom F = p := by
      change (MvPolynomial.finSuccEquiv ℂ m).symm
          ((MvPolynomial.finSuccEquiv ℂ m) p) = p
      exact (MvPolynomial.finSuccEquiv ℂ m).symm_apply_apply p
    rw [heq] at hpunit
    exact hpunit
  exact exists_aeval_eq_zero_outside_finite_of_constant_coefficient
    hm E hE hFC hqne hqnonunit

private lemma isUnit_of_aeval_ne_zero_on_finite_complement
    {n : ℕ} (hn : 2 ≤ n) (E : Set (Fin n → ℂ)) (hE : E.Finite)
    {p : MvPolynomial (Fin n) ℂ}
    (hp : ∀ x, x ∉ E → MvPolynomial.aeval x p ≠ 0) : IsUnit p := by
  classical
  by_contra hunit
  cases n with
  | zero => omega
  | succ m =>
    have hm : 0 < m := by omega
    have hp0 : p ≠ 0 := by
      intro hpzero
      obtain ⟨x, hxE, hx⟩ :=
        exists_aeval_ne_zero_of_finite_complement_single (by omega) E hE
          (one_ne_zero : (1 : MvPolynomial (Fin (m + 1)) ℂ) ≠ 0)
      apply hp x hxE
      simp [hpzero]
    let F := MvPolynomial.finSuccEquiv ℂ m p
    by_cases hdeg : 0 < F.natDegree
    · obtain ⟨x, hxE, hzero⟩ :=
        exists_aeval_eq_zero_outside_finite_of_positive_degree hm E hE hdeg
      exact (hp x hxE) hzero
    · obtain ⟨x, hxE, hzero⟩ :=
        exists_aeval_eq_zero_outside_finite_of_degree_zero hm E hE hp0 hunit hdeg
      exact (hp x hxE) hzero

private lemma exists_mem_inter_of_nonempty_principal_opens
    {n : ℕ} (hn : 0 < n) (E : Set (Fin n → ℂ)) (hE : E.Finite)
    {U V : Set (Fin n → ℂ)}
    (hU : IsZariskiOpenIn ℂ n (Set.univ \ E) U)
    (hV : IsZariskiOpenIn ℂ n (Set.univ \ E) V)
    (hUnonempty : U.Nonempty) (hVnonempty : V.Nonempty) :
    ∃ x, x ∈ U ∧ x ∈ V := by
  classical
  rcases hU with ⟨J, hUeq⟩
  rcases hV with ⟨K, hVeq⟩
  obtain ⟨u, hu⟩ := hUnonempty
  obtain ⟨v, hv⟩ := hVnonempty
  have hu' := hu
  have hv' := hv
  rw [hUeq] at hu'
  rw [hVeq] at hv'
  have huJ : ∃ p, p ∈ J ∧ MvPolynomial.aeval u p ≠ 0 := by
    have huJ0 := hu'.2
    rw [MvPolynomial.mem_zeroLocus_iff] at huJ0
    push_neg at huJ0
    exact huJ0
  have hvK : ∃ q, q ∈ K ∧ MvPolynomial.aeval v q ≠ 0 := by
    have hvK0 := hv'.2
    rw [MvPolynomial.mem_zeroLocus_iff] at hvK0
    push_neg at hvK0
    exact hvK0
  obtain ⟨p, hpJ, hpval⟩ := huJ
  obtain ⟨q, hqK, hqval⟩ := hvK
  have hpne : p ≠ 0 := by
    intro hp
    subst p
    simp at hpval
  have hqne : q ≠ 0 := by
    intro hq
    subst q
    simp at hqval
  obtain ⟨x, hxE, hpx, hqx⟩ :=
    exists_aeval_ne_zero_of_finite_complement hn E hE hpne hqne
  have hxZ : x ∈ Set.univ \ E := ⟨Set.mem_univ _, hxE⟩
  have hxJ : x ∉ MvPolynomial.zeroLocus ℂ J := by
    intro hx
    exact hpx ((MvPolynomial.mem_zeroLocus_iff.mp hx) p hpJ)
  have hxK : x ∉ MvPolynomial.zeroLocus ℂ K := by
    intro hx
    exact hqx ((MvPolynomial.mem_zeroLocus_iff.mp hx) q hqK)
  exact ⟨x, hUeq ▸ ⟨hxZ, hxJ⟩, hVeq ▸ ⟨hxZ, hxK⟩⟩

private lemma eq_zero_of_aeval_eq_zero_on_basic_open
    {n : ℕ} {p q : MvPolynomial (Fin n) ℂ} (hq : q ≠ 0)
    (hp : ∀ x : Fin n → ℂ, MvPolynomial.aeval x q ≠ 0 →
      MvPolynomial.aeval x p = 0) : p = 0 := by
  have hmul : q * p = 0 := by
    apply MvPolynomial.funext (R := ℂ)
    intro x
    by_cases hqx : MvPolynomial.aeval x q = 0
    · have hqx' : MvPolynomial.eval x q = 0 := by
        simpa [MvPolynomial.aeval_def] using hqx
      simpa [MvPolynomial.eval_mul, hqx']
    · have hp' : MvPolynomial.eval x p = 0 := by
        simpa [MvPolynomial.aeval_def] using hp x hqx
      simpa [MvPolynomial.eval_mul, hp']
  exact (mul_eq_zero.mp hmul).resolve_left hq

private lemma eq_zero_of_aeval_eq_zero_on_finite_complement_basic_open
    {n : ℕ} (hn : 0 < n) (E : Set (Fin n → ℂ)) (hE : E.Finite)
    {p q : MvPolynomial (Fin n) ℂ} (hq : q ≠ 0)
    (hp : ∀ x, x ∉ E → MvPolynomial.aeval x q ≠ 0 →
      MvPolynomial.aeval x p = 0) : p = 0 := by
  have hmul : q * p = 0 := by
    apply cofinite_aeval_eq_zero hn E hE
    intro x hxE
    by_cases hqx : MvPolynomial.aeval x q = 0
    · rw [map_mul, hqx, zero_mul]
    · rw [map_mul, hp x hxE hqx, mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_left hq

/-- A regular function on the complement of a finite subset of complex affine
`n`-space is induced by an ambient polynomial when `n ≥ 2`. -/
theorem regular_function_on_finite_complement_is_polynomial
    {n : ℕ} (hn : 2 ≤ n) (E : Set (Fin n → ℂ)) (hE : E.Finite)
    (φ : ↥(Set.univ \ E) → ℂ)
    (hφ : IsRegularFunction (Set.univ \ E) φ) :
    IsPolynomialRestriction (Set.univ \ E) φ := by
  classical
  unfold IsPolynomialRestriction
  have hn0 : 0 < n := by omega
  by_cases hZ : (Set.univ \ E).Nonempty
  · obtain ⟨z0, hz0⟩ := hZ
    rcases hφ ⟨z0, hz0⟩ with
      ⟨U0, hz0U, hU0, hOpen0, f0, g0, hg0, hfg0⟩
    have hOpen0' := hOpen0
    rcases hOpen0 with ⟨J0, hU0eq⟩
    have hg0ne : g0 ≠ 0 := by
      intro hg
      subst g0
      have hg0' := hg0 z0 hz0U
      simp at hg0'
    have hcross_of_local :
        ∀ (U : Set (Fin n → ℂ)) (hU : U ⊆ Set.univ \ E)
          (hOpen : IsZariskiOpenIn ℂ n (Set.univ \ E) U)
          (hUnonempty : U.Nonempty) (f g : MvPolynomial (Fin n) ℂ),
          (∀ u, u ∈ U → MvPolynomial.aeval u g ≠ 0) →
          (∀ u (hu : u ∈ U),
            φ ⟨u, hU hu⟩ = MvPolynomial.aeval u f /
              MvPolynomial.aeval u g) →
          f0 * g - f * g0 = 0 := by
      intro U hU hOpen hUnonempty f g hg hfg
      rcases hOpen with ⟨J, hUeq⟩
      have hp0data : ∃ p, p ∈ J0 ∧ MvPolynomial.aeval z0 p ≠ 0 := by
        have hz0' := hz0U
        rw [hU0eq] at hz0'
        have hz0J := hz0'.2
        rw [MvPolynomial.mem_zeroLocus_iff] at hz0J
        push Not at hz0J
        exact hz0J
      obtain ⟨p0, hp0J, hp0val⟩ := hp0data
      have hp0ne : p0 ≠ 0 := by
        intro hp0
        subst p0
        simp at hp0val
      obtain ⟨u, hu⟩ := hUnonempty
      have hu' := hu
      rw [hUeq] at hu'
      have hpdata : ∃ p, p ∈ J ∧ MvPolynomial.aeval u p ≠ 0 := by
        have huJ := hu'.2
        rw [MvPolynomial.mem_zeroLocus_iff] at huJ
        push Not at huJ
        exact huJ
      obtain ⟨p, hpJ, hpval⟩ := hpdata
      have hpne : p ≠ 0 := by
        intro hp
        subst p
        simp at hpval
      have hprodne : p0 * p ≠ 0 := mul_ne_zero hp0ne hpne
      apply eq_zero_of_aeval_eq_zero_on_finite_complement_basic_open
        hn0 E hE hprodne
      intro y hyE hyprod
      have hyp0 : MvPolynomial.aeval y p0 ≠ 0 := by
        intro hyp0
        apply hyprod
        rw [map_mul, hyp0, zero_mul]
      have hyp : MvPolynomial.aeval y p ≠ 0 := by
        intro hyp
        apply hyprod
        rw [map_mul, hyp, mul_zero]
      have hyZ : y ∈ Set.univ \ E := ⟨Set.mem_univ _, hyE⟩
      have hyJ0 : y ∉ MvPolynomial.zeroLocus ℂ J0 := by
        intro hyJ0
        exact hyp0 ((MvPolynomial.mem_zeroLocus_iff.mp hyJ0) p0 hp0J)
      have hyJ : y ∉ MvPolynomial.zeroLocus ℂ J := by
        intro hyJ
        exact hyp ((MvPolynomial.mem_zeroLocus_iff.mp hyJ) p hpJ)
      have hyU0 : y ∈ U0 := hU0eq ▸ ⟨hyZ, hyJ0⟩
      have hyU : y ∈ U := hUeq ▸ ⟨hyZ, hyJ⟩
      have hratio :
          MvPolynomial.aeval y f0 / MvPolynomial.aeval y g0 =
            MvPolynomial.aeval y f / MvPolynomial.aeval y g := by
        calc
          MvPolynomial.aeval y f0 / MvPolynomial.aeval y g0 =
              φ ⟨y, hU0 hyU0⟩ := (hfg0 y hyU0).symm
          _ = φ ⟨y, hU hyU⟩ := by rfl
          _ = MvPolynomial.aeval y f / MvPolynomial.aeval y g :=
            hfg y hyU
      have hratio' :=
        (div_eq_div_iff (hg0 y hyU0) (hg y hyU)).mp hratio
      rw [map_sub, map_mul, map_mul]
      exact sub_eq_zero.mpr hratio'
    by_cases hf0 : f0 = 0
    · refine ⟨0, ?_⟩
      intro z
      rcases hφ z with
        ⟨U, hzU, hU, hOpen, f, g, hg, hfg⟩
      have hc := hcross_of_local U hU hOpen ⟨z.1, hzU⟩ f g hg hfg
      have hfg0 : f * g0 = 0 := by
        simpa [hf0] using hc
      have hf : f = 0 := (mul_eq_zero.mp hfg0).resolve_right hg0ne
      rw [hfg z.1 hzU, hf]
      simp
    · obtain ⟨a, b, c, hab, hca, hcb⟩ :=
        UniqueFactorizationMonoid.exists_reduced_factors f0 hf0 g0
      have hcne : c ≠ 0 := by
        intro hc
        subst c
        simp at hca
        exact hf0 hca.symm
      have hbne : b ≠ 0 := by
        intro hb
        subst b
        simp at hcb
        exact hg0ne hcb.symm
      have hno_factors : ∀ {d}, d ∣ b → d ∣ a → ¬Prime d := by
        intro d hdb hda hd
        exact hd.not_isUnit (hab.symm hdb hda)
      have hb_dvd_of_local :
          ∀ (U : Set (Fin n → ℂ)) (hU : U ⊆ Set.univ \ E)
            (hOpen : IsZariskiOpenIn ℂ n (Set.univ \ E) U)
            (hUnonempty : U.Nonempty) (f g : MvPolynomial (Fin n) ℂ),
            (∀ u, u ∈ U → MvPolynomial.aeval u g ≠ 0) →
            (∀ u (hu : u ∈ U),
              φ ⟨u, hU hu⟩ = MvPolynomial.aeval u f /
                MvPolynomial.aeval u g) → b ∣ g := by
        intro U hU hOpen hUnonempty f g hg hfg
        have hcros := hcross_of_local U hU hOpen hUnonempty f g hg hfg
        have hcros' : a * g = f * b := by
          have htmp : c * (a * g - f * b) = 0 := by
            calc
              c * (a * g - f * b) = (c * a) * g - f * (c * b) := by ring
              _ = f0 * g - f * g0 := by rw [hca, hcb]
              _ = 0 := hcros
          exact sub_eq_zero.mp ((mul_eq_zero.mp htmp).resolve_left hcne)
        have hdiv : b ∣ a * g := by
          refine ⟨f, ?_⟩
          simpa [mul_comm] using hcros'
        exact UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors
          hbne hno_factors hdiv
      have hbunit : IsUnit b := isUnit_of_aeval_ne_zero_on_finite_complement
        hn E hE (by
          intro x hxE
          have hx : x ∈ Set.univ \ E := ⟨Set.mem_univ _, hxE⟩
          rcases hφ ⟨x, hx⟩ with
            ⟨U, hxU, hU, hOpen, f, g, hg, hfg⟩
          obtain ⟨t, ht⟩ :=
            hb_dvd_of_local U hU hOpen ⟨x, hxU⟩ f g hg hfg
          intro hbx
          apply hg x hxU
          rw [ht, map_mul, hbx, zero_mul])
      obtain ⟨d, hd, hdb⟩ :=
        (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := b)).mp hbunit
      refine ⟨(d⁻¹ : ℂ) • a, ?_⟩
      intro z
      rcases hφ z with
        ⟨U, hzU, hU, hOpen, f, g, hg, hfg⟩
      have hcros := hcross_of_local U hU hOpen ⟨z.1, hzU⟩ f g hg hfg
      have hcros' : a * g = f * b := by
        have htmp : c * (a * g - f * b) = 0 := by
          calc
            c * (a * g - f * b) = (c * a) * g - f * (c * b) := by ring
            _ = f0 * g - f * g0 := by rw [hca, hcb]
            _ = 0 := hcros
        exact sub_eq_zero.mp ((mul_eq_zero.mp htmp).resolve_left hcne)
      obtain ⟨t, ht⟩ := hb_dvd_of_local U hU hOpen ⟨z.1, hzU⟩ f g hg hfg
      have hbval : MvPolynomial.aeval z.1 b ≠ 0 := by
        intro hbz
        apply hg z.1 hzU
        rw [ht, map_mul, hbz, zero_mul]
      have hratio :
          MvPolynomial.aeval z.1 f / MvPolynomial.aeval z.1 g =
            MvPolynomial.aeval z.1 a / MvPolynomial.aeval z.1 b := by
        apply (div_eq_div_iff (hg z.1 hzU) hbval).2
        simpa [map_mul, mul_comm] using
          congrArg (fun q => MvPolynomial.aeval z.1 q) hcros'.symm
      calc
        φ z = MvPolynomial.aeval z.1 f / MvPolynomial.aeval z.1 g :=
          hfg z.1 hzU
        _ = MvPolynomial.aeval z.1 a / MvPolynomial.aeval z.1 b := hratio
        _ = MvPolynomial.aeval z.1 ((d⁻¹ : ℂ) • a) := by
          rw [hdb]
          simp [div_eq_mul_inv, Algebra.smul_def, mul_comm]
  · refine ⟨0, ?_⟩
    intro z
    exact False.elim (hZ ⟨z.1, z.2⟩)

/-! ## Exercise `cone` -/

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem aeval_smul_of_isHomogeneous
    {n : ℕ} {f : MvPolynomial (Fin n) ℂ} {d : ℕ}
    (hf : MvPolynomial.IsHomogeneous f d) (x : Fin n → ℂ) (c : ℂ) :
    MvPolynomial.aeval (fun i => c * x i) f =
      c ^ d * MvPolynomial.aeval x f := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hdeg : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (by
      rw [MvPolynomial.mem_support_iff] at hm
      exact hm)
  rw [← hdeg]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [Finsupp.degree_apply] at hdeg ⊢
  ring

/-- An ideal generated by homogeneous polynomials cuts out a cone. -/
theorem homogeneous_generated_zero_locus_is_cone
    {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ))
    (hp : ∃ S : Set (MvPolynomial (Fin n) ℂ), p = Ideal.span S ∧
      ∀ f ∈ S, ∃ d : ℕ, MvPolynomial.IsHomogeneous f d) :
    IsCone (MvPolynomial.zeroLocus ℂ p) := by
  rcases hp with ⟨S, hpS, hS⟩
  rw [hpS, IsCone]
  intro x hx c
  rw [MvPolynomial.zeroLocus_span] at hx ⊢
  intro f hf
  rcases hS f hf with ⟨d, hd⟩
  have hxf : MvPolynomial.aeval x f = 0 := hx f hf
  rw [aeval_smul_of_isHomogeneous hd x c, hxf, mul_zero]

/-- The prime ideal of a complex affine cone is generated by homogeneous
polynomials. -/
theorem cone_prime_ideal_is_homogeneous_generated
    {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) (hp : p.IsPrime)
    (hcone : IsCone (MvPolynomial.zeroLocus ℂ p)) :
    ∃ S : Set (MvPolynomial (Fin n) ℂ), p = Ideal.span S ∧
      ∀ f ∈ S, ∃ d : ℕ, MvPolynomial.IsHomogeneous f d := by
  have hpvan :
      MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ p) = p := by
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hp.radical]
  have hcomp :
      ∀ f ∈ p, ∀ d : ℕ,
        MvPolynomial.homogeneousComponent d f ∈ p := by
    intro f hf d
    rw [← hpvan]
    intro x hx
    have hq_eval (c : ℂ) :
        (∑ i ∈ Finset.range (f.totalDegree + 1),
            Polynomial.C (MvPolynomial.aeval x
              (MvPolynomial.homogeneousComponent i f)) * Polynomial.X ^ i).eval c =
          MvPolynomial.aeval (fun j => c * x j) f := by
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      calc
        (∑ i ∈ Finset.range (f.totalDegree + 1),
            MvPolynomial.aeval x (MvPolynomial.homogeneousComponent i f) * c ^ i) =
            ∑ i ∈ Finset.range (f.totalDegree + 1),
              MvPolynomial.aeval (fun j => c * x j)
                (MvPolynomial.homogeneousComponent i f) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [aeval_smul_of_isHomogeneous
            (MvPolynomial.homogeneousComponent_isHomogeneous i f) x c]
          ring
        _ = MvPolynomial.aeval (fun j => c * x j)
            (∑ i ∈ Finset.range (f.totalDegree + 1),
              MvPolynomial.homogeneousComponent i f) := by
          rw [map_sum]
        _ = MvPolynomial.aeval (fun j => c * x j) f := by
          rw [MvPolynomial.sum_homogeneousComponent]
    have hqzero :
        (∑ i ∈ Finset.range (f.totalDegree + 1),
            Polynomial.C (MvPolynomial.aeval x
              (MvPolynomial.homogeneousComponent i f)) * Polynomial.X ^ i) = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hrange : (Set.range (fun c : ℂ => c)).Infinite :=
        Set.infinite_range_of_injective (fun _ _ h => h)
      apply hrange.mono
      intro c hc
      rcases hc with ⟨c, rfl⟩
      change
        (∑ i ∈ Finset.range (f.totalDegree + 1),
            Polynomial.C (MvPolynomial.aeval x
              (MvPolynomial.homogeneousComponent i f)) * Polynomial.X ^ i).eval c = 0
      rw [hq_eval]
      exact (hcone x hx c) f hf
    have hcoeff :
        MvPolynomial.aeval x (MvPolynomial.homogeneousComponent d f) = 0 := by
      by_cases hdle : d ≤ f.totalDegree
      · have hcoeff' := congrArg (fun q => q.coeff d) hqzero
        rw [Polynomial.finsetSum_coeff] at hcoeff'
        rw [Finset.sum_eq_single d] at hcoeff'
        · simpa using hcoeff'
        · intro b hb hbd
          simp [Ne.symm hbd]
        · intro hdnot
          exact (hdnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hdle))).elim
      · rw [MvPolynomial.homogeneousComponent_eq_zero d f
          (Nat.lt_of_not_ge hdle)]
        simp
    exact hcoeff
  have hpHom : p.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
    intro d f hf
    change (MvPolynomial.decomposition.decompose' f d : MvPolynomial (Fin n) ℂ) ∈ p
    simpa only [MvPolynomial.decomposition.decompose'_apply] using hcomp f hf d
  obtain ⟨T, hT⟩ :=
    (Ideal.IsHomogeneous.iff_exists
      (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) p).mp hpHom
  refine ⟨(↑) '' T, hT, ?_⟩
  rintro f ⟨t, ht, rfl⟩
  exact t.property

/-! ## Exercise `extra-function-cone` -/

/-- The coordinate line `y = 0`, viewed as a cone in complex affine 2-space. -/
def affineLineCone : Set (Fin 2 → ℂ) :=
  MvPolynomial.zeroLocus ℂ
    (Ideal.span ({MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) ℂ)))

/-- The punctured coordinate line. -/
def affineLineConePunctured : Set (Fin 2 → ℂ) :=
  affineLineCone \ ({0} : Set (Fin 2 → ℂ))

/-- The inverse of the first coordinate on the punctured coordinate line. -/
def affineLineConeInverse (z : ↥affineLineConePunctured) : ℂ :=
  (z.1 0)⁻¹

/-- The coordinate line is an affine variety. -/
theorem affine_line_cone_is_affine_variety :
    IsAffineVariety ℂ 2 affineLineCone := by
  refine ⟨Ideal.span {MvPolynomial.X (1 : Fin 2)}, ?_, rfl⟩
  exact (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero _)).mpr
    (MvPolynomial.X_prime)

/-- The coordinate line is a cone. -/
theorem affine_line_cone_is_cone : IsCone affineLineCone := by
  rw [affineLineCone, MvPolynomial.zeroLocus_span]
  intro x hx c f hf
  have hx1 : x 1 = 0 := by
    have h := hx (MvPolynomial.X (1 : Fin 2)) (by simp)
    rw [MvPolynomial.aeval_X] at h
    exact h
  rw [Set.mem_singleton_iff.mp hf, MvPolynomial.aeval_X, hx1]
  simp

/-- The inverse coordinate function is regular on the punctured coordinate
line. -/
theorem affine_line_cone_inverse_is_regular :
    IsRegularFunction affineLineConePunctured affineLineConeInverse := by
  intro z
  have hline_zero : ∀ u : Fin 2 → ℂ, u ∈ affineLineCone → u 1 = 0 := by
    intro u hu
    have hu' := hu
    rw [affineLineCone, MvPolynomial.zeroLocus_span] at hu'
    have h := hu' (MvPolynomial.X (1 : Fin 2)) (by simp)
    rw [MvPolynomial.aeval_X] at h
    exact h
  have hzero_of_mem : ∀ u : Fin 2 → ℂ, u ∈ affineLineCone →
      MvPolynomial.aeval u (MvPolynomial.X (R := ℂ) (0 : Fin 2)) = 0 → u = 0 := by
    intro u hu hu0
    have hu1 : u 1 = 0 := hline_zero u hu
    have hu0' : u 0 = 0 := by
      simpa only [MvPolynomial.aeval_X] using hu0
    funext i
    fin_cases i
    · exact hu0'
    · exact hu1
  refine ⟨affineLineConePunctured, z.2, ?_, ?_, (1 : MvPolynomial (Fin 2) ℂ),
    MvPolynomial.X (0 : Fin 2), ?_, ?_⟩
  · intro u hu
    exact hu
  · refine ⟨Ideal.span {MvPolynomial.X (0 : Fin 2)}, ?_⟩
    ext u
    constructor
    · intro hu
      refine ⟨hu, ?_⟩
      intro hu0
      apply hu.2
      have hu0' := hu0
      rw [MvPolynomial.zeroLocus_span] at hu0'
      have h := hu0' (MvPolynomial.X (0 : Fin 2)) (by simp)
      apply Set.mem_singleton_iff.mpr
      exact hzero_of_mem u hu.1 h
    · intro hu
      exact hu.1
  · intro u hu hu0
    apply hu.2
    apply Set.mem_singleton_iff.mpr
    exact hzero_of_mem u hu.1 hu0
  · intro u hu
    simp [affineLineConeInverse, MvPolynomial.aeval_X]

/-- The inverse coordinate function is not induced by an ambient polynomial. -/
theorem affine_line_cone_inverse_not_polynomial :
    ¬ IsPolynomialRestriction affineLineConePunctured affineLineConeInverse := by
  rintro ⟨f, hf⟩
  let g : Fin 2 → Polynomial ℂ := ![Polynomial.X, 0]
  let F : Polynomial ℂ := MvPolynomial.aeval g f
  let q : Polynomial ℂ := Polynomial.X * F - 1
  have hF (t : ℂ) : F.eval t = MvPolynomial.aeval ![t, 0] f := by
    change Polynomial.evalRingHom t (MvPolynomial.aeval g f) = _
    rw [MvPolynomial.map_aeval]
    simp [g, MvPolynomial.aeval_eq_eval₂Hom]
    have hcoeff : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
      ext c
      simp
    have hvars : (fun i : Fin 2 => Polynomial.eval t (![Polynomial.X, 0] i)) =
        ![t, 0] := by
      funext i
      fin_cases i <;> simp
    rw [hcoeff, hvars]
    rw [MvPolynomial.eval₂_id]
  have hqroot : ∀ t : ℂ, t ≠ 0 → q.eval t = 0 := by
    intro t ht
    have ht_mem : ![t, 0] ∈ affineLineConePunctured := by
      refine ⟨?_, ?_⟩
      · rw [affineLineCone, MvPolynomial.zeroLocus_span]
        intro p hp
        have hp' : p = MvPolynomial.X (1 : Fin 2) := by simpa using hp
        rw [hp']
        simp
      · intro hzero
        have hcoord := congrFun (Set.mem_singleton_iff.mp hzero) (0 : Fin 2)
        simpa using (ht (by simpa using hcoord))
    have hval := hf ⟨![t, 0], ht_mem⟩
    simp only [affineLineConeInverse] at hval
    change (Polynomial.X * F - 1).eval t = 0
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, hF t,
      ← hval]
    simp [ht]
  have hqzero : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hrange : (Set.range (fun n : ℕ => (n + 1 : ℂ))).Infinite :=
      Set.infinite_range_of_injective (by
        intro m n h
        have h' : (m : ℂ) = n := add_right_cancel h
        exact_mod_cast h')
    apply hrange.mono
    intro t ht
    rcases ht with ⟨n, rfl⟩
    change q.eval ((n : ℂ) + 1) = 0
    apply hqroot
    exact_mod_cast Nat.succ_ne_zero n
  have hq0 := congrArg (fun p : Polynomial ℂ => p.eval 0) hqzero
  simp [q] at hq0

/-- An explicit affine cone with a regular function on its puncture which is
not induced by an ambient polynomial. -/
theorem extra_function_on_affine_cone :
    IsAffineVariety ℂ 2 affineLineCone ∧
      IsCone affineLineCone ∧
        IsRegularFunction affineLineConePunctured affineLineConeInverse ∧
          ¬ IsPolynomialRestriction affineLineConePunctured affineLineConeInverse := by
  exact ⟨affine_line_cone_is_affine_variety, affine_line_cone_is_cone,
    affine_line_cone_inverse_is_regular, affine_line_cone_inverse_not_polynomial⟩

/-! ## Exercise `regular-functions` -/

/-- Regular functions are closed under addition. -/
theorem isRegularFunction_add
    {k : Type u} [Field k] {n : ℕ} {Z : Set (Fin n → k)}
    {φ ψ : Z → k} (hφ : IsRegularFunction Z φ)
    (hψ : IsRegularFunction Z ψ) :
    IsRegularFunction Z (φ + ψ) := by
  classical
  intro z
  rcases hφ z with ⟨U, hzU, hU, hOpenU, f₁, g₁, hg₁, hfg₁⟩
  rcases hψ z with ⟨V, hzV, hV, hOpenV, f₂, g₂, hg₂, hfg₂⟩
  rcases hOpenU with ⟨J, hUJ⟩
  rcases hOpenV with ⟨K, hVK⟩
  let W := Z \ MvPolynomial.zeroLocus k (J * K)
  have hWU : W ⊆ U := by
    intro x hx
    change x ∈ Z \ MvPolynomial.zeroLocus k (J * K) at hx
    rw [hUJ]
    refine ⟨hx.1, ?_⟩
    intro hxJ
    apply hx.2
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    have hker : J * K ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
      refine Ideal.mul_le.2 ?_
      intro j hj k hk
      have hj0 := (MvPolynomial.mem_zeroLocus_iff.mp hxJ) j hj
      change MvPolynomial.aeval x (j * k) = 0
      rw [map_mul, hj0, zero_mul]
    exact hker hp
  have hWV : W ⊆ V := by
    intro x hx
    change x ∈ Z \ MvPolynomial.zeroLocus k (J * K) at hx
    rw [hVK]
    refine ⟨hx.1, ?_⟩
    intro hxK
    apply hx.2
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    have hker : J * K ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
      refine Ideal.mul_le.2 ?_
      intro j hj k hk
      have hk0 := (MvPolynomial.mem_zeroLocus_iff.mp hxK) k hk
      change MvPolynomial.aeval x (j * k) = 0
      rw [map_mul, hk0, mul_zero]
    exact hker hp
  have hzW : z.1 ∈ W := by
    change z.1 ∈ Z \ MvPolynomial.zeroLocus k (J * K)
    have hzU' := hzU
    rw [hUJ] at hzU'
    have hzV' := hzV
    rw [hVK] at hzV'
    refine ⟨hU hzU, ?_⟩
    intro hzprod
    have hzJ := hzU'.2
    rw [MvPolynomial.mem_zeroLocus_iff] at hzJ
    push Not at hzJ
    rcases hzJ with ⟨j, hj, hj0⟩
    apply hzV'.2
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro k hk
    have hprod := (MvPolynomial.mem_zeroLocus_iff.mp hzprod) (j * k)
      (Ideal.mul_mem_mul hj hk)
    rw [map_mul] at hprod
    exact (mul_eq_zero.mp hprod).resolve_left hj0
  refine ⟨W, hzW, ?_, ?_, f₁ * g₂ + f₂ * g₁, g₁ * g₂, ?_, ?_⟩
  · exact hWU.trans hU
  · exact ⟨J * K, rfl⟩
  · intro x hx
    rw [map_mul]
    exact mul_ne_zero (hg₁ x (hWU hx)) (hg₂ x (hWV hx))
  · intro x hx
    have h₁ := hfg₁ x (hWU hx)
    have h₂ := hfg₂ x (hWV hx)
    change φ ⟨x, hU (hWU hx)⟩ + ψ ⟨x, hV (hWV hx)⟩ = _
    rw [h₁, h₂]
    simp only [map_add, map_mul]
    rw [div_add_div _ _ (hg₁ x (hWU hx)) (hg₂ x (hWV hx))]
    ring

/-- Regular functions are closed under multiplication. -/
theorem isRegularFunction_mul
    {k : Type u} [Field k] {n : ℕ} {Z : Set (Fin n → k)}
    {φ ψ : Z → k} (hφ : IsRegularFunction Z φ)
    (hψ : IsRegularFunction Z ψ) :
    IsRegularFunction Z (φ * ψ) := by
  sorry

/-- Constant functions are regular. -/
theorem isRegularFunction_algebraMap
    {k : Type u} [Field k] {n : ℕ} (Z : Set (Fin n → k)) (c : k) :
    IsRegularFunction Z (algebraMap k (Z → k) c) := by
  sorry

/-- The ring of regular functions, with its canonical `k`-algebra structure. -/
def regularFunctionAlgebra {k : Type u} [Field k] {n : ℕ}
    (Z : Set (Fin n → k)) : Subalgebra k (Z → k) where
  carrier := {φ | IsRegularFunction Z φ}
  add_mem' := by
    intro φ ψ hφ hψ
    exact isRegularFunction_add hφ hψ
  mul_mem' := by
    intro φ ψ hφ hψ
    exact isRegularFunction_mul hφ hψ
  algebraMap_mem' c := isRegularFunction_algebraMap Z c

/-! ### Algebraically closed fields -/

/-- On affine space over an algebraically closed field, every regular function
is induced by a polynomial. -/
theorem regular_function_on_affine_space_is_polynomial
    (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (φ : ↥(Set.univ : Set (Fin n → k)) → k)
    (hφ : IsRegularFunction (Set.univ : Set (Fin n → k)) φ) :
    IsPolynomialRestriction (Set.univ : Set (Fin n → k)) φ := by
  sorry

/-! ### Finite fields -/

/-- Every function on a locally closed subset of affine space over a finite
field is regular. -/
theorem finite_field_every_function_is_regular
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (Z : Set (Fin n → k)) (hZ : IsZariskiLocallyClosed k n Z)
    (φ : Z → k) :
    IsRegularFunction Z φ := by
  sorry

/-- The ring of regular functions on a locally closed finite affine set is
finite-dimensional over its finite ground field. -/
theorem finite_field_regular_functions_moduleFinite
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (Z : Set (Fin n → k)) (hZ : IsZariskiLocallyClosed k n Z) :
    Module.Finite k (regularFunctionAlgebra Z) := by
  sorry

/-! ### The real example -/

/-- The everywhere-defined real function `x ↦ 1/(x²+1)` on the affine line.
The affine line is represented by `Fin 1 → ℝ`. -/
def realQuadraticInverse
    (x : ↥(Set.univ : Set (Fin 1 → ℝ))) : ℝ :=
  ((x.1 0) ^ 2 + 1)⁻¹

/-- The polynomial `x² + 1` for the real example. -/
def realQuadratic : MvPolynomial (Fin 1) ℝ :=
  MvPolynomial.X (0 : Fin 1) ^ 2 + MvPolynomial.C (1 : ℝ)

/-- The real quadratic inverse is regular everywhere. -/
theorem real_quadratic_inverse_is_regular :
    IsRegularFunction (Set.univ : Set (Fin 1 → ℝ)) realQuadraticInverse := by
  sorry

/-- The real quadratic inverse is not a polynomial function. -/
theorem real_quadratic_inverse_not_polynomial :
    ¬ IsPolynomialRestriction (Set.univ : Set (Fin 1 → ℝ)) realQuadraticInverse := by
  sorry

/-- A regular function on the real affine line which is not a polynomial. -/
theorem exists_real_regular_function_not_polynomial :
    ∃ φ : ↥(Set.univ : Set (Fin 1 → ℝ)) → ℝ,
      IsRegularFunction (Set.univ : Set (Fin 1 → ℝ)) φ ∧
        ¬ IsPolynomialRestriction (Set.univ : Set (Fin 1 → ℝ)) φ := by
  exact ⟨realQuadraticInverse, real_quadratic_inverse_is_regular,
    real_quadratic_inverse_not_polynomial⟩

/-! ### The p-adic example -/

/-- The everywhere-defined p-adic function `x ↦ 1/(x²-p)` on the affine line.
Here `p` is prime and `ℚ_[p]` is Mathlib's p-adic field. -/
def padicQuadraticInverse (p : ℕ) [Fact p.Prime]
    (x : ↥(Set.univ : Set (Fin 1 → ℚ_[p]))) : ℚ_[p] :=
  ((x.1 0) ^ 2 - (p : ℚ_[p]))⁻¹

/-- The polynomial `x²-p` for the p-adic example. -/
def padicQuadratic (p : ℕ) [Fact p.Prime] :
    MvPolynomial (Fin 1) ℚ_[p] :=
  MvPolynomial.X (0 : Fin 1) ^ 2 - MvPolynomial.C (p : ℚ_[p])

/-- The p-adic quadratic inverse is regular everywhere. -/
theorem padic_quadratic_inverse_is_regular
    (p : ℕ) [Fact p.Prime] :
    IsRegularFunction (Set.univ : Set (Fin 1 → ℚ_[p]))
      (padicQuadraticInverse p) := by
  sorry

/-- The p-adic quadratic inverse is not a polynomial function. -/
theorem padic_quadratic_inverse_not_polynomial
    (p : ℕ) [Fact p.Prime] :
    ¬ IsPolynomialRestriction (Set.univ : Set (Fin 1 → ℚ_[p]))
      (padicQuadraticInverse p) := by
  sorry

/-- A regular function on the p-adic affine line which is not a polynomial. -/
theorem exists_padic_regular_function_not_polynomial
    (p : ℕ) [Fact p.Prime] :
    ∃ φ : ↥(Set.univ : Set (Fin 1 → ℚ_[p])) → ℚ_[p],
      IsRegularFunction (Set.univ : Set (Fin 1 → ℚ_[p])) φ ∧
        ¬ IsPolynomialRestriction (Set.univ : Set (Fin 1 → ℚ_[p])) φ := by
  exact ⟨padicQuadraticInverse p, padic_quadratic_inverse_is_regular p,
    padic_quadratic_inverse_not_polynomial p⟩

end

end Formalization.Books.Exercises.Unit31
