import Formalization.Books.Exercises.Unit31.Core

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Prime

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
  (simp [affineCurve, MvPolynomial.zeroLocus_span, affineCurveEquation, affineCurvePoint];
    norm_num)

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

/-- A regular function on the complement of a finite subset of complex affine
`n`-space is induced by an ambient polynomial when `n ≥ 2`. -/
theorem regular_function_on_finite_complement_is_polynomial
    {n : ℕ} (hn : 2 ≤ n) (E : Set (Fin n → ℂ)) (hE : E.Finite)
    (φ : ↥(Set.univ \ E) → ℂ)
    (hφ : IsRegularFunction (Set.univ \ E) φ) :
    IsPolynomialRestriction (Set.univ \ E) φ := by
  sorry

/-! ## Exercise `cone` -/

/-- An ideal generated by homogeneous polynomials cuts out a cone. -/
theorem homogeneous_generated_zero_locus_is_cone
    {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ))
    (hp : ∃ S : Set (MvPolynomial (Fin n) ℂ), p = Ideal.span S ∧
      ∀ f ∈ S, ∃ d : ℕ, MvPolynomial.IsHomogeneous f d) :
    IsCone (MvPolynomial.zeroLocus ℂ p) := by
  sorry

/-- The prime ideal of a complex affine cone is generated by homogeneous
polynomials. -/
theorem cone_prime_ideal_is_homogeneous_generated
    {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) (hp : p.IsPrime)
    (hcone : IsCone (MvPolynomial.zeroLocus ℂ p)) :
    ∃ S : Set (MvPolynomial (Fin n) ℂ), p = Ideal.span S ∧
      ∀ f ∈ S, ∃ d : ℕ, MvPolynomial.IsHomogeneous f d := by
  sorry

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
  sorry

/-- The coordinate line is a cone. -/
theorem affine_line_cone_is_cone : IsCone affineLineCone := by
  sorry

/-- The inverse coordinate function is regular on the punctured coordinate
line. -/
theorem affine_line_cone_inverse_is_regular :
    IsRegularFunction affineLineConePunctured affineLineConeInverse := by
  sorry

/-- The inverse coordinate function is not induced by an ambient polynomial. -/
theorem affine_line_cone_inverse_not_polynomial :
    ¬ IsPolynomialRestriction affineLineConePunctured affineLineConeInverse := by
  sorry

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
  sorry

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
