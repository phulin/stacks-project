import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.CancelLeads

/-!
# Exercises, Chapter 15: Constructible sets

This file records the source-facing interface for the non-monic polynomial
division exercise.  The coefficient list is indexed by `Fin`, so the
polynomial with coefficients `a 0, ..., a (d - 1)` is available uniformly
also when `d = 0`.
-/

namespace Formalization.Books.Exercises.Unit15

universe u

noncomputable section

/-! ## Exercise `division-with-remainder` -/

/-- The polynomial `a 0 + a 1 X + ⋯ + a (d - 1) X^(d - 1)`. -/
def polynomialOfCoefficients {R : Type u} [Semiring R] (d : ℕ)
    (a : Fin d → R) : Polynomial R :=
  ∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

private theorem coeff_polynomialOfCoefficients_last
    {R : Type u} [Semiring R] (d : ℕ) (a : Fin (d + 1) → R) :
    (polynomialOfCoefficients (d + 1) a).coeff d = a (Fin.last d) := by
  classical
  rw [polynomialOfCoefficients, Fin.sum_univ_castSucc, Polynomial.coeff_add]
  simp [Polynomial.coeff_C_mul_X_pow]
  have hzero :
      (∑ i : Fin d, if d = (i : ℕ) then a i.castSucc else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Nat.ne_of_gt i.isLt]
  rw [hzero]
  simp

private theorem exists_coefficients_of_degree_lt
    {R : Type u} [Semiring R] (d : ℕ) (r : Polynomial R)
    (hr : r.degree < d) :
    ∃ c : Fin d → R, r = polynomialOfCoefficients d c := by
  refine ⟨fun i => r.coeff i, ?_⟩
  rw [polynomialOfCoefficients]
  exact ((Polynomial.sum_fin (fun n b => Polynomial.C b * Polynomial.X ^ n)
    (fun _ => by simp) hr).trans (Polynomial.sum_C_mul_X_pow_eq r)).symm

private theorem exists_pseudo_division_of_nonzero_leadingCoeff
    {R : Type u} [CommRing R] (d : ℕ) (a : Fin (d + 1) → R)
    (ha : a (Fin.last d) ≠ 0) (g : Polynomial R) :
    ∃ N : ℕ, ∃ q r : Polynomial R,
      Polynomial.C ((a (Fin.last d)) ^ N) * g =
        q * polynomialOfCoefficients (d + 1) a + r ∧
      Polynomial.degree r < d ∧
        ∃ c : Fin d → R, r = polynomialOfCoefficients d c := by
  letI : Nontrivial R := nontrivial_of_ne _ _ ha
  let f : Polynomial R := polynomialOfCoefficients (d + 1) a
  have hfcoeff : f.coeff d = a (Fin.last d) :=
    coeff_polynomialOfCoefficients_last d a
  have hfnd : f.natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_of_degree_le (p := f)
      apply (Polynomial.degree_le_iff_coeff_zero f (d : WithBot ℕ)).mpr
      intro m hm
      change (polynomialOfCoefficients (d + 1) a).coeff m = 0
      simp [polynomialOfCoefficients, Polynomial.coeff_C_mul_X_pow]
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt)
        (by exact_mod_cast hm))
    · simpa [hfcoeff] using ha
  by_cases hlt : g.natDegree < d
  · obtain ⟨c, hc⟩ := exists_coefficients_of_degree_lt d g
      (by
        by_cases hg : g = 0
        · simp [hg]
        · exact (Polynomial.natDegree_lt_iff_degree_lt (p := g) (n := d) hg).mp hlt)
    have hdeglt : g.degree < (d : WithBot ℕ) := by
      by_cases hg : g = 0
      · simp [hg]
      · exact (Polynomial.natDegree_lt_iff_degree_lt (p := g) (n := d) hg).mp hlt
    refine ⟨0, 0, g, ?_, hdeglt, c, hc⟩
    simp
  by_cases hzero : g.natDegree = 0
  · have hd : d = 0 := Nat.eq_zero_of_not_pos (by
      simpa [hzero] using hlt)
    have hgC : g = Polynomial.C (g.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hzero
    have hfzero : f.natDegree = 0 := by
      simpa [hfnd, hd]
    have hfC0 : f = Polynomial.C (f.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hfzero
    have hfcoeff0 : f.coeff 0 = a (Fin.last d) := by
      have hcoeff_nat : f.coeff 0 = f.coeff d := by
        simpa [hd]
      exact hcoeff_nat.trans hfcoeff
    have hfC : f = Polynomial.C (a (Fin.last d)) := by
      rw [hfC0, hfcoeff0]
    refine ⟨1, Polynomial.C (g.coeff 0), 0, ?_, ?_, ?_⟩
    · change Polynomial.C ((a (Fin.last d)) ^ 1) * g =
        Polynomial.C (g.coeff 0) * f + 0
      rw [hgC, hfC]
      simp [pow_one, mul_comm]
    · simpa [hd]
    · refine ⟨fun _ => 0, ?_⟩
      simp [polynomialOfCoefficients]
  · have hle : d ≤ g.natDegree := Nat.le_of_not_gt hlt
    let g' := f.cancelLeads g
    have hdeg : g'.natDegree < g.natDegree := by
      dsimp [g']
      apply Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree
      · simpa [hfnd] using hle
      · exact Nat.pos_of_ne_zero hzero
    obtain ⟨N, q, r, hqr, hr, c, hc⟩ :=
      exists_pseudo_division_of_nonzero_leadingCoeff d a ha g'
    refine ⟨N + 1,
      Polynomial.C ((a (Fin.last d)) ^ N) *
          (Polynomial.C (g.leadingCoeff) * Polynomial.X ^ (g.natDegree - d)) + q,
      r, ?_, hr, c, hc⟩
    have hcancel : g' =
        Polynomial.C (a (Fin.last d)) * g -
          (Polynomial.C (g.leadingCoeff) * Polynomial.X ^ (g.natDegree - d)) * f := by
      dsimp [g']
      rw [Polynomial.cancelLeads, hfnd, Nat.sub_eq_zero_of_le hle, pow_zero, mul_one]
      rw [show f.leadingCoeff = a (Fin.last d) by
        rw [Polynomial.leadingCoeff, hfnd]
        exact hfcoeff]
    have hpow :
        Polynomial.C ((a (Fin.last d)) ^ (N + 1)) =
          Polynomial.C ((a (Fin.last d)) ^ N) *
            Polynomial.C (a (Fin.last d)) := by
      simp [pow_succ', Polynomial.C_mul, mul_comm]
    rw [hpow]
    calc
      Polynomial.C ((a (Fin.last d)) ^ N) * Polynomial.C (a (Fin.last d)) * g =
          Polynomial.C ((a (Fin.last d)) ^ N) * (g' +
            (Polynomial.C (g.leadingCoeff) * Polynomial.X ^ (g.natDegree - d)) * f) := by
        calc
          Polynomial.C ((a (Fin.last d)) ^ N) * Polynomial.C (a (Fin.last d)) * g =
              Polynomial.C ((a (Fin.last d)) ^ N) *
                (Polynomial.C (a (Fin.last d)) * g) := mul_assoc _ _ _
          _ = Polynomial.C ((a (Fin.last d)) ^ N) * (g' +
              (Polynomial.C (g.leadingCoeff) * Polynomial.X ^ (g.natDegree - d)) * f) := by
            rw [hcancel]
            ring
      _ = (Polynomial.C ((a (Fin.last d)) ^ N) *
          (Polynomial.C (g.leadingCoeff) * Polynomial.X ^ (g.natDegree - d)) + q) * f + r := by
        rw [mul_add, hqr]
        ring
termination_by g.natDegree

/-- Pseudo-division by a polynomial over a ring: after multiplying by a power
of the leading coefficient, the remainder has degree strictly below the
prescribed degree. -/
theorem exists_pseudo_division
    {R : Type u} [CommRing R] (d : ℕ) (a : Fin (d + 1) → R)
    (g : Polynomial R) :
    ∃ N : ℕ, ∃ q r : Polynomial R,
      Polynomial.C ((a (Fin.last d)) ^ N) * g =
        q * polynomialOfCoefficients (d + 1) a + r ∧
        Polynomial.degree r < d ∧
        ∃ c : Fin d → R, r = polynomialOfCoefficients d c := by
  by_cases ha : a (Fin.last d) = 0
  · refine ⟨1, 0, 0, ?_, ?_, ?_⟩
    · simp [ha]
    · simp
    · refine ⟨fun i => 0, ?_⟩
      simp [polynomialOfCoefficients]
  · exact exists_pseudo_division_of_nonzero_leadingCoeff d a ha g

end

end Formalization.Books.Exercises.Unit15
