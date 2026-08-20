import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Basic

/-!
# Obsolete, Chapter 5: lemmas related to Zariski's Main Theorem

This file records the three elementary integral-equation lemmas at the start
of the source section.  Polynomial maps are represented by `Polynomial` and
the integral-element assertions use Mathlib's canonical `RingHom.IsIntegralElem`.
-/

namespace Formalization.Books.Obsolete.Unit05

open Polynomial
open Set

universe u v

noncomputable section

/-! ## Changing the polynomial coordinate -/

/- The coefficient map is the restriction of `φ` along `Polynomial.C`, while
   the new variable is sent to `φ (a * X)`. -/
def changeEquationMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R[X] →+* S) (a : R) : R[X] →+* S :=
  Polynomial.eval₂RingHom
    (φ.comp (Polynomial.C : R →+* R[X]))
    (φ (Polynomial.C a * Polynomial.X))

/- The source's `φ(a)` is the image of the constant polynomial `C a`. -/
theorem change_equation_multiply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R[X] →+* S) (t : S) (ht : φ.IsIntegralElem t) :
    ∃ ℓ : ℕ, ∀ a : R,
      (changeEquationMap φ a).IsIntegralElem
        (φ (Polynomial.C a) ^ ℓ * t) := by
  obtain ⟨p, hp, hp0⟩ := ht
  let d := p.natDegree
  let ℓ := ∑ i ∈ Finset.range (d + 1), (p.coeff i).natDegree

  have hcoeff_bound : ∀ i, i ≤ d → (p.coeff i).natDegree ≤ ℓ := by
    intro i hi
    dsimp [ℓ]
    exact Finset.single_le_sum (s := Finset.range (d + 1)) (a := i)
      (f := fun j ↦ (p.coeff j).natDegree)
      (fun j _ ↦ Nat.zero_le _) (by simp [hi])

  have hhom : ∀ (a : R) (f : R[X]) (L : ℕ),
      f.natDegree ≤ L →
      changeEquationMap φ a
          (MvPolynomial.eval₂ (Polynomial.C : R →+* R[X])
            ![Polynomial.X, Polynomial.C a] (f.homogenize L)) =
        φ (Polynomial.C a) ^ L * φ f := by
    intro a f L hf
    apply Polynomial.induction_with_natDegree_le
      (fun f ↦ changeEquationMap φ a
          (MvPolynomial.eval₂ (Polynomial.C : R →+* R[X])
            ![Polynomial.X, Polynomial.C a] (f.homogenize L)) =
        φ (Polynomial.C a) ^ L * φ f) L
    · simp
    · intro n r _hr hn
      rw [Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow hn]
      simp [changeEquationMap, Polynomial.eval₂_pow, Polynomial.eval₂_C, mul_pow]
      calc
        φ (Polynomial.C r) *
              (φ (Polynomial.C a) ^ n * φ Polynomial.X ^ n *
                φ (Polynomial.C a) ^ (L - n)) =
            φ (Polynomial.C r) *
              (φ (Polynomial.C a) ^ n * φ (Polynomial.C a) ^ (L - n) *
                φ Polynomial.X ^ n) := by
                  simp [mul_assoc, mul_comm]
        _ = φ (Polynomial.C r) *
              (φ (Polynomial.C a) ^ L * φ Polynomial.X ^ n) := by
                rw [← pow_add, Nat.add_sub_of_le hn]
        _ = φ (Polynomial.C a) ^ L *
              (φ (Polynomial.C r) * φ Polynomial.X ^ n) := by
                  simp [mul_assoc, mul_comm]
    · intro f g _hfg _hg hf hg
      rw [Polynomial.homogenize_add, MvPolynomial.eval₂_add]
      simp only [map_add]
      rw [hf, hg]
      simp [mul_add]
    · exact hf

  refine ⟨ℓ, ?_⟩
  intro a
  let b : ℕ → R[X] := fun i ↦
    MvPolynomial.eval₂ (Polynomial.C : R →+* R[X])
      ![Polynomial.X, Polynomial.C a]
      ((p.coeff i).homogenize (ℓ * (d - i)))
  let q : (R[X])[X] :=
    Polynomial.X ^ d +
      ∑ i ∈ Finset.range d, Polynomial.C (b i) * Polynomial.X ^ i

  have hb : ∀ i, i < d →
      changeEquationMap φ a (b i) =
        φ (Polynomial.C a) ^ (ℓ * (d - i)) * φ (p.coeff i) := by
    intro i hi
    dsimp [b]
    exact hhom a (p.coeff i) (ℓ * (d - i))
      ((hcoeff_bound i (Nat.le_of_lt hi)).trans
        (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hi)))

  have hlow :
      (∑ i ∈ Finset.range d,
        Polynomial.C (b i) * Polynomial.X ^ i : (R[X])[X]).degree < d := by
    refine (Polynomial.degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff <| WithBot.bot_lt_coe d).2 ?_
    intro i hi
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
      (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hi))

  have hq : q.Monic := by
    dsimp [q]
    exact Polynomial.monic_X_pow_add hlow

  let c : S := φ (Polynomial.C a)
  have hterm : ∀ i, i < d →
      changeEquationMap φ a (b i) * (c ^ ℓ * t) ^ i =
        c ^ (ℓ * d) * (φ (p.coeff i) * t ^ i) := by
    intro i hi
    rw [hb i hi, mul_pow, ← pow_mul]
    have hexp : i * ℓ + (d - i) * ℓ = ℓ * d := by
      rw [← Nat.add_mul, add_comm i, Nat.sub_add_cancel (Nat.le_of_lt hi),
        Nat.mul_comm]
    calc
      φ (Polynomial.C a) ^ (ℓ * (d - i)) * φ (p.coeff i) *
            (c ^ (ℓ * i) * t ^ i) =
          t ^ i * (φ (p.coeff i) *
            (c ^ (i * ℓ) * c ^ ((d - i) * ℓ))) := by
              simp only [c, mul_assoc, mul_comm, mul_left_comm]
      _ = t ^ i * (φ (p.coeff i) * c ^ (ℓ * d)) := by
            rw [← pow_add, hexp]
      _ = c ^ (ℓ * d) * (φ (p.coeff i) * t ^ i) := by
            simp only [mul_assoc, mul_comm]

  have hlead : (c ^ ℓ * t) ^ d =
      c ^ (ℓ * d) * (φ (p.coeff d) * t ^ d) := by
    rw [hp.coeff_natDegree]
    simp [mul_pow, ← pow_mul]

  have hp_sum :
      ∑ i ∈ Finset.range (d + 1), φ (p.coeff i) * t ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hp0

  have hq0 :
      Polynomial.eval₂ (changeEquationMap φ a) (c ^ ℓ * t) q = 0 := by
    dsimp [q]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow]
    have hterms :
        (∑ i ∈ Finset.range d,
          changeEquationMap φ a (b i) * (c ^ ℓ * t) ^ i) =
          c ^ (ℓ * d) *
            (∑ i ∈ Finset.range d, φ (p.coeff i) * t ^ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i (Finset.mem_range.mp hi)
    rw [hterms, hlead]
    calc
      c ^ (ℓ * d) * (φ (p.coeff d) * t ^ d) +
            c ^ (ℓ * d) *
              (∑ i ∈ Finset.range d, φ (p.coeff i) * t ^ i) =
          c ^ (ℓ * d) *
            ((∑ i ∈ Finset.range d, φ (p.coeff i) * t ^ i) +
              φ (p.coeff d) * t ^ d) := by
                simp [mul_add, add_comm]
      _ = 0 := by
        rw [← Finset.sum_range_succ, hp_sum, mul_zero]

  exact ⟨q, hq, hq0⟩

/-! ## Making an integral equation less trivial -/

/- For `1 ≤ i ≤ n`, this is the closed form of the recursively defined
   coefficient `u_i = u_{i+1} t + φ(a_i)`.  It also makes sense for all
   natural `i`, with an empty sum when `i > n`. -/
def integralRelationU
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (a : ℕ → R) (n i : ℕ) : S :=
  ∑ j ∈ Finset.Icc i n, φ (a j) * t ^ (j - i)

/- The finite coefficient set `(φ(a_0), ..., φ(a_n))`. -/
def integralRelationCoefficientSet
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : ℕ → R) (n : ℕ) : Set S :=
  {x | ∃ i, i ≤ n ∧ x = φ (a i)}

/- The set of the recursively defined elements `u_n, ..., u_1`. -/
def integralRelationUSet
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (a : ℕ → R) (n : ℕ) : Set S :=
  {x | ∃ i, 1 ≤ i ∧ i ≤ n ∧ x = integralRelationU φ t a n i}

theorem make_integral_less_trivial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (a : ℕ → R) (n : ℕ)
    (hrel : ∑ i ∈ Finset.range (n + 1), φ (a i) * t ^ i = 0) :
    (∀ i, 1 ≤ i → i ≤ n →
      φ.IsIntegralElem (integralRelationU φ t a n i) ∧
        φ.IsIntegralElem (integralRelationU φ t a n i * t)) ∧
      Ideal.span (integralRelationCoefficientSet φ a n) =
        Ideal.span (integralRelationUSet φ t a n) := by
  have hrec : ∀ i, 1 ≤ i → i ≤ n →
      integralRelationU φ t a n i * t + φ (a (i - 1)) =
        integralRelationU φ t a n (i - 1) := by
    intro i hi hin
    have hset : Finset.Icc (i - 1) n = insert (i - 1) (Finset.Icc i n) := by
      rw [← Nat.sub_add_cancel hi]
      exact (Finset.insert_Icc_succ_left_eq_Icc (by omega)).symm
    simp only [integralRelationU, Finset.sum_mul]
    rw [hset, Finset.sum_insert]
    · simp only [Nat.sub_self, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hji : i ≤ j := (Finset.mem_Icc.mp hj).1
      have hexp : j - (i - 1) = (j - i) + 1 := by omega
      rw [hexp, pow_succ, mul_assoc]
    · simp only [Finset.mem_Icc]
      omega

  have hsplit : ∀ i : ℕ, i ≤ n →
      (∑ j ∈ Finset.range (n + 1), φ (a j) * t ^ j) =
        (∑ j ∈ Finset.range i, φ (a j) * t ^ j) +
          (∑ j ∈ Finset.Icc i n, φ (a j) * t ^ j) := by
    intro i hi
    have hdis : Disjoint (Finset.range i) (Finset.Icc i n) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_range] at hj1
      exact (Nat.not_lt_of_ge (Finset.mem_Icc.mp hj2).1) hj1
    have hun : Finset.range i ∪ Finset.Icc i n = Finset.range (n + 1) := by
      ext j
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [← hun, Finset.sum_union hdis]

  have htail_sum : ∀ i : ℕ, i ≤ n →
      (∑ j ∈ Finset.Icc i n, φ (a j) * t ^ j) =
        integralRelationU φ t a n i * t ^ i := by
    intro i hi
    simp only [integralRelationU]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : i ≤ j := (Finset.mem_Icc.mp hj).1
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hji]

  have htail : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (∑ j ∈ Finset.range i, φ (a j) * t ^ j) +
          integralRelationU φ t a n i * t ^ i = 0 := by
    intro i hi hin
    calc
      (∑ j ∈ Finset.range i, φ (a j) * t ^ j) +
          integralRelationU φ t a n i * t ^ i =
          (∑ j ∈ Finset.range i, φ (a j) * t ^ j) +
            (∑ j ∈ Finset.Icc i n, φ (a j) * t ^ j) := by
              rw [htail_sum i hin]
      _ = ∑ j ∈ Finset.range (n + 1), φ (a j) * t ^ j :=
        (hsplit i hin).symm
      _ = 0 := hrel

  let _ : Algebra R S := φ.toAlgebra
  let A := integralClosure R S
  let _ : Algebra A S := A.toAlgebra
  let _ : IsScalarTower R A S := Subalgebra.isScalarTower_mid A
  have hprod : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      φ.IsIntegralElem (integralRelationU φ t a n k) →
        φ.IsIntegralElem (integralRelationU φ t a n k * t) := by
    intro k hk1 hkn hUk
    let c : A := ⟨integralRelationU φ t a n k, hUk⟩
    let b : ℕ → A := fun j => ⟨φ (a j), φ.isIntegralElem_map⟩
    let q : A[X] :=
      (∑ j ∈ Finset.range k, Polynomial.C (b j) * Polynomial.X ^ j) +
        Polynomial.C c * Polynomial.X ^ k
    have hq_eval : q.eval₂ (algebraMap A S) t = 0 := by
      simp only [q, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      simpa [c, b, RingHom.algebraMap_toAlgebra] using htail k hk1 hkn
    by_cases hc : c = 0
    · have hzero : integralRelationU φ t a n k = 0 := congrArg Subtype.val hc
      rw [hzero, zero_mul]
      exact φ.isIntegralElem_zero
    · have hq_le : q.natDegree ≤ k := by
        apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro m hm
        have hmk : ¬ m < k := Nat.not_lt_of_ge (Nat.le_of_lt hm)
        have hne : m ≠ k := Nat.ne_of_gt hm
        simp [q, hmk, hne]
      have hq_coeff : q.coeff k = c := by simp [q]
      have hq_nat : q.natDegree = k :=
        Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hq_le
          (by simp [hq_coeff, hc])
      have hq_lc : q.leadingCoeff = c := by
        simp [Polynomial.leadingCoeff, hq_nat, hq_coeff]
      have hi := (algebraMap A S).isIntegralElem_leadingCoeff_mul q t hq_eval
      rw [hq_lc] at hi
      have hi' := isIntegral_trans (R := R) (A := A) (B := S)
        (integralRelationU φ t a n k * t) hi
      change φ.IsIntegralElem (integralRelationU φ t a n k * t) at hi'
      exact hi'

  have hall : ∀ i, 1 ≤ i → i ≤ n →
      φ.IsIntegralElem (integralRelationU φ t a n i) ∧
        φ.IsIntegralElem (integralRelationU φ t a n i * t) := by
    intro i hi1 hin
    induction hdiff : n - i using Nat.strong_induction_on generalizing i with
    | h d ih =>
        by_cases hieq : i = n
        · subst i
          have hUn : integralRelationU φ t a n n = φ (a n) := by
            simp [integralRelationU]
          have hU : φ.IsIntegralElem (integralRelationU φ t a n n) := by
            rw [hUn]
            exact φ.isIntegralElem_map
          exact ⟨hU, hprod n (by omega) (by omega) hU⟩
        · have hilt : i < n := lt_of_le_of_ne hin hieq
          have hsucc : 1 ≤ i + 1 := by omega
          have hsle : i + 1 ≤ n := by omega
          have hdiff' : n - (i + 1) < d := by omega
          have hs := ih (n - (i + 1)) hdiff' (i + 1) hsucc hsle (by rfl)
          have hprev : φ.IsIntegralElem (integralRelationU φ t a n (i + 1) * t) := hs.2
          have hcoeff : φ.IsIntegralElem (φ (a i)) := φ.isIntegralElem_map
          have hrec' : integralRelationU φ t a n (i + 1) * t + φ (a i) =
              integralRelationU φ t a n i := by
            simpa using hrec (i + 1) hsucc hsle
          have hcur : φ.IsIntegralElem (integralRelationU φ t a n i) := by
            rw [← hrec']
            exact hprev.add φ hcoeff
          exact ⟨hcur, hprod i hi1 hin hcur⟩

  have hU0 : integralRelationU φ t a n 0 = 0 := by
    rw [integralRelationU]
    simpa [Nat.range_succ_eq_Icc_zero, Nat.sub_zero] using hrel
  have hU_mem_coeff : ∀ i, 1 ≤ i → i ≤ n →
      integralRelationU φ t a n i ∈
        Ideal.span (integralRelationCoefficientSet φ a n) := by
    intro i hi1 hin
    simp only [integralRelationU]
    apply (Ideal.span (integralRelationCoefficientSet φ a n)).sum_mem
    intro j hj
    exact (Ideal.span (integralRelationCoefficientSet φ a n)).mul_mem_right _
      (Ideal.subset_span ⟨j, (Finset.mem_Icc.mp hj).2, rfl⟩)
  have hcoeff_mem_U : ∀ i, i ≤ n →
      φ (a i) ∈ Ideal.span (integralRelationUSet φ t a n) := by
    intro i hin
    by_cases hi0 : i = 0
    · subst i
      by_cases hn0 : n = 0
      · subst n
        have hUn0 : integralRelationU φ t a 0 0 = φ (a 0) := by
          simp [integralRelationU]
        rw [← hUn0, hU0]
        exact (Ideal.span (integralRelationUSet φ t a 0)).zero_mem
      · have hn1 : 1 ≤ n := by omega
        have h := hrec 1 (by omega) hn1
        rw [hU0] at h
        have heq : φ (a 0) = 0 - integralRelationU φ t a n 1 * t :=
          (eq_sub_iff_add_eq).2 (by simpa [add_comm] using h)
        rw [heq]
        simpa using (Ideal.span (integralRelationUSet φ t a n)).neg_mem
          ((Ideal.span (integralRelationUSet φ t a n)).mul_mem_right t
            (Ideal.subset_span ⟨1, by omega, hn1, rfl⟩))
    · have hi1 : 1 ≤ i := by omega
      by_cases hieq : i = n
      · subst i
        have hUn : integralRelationU φ t a n n = φ (a n) := by
          simp [integralRelationU]
        rw [← hUn]
        exact Ideal.subset_span ⟨n, by omega, by omega, rfl⟩
      · have hilt : i < n := lt_of_le_of_ne hin hieq
        have hnext : 1 ≤ i + 1 := by omega
        have hnextle : i + 1 ≤ n := by omega
        have h := hrec (i + 1) hnext hnextle
        have heq : φ (a i) =
            integralRelationU φ t a n i -
              integralRelationU φ t a n (i + 1) * t :=
          (eq_sub_iff_add_eq).2 (by simpa [add_comm] using h)
        rw [heq]
        exact (Ideal.span (integralRelationUSet φ t a n)).sub_mem
          (Ideal.subset_span ⟨i, hi1, hin, rfl⟩)
          ((Ideal.span (integralRelationUSet φ t a n)).mul_mem_right t
            (Ideal.subset_span ⟨i + 1, hnext, hnextle, rfl⟩))
  have hspan1 :
      Ideal.span (integralRelationCoefficientSet φ a n) ≤
        Ideal.span (integralRelationUSet φ t a n) := by
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, hin, rfl⟩
    exact hcoeff_mem_U i hin
  have hspan2 :
      Ideal.span (integralRelationUSet φ t a n) ≤
        Ideal.span (integralRelationCoefficientSet φ a n) := by
    refine Ideal.span_le.2 ?_
    rintro x ⟨i, hi1, hin, rfl⟩
    exact hU_mem_coeff i hi1 hin
  exact ⟨hall, le_antisymm hspan1 hspan2⟩

theorem make_integral_not_in_ideal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (a : ℕ → R) (n : ℕ)
    (hrel : ∑ i ∈ Finset.range (n + 1), φ (a i) * t ^ i = 0)
    (J : Ideal S) (hnot : ∃ i, i ≤ n ∧ φ (a i) ∉ J) :
    ∃ u : S, u ∉ J ∧ φ.IsIntegralElem u ∧ φ.IsIntegralElem (u * t) := by
  have hless := make_integral_less_trivial φ t a n hrel
  obtain ⟨i, hin, hni⟩ := hnot
  have hex : ∃ i, 1 ≤ i ∧ i ≤ n ∧ integralRelationU φ t a n i ∉ J := by
    by_contra! hU
    have hUle : Ideal.span (integralRelationUSet φ t a n) ≤ J := by
      refine Ideal.span_le.2 ?_
      rintro x ⟨k, hk1, hkn, rfl⟩
      exact hU k hk1 hkn
    have hCLe : Ideal.span (integralRelationCoefficientSet φ a n) ≤ J := by
      rw [hless.2]
      exact hUle
    exact hni (hCLe (Ideal.subset_span ⟨i, hin, rfl⟩))
  obtain ⟨i, hi1, hin, hUi⟩ := hex
  refine ⟨integralRelationU φ t a n i, hUi, ?_, ?_⟩
  · exact (hless.1 i hi1 hin).1
  · exact (hless.1 i hi1 hin).2

end

end Formalization.Books.Obsolete.Unit05
