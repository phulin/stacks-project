import Formalization.Books.Models.Unit02.LinearAlgebra
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Numerical types

Formal statements from Chapter 3 of *Semistable Reduction*.  The source
indexes its data by `1, ..., n`; this file uses `Fin n`, with the positivity
of `n` recorded in the structure.
-/

noncomputable section

open scoped BigOperators

namespace Formalization.Books.Models.Unit03

/-! The combinatorial data attached to a special fibre. -/
structure NumericalType where
  n : ℕ
  hn : 1 ≤ n
  m : Fin n → ℤ
  a : Matrix (Fin n) (Fin n) ℤ
  w : Fin n → ℤ
  g : Fin n → ℤ
  m_pos : ∀ i, 0 < m i
  w_pos : ∀ i, 0 < w i
  g_nonneg : ∀ i, 0 ≤ g i
  a_symmetric : ∀ i j, a i j = a j i
  a_offdiag_nonneg : ∀ ⦃i j⦄, i ≠ j → 0 ≤ a i j
  connected : ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
    ∀ ⦃i j⦄, i ∈ I → j ∉ I → a i j = 0
  row_sum : ∀ i, (Finset.univ : Finset (Fin n)).sum (fun j => a i j * m j) = 0
  w_dvd : ∀ i j, w i ∣ a i j

/-! The equivalence relation obtained by reordering all indices. -/
def EquivalentNumericalType (T T' : NumericalType) : Prop :=
  ∃ e : Fin T.n ≃ Fin T'.n,
    (∀ i, T.m i = T'.m (e i)) ∧
      (∀ i j, T.a i j = T'.a (e i) (e j)) ∧
        (∀ i, T.w i = T'.w (e i)) ∧
          ∀ i, T.g i = T'.g (e i)

/-! A canonical index used when a one-component type is discussed. -/
def firstIndex (T : NumericalType) : Fin T.n :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one T.hn⟩

/-! The rational expression whose integrality is the first lemma of the section. -/
def genusExpression (T : NumericalType) : ℚ :=
  1 + (Finset.univ : Finset (Fin T.n)).sum (fun i =>
    (T.m i : ℚ) * ((T.w i : ℚ) * ((T.g i : ℚ) - 1) - (T.a i i : ℚ) / 2))

/-! The numerator form gives a canonical integer genus once the parity lemma is known. -/
def genusNumerator (T : NumericalType) : ℤ :=
  2 + (Finset.univ : Finset (Fin T.n)).sum (fun i =>
    2 * T.m i * T.w i * (T.g i - 1) - T.m i * T.a i i)

def genus (T : NumericalType) : ℤ :=
  genusNumerator T / 2

/-! The contribution of one component to the rational genus expression. -/
def genusContribution (T : NumericalType) (i : Fin T.n) : ℚ :=
  (T.m i : ℚ) * ((T.w i : ℚ) * ((T.g i : ℚ) - 1) - (T.a i i : ℚ) / 2)

def IsOfGenus (T : NumericalType) (genusValue : ℤ) : Prop :=
  genus T = genusValue

/-! The parity statement underlying the integrality of the genus. -/
theorem genus_diagonal_parity (T : NumericalType) :
    Even ((Finset.univ : Finset (Fin T.n)).sum (fun i => T.a i i * T.m i)) := by
  classical
  refine ZMod.intCast_eq_zero_iff_even.mp ?_
  have hrow : ∀ i, ∑ j, (T.m i : ZMod 2) * ((T.a i j : ZMod 2) * (T.m j : ZMod 2)) = 0 := by
    intro i
    have h := T.row_sum i
    have h' : ∑ j, ((T.a i j * T.m j : ℤ) : ZMod 2) = 0 := by
      simpa only [Int.cast_sum, Int.cast_zero] using congrArg (fun x : ℤ => (x : ZMod 2)) h
    simpa [Finset.mul_sum, ← Int.cast_mul] using
      congrArg (fun x : ZMod 2 => (T.m i : ZMod 2) * x) h'
  have hsum : (Finset.univ : Finset (Fin T.n)).sum (fun i =>
      (Finset.univ : Finset (Fin T.n)).sum (fun j =>
        (T.m i : ZMod 2) * (T.a i j : ZMod 2) * (T.m j : ZMod 2))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simpa [mul_assoc] using hrow i
  have hdouble : ((Finset.univ.product Finset.univ : Finset (Fin T.n × Fin T.n)).sum
      (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2))) = 0 := by
    change ((Finset.univ ×ˢ Finset.univ).sum
      (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2))) = 0
    rw [Finset.sum_product]
    convert hsum using 1
  let s : Finset (Fin T.n × Fin T.n) :=
    (Finset.univ.product Finset.univ).filter (fun p => p.1 ≠ p.2)
  have hoff : s.sum (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2)) = 0 := by
    apply Finset.sum_involution (s := s)
      (f := fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2))
      (fun p _ => (p.2, p.1))
    · intro p hp
      rw [T.a_symmetric p.1 p.2]
      ring_nf
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [htwo, mul_zero]
    · intro p hp hne heq
      have hp' : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      apply hp'
      have h : p.2 = p.1 := by
        simpa using congrArg Prod.fst heq
      exact h.symm
    · intro p hp
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simp
      · exact (Finset.mem_filter.mp hp).2.symm
    · intro p hp
      rfl
  let d : Finset (Fin T.n × Fin T.n) :=
    (Finset.univ.product Finset.univ).filter (fun p => ¬ p.1 ≠ p.2)
  have hdiag : d.sum (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2)) =
      (Finset.univ : Finset (Fin T.n)).sum (fun i =>
        (T.m i : ZMod 2) * (T.a i i : ZMod 2) * (T.m i : ZMod 2)) := by
    apply Finset.sum_bij (s := d) (t := (Finset.univ : Finset (Fin T.n)))
      (f := fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2))
      (g := fun i => (T.m i : ZMod 2) * (T.a i i : ZMod 2) * (T.m i : ZMod 2))
      (fun p _ => p.1)
    · intro p hp
      simp
    · intro p₁ hp₁ p₂ hp₂ heq
      have h₁ : p₁.1 = p₁.2 := Classical.not_not.mp (Finset.mem_filter.mp hp₁).2
      have h₂ : p₂.1 = p₂.2 := Classical.not_not.mp (Finset.mem_filter.mp hp₂).2
      apply Prod.ext heq
      exact h₁.symm.trans (heq.trans h₂)
    · intro i hi
      refine ⟨(i, i), ?_, rfl⟩
      simp [d]
    · intro p hp
      have heq : p.1 = p.2 := Classical.not_not.mp (Finset.mem_filter.mp hp).2
      simp [heq]
  have hpartition :
      (Finset.univ.product Finset.univ).sum
          (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2)) =
        s.sum (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2)) +
        d.sum (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2)) := by
    dsimp [s, d]
    rw [Finset.sum_filter_add_sum_filter_not]
  have hdiag_zero : d.sum (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2)) = 0 := by
    have hzero :
        s.sum (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2)) +
          d.sum (fun p => (T.m p.1 : ZMod 2) * (T.a p.1 p.2 : ZMod 2) * (T.m p.2 : ZMod 2)) = 0 := by
      rw [← hpartition, hdouble]
    rw [hoff, zero_add] at hzero
    exact hzero
  rw [Int.cast_sum]
  rw [hdiag] at hdiag_zero
  have hsq : (Finset.univ : Finset (Fin T.n)).sum (fun i =>
      (T.m i : ZMod 2) * (T.a i i : ZMod 2) * (T.m i : ZMod 2)) =
      (Finset.univ : Finset (Fin T.n)).sum (fun i =>
        (T.a i i : ZMod 2) * (T.m i : ZMod 2)) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hm : Even (T.m i)
    · have hc : (T.m i : ZMod 2) = 0 := Even.intCast_zmod_two hm
      simp [hc]
    · have hc : (T.m i : ZMod 2) = 1 :=
        Odd.intCast_zmod_two (Int.not_even_iff_odd.mp hm)
      simp [hc]
  rw [hsq] at hdiag_zero
  simpa only [Int.cast_mul] using hdiag_zero

private theorem genusNumerator_even (T : NumericalType) : Even (genusNumerator T) := by
  unfold genusNumerator
  rw [Finset.sum_sub_distrib]
  have hfirst : Even ((Finset.univ : Finset (Fin T.n)).sum (fun i =>
      2 * T.m i * T.w i * (T.g i - 1))) := by
    induction (Finset.univ : Finset (Fin T.n)) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hiEven : Even (2 * T.m i * T.w i * (T.g i - 1)) := by
        simp [mul_assoc]
      exact hiEven.add ih
  have hdiag : Even ((Finset.univ : Finset (Fin T.n)).sum (fun i => T.m i * T.a i i)) := by
    simpa [mul_comm] using genus_diagonal_parity T
  have htwo : Even (2 : ℤ) := by
    exact ⟨1, by ring⟩
  exact htwo.add (hfirst.sub hdiag)

theorem genus_integral (T : NumericalType) :
    ∃ genusValue : ℤ, (genusValue : ℚ) = genusExpression T := by
  have hN := genusNumerator_even T
  rcases hN with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hdiv : genusNumerator T / 2 = k := by
    rw [hk]
    omega
  have hkgenus : k = genus T := by
    dsimp [genus]
    exact hdiv.symm
  rw [hkgenus, genus, genusNumerator, genusExpression]
  have hquot :
      (2 + (Finset.univ : Finset (Fin T.n)).sum
        (fun i => 2 * T.m i * T.w i * (T.g i - 1) - T.m i * T.a i i)) / 2 = k := by
    rw [show 2 + (Finset.univ : Finset (Fin T.n)).sum
      (fun i => 2 * T.m i * T.w i * (T.g i - 1) - T.m i * T.a i i) = genusNumerator T by rfl, hk]
    omega
  rw [hquot]
  have hkq := congrArg (fun z : ℤ => (z : ℚ)) hk
  rw [genusNumerator] at hkq
  push_cast at hkq
  field_simp at hkq ⊢
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  linarith

theorem genus_formula (T : NumericalType) :
    (genus T : ℚ) = genusExpression T := by
  have hN := genusNumerator_even T
  rcases hN with ⟨k, hk⟩
  have hdiv : genusNumerator T / 2 = k := by
    rw [hk]
    omega
  have hkgenus : k = genus T := by
    dsimp [genus]
    exact hdiv.symm
  rw [← hkgenus, genusExpression]
  have hkq := congrArg (fun z : ℤ => (z : ℚ)) hk
  rw [genusNumerator] at hkq
  push_cast at hkq
  field_simp at hkq ⊢
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  linarith

/-! A numerical type can have negative genus in the irreducible case. -/
theorem exists_negative_genus_numerical_type :
    ∃ T : NumericalType, genus T < 0 := by
  refine ⟨{n := 1, hn := by norm_num, m := fun _ => 2, a := fun _ _ => 0, w := fun _ => 1, g := fun _ => 0, m_pos := by intro i; norm_num, w_pos := by intro i; norm_num, g_nonneg := by intro i; norm_num, a_symmetric := by intro i j; rfl, a_offdiag_nonneg := by intro i j h; norm_num, connected := by intro h; rcases h with ⟨I, hI, hne, hcross⟩; apply hne; apply Set.eq_univ_of_forall; intro i; rcases hI with ⟨x, hx⟩; simpa [Subsingleton.elim i x] using hx, row_sum := by intro i; simp, w_dvd := by intro i j; simp}, by norm_num [genus, genusNumerator]⟩

/-! The complete one-index classification. -/
theorem irreducible_numerical_type (T : NumericalType) (genusValue : ℤ)
    (hn : T.n = 1) (hgenus : IsOfGenus T genusValue) :
    (∀ i, T.a i i = 0) ∧
      genusValue = 1 + T.m (firstIndex T) * T.w (firstIndex T) *
        (T.g (firstIndex T) - 1) ∧
      (genusValue < 0 →
        T.g (firstIndex T) = 0 ∧
          T.m (firstIndex T) * T.w (firstIndex T) = 1 - genusValue ∧
            Set.Finite {U : NumericalType | U.n = 1 ∧ IsOfGenus U genusValue}) ∧
      (genusValue = 0 →
        T.m (firstIndex T) = 1 ∧ T.w (firstIndex T) = 1 ∧
          T.g (firstIndex T) = 0) ∧
      (genusValue = 1 → T.g (firstIndex T) = 1) ∧
      (genusValue > 1 →
        T.g (firstIndex T) > 1 ∧
          T.m (firstIndex T) * T.w (firstIndex T) *
              (T.g (firstIndex T) - 1) = genusValue - 1 ∧
            Set.Finite {U : NumericalType | U.n = 1 ∧ IsOfGenus U genusValue}) := by
  classical
  have hindex_one : ∀ (U : NumericalType), U.n = 1 →
      ∀ j : Fin U.n, j = firstIndex U := by
    intro U hUn j
    apply Fin.ext
    have hj : j.val = 0 := by omega
    simp [firstIndex, hj]
  have hdiag_one : ∀ (U : NumericalType), U.n = 1 →
      ∀ j : Fin U.n, U.a j j = 0 := by
    intro U hUn j
    have hrow : U.a j j * U.m j = 0 := by
      calc
        U.a j j * U.m j =
            (Finset.univ : Finset (Fin U.n)).sum (fun k => U.a j k * U.m k) := by
              symm
              apply Finset.sum_eq_single j
              · intro b hb hbi
                exact False.elim (hbi ((hindex_one U hUn b).trans
                  (hindex_one U hUn j).symm))
              · simp
        _ = 0 := U.row_sum j
    nlinarith [U.m_pos j]
  have hone_formula : ∀ (U : NumericalType), U.n = 1 →
      genus U = 1 + U.m (firstIndex U) * U.w (firstIndex U) *
        (U.g (firstIndex U) - 1) := by
    intro U hUn
    unfold genus genusNumerator
    have hsum : (Finset.univ : Finset (Fin U.n)).sum
        (fun j => 2 * U.m j * U.w j * (U.g j - 1) - U.m j * U.a j j) =
        2 * U.m (firstIndex U) * U.w (firstIndex U) *
            (U.g (firstIndex U) - 1) -
          U.m (firstIndex U) * U.a (firstIndex U) (firstIndex U) := by
      apply Finset.sum_eq_single (firstIndex U)
      · intro b hb hbi
        exact False.elim (hbi ((hindex_one U hUn b).trans
          (hindex_one U hUn (firstIndex U)).symm))
      · simp
    rw [hsum]
    simp only [hdiag_one U hUn (firstIndex U), mul_zero, sub_zero]
    rw [show 2 + 2 * U.m (firstIndex U) * U.w (firstIndex U) *
        (U.g (firstIndex U) - 1) =
        2 * (1 + U.m (firstIndex U) * U.w (firstIndex U) *
          (U.g (firstIndex U) - 1) : ℤ) by ring]
    simp
  have hdiag : ∀ j : Fin T.n, T.a j j = 0 := hdiag_one T hn
  have hformula := hone_formula T hn
  have hgv : genusValue = 1 + T.m (firstIndex T) * T.w (firstIndex T) *
      (T.g (firstIndex T) - 1) := by
    rw [← hgenus]
    exact hformula
  let S : Set NumericalType := {U : NumericalType |
    U.n = 1 ∧ IsOfGenus U genusValue}
  let f : NumericalType → ℤ × (ℤ × ℤ) := fun U =>
    (U.m (firstIndex U), (U.w (firstIndex U), U.g (firstIndex U)))
  have hstruct : ∀ (U V : NumericalType),
      U.n = 1 → V.n = 1 →
      U.m (firstIndex U) = V.m (firstIndex V) →
      U.w (firstIndex U) = V.w (firstIndex V) →
      U.g (firstIndex U) = V.g (firstIndex V) →
      U = V := by
    intro U V hUn hVn hm hw hg
    cases U with
    | mk n hn m a w g mpos wpos gnonneg asym off conn row dvd =>
      cases V with
      | mk n' hn' m' a' w' g' mpos' wpos' gnonneg' asym' off' conn' row' dvd' =>
        simp only at hUn hVn
        cases hUn
        cases hVn
        simp only [firstIndex] at hm hw hg
        have hzero (A : Matrix (Fin 1) (Fin 1) ℤ) (v : Fin 1 → ℤ)
            (hrow : ∀ i, ∑ j, A i j * v j = 0)
            (hv : 0 < v (⟨0, by omega⟩ : Fin 1)) :
            A (⟨0, by omega⟩ : Fin 1) (⟨0, by omega⟩ : Fin 1) = 0 := by
          have h := hrow (⟨0, by omega⟩ : Fin 1)
          simp at h
          rcases h with h | h
          · exact h
          · exact False.elim ((ne_of_gt hv) h)
        have hzero' := hzero a' m' row' (mpos' (⟨0, by omega⟩ : Fin 1))
        have hzero₁ := hzero a m row (mpos (⟨0, by omega⟩ : Fin 1))
        congr
        · funext x
          have hx : x = (⟨0, by omega⟩ : Fin 1) := Subsingleton.elim _ _
          simpa [hx] using hm
        · funext x y
          have hx : x = (⟨0, by omega⟩ : Fin 1) := Subsingleton.elim _ _
          have hy : y = (⟨0, by omega⟩ : Fin 1) := Subsingleton.elim _ _
          subst x
          subst y
          exact hzero₁.trans hzero'.symm
        · funext x
          have hx : x = (⟨0, by omega⟩ : Fin 1) := Subsingleton.elim _ _
          simpa [hx] using hw
        · funext x
          have hx : x = (⟨0, by omega⟩ : Fin 1) := Subsingleton.elim _ _
          simpa [hx] using hg
  have hfinite_of_bounds : ∀ Bm Bw Bg : ℤ,
      (∀ U ∈ S, 1 ≤ U.m (firstIndex U) ∧ U.m (firstIndex U) ≤ Bm ∧
        1 ≤ U.w (firstIndex U) ∧ U.w (firstIndex U) ≤ Bw ∧
        0 ≤ U.g (firstIndex U) ∧ U.g (firstIndex U) ≤ Bg) → S.Finite := by
    intro Bm Bw Bg hbound
    have himg : f '' S ⊆ Set.Icc (1 : ℤ) Bm ×ˢ
        (Set.Icc (1 : ℤ) Bw ×ˢ Set.Icc (0 : ℤ) Bg) := by
      rintro p ⟨U, hU, rfl⟩
      rcases hbound U hU with ⟨hm₁, hm₂, hw₁, hw₂, hg₁, hg₂⟩
      exact ⟨⟨hm₁, hm₂⟩, ⟨⟨hw₁, hw₂⟩, ⟨hg₁, hg₂⟩⟩⟩
    have himgfin : (f '' S).Finite :=
      (Set.finite_Icc (1 : ℤ) Bm).prod
        ((Set.finite_Icc (1 : ℤ) Bw).prod (Set.finite_Icc (0 : ℤ) Bg)) |>.subset himg
    apply himgfin.of_finite_image
    intro U hU V hV hUV
    apply hstruct U V hU.1 hV.1
    · exact congrArg Prod.fst hUV
    · exact congrArg (fun p => p.2.1) hUV
    · exact congrArg (fun p => p.2.2) hUV
  refine ⟨hdiag, hgv, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hneg
    have hmpos := T.m_pos (firstIndex T)
    have hwpos := T.w_pos (firstIndex T)
    have hxy : 0 < T.m (firstIndex T) * T.w (firstIndex T) :=
      mul_pos hmpos hwpos
    have hgnonneg := T.g_nonneg (firstIndex T)
    have hgzero : T.g (firstIndex T) = 0 := by
      by_contra h
      have hgone : 1 ≤ T.g (firstIndex T) := by omega
      have hterm : 0 ≤ T.m (firstIndex T) * T.w (firstIndex T) *
          (T.g (firstIndex T) - 1) :=
        mul_nonneg (le_of_lt hxy) (by omega)
      nlinarith [hgv]
    have hprod : T.m (firstIndex T) * T.w (firstIndex T) = 1 - genusValue := by
      rw [hgzero] at hgv
      omega
    have hfinite : S.Finite := by
      apply hfinite_of_bounds (1 - genusValue) (1 - genusValue) 0
      intro U hU
      rcases hU with ⟨hUn, hUg⟩
      have hUgenus := hone_formula U hUn
      have hUgv : genusValue = 1 + U.m (firstIndex U) * U.w (firstIndex U) *
          (U.g (firstIndex U) - 1) := by
        rw [← hUg]
        exact hUgenus
      have hUxy : 0 < U.m (firstIndex U) * U.w (firstIndex U) :=
        mul_pos (U.m_pos _) (U.w_pos _)
      have hUgnonneg := U.g_nonneg (firstIndex U)
      have hUgzero : U.g (firstIndex U) = 0 := by
        by_contra h
        have hgone : 1 ≤ U.g (firstIndex U) := by omega
        have hterm : 0 ≤ U.m (firstIndex U) * U.w (firstIndex U) *
            (U.g (firstIndex U) - 1) :=
          mul_nonneg (le_of_lt hUxy) (by omega)
        nlinarith [hUgv]
      have hUprod : U.m (firstIndex U) * U.w (firstIndex U) = 1 - genusValue := by
        rw [hUgzero] at hUgv
        omega
      have hmposU := U.m_pos (firstIndex U)
      have hwposU := U.w_pos (firstIndex U)
      have hm₁ : 1 ≤ U.m (firstIndex U) := by omega
      have hw₁ : 1 ≤ U.w (firstIndex U) := by omega
      have hm₂ : U.m (firstIndex U) ≤ 1 - genusValue := by
        nlinarith [hUprod, hw₁]
      have hw₂ : U.w (firstIndex U) ≤ 1 - genusValue := by
        nlinarith [hUprod, hm₁]
      exact ⟨hm₁, hm₂, hw₁, hw₂, by omega, by omega⟩
    exact ⟨hgzero, hprod, by simpa [S] using hfinite⟩
    
  · intro hzero
    have hmpos := T.m_pos (firstIndex T)
    have hwpos := T.w_pos (firstIndex T)
    have hxy : 0 < T.m (firstIndex T) * T.w (firstIndex T) :=
      mul_pos hmpos hwpos
    have hgnonneg := T.g_nonneg (firstIndex T)
    have hgzero : T.g (firstIndex T) = 0 := by
      by_contra h
      have hgone : 1 ≤ T.g (firstIndex T) := by omega
      have hterm : 0 ≤ T.m (firstIndex T) * T.w (firstIndex T) *
          (T.g (firstIndex T) - 1) :=
        mul_nonneg (le_of_lt hxy) (by omega)
      nlinarith [hgv]
    have hprod : T.m (firstIndex T) * T.w (firstIndex T) = 1 := by
      rw [hgzero] at hgv
      omega
    have hmone : T.m (firstIndex T) = 1 := by
      have hm₁ : 1 ≤ T.m (firstIndex T) := by omega
      have hw₁ : 1 ≤ T.w (firstIndex T) := by omega
      nlinarith [hprod]
    have hwone : T.w (firstIndex T) = 1 := by
      have hm₁ : 1 ≤ T.m (firstIndex T) := by omega
      have hw₁ : 1 ≤ T.w (firstIndex T) := by omega
      nlinarith [hprod]
    exact ⟨hmone, hwone, hgzero⟩
  · intro hone
    have hxy : 0 < T.m (firstIndex T) * T.w (firstIndex T) :=
      mul_pos (T.m_pos _) (T.w_pos _)
    have hprod : T.m (firstIndex T) * T.w (firstIndex T) *
        (T.g (firstIndex T) - 1) = 0 := by omega
    rcases mul_eq_zero.mp hprod with hxyzero | hgone
    · exact False.elim (ne_of_gt hxy hxyzero)
    · omega
  · intro hgtwo
    have hxy : 0 < T.m (firstIndex T) * T.w (firstIndex T) :=
      mul_pos (T.m_pos _) (T.w_pos _)
    have hprod : T.m (firstIndex T) * T.w (firstIndex T) *
        (T.g (firstIndex T) - 1) = genusValue - 1 := by omega
    have hgone : 1 ≤ T.g (firstIndex T) := by
      by_contra h
      have hnonpos : T.g (firstIndex T) - 1 ≤ 0 := by omega
      have hterm : T.m (firstIndex T) * T.w (firstIndex T) *
          (T.g (firstIndex T) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hxy) hnonpos
      nlinarith [hprod]
    have hgpos : 0 < T.g (firstIndex T) - 1 := by
      by_contra h
      have hnonpos : T.g (firstIndex T) - 1 ≤ 0 := by omega
      have hterm : T.m (firstIndex T) * T.w (firstIndex T) *
          (T.g (firstIndex T) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hxy) hnonpos
      nlinarith [hprod, hgtwo]
    have hgtwo' : 1 ≤ T.g (firstIndex T) - 1 := by omega
    have hmg : T.m (firstIndex T) ≤ genusValue - 1 := by
      nlinarith [hprod, T.w_pos (firstIndex T), hgtwo']
    have hwg : T.w (firstIndex T) ≤ genusValue - 1 := by
      nlinarith [hprod, T.m_pos (firstIndex T), hgtwo']
    have hgg : T.g (firstIndex T) ≤ genusValue := by
      nlinarith [hprod, hxy]
    have hfinite : S.Finite := by
      apply hfinite_of_bounds (genusValue - 1) (genusValue - 1) genusValue
      intro U hU
      rcases hU with ⟨hUn, hUg⟩
      have hUgenus := hone_formula U hUn
      have hUgv : genusValue = 1 + U.m (firstIndex U) * U.w (firstIndex U) *
          (U.g (firstIndex U) - 1) := by
        rw [← hUg]
        exact hUgenus
      have hUxy : 0 < U.m (firstIndex U) * U.w (firstIndex U) :=
        mul_pos (U.m_pos _) (U.w_pos _)
      have hUgnonneg := U.g_nonneg (firstIndex U)
      have hUprod : U.m (firstIndex U) * U.w (firstIndex U) *
          (U.g (firstIndex U) - 1) = genusValue - 1 := by omega
      have hUgone : 1 ≤ U.g (firstIndex U) := by
        by_contra h
        have hnonpos : U.g (firstIndex U) - 1 ≤ 0 := by omega
        have hterm : U.m (firstIndex U) * U.w (firstIndex U) *
            (U.g (firstIndex U) - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hUxy) hnonpos
        nlinarith [hUprod]
      have hUgpos : 0 < U.g (firstIndex U) - 1 := by
        by_contra h
        have hnonpos : U.g (firstIndex U) - 1 ≤ 0 := by omega
        have hterm : U.m (firstIndex U) * U.w (firstIndex U) *
            (U.g (firstIndex U) - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hUxy) hnonpos
        nlinarith [hUprod, hgtwo]
      have hUgtwo : 1 ≤ U.g (firstIndex U) - 1 := by omega
      have hmposU := U.m_pos (firstIndex U)
      have hwposU := U.w_pos (firstIndex U)
      have hm₁ : 1 ≤ U.m (firstIndex U) := by omega
      have hw₁ : 1 ≤ U.w (firstIndex U) := by omega
      have hm₂ : U.m (firstIndex U) ≤ genusValue - 1 := by
        nlinarith [hUprod, hw₁, hUgtwo]
      have hw₂ : U.w (firstIndex U) ≤ genusValue - 1 := by
        nlinarith [hUprod, hm₁, hUgtwo]
      have hg₂ : U.g (firstIndex U) ≤ genusValue := by
        nlinarith [hUprod, hUxy]
      exact ⟨hm₁, hm₂, hw₁, hw₂, by omega, hg₂⟩
    exact ⟨by omega, hprod, by simpa [S] using hfinite⟩

/-! Negative diagonal entries in the reducible case. -/
theorem diagonal_negative (T : NumericalType) (genusValue : ℤ)
    (_hgenus : IsOfGenus T genusValue) (hn : 1 < T.n) :
    ∀ i, T.a i i < 0 := by
  have hAm : Matrix.mulVec (fun i j => (T.a i j : ℝ)) (fun i => (T.m i : ℝ)) = 0 := by
    funext i
    change (∑ j, (T.a i j : ℝ) * (T.m j : ℝ)) = 0
    have h := T.row_sum i
    exact_mod_cast h
  have hreal := Formalization.Books.Models.Unit02.recurring_symmetric_real
    (fun i j => (T.a i j : ℝ)) (fun i => (T.m i : ℝ))
    (fun i j => by exact_mod_cast T.a_symmetric i j)
    (by intro i j h; exact_mod_cast T.a_offdiag_nonneg h)
    (by intro i; exact_mod_cast T.m_pos i) hAm
    (by
      intro h
      apply T.connected
      rcases h with ⟨I, hI, hne, hcross⟩
      refine ⟨I, hI, hne, ?_⟩
      intro i j hi hj
      exact_mod_cast hcross hi hj)
  intro i
  let x : Fin T.n → ℝ := fun j => if j = i then 1 else 0
  have hquad := (hreal x).1
  norm_num [x, Matrix.mulVec_apply_eq_sum] at hquad
  change (∑ j, (T.a i j : ℝ) * x j) ≤ 0 at hquad
  have hquad' : (T.a i i : ℝ) ≤ 0 := by
    simpa [x] using hquad
  have hle : T.a i i ≤ 0 := by exact_mod_cast hquad'
  by_contra hnot
  have hai : T.a i i = 0 := by omega
  have henergy : (Finset.univ : Finset (Fin T.n)).sum
      (fun j => x j * Matrix.mulVec (fun i j => (T.a i j : ℝ)) x j) = 0 := by
    change (∑ j, x j * (∑ k, (T.a j k : ℝ) * x k)) = 0
    simp [x, hai]
  rcases (hreal x).2.mp henergy with ⟨c, hc⟩
  have h1 : 1 < T.n := hn
  have hi_lt : i.val < T.n := i.isLt
  let j : Fin T.n := if i.val = 0 then ⟨1, h1⟩ else ⟨0, Nat.zero_lt_of_lt h1⟩
  have hji : j ≠ i := by
    apply Fin.ne_of_val_ne
    by_cases hi0 : i.val = 0
    · dsimp [j]
      rw [if_pos hi0]
      simp [hi0]
    · dsimp [j]
      rw [if_neg hi0]
      intro h
      exact hi0 h.symm
  have hcj := congrFun hc j
  have hc0 : c = 0 := by
    simp [x, hji] at hcj
    rcases hcj with hcj | hcj
    · exact hcj
    · have hmj : 0 < T.m j := T.m_pos j
      exfalso
      exact (ne_of_gt hmj) hcj
  have hci := congrFun hc i
  simp [x, hc0] at hci

/-! A negative genus contribution is exactly a `(-1)` component. -/
theorem minus_one_contribution (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hn : 1 < T.n) {i : Fin T.n}
    (hcontribution : genusContribution T i < 0) :
    T.g i = 0 ∧ T.a i i = -T.w i := by
  have hai : T.a i i < 0 := diagonal_negative T genusValue hgenus hn i
  have hmQ : (0 : ℚ) < (T.m i : ℚ) := by exact_mod_cast T.m_pos i
  have hcontribution' : (T.m i : ℚ) *
      ((T.w i : ℚ) * ((T.g i : ℚ) - 1) - (T.a i i : ℚ) / 2) < 0 := by
    simpa [genusContribution] using hcontribution
  have hinner : (T.w i : ℚ) * ((T.g i : ℚ) - 1) -
      (T.a i i : ℚ) / 2 < 0 := by
    nlinarith [hcontribution', hmQ]
  have hineqQ : (2 : ℚ) * (T.w i : ℚ) * ((T.g i : ℚ) - 1) <
      (T.a i i : ℚ) := by
    linarith
  have hineq : 2 * T.w i * (T.g i - 1) < T.a i i := by
    exact_mod_cast hineqQ
  have hgnonneg := T.g_nonneg i
  have hwpos := T.w_pos i
  have hgzero : T.g i = 0 := by
    by_contra h
    have hgone : 1 ≤ T.g i := by omega
    have hnonneg : 0 ≤ 2 * T.w i * (T.g i - 1) := by
      have hw : 0 ≤ T.w i := by omega
      have hg : 0 ≤ T.g i - 1 := by omega
      nlinarith
    omega
  refine ⟨hgzero, ?_⟩
  obtain ⟨k, hk⟩ := T.w_dvd i i
  have hkneg : k < 0 := by
    rw [hk] at hai
    have hw : 0 < T.w i := T.w_pos i
    nlinarith
  have hkgt : -2 < k := by
    rw [hk] at hineq
    rw [hgzero] at hineq
    have hw : 0 < T.w i := T.w_pos i
    nlinarith
  have hkval : k = -1 := by omega
  rw [hk, hkval]
  ring

def IsMinusOneIndex (T : NumericalType) (i : Fin T.n) : Prop :=
  T.g i = 0 ∧ T.a i i = -T.w i

/-! Indices left after removing one distinguished index. -/
abbrev RemainingIndex (T : NumericalType) (i : Fin T.n) :=
  {j : Fin T.n // j ≠ i}

/-! The three formulas in the contraction construction. -/
def contractedIntersection (T : NumericalType) (i : Fin T.n)
    (j k : RemainingIndex T i) : ℤ :=
  T.a j.1 k.1 - T.a j.1 i * T.a k.1 i / T.a i i

def contractedWeight (T : NumericalType) (i : Fin T.n)
    (j : RemainingIndex T i) : ℤ :=
  if Even (T.a j.1 i / T.w i) ∧ Odd (T.a j.1 i / T.w j.1) then
    T.w j.1 / 2
  else
    T.w j.1

def contractedComponentGenus (T : NumericalType) (i : Fin T.n)
    (j : RemainingIndex T i) : ℤ :=
  T.w j.1 / contractedWeight T i j * (T.g j.1 - 1) + 1 +
      (T.a j.1 i ^ 2 - T.w i * T.a j.1 i) /
      (2 * contractedWeight T i j * T.w i)

private theorem contracted_genus_expression
    (T : NumericalType) (i : Fin T.n) (hi : IsMinusOneIndex T i)
    (e : Fin (T.n - 1) ≃ RemainingIndex T i)
    (a' : Matrix (Fin (T.n - 1)) (Fin (T.n - 1)) ℤ)
    (w' g' : Fin (T.n - 1) → ℤ)
    (hcomponent : ∀ j, (w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2 =
      (T.w (e j).1 : ℚ) * ((T.g (e j).1 : ℚ) - 1) -
        (T.a (e j).1 i : ℚ) / 2 - (T.a (e j).1 (e j).1 : ℚ) / 2)
    (hsumQ : ∀ (f : Fin T.n → ℚ),
      (∑ j : Fin (T.n - 1), f (e j).1) =
        (Finset.univ.erase i).sum f) :
    1 + (∑ j : Fin (T.n - 1),
      (T.m (e j).1 : ℚ) * ((w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2)) =
      1 + (Finset.univ : Finset (Fin T.n)).sum (fun k =>
        (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
          (T.a k k : ℚ) / 2)) := by
  have hsum_component :
      (∑ j : Fin (T.n - 1),
        (T.m (e j).1 : ℚ) * ((w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2)) =
        (Finset.univ.erase i).sum (fun k =>
          (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
            (T.a k i : ℚ) / 2 - (T.a k k : ℚ) / 2)) := by
    calc
      (∑ j : Fin (T.n - 1),
          (T.m (e j).1 : ℚ) * ((w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2)) =
          ∑ j : Fin (T.n - 1),
            (T.m (e j).1 : ℚ) *
              ((T.w (e j).1 : ℚ) * ((T.g (e j).1 : ℚ) - 1) -
                (T.a (e j).1 i : ℚ) / 2 -
                (T.a (e j).1 (e j).1 : ℚ) / 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcomponent]
      _ = (Finset.univ.erase i).sum (fun k =>
          (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
            (T.a k i : ℚ) / 2 - (T.a k k : ℚ) / 2)) := by
            simpa using hsumQ (fun k =>
              (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
                (T.a k i : ℚ) / 2 - (T.a k k : ℚ) / 2))
  have hsum_b :
      (Finset.univ.erase i).sum (fun k =>
        (T.m k : ℚ) * (T.a k i : ℚ) / 2) =
          (T.w i : ℚ) * (T.m i : ℚ) / 2 := by
    have hrowQ := congrArg (fun z : ℤ => (z : ℚ))
      (show (Finset.univ.erase i).sum (fun k => T.a i k * T.m k) =
          -T.a i i * T.m i from by
        have hsplit := Finset.sum_erase_add
          (s := (Finset.univ : Finset (Fin T.n)))
          (f := fun k => T.a i k * T.m k) (Finset.mem_univ i)
        rw [T.row_sum i] at hsplit
        nlinarith)
    push_cast at hrowQ
    have hsumcast :
        (Finset.univ.erase i).sum (fun k =>
            (T.m k : ℚ) * (T.a k i : ℚ)) =
          (Finset.univ.erase i).sum (fun k =>
            ((T.a i k * T.m k : ℤ) : ℚ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [T.a_symmetric k i]
      push_cast
      ring
    have hrowQ' :
        (Finset.univ.erase i).sum (fun k =>
            ((T.a i k * T.m k : ℤ) : ℚ)) =
          ((-T.a i i * T.m i : ℤ) : ℚ) := by
      calc
        (Finset.univ.erase i).sum (fun k =>
            ((T.a i k * T.m k : ℤ) : ℚ)) =
            (Finset.univ.erase i).sum (fun k =>
              (T.a i k : ℚ) * (T.m k : ℚ)) := by
                apply Finset.sum_congr rfl
                intro k hk
                push_cast
                rfl
        _ = ((-T.a i i * T.m i : ℤ) : ℚ) := by
          simpa only [Int.cast_neg, Int.cast_mul] using hrowQ
    calc
      (Finset.univ.erase i).sum (fun k =>
          (T.m k : ℚ) * (T.a k i : ℚ) / 2) =
          (1 / 2 : ℚ) * (Finset.univ.erase i).sum (fun k =>
            (T.m k : ℚ) * (T.a k i : ℚ)) := by
              calc
                _ = (Finset.univ.erase i).sum (fun k =>
                    (1 / 2 : ℚ) * ((T.m k : ℚ) * (T.a k i : ℚ))) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
                _ = _ := by rw [Finset.mul_sum]
      _ = (1 / 2 : ℚ) * (Finset.univ.erase i).sum (fun k =>
            ((T.a i k * T.m k : ℤ) : ℚ)) := by rw [hsumcast]
      _ = (1 / 2 : ℚ) * ((-T.a i i * T.m i : ℤ) : ℚ) := by
        rw [hrowQ']
      _ = (T.w i : ℚ) * (T.m i : ℚ) / 2 := by
        rw [hi.2]
        push_cast
        ring
  calc
    1 + (∑ j : Fin (T.n - 1),
        (T.m (e j).1 : ℚ) * ((w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2)) =
        1 + (Finset.univ.erase i).sum (fun k =>
          (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
            (T.a k i : ℚ) / 2 - (T.a k k : ℚ) / 2)) := by
          rw [hsum_component]
    _ = 1 + (Finset.univ.erase i).sum (fun k =>
          (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
            (T.a k k : ℚ) / 2)) - (T.w i : ℚ) * (T.m i : ℚ) / 2 := by
          have hsum_rearrange :
              (Finset.univ.erase i).sum (fun k =>
                (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
                  (T.a k i : ℚ) / 2 - (T.a k k : ℚ) / 2)) =
                (Finset.univ.erase i).sum (fun k =>
                  (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
                    (T.a k k : ℚ) / 2)) -
                  (Finset.univ.erase i).sum (fun k =>
                    (T.m k : ℚ) * (T.a k i : ℚ) / 2) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          rw [hsum_rearrange, hsum_b]
          ring
    _ = 1 + (Finset.univ : Finset (Fin T.n)).sum (fun k =>
          (T.m k : ℚ) * ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
            (T.a k k : ℚ) / 2)) := by
          have hsplit := Finset.sum_erase_add
            (s := (Finset.univ : Finset (Fin T.n)))
            (f := fun k => (T.m k : ℚ) *
              ((T.w k : ℚ) * ((T.g k : ℚ) - 1) - (T.a k k : ℚ) / 2))
            (Finset.mem_univ i)
          rw [← hsplit]
          rw [hi.1, hi.2]
          push_cast
          ring

private theorem contracted_component_genus_data (T : NumericalType) (i : Fin T.n) :
    (∀ j : RemainingIndex T i,
      0 < contractedWeight T i j ∧ contractedWeight T i j ∣ T.w j.1) ∧
    (∀ (b c : ℤ), T.w i ∣ b → T.w i ∣ c →
      b * c / (-T.w i) = -(b / T.w i * c)) ∧
    (∀ (b c : ℤ), T.w i ∣ c →
      b * c / (-T.w i) = -(b * (c / T.w i))) ∧
    (∀ j : RemainingIndex T i, 0 ≤ contractedComponentGenus T i j) ∧
    (∀ j : RemainingIndex T i,
      Even (T.a j.1 i / T.w i) ∧ Odd (T.a j.1 i / T.w j.1) →
        (2 : ℤ) ∣ T.w j.1) := by
  have hdivwi (j : RemainingIndex T i) :
      T.w i ∣ T.a j.1 i := by
    rw [T.a_symmetric j.1 i]
    exact T.w_dvd i j.1
  have hdivwj (j : RemainingIndex T i) :
      T.w j.1 ∣ T.a j.1 i := T.w_dvd j.1 i
  have hhalf_dvd (j : RemainingIndex T i)
      (hcond : Even (T.a j.1 i / T.w i) ∧ Odd (T.a j.1 i / T.w j.1)) :
      (2 : ℤ) ∣ T.w j.1 := by
    have hw_even : Even (T.w j.1) := by
      rw [← Int.not_odd_iff_even]
      intro hwj_odd
      have hb_even : Even (T.a j.1 i) := by
        obtain ⟨r, hr⟩ := hcond.1
        refine ⟨r * T.w i, ?_⟩
        have hcancel := Int.ediv_mul_cancel (hdivwi j)
        rw [← hcancel, hr]
        ring
      have hb_odd : Odd (T.a j.1 i) := by
        have hcancel := Int.ediv_mul_cancel (hdivwj j)
        rw [← hcancel]
        exact hcond.2.mul hwj_odd
      exact (Int.not_odd_iff_even.mpr hb_even) hb_odd
    obtain ⟨r, hr⟩ := hw_even
    refine ⟨r, ?_⟩
    omega
  have hweight_data : ∀ j : RemainingIndex T i,
      0 < contractedWeight T i j ∧ contractedWeight T i j ∣ T.w j.1 := by
    intro j
    have hwj_pos := T.w_pos j.1
    unfold contractedWeight
    split
    next hcond =>
      have hdivtwo := hhalf_dvd j hcond
      constructor
      · exact Int.ediv_pos_of_pos_of_dvd hwj_pos (by norm_num) hdivtwo
      · refine ⟨2, ?_⟩
        have hcancel := Int.ediv_mul_cancel hdivtwo
        nlinarith
    next hcond => exact ⟨hwj_pos, dvd_refl _⟩
  have hdiv_formula : ∀ (b c : ℤ),
      T.w i ∣ b → T.w i ∣ c →
      b * c / (-T.w i) = -(b / T.w i * c) := by
    intro b c hb hc
    obtain ⟨r, hr⟩ := hb
    obtain ⟨s, hs⟩ := hc
    rw [hr, hs]
    simp only [Int.ediv_neg]
    rw [show (T.w i * r) * (T.w i * s) =
        T.w i * (r * (T.w i * s)) by ring]
    rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos i))]
    rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos i))]
  have hdiv_formula_right : ∀ (b c : ℤ),
      T.w i ∣ c →
      b * c / (-T.w i) = -(b * (c / T.w i)) := by
    intro b c hc
    obtain ⟨r, hr⟩ := hc
    rw [hr]
    simp only [Int.ediv_neg]
    rw [show b * (T.w i * r) = T.w i * (b * r) by ring]
    rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos i))]
    have hcancel : (T.w i * r) / T.w i = r := by
      rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos i))]
    rw [hcancel]
  have hgenus : ∀ j : RemainingIndex T i,
      0 ≤ contractedComponentGenus T i j := by
    intro j
    have hjne : j.1 ≠ i := j.2
    have hbnonneg : 0 ≤ T.a j.1 i := T.a_offdiag_nonneg hjne
    have hwi_pos : 0 < T.w i := T.w_pos i
    have hwj_pos : 0 < T.w j.1 := T.w_pos j.1
    have hqdiv := hdivwi j
    have hpdiv := hdivwj j
    have hqediv : T.a j.1 i / T.w i * T.w i = T.a j.1 i := by
      rw [Int.ediv_mul_cancel hqdiv]
    have hpediv : T.a j.1 i / T.w j.1 * T.w j.1 = T.a j.1 i := by
      rw [Int.ediv_mul_cancel hpdiv]
    let p : ℤ := T.a j.1 i / T.w j.1
    let q : ℤ := T.a j.1 i / T.w i
    have hp_nonneg : 0 ≤ p := by
      dsimp [p]
      exact Int.ediv_nonneg (by omega) (by omega)
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact Int.ediv_nonneg (by omega) (by omega)
    have hp_eq : T.a j.1 i = p * T.w j.1 := by
      dsimp [p]
      exact hpediv.symm
    have hq_eq : T.a j.1 i = q * T.w i := by
      dsimp [q]
      exact hqediv.symm
    have hnum_eq :
        T.a j.1 i ^ 2 - T.w i * T.a j.1 i =
          p * (q - 1) * (T.w j.1 * T.w i) := by
      have hsq : T.a j.1 i ^ 2 =
          (p * T.w j.1) * (q * T.w i) := by
        calc
          T.a j.1 i ^ 2 = T.a j.1 i * (q * T.w i) := by rw [hq_eq]; ring
          _ = (p * T.w j.1) * (q * T.w i) := by rw [hp_eq]
      calc
        T.a j.1 i ^ 2 - T.w i * T.a j.1 i =
            (p * T.w j.1) * (q * T.w i) - T.w i * (p * T.w j.1) := by
              rw [hsq, hp_eq]
        _ = p * (q - 1) * (T.w j.1 * T.w i) := by ring
    by_cases hhalf : Even q ∧ Odd p
    · have hq_two : 2 ≤ q := by
        have hqpos : 0 < q := by
          by_contra hqzero
          have hqz : q = 0 := by omega
          rw [hqz] at hq_eq
          have hbzero : T.a j.1 i = 0 := by simpa using hq_eq
          rw [hbzero] at hp_eq
          have hpz : p = 0 := by nlinarith [hwj_pos]
          have : ¬ Odd p := by simp [hpz]
          exact this hhalf.2
        obtain ⟨r, hr⟩ := hhalf.1
        omega
      have hp_one : 1 ≤ p := by
        obtain ⟨r, hr⟩ := hhalf.2
        omega
      have hprod : 1 ≤ p * (q - 1) := by
        nlinarith [hp_nonneg, hq_two, hp_one]
      have hhalf_pos : 0 < T.w j.1 / 2 := by
        exact Int.ediv_pos_of_pos_of_dvd hwj_pos (by norm_num)
          (hhalf_dvd j (by simpa [p, q] using hhalf))
      have htwohalf : 2 * (T.w j.1 / 2) = T.w j.1 := by
        have hcancel := Int.ediv_mul_cancel (hhalf_dvd j (by
          simpa [p, q] using hhalf))
        nlinarith
      have hratio : T.w j.1 / (T.w j.1 / 2) = 2 := by
        apply Int.ediv_eq_of_eq_mul_left (ne_of_gt hhalf_pos)
        nlinarith [htwohalf]
      have hden : 2 * (T.w j.1 / 2) * T.w i = T.w j.1 * T.w i := by
        nlinarith [htwohalf]
      have hquot :
          (T.a j.1 i ^ 2 - T.w i * T.a j.1 i) /
              (2 * (T.w j.1 / 2) * T.w i) = p * (q - 1) := by
        apply Int.ediv_eq_of_eq_mul_left
          (ne_of_gt (by nlinarith [hwi_pos, hhalf_pos]))
        rw [hden, hnum_eq]
      have hform : contractedComponentGenus T i j =
          2 * (T.g j.1 - 1) + 1 + p * (q - 1) := by
        unfold contractedComponentGenus
        rw [show contractedWeight T i j = T.w j.1 / 2 by
          simp [contractedWeight, p, q, hhalf], hratio, hquot]
      rw [hform]
      have hgj := T.g_nonneg j.1
      nlinarith
    · have hprod_even : Even (p * (q - 1)) := by
        by_cases hq_even : Even q
        · have hp_even : Even p := by
            by_contra hp_not
            exact hhalf ⟨hq_even, Int.not_even_iff_odd.mp hp_not⟩
          obtain ⟨r, hr⟩ := hp_even
          refine ⟨r * (q - 1), ?_⟩
          rw [hr]
          ring
        · have hq_odd : Odd q := Int.not_even_iff_odd.mp hq_even
          have hqsub_even : Even (q - 1) := by
            obtain ⟨r, hr⟩ := hq_odd
            refine ⟨r, ?_⟩
            omega
          obtain ⟨r, hr⟩ := hqsub_even
          refine ⟨p * r, ?_⟩
          rw [hr]
          ring
      have hprod : 0 ≤ p * (q - 1) := by
        by_cases hqz : q = 0
        · rw [hqz] at hq_eq
          have hbzero : T.a j.1 i = 0 := by simpa using hq_eq
          rw [hbzero] at hp_eq
          have hpz : p = 0 := by nlinarith [hwj_pos]
          simp [hpz]
        · have hqpos : 0 < q := by omega
          have hqone : 1 ≤ q := by omega
          exact mul_nonneg hp_nonneg (by omega)
      have hquot :
          (T.a j.1 i ^ 2 - T.w i * T.a j.1 i) /
              (2 * T.w j.1 * T.w i) = p * (q - 1) / 2 := by
        have hprod_dvd : (2 : ℤ) ∣ p * (q - 1) := by
          obtain ⟨r, hr⟩ := hprod_even
          refine ⟨r, ?_⟩
          omega
        have hnum' :
            T.a j.1 i ^ 2 - T.w i * T.a j.1 i =
              (p * (q - 1) / 2) * (2 * T.w j.1 * T.w i) := by
          rw [hnum_eq]
          have hc := Int.ediv_mul_cancel hprod_dvd
          calc
            p * (q - 1) * (T.w j.1 * T.w i) =
                (p * (q - 1) / 2 * 2) * (T.w j.1 * T.w i) := by rw [hc]
            _ = (p * (q - 1) / 2) * (2 * T.w j.1 * T.w i) := by ring
        apply Int.ediv_eq_of_eq_mul_left
          (ne_of_gt (by nlinarith [hwi_pos, hwj_pos]))
        exact hnum'
      have hform : contractedComponentGenus T i j =
          T.g j.1 + p * (q - 1) / 2 := by
        unfold contractedComponentGenus
        rw [show contractedWeight T i j = T.w j.1 by
          simp [contractedWeight, p, q, hhalf], Int.ediv_self (ne_of_gt hwj_pos), hquot]
        ring
      rw [hform]
      have hgj := T.g_nonneg j.1
      have hquot_nonneg : 0 ≤ p * (q - 1) / 2 :=
        Int.ediv_nonneg hprod (by norm_num)
      nlinarith
  exact ⟨hweight_data, hdiv_formula, hdiv_formula_right, hgenus, hhalf_dvd⟩

/-! Contraction of a `(-1)`-index, with the source formulas exposed through an equivalence. -/
theorem contract_minus_one_index (T : NumericalType) (i : Fin T.n)
    (hi : IsMinusOneIndex T i) :
    ∃ T' : NumericalType,
      T'.n = T.n - 1 ∧
        ∃ e : Fin T'.n ≃ RemainingIndex T i,
          (∀ j, T'.m j = T.m (e j).1) ∧
            (∀ j k, T'.a j k = contractedIntersection T i (e j) (e k)) ∧
                (∀ j, T'.w j = contractedWeight T i (e j)) ∧
                (∀ j, T'.g j = contractedComponentGenus T i (e j)) ∧
                  genus T' = genus T := by
  classical
  have hn1 : 1 < T.n := by
    by_contra h
    have hn_lower := T.hn
    have hn_eq : T.n = 1 := by omega
    have hrow : T.a i i * T.m i = 0 := by
      calc
        T.a i i * T.m i =
            (Finset.univ : Finset (Fin T.n)).sum (fun j => T.a i j * T.m j) := by
              symm
              apply Finset.sum_eq_single i
              · intro b hb hbi
                apply False.elim
                apply hbi
                apply Fin.ext
                omega
              · simp
        _ = 0 := T.row_sum i
    have hai0 : T.a i i = 0 := by nlinarith [hrow, T.m_pos i]
    rw [hi.2] at hai0
    have hwi := T.w_pos i
    nlinarith
  have hcard : Fintype.card (RemainingIndex T i) = T.n - 1 := by
    simp [RemainingIndex, Fintype.card_subtype_compl]
  let e : Fin (T.n - 1) ≃ RemainingIndex T i :=
    (Fintype.equivFinOfCardEq hcard).symm
  have hsum (f : Fin T.n → ℤ) :
      (∑ j : Fin (T.n - 1), f (e j).1) =
        (Finset.univ.erase i).sum f := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (Fin (T.n - 1))))
      (t := Finset.univ.erase i) (f := fun j => f (e j).1) (g := f)
      (fun j _ => (e j).1)
    · intro j hj
      rw [Finset.mem_erase]
      exact ⟨(e j).2, Finset.mem_univ _⟩
    · intro a ha b hb hab
      exact e.injective (Subtype.ext hab)
    · intro b hb
      let b' : RemainingIndex T i := ⟨b, (Finset.mem_erase.mp hb).1⟩
      refine ⟨e.symm b', Finset.mem_univ _, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply b')
    · intro j hj
      rfl
  have hdivwi (j : RemainingIndex T i) :
      T.w i ∣ T.a j.1 i := by
    rw [T.a_symmetric j.1 i]
    exact T.w_dvd i j.1
  have hdivwj (j : RemainingIndex T i) :
      T.w j.1 ∣ T.a j.1 i := T.w_dvd j.1 i
  have hcontract_data := contracted_component_genus_data T i
  have hweight_data := hcontract_data.1
  have hweight_pos : ∀ j : RemainingIndex T i,
      0 < contractedWeight T i j := fun j => (hweight_data j).1
  have hdiv_formula := hcontract_data.2.1
  have hdiv_formula_right := hcontract_data.2.2.1
  have hgenus := hcontract_data.2.2.2.1
  have hhalf_dvd := hcontract_data.2.2.2.2
  /-
  have hdivwi (j : RemainingIndex T i) :
      T.w i ∣ T.a j.1 i := by
    rw [T.a_symmetric j.1 i]
    exact T.w_dvd i j.1
  have hdivwj (j : RemainingIndex T i) :
      T.w j.1 ∣ T.a j.1 i := T.w_dvd j.1 i
  have hhalf_dvd (j : RemainingIndex T i)
      (hcond : Even (T.a j.1 i / T.w i) ∧ Odd (T.a j.1 i / T.w j.1)) :
      (2 : ℤ) ∣ T.w j.1 := by
    have hw_even : Even (T.w j.1) := by
      rw [← Int.not_odd_iff_even]
      intro hwj_odd
      have hb_even : Even (T.a j.1 i) := by
        obtain ⟨r, hr⟩ := hcond.1
        refine ⟨r * T.w i, ?_⟩
        have hcancel := Int.ediv_mul_cancel (hdivwi j)
        rw [← hcancel, hr]
        ring
      have hb_odd : Odd (T.a j.1 i) := by
        have hcancel := Int.ediv_mul_cancel (hdivwj j)
        rw [← hcancel]
        exact hcond.2.mul hwj_odd
      exact (Int.not_odd_iff_even.mpr hb_even) hb_odd
    obtain ⟨r, hr⟩ := hw_even
    refine ⟨r, ?_⟩
    omega
  have hweight_data : ∀ j : RemainingIndex T i,
      0 < contractedWeight T i j ∧ contractedWeight T i j ∣ T.w j.1 := by
    intro j
    have hwj_pos := T.w_pos j.1
    unfold contractedWeight
    split
    next hcond =>
      have hdivtwo := hhalf_dvd j hcond
      constructor
      · exact Int.ediv_pos_of_pos_of_dvd hwj_pos (by norm_num) hdivtwo
      · refine ⟨2, ?_⟩
        have hcancel := Int.ediv_mul_cancel hdivtwo
        nlinarith
    next hcond => exact ⟨hwj_pos, dvd_refl _⟩
  have hweight_pos : ∀ j : RemainingIndex T i,
      0 < contractedWeight T i j := fun j => (hweight_data j).1
  have hdiv_formula : ∀ (b c : ℤ),
      T.w i ∣ b → T.w i ∣ c →
      b * c / (-T.w i) = -(b / T.w i * c) := by
    intro b c hb hc
    obtain ⟨r, hr⟩ := hb
    obtain ⟨s, hs⟩ := hc
    rw [hr, hs]
    simp only [Int.ediv_neg]
    rw [show (T.w i * r) * (T.w i * s) =
        T.w i * (r * (T.w i * s)) by ring]
    rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos i))]
    rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos i))]
  have hdiv_formula_right : ∀ (b c : ℤ),
      T.w i ∣ c →
      b * c / (-T.w i) = -(b * (c / T.w i)) := by
    intro b c hc
    obtain ⟨r, hr⟩ := hc
    rw [hr]
    simp only [Int.ediv_neg]
    rw [show b * (T.w i * r) = T.w i * (b * r) by ring]
    rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos i))]
    have hcancel : (T.w i * r) / T.w i = r := by
      rw [Int.mul_ediv_cancel_left _ (ne_of_gt (T.w_pos i))]
    rw [hcancel]
  have hgenus : ∀ j : RemainingIndex T i,
      0 ≤ contractedComponentGenus T i j := by
    intro j
    have hjne : j.1 ≠ i := j.2
    have hbnonneg : 0 ≤ T.a j.1 i := T.a_offdiag_nonneg hjne
    have hwi_pos : 0 < T.w i := T.w_pos i
    have hwj_pos : 0 < T.w j.1 := T.w_pos j.1
    have hqdiv := hdivwi j
    have hpdiv := hdivwj j
    have hqediv : T.a j.1 i / T.w i * T.w i = T.a j.1 i := by
      rw [Int.ediv_mul_cancel hqdiv]
    have hpediv : T.a j.1 i / T.w j.1 * T.w j.1 = T.a j.1 i := by
      rw [Int.ediv_mul_cancel hpdiv]
    let p : ℤ := T.a j.1 i / T.w j.1
    let q : ℤ := T.a j.1 i / T.w i
    have hp_nonneg : 0 ≤ p := by
      dsimp [p]
      exact Int.ediv_nonneg (by omega) (by omega)
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact Int.ediv_nonneg (by omega) (by omega)
    have hp_eq : T.a j.1 i = p * T.w j.1 := by
      dsimp [p]
      exact hpediv.symm
    have hq_eq : T.a j.1 i = q * T.w i := by
      dsimp [q]
      exact hqediv.symm
    have hnum_eq :
        T.a j.1 i ^ 2 - T.w i * T.a j.1 i =
          p * (q - 1) * (T.w j.1 * T.w i) := by
      have hsq :
          T.a j.1 i ^ 2 = (p * T.w j.1) * (q * T.w i) := by
        calc
          T.a j.1 i ^ 2 = T.a j.1 i * (q * T.w i) := by rw [hq_eq]; ring
          _ = (p * T.w j.1) * (q * T.w i) := by rw [hp_eq]
      calc
        T.a j.1 i ^ 2 - T.w i * T.a j.1 i =
            (p * T.w j.1) * (q * T.w i) - T.w i * (p * T.w j.1) := by
              rw [hsq, hp_eq]
        _ = p * (q - 1) * (T.w j.1 * T.w i) := by ring
    by_cases hhalf : Even q ∧ Odd p
    · have hq_two : 2 ≤ q := by
        have hqpos : 0 < q := by
          by_contra hqzero
          have hqz : q = 0 := by omega
          rw [hqz] at hq_eq
          have hbzero : T.a j.1 i = 0 := by simpa using hq_eq
          rw [hbzero] at hp_eq
          have hpz : p = 0 := by nlinarith [hwj_pos]
          have : ¬ Odd p := by simp [hpz]
          exact this hhalf.2
        obtain ⟨r, hr⟩ := hhalf.1
        omega
      have hp_one : 1 ≤ p := by
        obtain ⟨r, hr⟩ := hhalf.2
        omega
      have hprod : 1 ≤ p * (q - 1) := by
        nlinarith [hp_nonneg, hq_two, hp_one]
      have hhalf_pos : 0 < T.w j.1 / 2 := by
        exact Int.ediv_pos_of_pos_of_dvd hwj_pos (by norm_num)
          (hhalf_dvd j (by simpa [p, q] using hhalf))
      have htwohalf : 2 * (T.w j.1 / 2) = T.w j.1 := by
        have hcancel := Int.ediv_mul_cancel (hhalf_dvd j (by
          simpa [p, q] using hhalf))
        nlinarith
      have hratio : T.w j.1 / (T.w j.1 / 2) = 2 := by
        apply Int.ediv_eq_of_eq_mul_left (ne_of_gt hhalf_pos)
        nlinarith [htwohalf]
      have hden : 2 * (T.w j.1 / 2) * T.w i = T.w j.1 * T.w i := by
        nlinarith [htwohalf]
      have hquot :
          (T.a j.1 i ^ 2 - T.w i * T.a j.1 i) /
              (2 * (T.w j.1 / 2) * T.w i) = p * (q - 1) := by
        apply Int.ediv_eq_of_eq_mul_left
          (ne_of_gt (by nlinarith [hwi_pos, hhalf_pos]))
        rw [hden, hnum_eq]
      have hform :
          contractedComponentGenus T i j =
            2 * (T.g j.1 - 1) + 1 + p * (q - 1) := by
        unfold contractedComponentGenus
        rw [show contractedWeight T i j = T.w j.1 / 2 by
          simp [contractedWeight, p, q, hhalf], hratio, hquot]
      rw [hform]
      have hgj := T.g_nonneg j.1
      nlinarith
    · have hprod_even : Even (p * (q - 1)) := by
        by_cases hq_even : Even q
        · have hp_even : Even p := by
            by_contra hp_not
            exact hhalf ⟨hq_even, Int.not_even_iff_odd.mp hp_not⟩
          obtain ⟨r, hr⟩ := hp_even
          refine ⟨r * (q - 1), ?_⟩
          rw [hr]
          ring
        · have hq_odd : Odd q := Int.not_even_iff_odd.mp hq_even
          have hqsub_even : Even (q - 1) := by
            obtain ⟨r, hr⟩ := hq_odd
            refine ⟨r, ?_⟩
            omega
          obtain ⟨r, hr⟩ := hqsub_even
          refine ⟨p * r, ?_⟩
          rw [hr]
          ring
      have hprod : 0 ≤ p * (q - 1) := by
        by_cases hqz : q = 0
        · rw [hqz] at hq_eq
          have hbzero : T.a j.1 i = 0 := by simpa using hq_eq
          rw [hbzero] at hp_eq
          have hpz : p = 0 := by nlinarith [hwj_pos]
          simp [hpz]
        · have hqpos : 0 < q := by omega
          have hqone : 1 ≤ q := by omega
          exact mul_nonneg hp_nonneg (by omega)
      have hquot :
          (T.a j.1 i ^ 2 - T.w i * T.a j.1 i) /
              (2 * T.w j.1 * T.w i) = p * (q - 1) / 2 := by
        have hprod_dvd : (2 : ℤ) ∣ p * (q - 1) := by
          obtain ⟨r, hr⟩ := hprod_even
          refine ⟨r, ?_⟩
          omega
        have hnum' :
            T.a j.1 i ^ 2 - T.w i * T.a j.1 i =
              (p * (q - 1) / 2) * (2 * T.w j.1 * T.w i) := by
          rw [hnum_eq]
          have hc := Int.ediv_mul_cancel hprod_dvd
          calc
            p * (q - 1) * (T.w j.1 * T.w i) =
                (p * (q - 1) / 2 * 2) * (T.w j.1 * T.w i) := by rw [hc]
            _ = (p * (q - 1) / 2) * (2 * T.w j.1 * T.w i) := by ring
        apply Int.ediv_eq_of_eq_mul_left
          (ne_of_gt (by nlinarith [hwi_pos, hwj_pos]))
        exact hnum'
      have hform :
          contractedComponentGenus T i j =
            T.g j.1 + p * (q - 1) / 2 := by
        unfold contractedComponentGenus
        rw [show contractedWeight T i j = T.w j.1 by
          simp [contractedWeight, p, q, hhalf], Int.ediv_self (ne_of_gt hwj_pos), hquot]
        ring
      rw [hform]
      have hgj := T.g_nonneg j.1
      have hquot_nonneg : 0 ≤ p * (q - 1) / 2 :=
        Int.ediv_nonneg hprod (by norm_num)
      nlinarith
  -/
  let m' : Fin (T.n - 1) → ℤ := fun j => T.m (e j).1
  let a' : Matrix (Fin (T.n - 1)) (Fin (T.n - 1)) ℤ :=
    fun j k => contractedIntersection T i (e j) (e k)
  let w' : Fin (T.n - 1) → ℤ := fun j => contractedWeight T i (e j)
  let g' : Fin (T.n - 1) → ℤ :=
    fun j => contractedComponentGenus T i (e j)
  have ha'_symm : ∀ j k, a' j k = a' k j := by
    intro j k
    dsimp [a', contractedIntersection]
    rw [T.a_symmetric (e j).1 (e k).1]
    ring_nf
  have ha'_offdiag : ∀ ⦃j k⦄, j ≠ k → 0 ≤ a' j k := by
    intro j k hjk
    have hje : (e j).1 ≠ (e k).1 := by
      intro hje
      apply hjk
      exact e.injective (Subtype.ext hje)
    have hbj : 0 ≤ T.a (e j).1 i := T.a_offdiag_nonneg (e j).2
    have hbk : 0 ≤ T.a (e k).1 i := T.a_offdiag_nonneg (e k).2
    have hAjk : 0 ≤ T.a (e j).1 (e k).1 := T.a_offdiag_nonneg hje
    have hprod : 0 ≤ T.a (e j).1 i * T.a (e k).1 i :=
      mul_nonneg hbj hbk
    have hai_neg : T.a i i < 0 := by
      rw [hi.2]
      nlinarith [T.w_pos i]
    have hquot := Int.ediv_nonpos_of_nonneg_of_nonpos hprod (le_of_lt hai_neg)
    dsimp [a', contractedIntersection]
    linarith
  have hcontract_formula (j k : Fin (T.n - 1)) :
      contractedIntersection T i (e j) (e k) =
        T.a (e j).1 (e k).1 +
          (T.a (e j).1 i / T.w i) * T.a (e k).1 i := by
    dsimp [contractedIntersection]
    rw [hi.2, hdiv_formula _ _ (hdivwi (e j)) (hdivwi (e k))]
    ring
  have hcontract_formula_right (j k : Fin (T.n - 1)) :
      contractedIntersection T i (e j) (e k) =
        T.a (e j).1 (e k).1 +
          T.a (e j).1 i * (T.a (e k).1 i / T.w i) := by
    dsimp [contractedIntersection]
    rw [hi.2, hdiv_formula_right _ _ (hdivwi (e k))]
    ring
  have hcross_data :
      ∀ (I : Set (Fin (T.n - 1))),
        (∀ ⦃j k⦄, j ∈ I → k ∉ I → a' j k = 0) →
          ∀ ⦃j k⦄, j ∈ I → k ∉ I →
            T.a (e j).1 (e k).1 = 0 ∧
              (T.a (e j).1 i = 0 ∨ T.a (e k).1 i = 0) := by
    intro I hcross j k hj hk
    have hjk : (e j).1 ≠ (e k).1 := by
      intro hjk
      apply hk
      simpa [e.injective (Subtype.ext hjk)] using hj
    have hAjk : 0 ≤ T.a (e j).1 (e k).1 := T.a_offdiag_nonneg hjk
    have hbj : 0 ≤ T.a (e j).1 i := T.a_offdiag_nonneg (e j).2
    have hbk : 0 ≤ T.a (e k).1 i := T.a_offdiag_nonneg (e k).2
    have hqj : 0 ≤ T.a (e j).1 i / T.w i :=
      Int.ediv_nonneg hbj (by nlinarith [T.w_pos i])
    have hterm : 0 ≤ (T.a (e j).1 i / T.w i) * T.a (e k).1 i :=
      mul_nonneg hqj hbk
    have hz := hcross hj hk
    have hz' : contractedIntersection T i (e j) (e k) = 0 := by
      simpa [a'] using hz
    rw [hcontract_formula j k] at hz'
    have hzero : T.a (e j).1 (e k).1 = 0 := by nlinarith
    have htermzero :
        (T.a (e j).1 i / T.w i) * T.a (e k).1 i = 0 := by nlinarith
    refine ⟨hzero, ?_⟩
    rcases mul_eq_zero.mp htermzero with hqzero | hbkzero
    · left
      have hcancel := Int.ediv_mul_cancel (hdivwi (e j))
      rw [hqzero] at hcancel
      omega
    · right
      exact hbkzero
  have hconnected' : ¬ ∃ I : Set (Fin (T.n - 1)), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ ⦃j k⦄, j ∈ I → k ∉ I → a' j k = 0 := by
    rintro ⟨I, hI, hIne, hcross⟩
    have hnotall : ¬ (∀ j : Fin (T.n - 1), j ∈ I) := by
      intro hall
      apply hIne
      exact Set.eq_univ_of_forall hall
    by_cases hIzero : ∀ j, j ∈ I → T.a (e j).1 i = 0
    · let I' : Set (Fin T.n) := (fun j : Fin (T.n - 1) => (e j).1) '' I
      have hInon : I'.Nonempty := by
        rcases hI with ⟨j, hj⟩
        exact ⟨(e j).1, ⟨j, hj, rfl⟩⟩
      have hIne' : I' ≠ Set.univ := by
        intro hI'
        have : i ∈ I' := by rw [hI']; exact Set.mem_univ i
        rcases this with ⟨j, hj, hji⟩
        exact (e j).2 hji
      apply T.connected
      refine ⟨I', hInon, hIne', ?_⟩
      intro x y hx hy
      rcases hx with ⟨j, hj, rfl⟩
      by_cases hyi : y = i
      · simpa [hyi] using hIzero j hj
      · let k : RemainingIndex T i := ⟨y, hyi⟩
        have hk : e.symm k ∉ I := by
          intro hkI
          apply hy
          exact ⟨e.symm k, hkI, by simp [k]⟩
        have hzero := (hcross_data I hcross hj hk).1
        simpa [k] using hzero
    · push Not at hIzero
      obtain ⟨j₀, hj₀, hbj₀⟩ := hIzero
      have hcompzero : ∀ k, k ∉ I → T.a (e k).1 i = 0 := by
        intro k hk
        rcases (hcross_data I hcross hj₀ hk).2 with h | h
        · exact (hbj₀ h).elim
        · exact h
      have hnotall' : ∃ k, k ∉ I := by
        by_contra h
        apply hnotall
        intro k
        by_contra hk
        exact h ⟨k, hk⟩
      obtain ⟨k₀, hk₀⟩ := hnotall'
      let I' : Set (Fin T.n) :=
        (fun j : Fin (T.n - 1) => (e j).1) '' I ∪ {i}
      have hInon : I'.Nonempty := ⟨i, Or.inr rfl⟩
      have hIne' : I' ≠ Set.univ := by
        intro hI'
        have hmem : (e k₀).1 ∈ I' := by rw [hI']; exact Set.mem_univ _
        change (e k₀).1 ∈ (fun j : Fin (T.n - 1) => (e j).1) '' I ∨
          (e k₀).1 ∈ ({i} : Set (Fin T.n)) at hmem
        rcases hmem with hmem | hmem
        · rcases hmem with ⟨k, hk, heq⟩
          apply hk₀
          rw [← e.injective (Subtype.ext heq)]
          exact hk
        · exact (e k₀).2 hmem
      apply T.connected
      refine ⟨I', hInon, hIne', ?_⟩
      intro x y hx hy
      rcases hx with hx | hx
      · rcases hx with ⟨j, hj, rfl⟩
        have hyi : y ≠ i := by
          intro hyi
          apply hy
          exact Or.inr hyi
        let k : RemainingIndex T i := ⟨y, hyi⟩
        have hk : e.symm k ∉ I := by
          intro hkI
          apply hy
          exact Or.inl ⟨e.symm k, hkI, by simp [k]⟩
        have hzero := (hcross_data I hcross hj hk).1
        simpa [k] using hzero
      · have hxi : x = i := hx
        rw [hxi]
        have hyi : y ≠ i := by
          intro hyi
          apply hy
          exact Or.inr hyi
        let k : RemainingIndex T i := ⟨y, hyi⟩
        have hk : e.symm k ∉ I := by
          intro hkI
          apply hy
          exact Or.inl ⟨e.symm k, hkI, by simp [k]⟩
        have hzero := hcompzero (e.symm k) hk
        simpa [k, T.a_symmetric] using hzero
  have hrow_erase (j : Fin (T.n - 1)) :
      (Finset.univ.erase i).sum (fun k => T.a (e j).1 k * T.m k) =
        -T.a (e j).1 i * T.m i := by
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin T.n)))
      (f := fun k => T.a (e j).1 k * T.m k) (Finset.mem_univ i)
    rw [T.row_sum (e j).1] at hsplit
    nlinarith
  have hrow_i_erase :
      (Finset.univ.erase i).sum (fun k => T.a i k * T.m k) =
        -T.a i i * T.m i := by
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin T.n)))
      (f := fun k => T.a i k * T.m k) (Finset.mem_univ i)
    rw [T.row_sum i] at hsplit
    nlinarith
  have hrow_j (j : Fin (T.n - 1)) :
      (∑ k : Fin (T.n - 1), T.a (e j).1 (e k).1 * T.m (e k).1) =
        -T.a (e j).1 i * T.m i := by
    calc
      (∑ k : Fin (T.n - 1), T.a (e j).1 (e k).1 * T.m (e k).1) =
          (Finset.univ.erase i).sum (fun k => T.a (e j).1 k * T.m k) :=
        by simpa using hsum (fun k => T.a (e j).1 k * T.m k)
      _ = _ := hrow_erase j
  have hrow_i :
      (∑ k : Fin (T.n - 1), T.a i (e k).1 * T.m (e k).1) =
        -T.a i i * T.m i := by
    calc
      (∑ k : Fin (T.n - 1), T.a i (e k).1 * T.m (e k).1) =
          (Finset.univ.erase i).sum (fun k => T.a i k * T.m k) := by
            simpa using hsum (fun k => T.a i k * T.m k)
      _ = _ := hrow_i_erase
  have hrow' : ∀ j : Fin (T.n - 1),
      (Finset.univ : Finset (Fin (T.n - 1))).sum
        (fun k => a' j k * m' k) = 0 := by
    intro j
    have hcancel := Int.ediv_mul_cancel (hdivwi (e j))
    change (∑ k : Fin (T.n - 1),
      contractedIntersection T i (e j) (e k) * T.m (e k).1) = 0
    calc
      (∑ k : Fin (T.n - 1),
          contractedIntersection T i (e j) (e k) * T.m (e k).1) =
          ∑ k : Fin (T.n - 1),
            (T.a (e j).1 (e k).1 +
              (T.a (e j).1 i / T.w i) * T.a (e k).1 i) * T.m (e k).1 := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hcontract_formula]
      _ = (∑ k : Fin (T.n - 1),
            T.a (e j).1 (e k).1 * T.m (e k).1) +
          ∑ k : Fin (T.n - 1),
            (T.a (e j).1 i / T.w i) *
              (T.a (e k).1 i * T.m (e k).1) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = (∑ k : Fin (T.n - 1),
            T.a (e j).1 (e k).1 * T.m (e k).1) +
          (T.a (e j).1 i / T.w i) *
            (∑ k : Fin (T.n - 1), T.a i (e k).1 * T.m (e k).1) := by
              have heq :
                  (∑ k : Fin (T.n - 1),
                    T.a (e k).1 i * T.m (e k).1) =
                    ∑ k : Fin (T.n - 1), T.a i (e k).1 * T.m (e k).1 := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [T.a_symmetric (e k).1 i]
              rw [← Finset.mul_sum, heq]
      _ = 0 := by
        rw [hrow_j j, hrow_i, hi.2]
        calc
          -T.a (e j).1 i * T.m i +
                (T.a (e j).1 i / T.w i) * (- -T.w i * T.m i) =
              -(T.a (e j).1 i * T.m i) +
                (T.a (e j).1 i / T.w i * T.w i) * T.m i := by ring
          _ = 0 := by rw [hcancel]; ring
  have hterm_div (j k : Fin (T.n - 1)) :
      T.w (e j).1 ∣
        T.a (e j).1 i * T.a (e k).1 i / T.a i i := by
    have hwj := T.w_dvd (e j).1 i
    obtain ⟨r, hr⟩ := hwj
    rw [hi.2, hdiv_formula_right _ _ (hdivwi (e k))]
    refine ⟨-r * (T.a (e k).1 i / T.w i), ?_⟩
    rw [hr]
    ring
  have hwdiv' : ∀ j k : Fin (T.n - 1), w' j ∣ a' j k := by
    intro j k
    have hbase : T.w (e j).1 ∣
        T.a (e j).1 (e k).1 -
          T.a (e j).1 i * T.a (e k).1 i / T.a i i :=
      dvd_sub (T.w_dvd (e j).1 (e k).1) (hterm_div j k)
    have hweight := (hweight_data (e j)).2
    exact dvd_trans hweight (by simpa [a', contractedIntersection] using hbase)
  have hm'_pos : ∀ j : Fin (T.n - 1), 0 < m' j := by
    intro j
    simpa [m'] using T.m_pos (e j).1
  have hw'_pos : ∀ j : Fin (T.n - 1), 0 < w' j := by
    intro j
    simpa [w'] using hweight_pos (e j)
  have hg'_nonneg : ∀ j : Fin (T.n - 1), 0 ≤ g' j := by
    intro j
    simpa [g'] using hgenus (e j)
  have hprod_even_of_not : ∀ (p q : ℤ), ¬(Even q ∧ Odd p) →
      Even (p * (q - 1)) := by
    intro p q h
    by_cases hq_even : Even q
    · have hp_even : Even p := by
        by_contra hp_not
        exact h ⟨hq_even, Int.not_even_iff_odd.mp hp_not⟩
      obtain ⟨r, hr⟩ := hp_even
      refine ⟨r * (q - 1), ?_⟩
      rw [hr]
      ring
    · have hq_odd : Odd q := Int.not_even_iff_odd.mp hq_even
      have hqsub_even : Even (q - 1) := by
        obtain ⟨r, hr⟩ := hq_odd
        refine ⟨r, ?_⟩
        omega
      obtain ⟨r, hr⟩ := hqsub_even
      refine ⟨p * r, ?_⟩
      rw [hr]
      ring
  have hcomponent (j : Fin (T.n - 1)) :
      (w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2 =
        (T.w (e j).1 : ℚ) * ((T.g (e j).1 : ℚ) - 1) -
          (T.a (e j).1 i : ℚ) / 2 - (T.a (e j).1 (e j).1 : ℚ) / 2 := by
    have jne : (e j).1 ≠ i := (e j).2
    have hbnonneg : 0 ≤ T.a (e j).1 i := T.a_offdiag_nonneg jne
    have hwi_pos : 0 < T.w i := T.w_pos i
    have hwj_pos : 0 < T.w (e j).1 := T.w_pos (e j).1
    have hqdiv := hdivwi (e j)
    have hpdiv := hdivwj (e j)
    have hqediv : T.a (e j).1 i / T.w i * T.w i = T.a (e j).1 i := by
      rw [Int.ediv_mul_cancel hqdiv]
    have hpediv :
        T.a (e j).1 i / T.w (e j).1 * T.w (e j).1 = T.a (e j).1 i := by
      rw [Int.ediv_mul_cancel hpdiv]
    let p : ℤ := T.a (e j).1 i / T.w (e j).1
    let q : ℤ := T.a (e j).1 i / T.w i
    have hp_eq : T.a (e j).1 i = p * T.w (e j).1 := by
      dsimp [p]
      exact hpediv.symm
    have hq_eq : T.a (e j).1 i = q * T.w i := by
      dsimp [q]
      exact hqediv.symm
    have hnum_eq :
        T.a (e j).1 i ^ 2 - T.w i * T.a (e j).1 i =
          p * (q - 1) * (T.w (e j).1 * T.w i) := by
      have hsq : T.a (e j).1 i ^ 2 =
          (p * T.w (e j).1) * (q * T.w i) := by
        calc
          T.a (e j).1 i ^ 2 = T.a (e j).1 i * (q * T.w i) := by
            rw [hq_eq]
            ring
          _ = (p * T.w (e j).1) * (q * T.w i) := by rw [hp_eq]
      calc
        T.a (e j).1 i ^ 2 - T.w i * T.a (e j).1 i =
            (p * T.w (e j).1) * (q * T.w i) -
              T.w i * (p * T.w (e j).1) := by rw [hsq, hp_eq]
        _ = p * (q - 1) * (T.w (e j).1 * T.w i) := by ring
    have hAdiag := hcontract_formula_right j j
    by_cases hhalf : Even q ∧ Odd p
    · have hdivtwo := hhalf_dvd (e j) (by simpa [p, q] using hhalf)
      have htwohalf : 2 * (T.w (e j).1 / 2) = T.w (e j).1 := by
        have hcancel := Int.ediv_mul_cancel hdivtwo
        calc
          2 * (T.w (e j).1 / 2) =
              (T.w (e j).1 / 2) * 2 := by ring
          _ = T.w (e j).1 := hcancel
      have hhalf_pos : 0 < T.w (e j).1 / 2 :=
        Int.ediv_pos_of_pos_of_dvd hwj_pos (by norm_num) hdivtwo
      have hratio : T.w (e j).1 / (T.w (e j).1 / 2) = 2 := by
        apply Int.ediv_eq_of_eq_mul_left (ne_of_gt hhalf_pos)
        simpa [mul_comm] using htwohalf.symm
      have hden : 2 * (T.w (e j).1 / 2) * T.w i =
          T.w (e j).1 * T.w i := by rw [htwohalf]
      have hquot :
          (T.a (e j).1 i ^ 2 - T.w i * T.a (e j).1 i) /
              (2 * (T.w (e j).1 / 2) * T.w i) = p * (q - 1) := by
        have hden_pos : 0 < 2 * (T.w (e j).1 / 2) * T.w i :=
          mul_pos (mul_pos (by norm_num) hhalf_pos) hwi_pos
        apply Int.ediv_eq_of_eq_mul_left
          (ne_of_gt hden_pos)
        rw [hden, hnum_eq]
      have hcg : g' j = 2 * (T.g (e j).1 - 1) + 1 + p * (q - 1) := by
        dsimp [g']
        unfold contractedComponentGenus
        rw [show contractedWeight T i (e j) = T.w (e j).1 / 2 by
          simp [contractedWeight, p, q, hhalf], hratio, hquot]
      have hcw : w' j = T.w (e j).1 / 2 := by
        simp [w', contractedWeight, p, q, hhalf]
      have hAdiag' : a' j j =
          T.a (e j).1 (e j).1 +
            T.a (e j).1 i * (T.a (e j).1 i / T.w i) := by
        simpa [a'] using hAdiag
      have hinner :
          (w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2 =
            (T.w (e j).1 : ℚ) * ((T.g (e j).1 : ℚ) - 1) -
              (T.a (e j).1 i : ℚ) / 2 -
                (T.a (e j).1 (e j).1 : ℚ) / 2 := by
        rw [hcw, hcg, hAdiag']
        push_cast
        have htwohalfQ :
            (2 : ℚ) * (T.w (e j).1 / 2 : ℤ) = T.w (e j).1 := by
          exact_mod_cast htwohalf
        have htwohalfQ' :
            ((T.w (e j).1 / 2 : ℤ) : ℚ) * 2 =
              (T.w (e j).1 : ℚ) := by
          calc
            ((T.w (e j).1 / 2 : ℤ) : ℚ) * 2 =
                2 * ((T.w (e j).1 / 2 : ℤ) : ℚ) := by ring
            _ = (T.w (e j).1 : ℚ) := htwohalfQ
        have hp_eqQ : (T.a (e j).1 i : ℚ) =
            (p : ℚ) * (T.w (e j).1 : ℚ) := by exact_mod_cast hp_eq
        have hq_def : T.a (e j).1 i / T.w i = q := by rfl
        field_simp
        rw [hq_def, hp_eqQ, htwohalfQ']
        ring
      exact hinner
    · have hprod_even : Even (p * (q - 1)) :=
        hprod_even_of_not p q hhalf
      have hprod_dvd : (2 : ℤ) ∣ p * (q - 1) := by
        obtain ⟨r, hr⟩ := hprod_even
        refine ⟨r, ?_⟩
        omega
      have hnum' :
          T.a (e j).1 i ^ 2 - T.w i * T.a (e j).1 i =
            (p * (q - 1) / 2) * (2 * T.w (e j).1 * T.w i) := by
        rw [hnum_eq]
        have hc := Int.ediv_mul_cancel hprod_dvd
        calc
          p * (q - 1) * (T.w (e j).1 * T.w i) =
              (p * (q - 1) / 2 * 2) * (T.w (e j).1 * T.w i) := by rw [hc]
          _ = (p * (q - 1) / 2) *
              (2 * T.w (e j).1 * T.w i) := by ring
      have hquot :
          (T.a (e j).1 i ^ 2 - T.w i * T.a (e j).1 i) /
              (2 * T.w (e j).1 * T.w i) = p * (q - 1) / 2 := by
        have hden_pos : 0 < 2 * T.w (e j).1 * T.w i :=
          mul_pos (mul_pos (by norm_num) hwj_pos) hwi_pos
        apply Int.ediv_eq_of_eq_mul_left
          (ne_of_gt hden_pos)
        exact hnum'
      have hcg : g' j = T.g (e j).1 + p * (q - 1) / 2 := by
        dsimp [g']
        unfold contractedComponentGenus
        rw [show contractedWeight T i (e j) = T.w (e j).1 by
          simp [contractedWeight, p, q, hhalf], Int.ediv_self (ne_of_gt hwj_pos), hquot]
        ring
      have hcw : w' j = T.w (e j).1 := by
        simp [w', contractedWeight, p, q, hhalf]
      have hAdiag' : a' j j =
          T.a (e j).1 (e j).1 +
            T.a (e j).1 i * (T.a (e j).1 i / T.w i) := by
        simpa [a'] using hAdiag
      have hinner :
          (w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2 =
            (T.w (e j).1 : ℚ) * ((T.g (e j).1 : ℚ) - 1) -
              (T.a (e j).1 i : ℚ) / 2 -
                (T.a (e j).1 (e j).1 : ℚ) / 2 := by
        rw [hcw, hcg, hAdiag']
        push_cast
        have hcancel := Int.ediv_mul_cancel hprod_dvd
        have hcancelQ :
            ((p * (q - 1) / 2 : ℤ) : ℚ) * 2 =
              (p * (q - 1) : ℚ) := by
          exact_mod_cast hcancel
        have htwohalfQ' :
            ((p * (q - 1) / 2 : ℤ) : ℚ) * 2 =
              (p * (q - 1) : ℚ) := hcancelQ
        have hp_eqQ : (T.a (e j).1 i : ℚ) =
            (p : ℚ) * (T.w (e j).1 : ℚ) := by exact_mod_cast hp_eq
        have hq_def : T.a (e j).1 i / T.w i = q := by rfl
        field_simp
        rw [hq_def, hp_eqQ]
        calc
          (T.w (e j).1 : ℚ) *
                ((T.g (e j).1 : ℚ) +
                  ((p * (q - 1) / 2 : ℤ) : ℚ) - 1) * 2 -
              ((T.a (e j).1 (e j).1 : ℚ) +
                (p : ℚ) * (T.w (e j).1 : ℚ) * (q : ℚ)) =
            (T.w (e j).1 : ℚ) * 2 * ((T.g (e j).1 : ℚ) - 1) -
                (p : ℚ) * (T.w (e j).1 : ℚ) -
                (T.a (e j).1 (e j).1 : ℚ) +
              (T.w (e j).1 : ℚ) *
                (((p * (q - 1) / 2 : ℤ) : ℚ) * 2 -
                  (p : ℚ) * ((q : ℚ) - 1)) := by ring
          _ = (T.w (e j).1 : ℚ) * 2 * ((T.g (e j).1 : ℚ) - 1) -
                (p : ℚ) * (T.w (e j).1 : ℚ) -
                (T.a (e j).1 (e j).1 : ℚ) := by
              rw [hcancelQ]
              ring
      exact hinner
  have hsumQ (f : Fin T.n → ℚ) :
      (∑ j : Fin (T.n - 1), f (e j).1) =
        (Finset.univ.erase i).sum f := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (Fin (T.n - 1))))
      (t := Finset.univ.erase i) (f := fun j => f (e j).1) (g := f)
      (fun j _ => (e j).1)
    · intro j hj
      simp [Finset.mem_erase, (e j).2]
    · intro a ha b hb hab
      exact e.injective (Subtype.ext hab)
    · intro b hb
      let b' : RemainingIndex T i := ⟨b, (Finset.mem_erase.mp hb).1⟩
      refine ⟨e.symm b', by simp, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply b')
    · intro j hj
      rfl
  let T' : NumericalType :=
    { n := T.n - 1
      hn := by omega
      m := m'
      a := a'
      w := w'
      g := g'
      m_pos := hm'_pos
      w_pos := hw'_pos
      g_nonneg := hg'_nonneg
      a_symmetric := ha'_symm
      a_offdiag_nonneg := ha'_offdiag
      connected := hconnected'
      row_sum := hrow'
      w_dvd := hwdiv' }
  have hgenus_expr : genusExpression T' = genusExpression T := by
    exact contracted_genus_expression T i hi e a' w' g' hcomponent hsumQ
    /-
    have hsum_component :
        (∑ j : Fin (T.n - 1),
          (m' j : ℚ) *
            ((w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2)) =
          (Finset.univ.erase i).sum (fun k =>
            (T.m k : ℚ) *
              ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
                (T.a k k : ℚ) / 2 - (T.a k i : ℚ) / 2)) := by
      calc
        (∑ j : Fin (T.n - 1),
            (m' j : ℚ) *
              ((w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2)) =
            ∑ j : Fin (T.n - 1),
              (m' j : ℚ) *
                ((T.w (e j).1 : ℚ) * ((T.g (e j).1 : ℚ) - 1) -
                  (T.a (e j).1 i : ℚ) / 2 -
                    (T.a (e j).1 (e j).1 : ℚ) / 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hcomponent]
        _ = (Finset.univ.erase i).sum (fun k =>
            (T.m k : ℚ) *
              ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
                (T.a k k : ℚ) / 2 - (T.a k i : ℚ) / 2)) := by
              simpa [m'] using hsumQ (fun k =>
                (T.m k : ℚ) *
                  ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
                    (T.a k k : ℚ) / 2 - (T.a k i : ℚ) / 2))
    have hsum_b :
        (Finset.univ.erase i).sum (fun k =>
          (T.m k : ℚ) * (T.a k i : ℚ) / 2) =
            (T.w i : ℚ) * (T.m i : ℚ) / 2 := by
      have hrowQ := congrArg (fun z : ℤ => (z : ℚ)) hrow_i_erase
      push_cast at hrowQ
      calc
        (Finset.univ.erase i).sum (fun k =>
            (T.m k : ℚ) * (T.a k i : ℚ) / 2) =
            (1 / 2 : ℚ) * (Finset.univ.erase i).sum (fun k =>
              (T.a i k * T.m k : ℤ) : ℚ) := by
                rw [← Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k hk
                rw [T.a_symmetric k i]
                push_cast
                ring
        _ = (1 / 2 : ℚ) *
            ((-T.a i i * T.m i : ℤ) : ℚ) := by rw [hrowQ]
        _ = (T.w i : ℚ) * (T.m i : ℚ) / 2 := by
          rw [hi.2]
          push_cast
          ring
    dsimp [T', genusExpression]
    calc
      1 + (∑ j : Fin (T.n - 1),
          (m' j : ℚ) *
            ((w' j : ℚ) * ((g' j : ℚ) - 1) - (a' j j : ℚ) / 2)) =
          1 + (Finset.univ.erase i).sum (fun k =>
            (T.m k : ℚ) *
              ((T.w k : ℚ) * ((T.g k : ℚ) - 1) -
                (T.a k k : ℚ) / 2 - (T.a k i : ℚ) / 2)) := by
              rw [hsum_component]
      _ = 1 + (Finset.univ.erase i).sum (fun k =>
            (T.m k : ℚ) *
              ((T.w k : ℚ) * ((T.g k : ℚ) - 1) - (T.a k k : ℚ) / 2)) -
            (T.w i : ℚ) * (T.m i : ℚ) / 2 := by
              rw [Finset.sum_sub_distrib]
              rw [hsum_b]
              ring
      _ = 1 + (Finset.univ : Finset (Fin T.n)).sum (fun k =>
            (T.m k : ℚ) *
              ((T.w k : ℚ) * ((T.g k : ℚ) - 1) - (T.a k k : ℚ) / 2)) := by
              have hsplit := Finset.sum_erase_add
                (s := (Finset.univ : Finset (Fin T.n)))
                (f := fun k => (T.m k : ℚ) *
                  ((T.w k : ℚ) * ((T.g k : ℚ) - 1) - (T.a k k : ℚ) / 2))
                (Finset.mem_univ i)
              rw [← hsplit]
              have hgi := hi.1
              have hai := hi.2
              rw [hgi, hai]
              push_cast
              ring
    -/
  have hgenus_eq : genus T' = genus T := by
    have hcast : (genus T' : ℚ) = (genus T : ℚ) := by
      rw [genus_formula T', genus_formula T, hgenus_expr]
    exact_mod_cast hcast
  exact ⟨T', rfl, e, by simp [T', m'], by simp [T', a'],
    by simp [T', w'], by simp [T', g'], hgenus_eq⟩

def topologicalGenus (T : NumericalType) : ℤ :=
  1 - (T.n : ℤ) +
    (Formalization.Books.Models.Unit02.positiveOffDiagonalEdgeCount T.a : ℤ)

theorem topological_genus_nonnegative (T : NumericalType) :
    0 ≤ topologicalGenus T := by
  classical
  let G : SimpleGraph (Fin T.n) :=
    SimpleGraph.fromRel (fun i j => 0 < T.a i j)
  have hAdjReach : ∀ {x y : Fin T.n}, G.Adj x y → G.Reachable x y := by
    intro x y hxy
    exact (SimpleGraph.reachable_iff_reflTransGen (G := G) x y).2
      (Relation.ReflTransGen.single hxy)
  have hG : G.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨firstIndex T, ?_⟩
    intro v
    by_contra hv
    let I : Set (Fin T.n) := {x | G.Reachable (firstIndex T) x}
    have hInon : I.Nonempty := by
      refine ⟨firstIndex T, ?_⟩
      change G.Reachable (firstIndex T) (firstIndex T)
      exact SimpleGraph.Reachable.refl _
    have hIne : I ≠ Set.univ := by
      intro hI
      apply hv
      change v ∈ I
      rw [hI]
      exact Set.mem_univ v
    apply T.connected
    refine ⟨I, hInon, hIne, ?_⟩
    intro x y hx hy
    by_contra hzero
    have hxy : x ≠ y := by
      intro hxy
      subst y
      exact hy hx
    have hnonneg : 0 ≤ T.a x y := T.a_offdiag_nonneg hxy
    have hpos : 0 < T.a x y := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    have hadj : G.Adj x y := by
      simp [G, SimpleGraph.fromRel_adj]
      exact ⟨hxy, by simpa [T.a_symmetric x y] using hpos⟩
    have hyin : y ∈ I := by
      change G.Reachable (firstIndex T) y
      exact SimpleGraph.Reachable.trans hx (hAdjReach hadj)
    exact (hy hyin).elim
  have hsimp : ∀ {a b c d : Fin T.n},
      s(a, b) = s(c, d) →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    intro a b c d h
    exact Sym2.eq_iff.mp h
  have hsurj : ∀ (z : Sym2 (Fin T.n)), z ∈ G.edgeSet →
      ∃ e : Formalization.Books.Models.Unit02.positiveEdge T.a,
        (s(e.1.1, e.1.2) : Sym2 (Fin T.n)) = z := by
    intro z
    refine Sym2.inductionOn z ?_
    intro x y hmem
    change G.Adj x y at hmem
    simp [G, SimpleGraph.fromRel_adj] at hmem
    rcases hmem with ⟨hne, hpos | hpos⟩
    · have hposxy : 0 < T.a x y := hpos
      have hposyx : 0 < T.a y x := by
        simpa [T.a_symmetric x y] using hpos
      rcases lt_or_gt_of_ne hne with hxy | hyx
      · exact ⟨⟨(x, y), hxy, hposxy⟩, rfl⟩
      · exact ⟨⟨(y, x), hyx, hposyx⟩, by simp⟩
    · have hposxy : 0 < T.a x y := by
        simpa [T.a_symmetric x y] using hpos
      have hposyx : 0 < T.a y x := hpos
      rcases lt_or_gt_of_ne hne with hxy | hyx
      · exact ⟨⟨(x, y), hxy, hposxy⟩, rfl⟩
      · exact ⟨⟨(y, x), hyx, hposyx⟩, by simp⟩
  let f : Formalization.Books.Models.Unit02.positiveEdge T.a → G.edgeSet :=
    fun e => ⟨s(e.1.1, e.1.2), by
      change G.Adj e.1.1 e.1.2
      simp [G, SimpleGraph.fromRel_adj]
      exact ⟨ne_of_lt e.2.1, Or.inl e.2.2⟩⟩
  have hf_surj : Function.Surjective f := by
    intro z
    obtain ⟨e, he⟩ := hsurj z.1 z.2
    refine ⟨e, ?_⟩
    apply Subtype.ext
    exact he
  have hf_inj : Function.Injective f := by
    intro e₁ e₂ he
    apply Subtype.ext
    apply Prod.ext
    · have hsym : s(e₁.1.1, e₁.1.2) = s(e₂.1.1, e₂.1.2) :=
        congrArg Subtype.val he
      rcases hsimp hsym with h | h
      · exact h.1
      · omega
    · have hsym : s(e₁.1.1, e₁.1.2) = s(e₂.1.1, e₂.1.2) :=
        congrArg Subtype.val he
      rcases hsimp hsym with h | h
      · exact h.2
      · omega
  let ecard : Formalization.Books.Models.Unit02.positiveEdge T.a ≃ G.edgeSet :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hcardeq : Fintype.card G.edgeSet =
      Fintype.card (Formalization.Books.Models.Unit02.positiveEdge T.a) := by
    symm
    exact Fintype.card_congr ecard
  have hcard := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hG
  have hcard' : T.n ≤ Fintype.card G.edgeSet + 1 := by
    simpa using hcard
  have hnat : T.n ≤
      Formalization.Books.Models.Unit02.positiveOffDiagonalEdgeCount T.a + 1 := by
    simpa [hcardeq, Formalization.Books.Models.Unit02.positiveOffDiagonalEdgeCount] using hcard'
  have hint : (T.n : ℤ) ≤
      (Formalization.Books.Models.Unit02.positiveOffDiagonalEdgeCount T.a : ℤ) + 1 := by
    exact_mod_cast hnat
  dsimp [topologicalGenus]
  omega

/-! Minimality excludes all `(-1)`-indices. -/
def IsMinimal (T : NumericalType) : Prop :=
  ¬ ∃ i, IsMinusOneIndex T i

theorem minimal_genus_at_least_one (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hminimal : IsMinimal T)
    (hn : 1 < T.n) :
    genusValue ≥ 1 := by
  have hcontrib : ∀ i, (0 : ℚ) ≤ genusContribution T i := by
    intro i
    by_contra hneg
    exact hminimal ⟨i, minus_one_contribution T genusValue hgenus hn (lt_of_not_ge hneg)⟩
  have hsum : (0 : ℚ) ≤ ∑ i : Fin T.n, genusContribution T i :=
    Finset.sum_nonneg (fun i hi => hcontrib i)
  have hsum' : (0 : ℚ) ≤ ∑ i : Fin T.n,
      (T.m i : ℚ) * ((T.w i : ℚ) * ((T.g i : ℚ) - 1) - (T.a i i : ℚ) / 2) := by
    simpa [genusContribution] using hsum
  have hformula := genus_formula T
  rw [hgenus, genusExpression] at hformula
  have hbound : (1 : ℚ) ≤ (genusValue : ℚ) := by
    linarith [hsum', hformula]
  exact_mod_cast hbound

theorem minimal_genus_ge_topological_genus (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hminimal : IsMinimal T)
    (hn : 1 < T.n) :
    genusValue ≥ topologicalGenus T := by
  classical
  let k : Fin T.n → ℤ := fun i => -Classical.choose (T.w_dvd i i)
  have hk_eq (i : Fin T.n) : T.a i i = -T.w i * k i := by
    dsimp [k]
    rw [Classical.choose_spec (T.w_dvd i i)]
    ring
  have hk_pos (i : Fin T.n) : 0 < k i := by
    have hai := diagonal_negative T genusValue hgenus hn i
    have hwi := T.w_pos i
    rw [hk_eq] at hai
    nlinarith
  have hk_ge_two (i : Fin T.n) (hgi : T.g i = 0) : 2 ≤ k i := by
    by_contra hnot
    have hki : k i = 1 := by omega
    apply hminimal
    refine ⟨i, hgi, ?_⟩
    rw [hk_eq, hki]
    ring

  let f : Fin T.n × Fin T.n → ℚ := fun p =>
    (T.a p.1 p.2 : ℚ) * (T.m p.2 : ℚ) /
      ((T.w p.1 : ℚ) * (T.m p.1 : ℚ))
  have hki_formula (i : Fin T.n) :
      (k i : ℚ) = (Finset.univ.erase i).sum (fun j => f (i, j)) := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin T.n)))
      (f := fun j => T.a i j * T.m j) (Finset.mem_univ i)
    have hrow :
        (Finset.univ.erase i).sum (fun j => T.a i j * T.m j) +
            T.a i i * T.m i = 0 := by
      calc
        (Finset.univ.erase i).sum (fun j => T.a i j * T.m j) +
            T.a i i * T.m i =
            (Finset.univ : Finset (Fin T.n)).sum
              (fun j => T.a i j * T.m j) := hsplit
        _ = 0 := T.row_sum i
    have hrowQ := congrArg (fun z : ℤ => (z : ℚ)) hrow
    push_cast at hrowQ
    rw [hk_eq] at hrowQ
    have hrowQ' :
        (Finset.univ.erase i).sum
            (fun j => (T.a i j : ℚ) * (T.m j : ℚ)) =
          (T.w i : ℚ) * (k i : ℚ) * (T.m i : ℚ) := by
      linarith
    dsimp [f]
    calc
      (k i : ℚ) =
          ((T.w i : ℚ) * (k i : ℚ) * (T.m i : ℚ)) /
            ((T.w i : ℚ) * (T.m i : ℚ)) := by
              field_simp
      _ =
          ((Finset.univ.erase i).sum
            (fun j => (T.a i j : ℚ) * (T.m j : ℚ))) /
            ((T.w i : ℚ) * (T.m i : ℚ)) := by rw [hrowQ']
      _ = (Finset.univ.erase i).sum (fun j =>
          (T.a i j : ℚ) * (T.m j : ℚ) /
            ((T.w i : ℚ) * (T.m i : ℚ))) := by
              rw [Finset.sum_div]

  let P : Finset (Fin T.n × Fin T.n) := Finset.univ ×ˢ Finset.univ
  let D : Finset (Fin T.n × Fin T.n) :=
    P.filter (fun p => p.1 ≠ p.2)
  let U : Finset (Fin T.n × Fin T.n) :=
    P.filter (fun p => p.1 < p.2)
  let L : Finset (Fin T.n × Fin T.n) :=
    D.filter (fun p => ¬p.1 < p.2)
  have hsplit : D.sum f = U.sum f + L.sum f := by
    have hUeq : U = D.filter (fun p => p.1 < p.2) := by
      ext p
      simp only [U, D, Finset.mem_filter, P]
      constructor
      · rintro ⟨hp, hlt⟩
        exact ⟨⟨hp, ne_of_lt hlt⟩, hlt⟩
      · rintro ⟨⟨hp, hne⟩, hlt⟩
        exact ⟨hp, hlt⟩
    rw [hUeq]
    have h := Finset.sum_filter_add_sum_filter_not
      (s := D) (p := fun p : Fin T.n × Fin T.n => p.1 < p.2) (f := f)
    have h' := h.symm
    simpa only [L] using h'
  have hL : L.sum f = U.sum (fun p => f (p.2, p.1)) := by
    apply Finset.sum_bij (s := L) (t := U)
      (f := f) (g := fun p => f (p.2, p.1)) (fun p _ => (p.2, p.1))
    · intro p hp
      have hpD : p ∈ D := (Finset.mem_filter.mp hp).1
      have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hpD).2
      have hpnot : ¬p.1 < p.2 := (Finset.mem_filter.mp hp).2
      have hlt : p.2 < p.1 :=
        lt_of_le_of_ne (le_of_not_gt hpnot) (Ne.symm hpne)
      simpa [U, P] using hlt
    · intro p hp q hq heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro q hq
      have hq' : q ∈ P.filter (fun p => p.1 < p.2) := by
        simpa [U] using hq
      have hlt : q.1 < q.2 := (Finset.mem_filter.mp hq').2
      have hne : q.2 ≠ q.1 := ne_of_gt hlt
      have hnlt : ¬q.2 < q.1 := not_lt_of_ge (le_of_lt hlt)
      refine ⟨(q.2, q.1), ?_, ?_⟩
      · simp only [L, Finset.mem_filter]
        refine ⟨?_, hnlt⟩
        simp only [D, Finset.mem_filter]
        exact ⟨by simp [P], hne⟩
      · rfl
    · intro p hp
      rfl
  have hDpair : D.sum f = U.sum (fun p => f p + f (p.2, p.1)) := by
    rw [hsplit, hL]
    rw [← Finset.sum_add_distrib]

  let Upos : Finset (Fin T.n × Fin T.n) :=
    U.filter (fun p => 0 < T.a p.1 p.2)
  have hUzero :
      (U.filter (fun p => ¬0 < T.a p.1 p.2)).sum
          (fun p => f p + f (p.2, p.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
    have hlt : p.1 < p.2 := by
      simpa [U, P] using (Finset.mem_filter.mp hpU).2
    have hnot : ¬0 < T.a p.1 p.2 := (Finset.mem_filter.mp hp).2
    have hnonneg : 0 ≤ T.a p.1 p.2 := T.a_offdiag_nonneg (ne_of_lt hlt)
    have haz : T.a p.1 p.2 = 0 := by omega
    have haz' : T.a p.2 p.1 = 0 := by
      rw [T.a_symmetric]
      exact haz
    simp [f, haz, haz']
  have hDpos :
      D.sum f = Upos.sum (fun p => f p + f (p.2, p.1)) := by
    rw [hDpair]
    have h := Finset.sum_filter_add_sum_filter_not
      (s := U) (p := fun p : Fin T.n × Fin T.n => 0 < T.a p.1 p.2)
      (f := fun p => f p + f (p.2, p.1))
    have h' := h.symm
    rw [hUzero, add_zero] at h'
    simpa only [Upos] using h'

  have hpair (p : Fin T.n × Fin T.n) (hp : p ∈ Upos) :
      (2 : ℚ) ≤ f p + f (p.2, p.1) := by
    have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
    have hlt : p.1 < p.2 := by
      simpa [U, P] using (Finset.mem_filter.mp hpU).2
    have hpos : 0 < T.a p.1 p.2 := (Finset.mem_filter.mp hp).2
    have hpos' : 0 < T.a p.2 p.1 := by
      rw [T.a_symmetric]
      exact hpos
    have hw1 : (0 : ℚ) < (T.w p.1 : ℚ) := by exact_mod_cast T.w_pos p.1
    have hw2 : (0 : ℚ) < (T.w p.2 : ℚ) := by exact_mod_cast T.w_pos p.2
    have hm1 : (0 : ℚ) < (T.m p.1 : ℚ) := by exact_mod_cast T.m_pos p.1
    have hm2 : (0 : ℚ) < (T.m p.2 : ℚ) := by exact_mod_cast T.m_pos p.2
    rcases T.w_dvd p.1 p.2 with ⟨c₁, hc₁⟩
    rcases T.w_dvd p.2 p.1 with ⟨c₂, hc₂⟩
    have hc₁pos : 0 < c₁ := by nlinarith [hpos, T.w_pos p.1]
    have hc₂pos : 0 < c₂ := by nlinarith [hpos', T.w_pos p.2]
    have hprod : f p * f (p.2, p.1) = (c₁ : ℚ) * c₂ := by
      dsimp [f]
      rw [hc₁, hc₂, T.a_symmetric p.2 p.1]
      push_cast
      field_simp
      ring
    have hprod' : (1 : ℚ) ≤ f p * f (p.2, p.1) := by
      rw [hprod]
      have hc₁' : (1 : ℚ) ≤ c₁ := by exact_mod_cast (show (1 : ℤ) ≤ c₁ by omega)
      have hc₂' : (1 : ℚ) ≤ c₂ := by exact_mod_cast (show (1 : ℤ) ≤ c₂ by omega)
      nlinarith
    have hf1 : 0 < f p := by
      dsimp [f]
      positivity
    have hf2 : 0 < f (p.2, p.1) := by
      dsimp [f]
      positivity
    have hsq : (4 : ℚ) ≤ (f p + f (p.2, p.1)) ^ 2 := by
      nlinarith [sq_nonneg (f p - f (p.2, p.1))]
    nlinarith
  have hDlower :
      (2 : ℚ) * (Upos.card : ℚ) ≤ D.sum f := by
    rw [hDpos]
    calc
      (2 : ℚ) * (Upos.card : ℚ) = Upos.sum (fun _ => (2 : ℚ)) := by simp
      _ ≤ Upos.sum (fun p => f p + f (p.2, p.1)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpair p hp

  let E : Finset (Fin T.n × Fin T.n) :=
    U.filter (fun p => 0 < T.a p.1 p.2)
  have hcard : Upos.card = Fintype.card
      (Formalization.Books.Models.Unit02.positiveEdge T.a) := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      simp only [Upos, U, P, Finset.mem_filter]
      exact ⟨by simp, e.2.1, e.2.2⟩
    · intro e he e' he' heq
      exact Subtype.ext heq
    · intro p hp
      have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
      have hlt : p.1 < p.2 := by
        simpa [U, P] using (Finset.mem_filter.mp hpU).2
      have hpos : 0 < T.a p.1 p.2 := (Finset.mem_filter.mp hp).2
      let e : Formalization.Books.Models.Unit02.positiveEdge T.a :=
        ⟨p, ⟨hlt, hpos⟩⟩
      exact ⟨e, by simp, rfl⟩

  have hsumk :
      (∑ i : Fin T.n, (k i : ℚ)) = D.sum f := by
    calc
      (∑ i : Fin T.n, (k i : ℚ)) =
          ∑ i : Fin T.n, (Finset.univ.erase i).sum (fun j => f (i, j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hki_formula i
      _ = D.sum f := by
        dsimp [D, P]
        rw [Finset.sum_filter]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show (Finset.univ.erase i : Finset (Fin T.n)) =
            Finset.univ.filter (fun j => j ≠ i) by ext j; simp]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji, Ne.symm hji]
  have hsumk_lower :
      (2 : ℚ) * (Fintype.card
        (Formalization.Books.Models.Unit02.positiveEdge T.a) : ℚ) ≤
        ∑ i : Fin T.n, (k i : ℚ) := by
    rw [hsumk]
    rw [← hcard]
    exact hDlower

  have hgenusQ : (genusValue : ℚ) =
      1 + ∑ i : Fin T.n,
        ((T.m i : ℚ) * (T.w i : ℚ)) *
          ((T.g i : ℚ) - 1 + (k i : ℚ) / 2) := by
    have hformula := genus_formula T
    rw [hgenus, genusExpression] at hformula
    rw [← hformula]
    apply congrArg (fun x : ℚ => 1 + x)
    apply Finset.sum_congr rfl
    intro i hi
    rw [hk_eq]
    push_cast
    ring
  have hb_nonneg (i : Fin T.n) :
      (0 : ℚ) ≤ (T.g i : ℚ) - 1 + (k i : ℚ) / 2 := by
    by_cases hgi : T.g i = 0
    · have hki := hk_ge_two i hgi
      rw [hgi]
      norm_num
      exact_mod_cast hki
    · have hgi' : 1 ≤ T.g i := by omega
      have hkp := hk_pos i
      exact_mod_cast (show (0 : ℤ) ≤ T.g i - 1 + k i / 2 by
        have : (0 : ℚ) ≤ (T.g i : ℚ) - 1 := by exact_mod_cast (by omega : (0 : ℤ) ≤ T.g i - 1)
        positivity)
  have hp_nonneg (i : Fin T.n) :
      (1 : ℚ) ≤ (T.m i : ℚ) * (T.w i : ℚ) := by
    have hm := T.m_pos i
    have hw := T.w_pos i
    exact_mod_cast (show (1 : ℤ) ≤ T.m i * T.w i by nlinarith)
  have hsum_b :
      (-(T.n : ℚ) +
        (Fintype.card (Formalization.Books.Models.Unit02.positiveEdge T.a) : ℚ)) ≤
      ∑ i : Fin T.n, ((T.g i : ℚ) - 1 + (k i : ℚ) / 2) := by
    have hg_sum : (-(T.n : ℚ)) ≤ ∑ i : Fin T.n, ((T.g i : ℚ) - 1) := by
      simp only [Finset.sum_sub_distrib]
      have := Finset.sum_nonneg (fun i hi => T.g_nonneg i)
      push_cast at this
      linarith
    have hk_sum :
        (2 : ℚ) * (Fintype.card
          (Formalization.Books.Models.Unit02.positiveEdge T.a) : ℚ) ≤
        ∑ i : Fin T.n, (k i : ℚ) := hsumk_lower
    rw [Finset.sum_add_distrib]
    linarith
  have hsum_prod :
      (∑ i : Fin T.n, ((T.g i : ℚ) - 1 + (k i : ℚ) / 2)) ≤
      ∑ i : Fin T.n,
        ((T.m i : ℚ) * (T.w i : ℚ)) *
          ((T.g i : ℚ) - 1 + (k i : ℚ) / 2) := by
    apply Finset.sum_le_sum
    intro i hi
    have hb := hb_nonneg i
    have hp := hp_nonneg i
    nlinarith
  have hgenus_lower :
      (1 - (T.n : ℚ) +
        (Fintype.card (Formalization.Books.Models.Unit02.positiveEdge T.a) : ℚ)) ≤
      (genusValue : ℚ) := by
    rw [hgenusQ]
    linarith [hsum_b, hsum_prod]
  dsimp [topologicalGenus]
  exact_mod_cast hgenus_lower

/-! The combined bound stated before the two component lemmas. -/
theorem minimal_genus_ge_max_one_topological_genus (T : NumericalType)
    (genusValue : ℤ) (hgenus : IsOfGenus T genusValue)
    (hminimal : IsMinimal T) (hn : 1 < T.n) :
    max 1 (topologicalGenus T) ≤ genusValue := by
  exact (max_le_iff).2 ⟨minimal_genus_at_least_one T genusValue hgenus hminimal hn,
    minimal_genus_ge_topological_genus T genusValue hgenus hminimal hn⟩

/-! A zero genus contribution is exactly a `(-2)` component in the reducible case. -/
theorem minus_two_contribution (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hn : 1 < T.n) {i : Fin T.n}
    (hcontribution : genusContribution T i = 0) :
    T.g i = 0 ∧ T.a i i = -2 * T.w i := by
  have hai : T.a i i < 0 := diagonal_negative T genusValue hgenus hn i
  have hmQ : (0 : ℚ) < (T.m i : ℚ) := by
    exact_mod_cast T.m_pos i
  have hcontribution' : (T.m i : ℚ) *
      ((T.w i : ℚ) * ((T.g i : ℚ) - 1) - (T.a i i : ℚ) / 2) = 0 := by
    simpa [genusContribution] using hcontribution
  have hinner : (T.w i : ℚ) * ((T.g i : ℚ) - 1) -
      (T.a i i : ℚ) / 2 = 0 := by
    nlinarith [hcontribution', hmQ]
  have hineqQ : (2 : ℚ) * (T.w i : ℚ) * ((T.g i : ℚ) - 1) =
      (T.a i i : ℚ) := by
    linarith
  have hineq : 2 * T.w i * (T.g i - 1) = T.a i i := by
    exact_mod_cast hineqQ
  have hgnonneg := T.g_nonneg i
  have hwpos := T.w_pos i
  have hgzero : T.g i = 0 := by
    by_contra h
    have hgone : 1 ≤ T.g i := by omega
    have hnonneg : 0 ≤ 2 * T.w i * (T.g i - 1) := by
      have hw : 0 ≤ T.w i := by omega
      have hg : 0 ≤ T.g i - 1 := by omega
      nlinarith
    omega
  refine ⟨hgzero, ?_⟩
  rw [hgzero] at hineq
  nlinarith

def IsMinusTwoIndex (T : NumericalType) (i : Fin T.n) : Prop :=
  T.g i = 0 ∧ T.a i i = -2 * T.w i

theorem minus_two_index_iff_zero_contribution (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.n) (i : Fin T.n) :
    IsMinusTwoIndex T i ↔ genusContribution T i = 0 := by
  have _hminimal : IsMinimal T := hminimal
  constructor
  · rintro ⟨hg, ha⟩
    rw [genusContribution, hg, ha]
    push_cast
    ring
  · intro h
    exact minus_two_contribution T (genus T) rfl hn h

theorem minus_two_index_iff_not_positive_contribution (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.n) (i : Fin T.n) :
    IsMinusTwoIndex T i ↔ ¬ 0 < genusContribution T i := by
  have hnonneg : 0 ≤ genusContribution T i := by
    by_contra hneg
    have hneg' : genusContribution T i < 0 := lt_of_not_ge hneg
    exact hminimal ⟨i, minus_one_contribution T (genus T) rfl hn hneg'⟩
  have hzero := minus_two_index_iff_zero_contribution T hminimal hn i
  constructor
  · intro htwo
    have hz : genusContribution T i = 0 := hzero.1 htwo
    rw [hz]
    norm_num
  · intro hnot
    apply hzero.2
    exact le_antisymm (not_lt.mp hnot) hnonneg

/-! The equality case exhibited in the source remark. -/
theorem genus_eq_topological_genus_of_unit_data (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.n)
    (hm : ∀ i, T.m i = 1) (hw : ∀ i, T.w i = 1)
    (hg : ∀ i, T.g i = 0)
    (ha : ∀ ⦃i j⦄, i < j → T.a i j = 0 ∨ T.a i j = 1) :
    genus T = topologicalGenus T := by
  have _hminimal : IsMinimal T := hminimal
  have _hn : 1 < T.n := hn
  have hdiag (i : Fin T.n) :
      T.a i i = - (Finset.univ.erase i).sum (fun j => T.a i j) := by
    have hrow : (Finset.univ : Finset (Fin T.n)).sum (fun j => T.a i j) = 0 := by
      simpa [hm] using T.row_sum i
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin T.n)))
      (f := fun j => T.a i j) (Finset.mem_univ i)
    rw [hrow] at hsplit
    nlinarith
  let P : Finset (Fin T.n × Fin T.n) := Finset.univ ×ˢ Finset.univ
  let D : Finset (Fin T.n × Fin T.n) :=
    P.filter (fun p => p.1 ≠ p.2)
  let U : Finset (Fin T.n × Fin T.n) :=
    P.filter (fun p => p.1 < p.2)
  let L : Finset (Fin T.n × Fin T.n) :=
    D.filter (fun p => ¬ p.1 < p.2)
  let f : Fin T.n × Fin T.n → ℤ := fun p => T.a p.1 p.2
  have hD :
      D.sum f = ∑ i : Fin T.n, (Finset.univ.erase i).sum (fun j => T.a i j) := by
    dsimp [D, P]
    rw [Finset.sum_filter]
    change ((Finset.univ ×ˢ Finset.univ).sum
      (fun p => if p.1 ≠ p.2 then T.a p.1 p.2 else 0)) =
      ∑ i : Fin T.n, (Finset.univ.erase i).sum (fun j => T.a i j)
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (Finset.univ.erase i : Finset (Fin T.n)) =
        Finset.univ.filter (fun j => j ≠ i) by ext j; simp]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = i
    · subst j
      simp
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]
  have hL : L.sum f = U.sum f := by
    apply Finset.sum_bij (s := L) (t := U) (f := f) (g := f)
      (fun p _ => (p.2, p.1))
    · intro p hp
      have hpD : p ∈ D := (Finset.mem_filter.mp hp).1
      have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hpD).2
      have hpnot : ¬ p.1 < p.2 := (Finset.mem_filter.mp hp).2
      have hlt : p.2 < p.1 :=
        lt_of_le_of_ne (le_of_not_gt hpnot) (Ne.symm hpne)
      simpa [U, P] using hlt
    · intro p hp q hq hEq
      exact Prod.ext (congrArg Prod.snd hEq) (congrArg Prod.fst hEq)
    · intro q hq
      have hq' : q ∈ P.filter (fun p => p.1 < p.2) := by
        simpa [U] using hq
      have hqlt : q.1 < q.2 := (Finset.mem_filter.mp hq').2
      have hne : q.2 ≠ q.1 := ne_of_gt hqlt
      have hnlt : ¬ q.2 < q.1 := not_lt_of_ge (le_of_lt hqlt)
      refine ⟨(q.2, q.1), ?_, ?_⟩
      · simp only [L, Finset.mem_filter]
        refine ⟨?_, hnlt⟩
        simp only [D, Finset.mem_filter]
        refine ⟨?_, hne⟩
        change (q.2, q.1) ∈ (Finset.univ ×ˢ Finset.univ)
        simp
      · rfl
    · intro p hp
      change T.a p.1 p.2 = T.a p.2 p.1
      exact T.a_symmetric _ _
  have hsplit :
      D.sum f = U.sum f + L.sum f := by
    have hUeq : U = D.filter (fun p => p.1 < p.2) := by
      ext p
      simp only [U, D, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hlt⟩
        exact ⟨⟨hp, ne_of_lt hlt⟩, hlt⟩
      · rintro ⟨⟨hp, hne⟩, hlt⟩
        exact ⟨hp, hlt⟩
    rw [hUeq]
    have h := Finset.sum_filter_add_sum_filter_not
      (s := D) (p := fun p : Fin T.n × Fin T.n => p.1 < p.2) (f := f)
    have h' := h.symm
    simpa only [L] using h'
  have hdiag_sum :
      (Finset.univ : Finset (Fin T.n)).sum (fun i => T.a i i) = -D.sum f := by
    calc
      (Finset.univ : Finset (Fin T.n)).sum (fun i => T.a i i) =
          ∑ i : Fin T.n, -(Finset.univ.erase i).sum (fun j => T.a i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hdiag i
      _ = -∑ i : Fin T.n, (Finset.univ.erase i).sum (fun j => T.a i j) := by
            rw [Finset.sum_neg_distrib]
      _ = -D.sum f := by rw [hD]
  have hDtwo : D.sum f = 2 * U.sum f := by
    rw [hsplit, hL]
    ring
  let E : Finset (Fin T.n × Fin T.n) :=
    U.filter (fun p => 0 < T.a p.1 p.2)
  have hUzero :
      (U.filter (fun p => ¬ 0 < T.a p.1 p.2)).sum f = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
    have hpU' : p ∈ P.filter (fun p => p.1 < p.2) := by
      change p ∈ P.filter (fun p => p.1 < p.2) at hpU
      exact hpU
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hpU').2
    have hnot : ¬ 0 < T.a p.1 p.2 := (Finset.mem_filter.mp hp).2
    rcases ha hlt with hzero | hone
    · simp [hzero]
    · exfalso
      apply hnot
      rw [hone]
      norm_num
  have hUsum : U.sum f = E.sum f := by
    have h := Finset.sum_filter_add_sum_filter_not
      (s := U) (p := fun p : Fin T.n × Fin T.n => 0 < T.a p.1 p.2) (f := f)
    have h' := h.symm
    rw [hUzero, add_zero] at h'
    simpa only [E] using h'
  have hedge : E.sum f = Fintype.card (Formalization.Books.Models.Unit02.positiveEdge T.a) := by
    have hbij :
        E.sum f =
          ∑ e : Formalization.Books.Models.Unit02.positiveEdge T.a,
            T.a e.1.1 e.1.2 := by
      symm
      apply Finset.sum_bij
        (s := (Finset.univ :
          Finset (Formalization.Books.Models.Unit02.positiveEdge T.a)))
        (t := E)
        (f := fun e => T.a e.1.1 e.1.2) (g := f)
        (fun e _ => e.1)
      · intro e he
        simp only [E, Finset.mem_filter]
        refine ⟨?_, e.2.2⟩
        simpa [U, P] using e.2.1
      · intro e he e' he' heq
        exact Subtype.ext heq
      · intro p hp
        have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
        have hpU' : p ∈ P.filter (fun p => p.1 < p.2) := by
          simpa [U] using hpU
        have hlt : p.1 < p.2 := (Finset.mem_filter.mp hpU').2
        have hpos : 0 < T.a p.1 p.2 := (Finset.mem_filter.mp hp).2
        let e : Formalization.Books.Models.Unit02.positiveEdge T.a :=
          { val := p, property := ⟨hlt, hpos⟩ }
        exact ⟨e, by simp, rfl⟩
      · intro e he
        rfl
    rw [hbij]
    have hedgeval : ∀ e : Formalization.Books.Models.Unit02.positiveEdge T.a,
        T.a e.1.1 e.1.2 = 1 := by
      intro e
      rcases ha e.2.1 with hzero | hone
      · exfalso
        have hepos := e.2.2
        rw [hzero] at hepos
        norm_num at hepos
      · exact hone
    simp [hedgeval]
  have hdiag_edges :
      (Finset.univ : Finset (Fin T.n)).sum (fun i => T.a i i) =
        -2 * (Formalization.Books.Models.Unit02.positiveOffDiagonalEdgeCount T.a : ℤ) := by
    rw [hdiag_sum, hDtwo, hUsum, hedge]
    rfl
  have hformula := genus_formula T
  have hformula' : (genus T : ℚ) =
      1 + ∑ i : Fin T.n,
        (1 : ℚ) * ((1 : ℚ) * ((0 : ℚ) - 1) - (T.a i i : ℚ) / 2) := by
    rw [hformula]
    apply congrArg (fun x : ℚ => x) ?_
    apply congrArg (fun x : ℚ => 1 + x)
    apply Finset.sum_congr rfl
    intro i hi
    rw [hm i, hw i, hg i]
    norm_num
  have hdiagQ := congrArg (fun z : ℤ => (z : ℚ)) hdiag_edges
  push_cast at hdiagQ
  have hsum_simpl :
      (∑ i : Fin T.n,
        (1 : ℚ) * ((1 : ℚ) * ((0 : ℚ) - 1) - (T.a i i : ℚ) / 2)) =
        -(T.n : ℚ) - (∑ i : Fin T.n, (T.a i i : ℚ)) / 2 := by
    calc
      (∑ i : Fin T.n,
          (1 : ℚ) * ((1 : ℚ) * ((0 : ℚ) - 1) - (T.a i i : ℚ) / 2)) =
          ∑ i : Fin T.n, (-(1 : ℚ) - (T.a i i : ℚ) / 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin T.n, -(1 : ℚ)) -
            ∑ i : Fin T.n, (T.a i i : ℚ) / 2 := by
            rw [Finset.sum_sub_distrib]
      _ = -(T.n : ℚ) - (∑ i : Fin T.n, (T.a i i : ℚ)) / 2 := by
            simp
            simp only [div_eq_mul_inv]
            rw [← Finset.sum_mul]
  have hcast : (genus T : ℚ) = (topologicalGenus T : ℚ) := by
    rw [hformula', hsum_simpl, hdiagQ]
    simp [topologicalGenus,
      Formalization.Books.Models.Unit02.positiveOffDiagonalEdgeCount]
    ring
  exact_mod_cast hcast

end Formalization.Books.Models.Unit03
