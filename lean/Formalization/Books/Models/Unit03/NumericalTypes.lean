import Formalization.Books.Models.Unit02.LinearAlgebra

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
  sorry

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
  sorry

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
  sorry

def topologicalGenus (T : NumericalType) : ℤ :=
  1 - (T.n : ℤ) +
    (Formalization.Books.Models.Unit02.positiveOffDiagonalEdgeCount T.a : ℤ)

theorem topological_genus_nonnegative (T : NumericalType) :
    0 ≤ topologicalGenus T := by
  sorry

/-! Minimality excludes all `(-1)`-indices. -/
def IsMinimal (T : NumericalType) : Prop :=
  ¬ ∃ i, IsMinusOneIndex T i

theorem minimal_genus_at_least_one (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hminimal : IsMinimal T)
    (hn : 1 < T.n) :
    genusValue ≥ 1 := by
  sorry

theorem minimal_genus_ge_topological_genus (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hminimal : IsMinimal T)
    (hn : 1 < T.n) :
    genusValue ≥ topologicalGenus T := by
  sorry

/-! The combined bound stated before the two component lemmas. -/
theorem minimal_genus_ge_max_one_topological_genus (T : NumericalType)
    (genusValue : ℤ) (hgenus : IsOfGenus T genusValue)
    (hminimal : IsMinimal T) (hn : 1 < T.n) :
    max 1 (topologicalGenus T) ≤ genusValue := by
  sorry

/-! A zero genus contribution is exactly a `(-2)` component in the reducible case. -/
theorem minus_two_contribution (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hn : 1 < T.n) {i : Fin T.n}
    (hcontribution : genusContribution T i = 0) :
    T.g i = 0 ∧ T.a i i = -2 * T.w i := by
  sorry

def IsMinusTwoIndex (T : NumericalType) (i : Fin T.n) : Prop :=
  T.g i = 0 ∧ T.a i i = -2 * T.w i

theorem minus_two_index_iff_zero_contribution (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.n) (i : Fin T.n) :
    IsMinusTwoIndex T i ↔ genusContribution T i = 0 := by
  sorry

theorem minus_two_index_iff_not_positive_contribution (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.n) (i : Fin T.n) :
    IsMinusTwoIndex T i ↔ ¬ 0 < genusContribution T i := by
  sorry

/-! The equality case exhibited in the source remark. -/
theorem genus_eq_topological_genus_of_unit_data (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.n)
    (hm : ∀ i, T.m i = 1) (hw : ∀ i, T.w i = 1)
    (hg : ∀ i, T.g i = 0)
    (ha : ∀ ⦃i j⦄, i < j → T.a i j = 0 ∨ T.a i j = 1) :
    genus T = topologicalGenus T := by
  sorry

end Formalization.Books.Models.Unit03
