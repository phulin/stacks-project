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
  sorry

theorem genus_integral (T : NumericalType) :
    ∃ genusValue : ℤ, (genusValue : ℚ) = genusExpression T := by
  sorry

theorem genus_formula (T : NumericalType) :
    (genus T : ℚ) = genusExpression T := by
  sorry

/-! A numerical type can have negative genus in the irreducible case. -/
theorem exists_negative_genus_numerical_type :
    ∃ T : NumericalType, genus T < 0 := by
  sorry

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
    (hgenus : IsOfGenus T genusValue) (hn : 1 < T.n) :
    ∀ i, T.a i i < 0 := by
  sorry

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

/-! Positive off-diagonal pairs and the topological genus. -/
def positiveEdgePairs (T : NumericalType) : Finset (Fin T.n × Fin T.n) := by
  classical
  exact (Finset.univ.product Finset.univ).filter (fun p =>
    p.1 < p.2 ∧ 0 < T.a p.1 p.2)

def positiveEdgeCount (T : NumericalType) : ℕ :=
  (positiveEdgePairs T).card

def topologicalGenus (T : NumericalType) : ℤ :=
  1 - (T.n : ℤ) + (positiveEdgeCount T : ℤ)

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
