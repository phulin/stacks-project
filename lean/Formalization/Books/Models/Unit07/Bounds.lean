import Formalization.Books.Models.Unit04.PicardGroup
import Formalization.Books.Models.Unit05.Classification

/-!
# Bounding invariants of numerical types

Formal statements from Chapter 7 of *Semistable Reduction*.  The source
uses indices `1, ..., n`; the preceding formalization uses `Fin n`.
-/

noncomputable section

namespace Formalization.Books.Models.Unit07

open Formalization.Books.Models.Unit02
open Formalization.Books.Models.Unit03
open Formalization.Books.Models.Unit04

/-! The indices which are not `(-2)`-indices. -/
def nonMinusTwoIndices (T : NumericalType) : Finset (Fin T.n) := by
  classical
  exact Finset.univ.filter (fun i => ¬ IsMinusTwoIndex T i)

/-! The two bounds in the source's neighbour lemma. -/
theorem bound_neighbours (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) {i j : Fin T.n}
    (hij : 0 < T.a i j) :
    T.m i * T.a i j ≤ T.m j * |T.a j j| ∧
      T.m i * T.w i ≤ T.m j * |T.a j j| := by
  have hji : 0 < T.a j i := by
    rw [T.a_symmetric]
    exact hij
  have hne : i ≠ j := by
    intro h
    subst j
    have hrow := T.row_sum i
    have hsumpos : 0 < ∑ k, T.a i k * T.m k := by
      apply Finset.sum_pos'
      · intro k hk
        by_cases hki : k = i
        · subst k
          exact le_of_lt (mul_pos hij (T.m_pos _))
        · exact mul_nonneg (T.a_offdiag_nonneg (Ne.symm hki))
            (le_of_lt (T.m_pos _))
      · refine ⟨i, Finset.mem_univ _, ?_⟩
        exact mul_pos hij (T.m_pos _)
    rw [hrow] at hsumpos
    omega
  have hdiag : T.a j j < 0 := by
    by_contra hnot
    have hnonneg : 0 ≤ T.a j j := le_of_not_gt hnot
    have hsumpos : 0 < ∑ k, T.a j k * T.m k := by
      apply Finset.sum_pos'
      · intro k hk
        by_cases hkj : k = j
        · subst k
          exact mul_nonneg hnonneg (le_of_lt (T.m_pos _))
        · exact mul_nonneg (T.a_offdiag_nonneg (Ne.symm hkj))
            (le_of_lt (T.m_pos _))
      · refine ⟨i, Finset.mem_univ _, ?_⟩
        exact mul_pos hji (T.m_pos _)
    rw [T.row_sum j] at hsumpos
    omega
  have hnonneg : ∀ k ∈ (Finset.univ.erase j), 0 ≤ T.a j k * T.m k := by
    intro k hk
    exact mul_nonneg
      (T.a_offdiag_nonneg (Ne.symm (Finset.mem_erase.mp hk).1))
      (le_of_lt (T.m_pos _))
  have hle_sum : T.a j i * T.m i ≤
      (Finset.univ.erase j).sum (fun k => T.a j k * T.m k) :=
    Finset.single_le_sum hnonneg (by simp [hne])
  have hrow : (Finset.univ.erase j).sum (fun k => T.a j k * T.m k) +
      T.a j j * T.m j = 0 := by
    simpa [Finset.sum_erase_add] using T.row_sum j
  have hfirst : T.m i * T.a i j ≤ T.m j * |T.a j j| := by
    rw [T.a_symmetric i j, abs_of_neg hdiag]
    nlinarith [hle_sum, hrow]
  constructor
  · exact hfirst
  · rcases T.w_dvd i j with ⟨c, hc⟩
    have hcpos : 0 < c := by
      nlinarith [hij, T.w_pos i]
    have hwle : T.w i ≤ T.a i j := by
      nlinarith [hc, T.w_pos i]
    have hmw : T.m i * T.w i ≤ T.m i * T.a i j := by
      nlinarith [hwle, T.m_pos i]
    exact hmw.trans hfirst

/-!
The four bounds for the non-`(-2)` part of a minimal type of genus at least
two.  The cardinality is compared in `ℤ` so that it has the same arithmetic
type as the genus and the displayed numerical bounds.
-/
theorem bound_heart (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hgenus_ge_two : 2 ≤ genusValue)
    (hminimal : IsMinimal T) (hn : 1 < T.n) :
    ((nonMinusTwoIndices T).card : ℤ) ≤ 2 * genusValue - 2 ∧
      (∀ j, j ∈ nonMinusTwoIndices T → T.g j < genusValue) ∧
        (∀ j, j ∈ nonMinusTwoIndices T →
          T.m j * |T.a j j| ≤ 6 * genusValue - 6) ∧
          (∀ j, j ∈ nonMinusTwoIndices T →
            ∀ i, T.m i * T.a i j ≤ 6 * genusValue - 6) := by
  classical
  have hnonneg : ∀ i, 0 ≤ genusContribution T i := by
    intro i
    by_contra h
    have hneg : genusContribution T i < 0 := lt_of_not_ge h
    exact hminimal ⟨i, minus_one_contribution T genusValue hgenus hn hneg⟩
  have hzero : ∀ i, i ∉ nonMinusTwoIndices T →
      genusContribution T i = 0 := by
    intro i hi
    have htwo : IsMinusTwoIndex T i := by
      by_contra h
      apply hi
      simp [nonMinusTwoIndices, h]
    exact (minus_two_index_iff_zero_contribution T hminimal hn i).1 htwo
  have hsum_nonminus :
      (nonMinusTwoIndices T).sum (fun i => genusContribution T i) =
        (Finset.univ : Finset (Fin T.n)).sum (fun i => genusContribution T i) := by
    apply Finset.sum_subset
    · intro i hi
      simp
    · intro i hi hnot
      exact hzero i hnot
  have hgenusQ : (genusValue : ℚ) =
      1 + ∑ i : Fin T.n, genusContribution T i := by
    rw [← hgenus]
    exact genus_formula T
  have hsum : (∑ i : Fin T.n, genusContribution T i) =
      (genusValue : ℚ) - 1 := by
    linarith
  have hcle : ∀ j, genusContribution T j ≤ (genusValue : ℚ) - 1 := by
    intro j
    have h := Finset.single_le_sum (fun i _ => hnonneg i) (by simp :
        j ∈ (Finset.univ : Finset (Fin T.n)))
    rw [hsum] at h
    exact h
  have hhalf : ∀ j, j ∈ nonMinusTwoIndices T →
      (1 : ℚ) / 2 ≤ genusContribution T j := by
    intro j hj
    have hnot : ¬ IsMinusTwoIndex T j := by
      intro htwo
      exact (Finset.mem_filter.mp hj).2 htwo
    have hpos : 0 < genusContribution T j := by
      by_contra h
      exact hnot ((minus_two_index_iff_not_positive_contribution T hminimal hn j).2 h)
    have hnumpos : 0 <
        2 * T.m j * T.w j * (T.g j - 1) - T.m j * T.a j j := by
      have hq := hpos
      unfold genusContribution at hq
      have hq' : (0 : ℚ) <
          ((2 * T.m j * T.w j * (T.g j - 1) - T.m j * T.a j j : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast hq'
    have hnumge : 1 ≤
        2 * T.m j * T.w j * (T.g j - 1) - T.m j * T.a j j := by
      omega
    have hnumgeQ : (1 : ℚ) ≤
        ((2 * T.m j * T.w j * (T.g j - 1) - T.m j * T.a j j : ℤ) : ℚ) := by
      exact_mod_cast hnumge
    unfold genusContribution
    push_cast at hnumgeQ ⊢
    linarith
  have hcardQ : ((nonMinusTwoIndices T).card : ℚ) ≤
      2 * (genusValue : ℚ) - 2 := by
    have hsumlower : ((nonMinusTwoIndices T).card : ℚ) / 2 ≤
        (nonMinusTwoIndices T).sum (fun i => genusContribution T i) := by
      calc
        ((nonMinusTwoIndices T).card : ℚ) / 2 =
            (nonMinusTwoIndices T).sum (fun _ => (1 : ℚ) / 2) := by
              simp [div_eq_mul_inv]
        _ ≤ (nonMinusTwoIndices T).sum (fun i => genusContribution T i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hhalf i hi
    rw [hsum_nonminus, hsum] at hsumlower
    linarith
  have hcard : ((nonMinusTwoIndices T).card : ℤ) ≤
      2 * genusValue - 2 := by
    exact_mod_cast hcardQ
  have hgj : ∀ j, j ∈ nonMinusTwoIndices T → T.g j < genusValue := by
    intro j hj
    have hdiag : T.a j j < 0 :=
      diagonal_negative T genusValue hgenus hn j
    have hstrict :
        (T.m j : ℚ) * (T.w j : ℚ) * ((T.g j : ℚ) - 1) <
          genusContribution T j := by
      have hmQ : (0 : ℚ) < T.m j := by exact_mod_cast T.m_pos j
      have hdiagQ : (T.a j j : ℚ) < 0 := by exact_mod_cast hdiag
      unfold genusContribution
      push_cast
      nlinarith
    by_contra h
    have hgj_ge : genusValue ≤ T.g j := le_of_not_gt h
    have hgj_geQ : (genusValue : ℚ) ≤ T.g j := by exact_mod_cast hgj_ge
    have hmpos := T.m_pos j
    have hm1 : (1 : ℚ) ≤ T.m j := by
      exact_mod_cast (show (1 : ℤ) ≤ T.m j by omega)
    have hwpos := T.w_pos j
    have hw1 : (1 : ℚ) ≤ T.w j := by
      exact_mod_cast (show (1 : ℤ) ≤ T.w j by omega)
    have hmw : (1 : ℚ) ≤ (T.m j : ℚ) * T.w j := by
      have hprod : 0 ≤ ((T.m j : ℚ) - 1) * (T.w j - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hxZ : (0 : ℤ) ≤ genusValue - 1 := by
      omega
    have hx : (0 : ℚ) ≤ (genusValue : ℚ) - 1 := by
      exact_mod_cast hxZ
    have hbase : (genusValue : ℚ) - 1 ≤ (T.g j : ℚ) - 1 := by
      linarith
    have hmul1 :
        (genusValue : ℚ) - 1 ≤
          ((T.m j : ℚ) * T.w j) * ((genusValue : ℚ) - 1) := by
      have hprod : 0 ≤
          ((T.m j : ℚ) * T.w j - 1) * ((genusValue : ℚ) - 1) :=
        mul_nonneg (by linarith) hx
      nlinarith
    have hmul2 :
        ((T.m j : ℚ) * T.w j) * ((genusValue : ℚ) - 1) ≤
          ((T.m j : ℚ) * T.w j) * ((T.g j : ℚ) - 1) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    have hmul :
        (genusValue : ℚ) - 1 ≤
          (T.m j : ℚ) * (T.w j : ℚ) * ((T.g j : ℚ) - 1) :=
      hmul1.trans hmul2
    have hle := hcle j
    linarith
  have hjbound : ∀ j, j ∈ nonMinusTwoIndices T →
      T.m j * |T.a j j| ≤ 6 * genusValue - 6 := by
    intro j hj
    have hdiag : T.a j j < 0 :=
      diagonal_negative T genusValue hgenus hn j
    have hle := hcle j
    by_cases hgzero : T.g j = 0
    · rcases T.w_dvd j j with ⟨k, hk⟩
      have hkneg : k < 0 := by
        have hw := T.w_pos j
        nlinarith [hdiag, hk]
      have hkne1 : k ≠ -1 := by
        intro hk1
        apply hminimal
        refine ⟨j, hgzero, ?_⟩
        rw [hk, hk1]
        ring
      have hkne2 : k ≠ -2 := by
        intro hk2
        apply (Finset.mem_filter.mp hj).2
        refine ⟨hgzero, ?_⟩
        rw [hk, hk2]
        ring
      have hk_le : k ≤ -3 := by omega
      have hkmQ : (3 : ℚ) ≤ -(k : ℚ) := by
        exact_mod_cast (show (3 : ℤ) ≤ -k by omega)
      have hmQ : (0 : ℚ) < T.m j := by exact_mod_cast T.m_pos j
      have hwQ : (0 : ℚ) < T.w j := by exact_mod_cast T.w_pos j
      have hmwQ : (0 : ℚ) < (T.m j : ℚ) * T.w j := mul_pos hmQ hwQ
      unfold genusContribution at hle
      rw [hgzero, hk] at hle
      push_cast at hle
      have hfactor : 0 ≤
          3 * (-(k : ℚ) - 2) - (-(k : ℚ)) := by
        linarith
      have hmul : 0 ≤
          ((T.m j : ℚ) * T.w j) *
            (3 * (-(k : ℚ) - 2) - (-(k : ℚ))) :=
        mul_nonneg (le_of_lt hmwQ) hfactor
      have hboundQ :
          (T.m j : ℚ) * T.w j * (-(k : ℚ)) ≤
            6 * (genusValue : ℚ) - 6 := by
        nlinarith
      rw [abs_of_neg hdiag, hk]
      have hboundQ' :
          (T.m j : ℚ) * (-(T.w j * k : ℤ) : ℚ) ≤
            6 * (genusValue : ℚ) - 6 := by
        push_cast
        nlinarith [hboundQ]
      exact_mod_cast hboundQ'
    · have hgpos : 0 < T.g j := by
        have hgnonneg := T.g_nonneg j
        omega
      have hmQ : (0 : ℚ) < T.m j := by exact_mod_cast T.m_pos j
      have hwQ : (0 : ℚ) < T.w j := by exact_mod_cast T.w_pos j
      have hdiagQ : (T.a j j : ℚ) < 0 := by exact_mod_cast hdiag
      have hgQ : (1 : ℚ) ≤ T.g j := by
        exact_mod_cast (show (1 : ℤ) ≤ T.g j by omega)
      rw [abs_of_neg hdiag]
      have hboundQ : (T.m j : ℚ) * (-(T.a j j : ℚ)) ≤
          6 * (genusValue : ℚ) - 6 := by
        unfold genusContribution at hle
        push_cast at hle
        have hnonneg :
            0 ≤ (T.w j : ℚ) * ((T.g j : ℚ) - 1) :=
          mul_nonneg (le_of_lt hwQ) (by linarith)
        nlinarith [hle, hgenus_ge_two]
      exact_mod_cast hboundQ
  have hlast : ∀ j, j ∈ nonMinusTwoIndices T →
      ∀ i, T.m i * T.a i j ≤ 6 * genusValue - 6 := by
    intro j hj i
    have hR : 0 ≤ 6 * genusValue - 6 := by omega
    by_cases hpos : 0 < T.a i j
    · exact (bound_neighbours T genusValue hgenus hpos).1 |>.trans (hjbound j hj)
    · have hnonpos : T.a i j ≤ 0 := le_of_not_gt hpos
      have hmpos := T.m_pos i
      nlinarith
  exact ⟨hcard, hgj, hjbound, hlast⟩

/-!
The uniform bound on all weighted intersection entries in a minimal type.
-/
theorem bound_wm (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hgenus_ge_two : 2 ≤ genusValue)
    (hminimal : IsMinimal T) :
    ∀ i j, T.m i * |T.a i j| ≤ 768 * genusValue := by
  sorry

/-!
The chain estimates, maximal connected-subset reduction, concavity argument,
and the long-path/branch diagrams in the source are proof-level reductions
of `bound_wm`.  Their reusable classification interfaces are already
available from Chapter 5 as `lemma_long`, `lemma_Dn`, and
`proposition_classify_subgraphs`; the displayed row-sum and genus identities
are fields and definitions of `NumericalType` from Chapter 3.  The printed
path equality containing `-a_{i₁i₂}/2` and `-a_{(t-1)t}/2` is not encoded,
since it has a sign/index typo; the valid path data and the `(-2)` diagonal
relations are already part of the earlier classification interfaces.  The
intermediate `w_i |a_{ii}|` bound in that proof is likewise normalized to the
target quantity `m_i |a_{ii}|` in `bound_wm`.
-/

/-! The `ell`-torsion subgroup of the Picard group of a numerical type. -/
def picardPrimaryTorsion (T : NumericalType) (ell : ℕ) :
    AddSubgroup (picardGroup T) :=
  AddSubgroup.torsionBy (picardGroup T) (ell : ℤ)

/-!
The dimension over `ZMod ell` of the `ell`-torsion subgroup of the
Picard group.  For a prime `ell`, this is the source's
`dim_{F_ell} Pic(T)[ell]`.
-/
def picardPrimaryTorsionFinrank (T : NumericalType) (ell : ℕ)
    (hell : Nat.Prime ell) : ℕ :=
  letI : Fact (Nat.Prime ell) := ⟨hell⟩
  letI : NeZero ell := ⟨hell.ne_zero⟩
  letI : Module (ZMod ell) (picardPrimaryTorsion T ell) :=
    AddSubgroup.torsionBy.zmodModule
  Module.finrank (ZMod ell) (picardPrimaryTorsion T ell)

/-!
For a numerical type of genus at least two and a prime larger than the
uniform coefficient bound, the Picard `ell`-torsion has the stated dimension
bound.  In the minimal case the source gives the sharper topological-genus
bound as well.
-/
theorem bound_picard_group (T : NumericalType) (genusValue : ℤ)
    (hgenus : IsOfGenus T genusValue) (hgenus_ge_two : 2 ≤ genusValue)
    (ell : ℕ) (hell : Nat.Prime ell)
    (hell_bound : (768 : ℤ) * genusValue < (ell : ℤ)) :
    (picardPrimaryTorsionFinrank T ell hell : ℤ) ≤ genusValue ∧
      (IsMinimal T →
        (picardPrimaryTorsionFinrank T ell hell : ℤ) ≤ topologicalGenus T ∧
          topologicalGenus T ≤ genusValue) := by
  sorry

end Formalization.Books.Models.Unit07
