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
  sorry

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
