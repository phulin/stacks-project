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
  sorry

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

/-! The `ell`-primary torsion subgroup of the Picard group of a numerical type. -/
def picardPrimaryTorsion (T : NumericalType) (ell : ℕ) :
    AddSubgroup (picardGroup T) :=
  AddSubgroup.torsionBy (picardGroup T) (ell : ℤ)

/-!
The dimension over `ZMod ell` of the `ell`-primary torsion subgroup of the
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
