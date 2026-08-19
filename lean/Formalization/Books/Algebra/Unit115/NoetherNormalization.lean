import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Formalization.Books.Topology.Unit10.KrullDimension

/-!
# Commutative Algebra, Chapter 115: Noether normalization

The canonical polynomial-ring, finite-map, residue-field, localization, and
Krull-dimension interfaces are used throughout.  The source-facing auxiliary
definitions below make the weighted multi-index and normalization statements
explicit without duplicating Mathlib's polynomial-ring API.
-/

namespace Formalization.Books.Algebra.Unit115

universe u v

noncomputable section

open Set
open scoped Polynomial
open Formalization.Books.Topology.Unit10

/-! ## The two helper lemmas -/

/-- The weighted degree of a multi-index for a chosen family of weights. -/
def weightedMultiIndex {σ : Type u} [Fintype σ]
    (e : σ → ℕ) (ν : σ →₀ ℕ) : ℕ :=
  ∑ i, e i * ν i

/-- The absolute difference of two natural numbers. -/
def natDifference (a b : ℕ) : ℕ :=
  if a ≤ b then b - a else a - b

/-- A concrete version of the source's notation `e₁ ≫ e₂ ≫ ⋯`: at the first
coordinate where two multi-indices differ, that difference dominates all
possible contributions from later coordinates on the given finite set. -/
def multiIndexDominates {σ : Type u} [Fintype σ] [LinearOrder σ]
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) : Prop :=
  (∀ i, 0 < e i) ∧
    ∀ ⦃i : σ⦄ ⦃ν ν' : σ →₀ ℕ⦄,
      ν ∈ N → ν' ∈ N → (∀ j, j < i → ν j = ν' j) → ν i ≠ ν' i →
        e i * natDifference (ν i) (ν' i) >
          ∑ j, if i < j then e j * natDifference (ν j) (ν' j) else 0

/-- A finite set of multi-indices admits a family of sufficiently separated
positive weights. -/
theorem exists_multiIndexDominates
    {n : ℕ} (N : Finset (Fin n →₀ ℕ)) :
    ∃ e : Fin n → ℕ, multiIndexDominates N e := by
  sorry

/-- Distinct multi-indices in a finite nonempty set have distinct weighted
degrees for a dominating family of weights. -/
theorem helper_multiIndex_separation
    {n : ℕ} (N : Finset (Fin n →₀ ℕ))
    (e : Fin n → ℕ) (he : multiIndexDominates N e) :
    ∀ ⦃ν ν' : Fin n →₀ ℕ⦄,
      ν ∈ N → ν' ∈ N →
        (weightedMultiIndex e ν = weightedMultiIndex e ν' ↔ ν = ν') := by
  classical
  have hsplit (i : Fin n) (f : Fin n → ℕ) :
      (∑ j, f j) =
        (∑ j ∈ Finset.univ.filter (fun j => j < i), f j) +
          (∑ j ∈ Finset.univ.filter (fun j => ¬ j < i), f j) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hsplit2 (i : Fin n) (f : Fin n → ℕ) :
      (∑ j, f j) =
        (∑ j ∈ Finset.univ.filter (fun j => j < i), f j) + f i +
          (∑ j ∈ Finset.univ.filter (fun j => i < j), f j) := by
    rw [hsplit]
    have hi : i ∈ Finset.univ.filter (fun j : Fin n => ¬ j < i) := by simp
    have hs :
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j < i), f j) =
          f i +
            (∑ j ∈ (Finset.univ.filter (fun j : Fin n => ¬ j < i)).erase i, f j) := by
      rw [add_comm]
      exact (Finset.sum_erase_add _ _ hi).symm
    rw [hs]
    have heq :
        (∑ j ∈ (Finset.univ.filter (fun j : Fin n => ¬ j < i)).erase i, f j) =
          (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f j) := by
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · intro j hj
        rfl
    rw [heq]
    ac_rfl
  have hsumfilter (i : Fin n) (f : Fin n → ℕ) :
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f j) =
        ∑ j, if i < j then f j else 0 := by
    rw [Finset.sum_filter]
  have hdiff_comm (a b : ℕ) : natDifference a b = natDifference b a := by
    simp [natDifference]
    split_ifs <;> omega
  have hmul {a b c : ℕ} (h : a ≤ b) :
      c * b = c * (b - a) + c * a := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h]
  have htail_aux (i : Fin n) (u v : Fin n →₀ ℕ) :
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * u j) ≤
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * v j) +
          ∑ j, if i < j then e j * natDifference (u j) (v j) else 0 := by
    calc
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * u j) ≤
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            (e j * v j + e j * natDifference (u j) (v j)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hc : u j ≤ v j + natDifference (u j) (v j) := by
          simp [natDifference]
          split_ifs <;> omega
        have hm := Nat.mul_le_mul_left (e j) hc
        simpa [Nat.mul_add] using hm
      _ = (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * v j) +
          ∑ j, if i < j then e j * natDifference (u j) (v j) else 0 := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact hsumfilter i (fun j => e j * natDifference (u j) (v j))
  intro ν ν' hν hν'
  constructor
  · intro hsum
    by_contra hne
    let D : Finset (Fin n) := Finset.univ.filter (fun i => ν i ≠ ν' i)
    have hD : D.Nonempty := by
      by_contra hD
      apply hne
      ext i
      by_contra hdiff
      have hiD : i ∈ D := by simp [D, hdiff]
      have heq : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
      rw [heq] at hiD
      simp at hiD
    let i : Fin n := D.min' hD
    have hiD : i ∈ D := by exact D.min'_mem hD
    have hi_ne : ν i ≠ ν' i := by simpa [D] using hiD
    have hbefore : ∀ j : Fin n, j < i → ν j = ν' j := by
      intro j hji
      by_contra hjne
      have hjD : j ∈ D := by simp [D, hjne]
      have hle : i ≤ j := D.min'_le j hjD
      omega
    let B : ℕ := ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), e j * ν j
    let B' : ℕ := ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), e j * ν' j
    let T : ℕ := ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * ν j
    let T' : ℕ := ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), e j * ν' j
    have hB : B = B' := by
      apply Finset.sum_congr
      · rfl
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hbefore j hj]
    have hmid : e i * ν i + T = e i * ν' i + T' := by
      dsimp [B, B', T, T'] at *
      have hp := hsplit2 i (fun j => e j * ν j)
      have hp' := hsplit2 i (fun j => e j * ν' j)
      simp only [weightedMultiIndex] at hsum
      omega
    have hdom := he.2 hν hν' hbefore hi_ne
    by_cases hle : ν i ≤ ν' i
    · have hlt : ν i < ν' i := lt_of_le_of_ne hle hi_ne
      have hm := hmul (c := e i) hle
      have hrel : T = T' + e i * (ν' i - ν i) := by
        omega
      have htail := htail_aux i ν ν'
      have hndi : natDifference (ν i) (ν' i) = ν' i - ν i := by
        simp [natDifference, hle]
      rw [hndi] at hdom
      omega
    · have hle' : ν' i ≤ ν i := Nat.le_of_lt (lt_of_not_ge hle)
      have hm := hmul (c := e i) hle'
      have hrel : T' = T + e i * (ν i - ν' i) := by
        omega
      have htail := htail_aux i ν' ν
      have htail' :
          T' ≤ T + ∑ j, if i < j then e j * natDifference (ν j) (ν' j) else 0 := by
        simpa only [hdiff_comm] using htail
      have hndi : natDifference (ν i) (ν' i) = ν i - ν' i := by
        simp [natDifference, hle]
      rw [hndi] at hdom
      omega
  · intro h
    subst ν'
    rfl

/-- The substitution used in the polynomial helper lemma.  The last variable
is retained as the polynomial variable and each earlier variable is shifted
by a power of it. -/
def lastVariableSubstitution {R : Type u} [CommRing R]
    (n : ℕ) (e : Fin n → ℕ) :
    Fin (n + 1) → Polynomial (MvPolynomial (Fin n) R) :=
  Fin.lastCases Polynomial.X
    (fun i => Polynomial.C (MvPolynomial.X i) + Polynomial.X ^ e i)

/-- The polynomial obtained from a multivariable polynomial by the preceding
substitution. -/
def noetherPolynomialSubstitution {R : Type u} [CommRing R]
    {n : ℕ} (g : MvPolynomial (Fin (n + 1)) R) (e : Fin n → ℕ) :
    Polynomial (MvPolynomial (Fin n) R) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : MvPolynomial (Fin n) R →+* Polynomial (MvPolynomial (Fin n) R)).comp
      (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
    (lastVariableSubstitution n e) g

/-- The full family of weights in the polynomial helper lemma; the retained
last variable has weight one, as in the source. -/
def lastVariableWeight {n : ℕ} (e : Fin n → ℕ) : Fin (n + 1) → ℕ :=
  Fin.lastCases 1 e

/-- The preceding existence result can keep the last variable at weight one,
as required by the polynomial substitution argument. -/
theorem exists_lastVariableWeights
    {n : ℕ} (N : Finset (Fin (n + 1) →₀ ℕ)) :
    ∃ e : Fin n → ℕ, multiIndexDominates N (lastVariableWeight e) := by
  sorry

private theorem helper_monomial_substitution_natDegree
    {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ}
    (N : Finset (Fin (n + 1) →₀ ℕ)) (e : Fin n → ℕ)
    (he : multiIndexDominates N (lastVariableWeight e))
    (ν : Fin (n + 1) →₀ ℕ) (a : R) (ha : a ≠ 0) :
    (noetherPolynomialSubstitution (MvPolynomial.monomial ν a) e).natDegree =
      weightedMultiIndex (lastVariableWeight e) ν := by
  rw [noetherPolynomialSubstitution, MvPolynomial.eval₂Hom_monomial]
  have hlead (i : Fin n) :
      ((Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^ ν i.castSucc).leadingCoeff = 1 := by
    have hei : 0 < e i := by
      simpa [lastVariableWeight] using he.1 i.castSucc
    change Polynomial.Monic ((Polynomial.C (MvPolynomial.X (R := R) i) +
      Polynomial.X ^ e i) ^ ν i.castSucc)
    simpa [add_comm] using
      (Polynomial.monic_X_pow_add_C (MvPolynomial.X (R := R) i)
        (Nat.ne_of_gt hei)).pow (ν i.castSucc)
  have hdeg (i : Fin n) :
      ((Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^
        ν i.castSucc).natDegree = ν i.castSucc * e i := by
    rw [show Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i =
      Polynomial.X ^ e i + Polynomial.C (MvPolynomial.X (R := R) i) by rw [add_comm]]
    rw [(Polynomial.monic_X_pow_add_C (MvPolynomial.X (R := R) i)
      (by exact Nat.ne_of_gt (by simpa [lastVariableWeight] using he.1 i.castSucc))).natDegree_pow]
    simp
  have hνprod :
      ν.prod (fun i k => (lastVariableSubstitution (R := R) n e i) ^ k) =
        ∏ i : Fin (n + 1),
          (lastVariableSubstitution (R := R) n e i) ^ ν i := by
    apply Finsupp.prod_fintype
    intro i
    simp
  have hprod_lc :
      (∏ i : Fin (n + 1),
        (lastVariableSubstitution (R := R) n e i) ^ ν i).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_prod']
    · rw [Fin.prod_univ_castSucc]
      simp only [lastVariableSubstitution, Fin.lastCases_castSucc, Fin.lastCases_last]
      simp [hlead]
    · rw [Fin.prod_univ_castSucc]
      simp only [lastVariableSubstitution, Fin.lastCases_castSucc, Fin.lastCases_last]
      simp [hlead]
  have hprod :
      (∏ i : Fin (n + 1),
        (lastVariableSubstitution (R := R) n e i) ^ ν i).natDegree =
          ∑ i : Fin (n + 1),
            ((lastVariableSubstitution (R := R) n e i) ^ ν i).natDegree := by
    apply Polynomial.natDegree_prod'
    rw [Fin.prod_univ_castSucc]
    simp only [lastVariableSubstitution, Fin.lastCases_castSucc, Fin.lastCases_last]
    simp [hlead]
  simp only [hνprod]
  rw [Polynomial.natDegree_mul' (by rw [hprod_lc]; simp [ha])]
  rw [hprod]
  rw [Fin.sum_univ_castSucc]
  simp only [lastVariableSubstitution, Fin.lastCases_castSucc, Fin.lastCases_last]
  simp_rw [hdeg]
  simp [weightedMultiIndex, lastVariableWeight, Fin.sum_univ_castSucc,
    add_assoc, add_comm, add_left_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.mul_comm]

private theorem helper_monomial_substitution_leadingCoeff
    {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ}
    (N : Finset (Fin (n + 1) →₀ ℕ)) (e : Fin n → ℕ)
    (he : multiIndexDominates N (lastVariableWeight e))
    (ν : Fin (n + 1) →₀ ℕ) (a : R) (ha : a ≠ 0) :
    (noetherPolynomialSubstitution (MvPolynomial.monomial ν a) e).leadingCoeff =
      MvPolynomial.C a := by
  rw [noetherPolynomialSubstitution, MvPolynomial.eval₂Hom_monomial]
  have hlead (i : Fin n) :
      ((Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^ ν i.castSucc).leadingCoeff = 1 := by
    have hei : 0 < e i := by
      simpa [lastVariableWeight] using he.1 i.castSucc
    change Polynomial.Monic ((Polynomial.C (MvPolynomial.X (R := R) i) +
      Polynomial.X ^ e i) ^ ν i.castSucc)
    simpa [add_comm] using
      (Polynomial.monic_X_pow_add_C (MvPolynomial.X (R := R) i)
        (Nat.ne_of_gt hei)).pow (ν i.castSucc)
  have hνprod :
      ν.prod (fun i k => (lastVariableSubstitution (R := R) n e i) ^ k) =
        ∏ i : Fin (n + 1),
          (lastVariableSubstitution (R := R) n e i) ^ ν i := by
    apply Finsupp.prod_fintype
    intro i
    simp
  have hprod_lc :
      (∏ i : Fin (n + 1),
        (lastVariableSubstitution (R := R) n e i) ^ ν i).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_prod']
    · rw [Fin.prod_univ_castSucc]
      simp only [lastVariableSubstitution, Fin.lastCases_castSucc, Fin.lastCases_last]
      simp [hlead]
    · rw [Fin.prod_univ_castSucc]
      simp only [lastVariableSubstitution, Fin.lastCases_castSucc, Fin.lastCases_last]
      simp [hlead]
  simp only [hνprod]
  rw [Polynomial.leadingCoeff_mul' (by rw [hprod_lc]; simp [ha])]
  simp [hprod_lc]

/-- After a sufficiently separated substitution, the resulting polynomial has
positive degree and scalar leading coefficient equal to a nonzero coefficient
of the original polynomial. -/
theorem helper_polynomial_leading_term
    {R : Type u} [CommRing R] {n : ℕ}
    (g : MvPolynomial (Fin (n + 1)) R)
    (hg : g ∉ Set.range (fun a : R => MvPolynomial.C a))
    (e : Fin n → ℕ)
    (he : multiIndexDominates g.support (lastVariableWeight e)) :
    ∃ d : ℕ, ∃ a : R, 0 < d ∧ a ≠ 0 ∧
      ∃ ν ∈ g.support, a = g.coeff ν ∧
        (noetherPolynomialSubstitution g e).natDegree = d ∧
          (noetherPolynomialSubstitution g e).leadingCoeff =
            MvPolynomial.C a := by
  have hnontrivial (a : R) (ha : a ≠ 0) : Nontrivial R :=
    ⟨⟨0, a, ha.symm⟩⟩
  have hsub (ν : Fin (n + 1) →₀ ℕ) (a : R) (ha : a ≠ 0) :
      (noetherPolynomialSubstitution (MvPolynomial.monomial ν a) e).natDegree =
        weightedMultiIndex (lastVariableWeight e) ν := by
    exact @helper_monomial_substitution_natDegree R _ (hnontrivial a ha) n
      g.support e he ν a ha
  have hsubLC (ν : Fin (n + 1) →₀ ℕ) (a : R) (ha : a ≠ 0) :
      (noetherPolynomialSubstitution (MvPolynomial.monomial ν a) e).leadingCoeff =
        MvPolynomial.C a := by
    exact @helper_monomial_substitution_leadingCoeff R _ (hnontrivial a ha) n
      g.support e he ν a ha
  have hg0 : g ≠ 0 := by
    intro hz
    apply hg
    exact ⟨0, by simp [hz]⟩
  have hsupp : g.support.Nonempty := MvPolynomial.support_nonempty.mpr hg0
  obtain ⟨ν, hν, hνmax⟩ := Finset.exists_max_image g.support
    (fun μ => weightedMultiIndex (lastVariableWeight e) μ) hsupp
  have hdpos : 0 < weightedMultiIndex (lastVariableWeight e) ν := by
    by_contra hnot
    have hd0 : weightedMultiIndex (lastVariableWeight e) ν = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hzero (μ : Fin (n + 1) →₀ ℕ) (hμ : μ ∈ g.support) :
        weightedMultiIndex (lastVariableWeight e) μ = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hd0] using hνmax μ hμ
    have hμzero (μ : Fin (n + 1) →₀ ℕ) (hμ : μ ∈ g.support) : μ = 0 := by
      ext i
      have hterm_all :
          ∀ i : Fin (n + 1), lastVariableWeight e i * μ i = 0 := by
        intro i
        exact
          (Finset.sum_eq_zero_iff_of_nonneg
            (f := fun j : Fin (n + 1) => lastVariableWeight e j * μ j)
            (s := Finset.univ) (fun _ _ => Nat.zero_le _)).mp
            (by simpa [weightedMultiIndex] using hzero μ hμ) i (by simp)
      rcases Nat.mul_eq_zero.mp (hterm_all i) with hw | hμi
      · exact False.elim (Nat.ne_of_gt (he.1 i) hw)
      · exact hμi
    have hsupp_sub : g.support ⊆ ({0} : Finset (Fin (n + 1) →₀ ℕ)) := by
      intro μ hμ
      simpa using hμzero μ hμ
    have hgconst : g = MvPolynomial.C (g.coeff 0) := by
      apply MvPolynomial.ext
      intro μ
      by_cases hμ : μ = 0
      · subst μ
        simp
      · have hc : g.coeff μ = 0 := by
          by_contra hc
          exact hμ (Finset.mem_singleton.mp
            (hsupp_sub (MvPolynomial.mem_support_iff.mpr hc)))
        rw [hc]
        simp [Ne.symm hμ]
    exact hg ⟨g.coeff 0, hgconst.symm⟩
  let T : (Fin (n + 1) →₀ ℕ) → Polynomial (MvPolynomial (Fin n) R) :=
    fun μ => noetherPolynomialSubstitution (MvPolynomial.monomial μ (g.coeff μ)) e
  have hTLC (μ : Fin (n + 1) →₀ ℕ) (hμ : μ ∈ g.support) :
      (T μ).leadingCoeff = MvPolynomial.C (g.coeff μ) := by
    simpa [T] using hsubLC μ (g.coeff μ) (MvPolynomial.mem_support_iff.mp hμ)
  have hTdeg (μ : Fin (n + 1) →₀ ℕ) (hμ : μ ∈ g.support) :
      (T μ).natDegree = weightedMultiIndex (lastVariableWeight e) μ := by
    simpa [T] using hsub μ (g.coeff μ) (MvPolynomial.mem_support_iff.mp hμ)
  have hTne (μ : Fin (n + 1) →₀ ℕ) (hμ : μ ∈ g.support) : T μ ≠ 0 := by
    intro hz
    have hlcz : (T μ).leadingCoeff = 0 := by
      simpa [hz] using congrArg Polynomial.leadingCoeff hz
    have hc : MvPolynomial.C (g.coeff μ) = 0 := (hTLC μ hμ).symm.trans hlcz
    exact (MvPolynomial.C_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hμ)) hc
  have hνdeg : (T ν).degree ≠ ⊥ := by
    exact Polynomial.degree_ne_bot.mpr (hTne ν hν)
  have hdeg_lt {μ : Fin (n + 1) →₀ ℕ} (hμ : μ ∈ g.support)
      (hμν : μ ≠ ν) : (T μ).degree < (T ν).degree := by
    have hweight : weightedMultiIndex (lastVariableWeight e) μ <
        weightedMultiIndex (lastVariableWeight e) ν := by
      exact Nat.lt_of_le_of_ne (hνmax μ hμ)
        (by
          intro heq
          have hsep : weightedMultiIndex (lastVariableWeight e) μ =
              weightedMultiIndex (lastVariableWeight e) ν ↔ μ = ν :=
            (helper_multiIndex_separation g.support (lastVariableWeight e) he) hμ hν
          exact hμν (hsep.mp heq))
    calc
      (T μ).degree = (T μ).natDegree :=
        Polynomial.degree_eq_natDegree (hTne μ hμ)
      _ < (T ν).natDegree := by
        rw [hTdeg μ hμ, hTdeg ν hν]
        exact WithBot.coe_lt_coe.mpr hweight
      _ = (T ν).degree := (Polynomial.degree_eq_natDegree (hTne ν hν)).symm
  have hsum_degree {s : Finset (Fin (n + 1) →₀ ℕ)}
      (hs : ∀ μ ∈ s, (T μ).degree < (T ν).degree) :
      (Finset.sum s T).degree < (T ν).degree := by
    induction s using Finset.induction_on with
    | empty => exact bot_lt_iff_ne_bot.mpr hνdeg
    | @insert μ s hμs ih =>
        rw [Finset.sum_insert hμs]
        apply (Polynomial.degree_add_le _ _).trans_lt
        exact max_lt (hs μ (by simp))
          (ih (fun x hx => hs x (by simp [hx])))
  have htail : (Finset.sum (g.support \ {ν}) T).degree < (T ν).degree := by
    apply hsum_degree
    intro μ hμ
    have hμ' : μ ∈ g.support ∧ μ ∉ ({ν} : Finset (Fin (n + 1) →₀ ℕ)) :=
      Finset.mem_sdiff.mp hμ
    exact hdeg_lt hμ'.1 (by
      intro h
      exact hμ'.2 (Finset.mem_singleton.mpr h))
  have hsum : noetherPolynomialSubstitution g e = Finset.sum g.support T := by
    rw [noetherPolynomialSubstitution, ← g.support_sum_monomial_coeff, map_sum]
    simp [T, noetherPolynomialSubstitution]
  have hLCsum :
      (Finset.sum g.support T).leadingCoeff = (T ν).leadingCoeff := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hν T]
    simpa [add_comm] using Polynomial.leadingCoeff_add_of_degree_lt htail
  refine ⟨weightedMultiIndex (lastVariableWeight e) ν, g.coeff ν, hdpos,
    MvPolynomial.mem_support_iff.mp hν, ν, hν, rfl, ?_, ?_⟩
  · rw [hsum, Finset.sum_eq_add_sum_sdiff_singleton_of_mem hν T, add_comm]
    rw [Polynomial.natDegree_add_eq_right_of_degree_lt htail]
    exact hTdeg ν hν
  · rw [hsum, hLCsum]
    exact hTLC ν hν

/-! ## Polynomial quotients and one relation -/

/-- The subalgebra generated by chosen polynomial representatives in a
polynomial quotient. -/
def quotientGeneratorSubalgebra
    {k : Type u} [CommRing k] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (y : Fin r → MvPolynomial (Fin n) k) :
    Subalgebra k ((MvPolynomial (Fin n) k) ⧸ I) :=
  Algebra.adjoin k (Set.range (fun i => Ideal.Quotient.mk I (y i)))

/-- The `ℤ`-subalgebra of a polynomial ring generated by its variables. -/
def integerPolynomialSubalgebra
    (k : Type u) [CommRing k] (n : ℕ) :
    Subalgebra ℤ (MvPolynomial (Fin n) k) :=
  Algebra.adjoin ℤ (Set.range (fun i : Fin n => MvPolynomial.X i))

/-- One nonzero relation in a polynomial quotient makes the quotient finite
over a polynomial subalgebra on one fewer variable. -/
theorem one_relation
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hIproper : I ≠ ⊤) (hInonzero : I ≠ ⊥) :
    ∃ y : Fin (n - 1) → MvPolynomial (Fin n) k,
      RingHom.Finite
          (quotientGeneratorSubalgebra I y).val.toRingHom ∧
        ∀ i, y i ∈ integerPolynomialSubalgebra k n := by
  sorry

/-! ## Noether normalization -/

/-- The integral, injective core of Noether normalization is Mathlib's
canonical quotient theorem. -/
theorem noether_normalization_integral_core
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ r : ℕ, r ≤ n ∧
      ∃ g : MvPolynomial (Fin r) k →ₐ[k]
          ((MvPolynomial (Fin n) k) ⧸ I),
        Function.Injective g ∧ g.IsIntegral := by
  exact exists_integral_inj_algHom_of_quotient I hI

/-- Noether normalization for a polynomial quotient, with the source-facing
representatives of the normalized variables recorded in the original
polynomial ring.  The finite and injective map uses Mathlib's canonical
`AlgHom` interface. -/
theorem noether_normalization
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ r : ℕ, r ≤ n ∧
      ∃ g : MvPolynomial (Fin r) k →ₐ[k]
          ((MvPolynomial (Fin n) k) ⧸ I),
        Function.Injective g ∧
          RingHom.Finite g.toRingHom ∧
            ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) = r ∧
              ∃ y : Fin r → MvPolynomial (Fin n) k,
                (∀ i, g (MvPolynomial.X i) = Ideal.Quotient.mk I (y i)) ∧
                  ∀ i, y i ∈ integerPolynomialSubalgebra k n := by
  sorry

/-! ## Normalization at a point -/

/-- At a point of a finite-type affine algebra over a field, one principal
neighborhood realizes the local dimension and admits finite injective
normalization. -/
theorem noether_normalization_at_point
    {k : Type u} [Field k] {S : Type u} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) (hq : q.IsPrime) :
    let x : PrimeSpectrum S := ⟨q, hq⟩
    ∃ g : S, g ∉ x.asIdeal ∧
      ∃ d : ℕ,
        krullDimensionAt x = d ∧
          ringKrullDim (Localization.Away g) = d ∧
            ∃ φ : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g,
              Function.Injective φ ∧ RingHom.Finite φ.toRingHom := by
  sorry

/-! ## Refined normalization -/

/-- The ideal generated by the last `n - r` variables of an `n`-variable
polynomial ring. -/
def tailVariableIdeal
    (k : Type u) [CommRing k] (n r : ℕ) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span {p | ∃ i : Fin n, r ≤ i.1 ∧ p = MvPolynomial.X i}

/-- A prime ideal in a polynomial ring admits a finite polynomial-ring map
whose contraction is generated by the variables beyond its transcendence
degree. -/
theorem refined_noether_normalization
    {k : Type u} [Field k] {n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) k)) (hq : q.IsPrime) :
    letI : q.IsPrime := hq
    ∃ r : ℕ, r ≤ n ∧
      Algebra.trdeg k q.ResidueField = r ∧
        ∃ φ : MvPolynomial (Fin n) k →+*
            MvPolynomial (Fin n) k,
          RingHom.Finite φ ∧ q.comap φ = tailVariableIdeal k n r := by
  sorry

/-! ## Normalization over a domain -/

/-- The domain version of Noether normalization: the finite polynomial
subalgebra is realized by an injective intermediate `R`-subalgebra, and it
becomes the original algebra after inverting one nonzero base element. -/
theorem noether_normalization_over_domain
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (hfiniteType : RingHom.FiniteType φ) :
    letI : Algebra R S := φ.toAlgebra
    ∃ d : ℕ, ∃ S' : Subalgebra R S,
      ∃ g : MvPolynomial (Fin d) R →ₐ[R] S',
        Function.Injective (MvPolynomial.C : R →+* MvPolynomial (Fin d) R) ∧
          Function.Injective g.toRingHom ∧
            RingHom.Finite g.toRingHom ∧
              Function.Injective S'.val ∧
                (S'.val.toRingHom.comp g.toRingHom).comp
                    (MvPolynomial.C : R →+* MvPolynomial (Fin d) R) = φ ∧
                  ∃ f : R, f ≠ 0 ∧
                    Nonempty
                      (Localization.Away (algebraMap R S' f) ≃+*
                        Localization.Away (φ f)) := by
  sorry

end

end Formalization.Books.Algebra.Unit115
