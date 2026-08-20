import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Polynomial
import Formalization.Books.Topology.Unit10.KrullDimension
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension

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
  classical
  let M : ℕ := ∑ ν ∈ N, ∑ i : Fin n, ν i
  let B : ℕ := n * M + 2
  let e : Fin n → ℕ := fun i => B ^ (n - i.1)
  have hM (ν : Fin n →₀ ℕ) (hν : ν ∈ N) (i : Fin n) : ν i ≤ M := by
    dsimp [M]
    calc
      ν i ≤ ∑ j : Fin n, ν j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ ≤ ∑ μ ∈ N, ∑ j : Fin n, μ j := by
        exact Finset.single_le_sum (s := N) (f := fun μ => ∑ j : Fin n, μ j)
          (fun _ _ => Nat.zero_le _) hν
  have hpow (i j : Fin n) (hij : i < j) :
      B ^ (n - j.1) ≤ B ^ (n - i.1 - 1) := by
    apply Nat.pow_le_pow_right
    · omega
    · have hij' : i.1 < j.1 := by exact hij
      have h' : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hij'
      have h'' := Nat.sub_le_sub_left h' n
      have heq : n - (i.1 + 1) = n - i.1 - 1 := by omega
      simpa [heq] using h''
  refine ⟨e, ?_⟩
  rw [multiIndexDominates]
  constructor
  · intro i
    exact pow_pos (by omega) _
  · intro i ν ν' hν hν' _ hdiff
    have hdiff_le (j : Fin n) : natDifference (ν j) (ν' j) ≤ M := by
      by_cases hle : ν j ≤ ν' j
      · rw [natDifference, if_pos hle]
        exact (Nat.sub_le _ _).trans (hM ν' hν' j)
      · rw [natDifference, if_neg hle]
        exact (Nat.sub_le _ _).trans (hM ν hν j)
    have hdiff_pos : 0 < natDifference (ν i) (ν' i) := by
      simp [natDifference]
      split_ifs <;> omega
    let p : ℕ := B ^ (n - i.1 - 1)
    have hterm (j : Fin n) (hij : i < j) :
        e j * natDifference (ν j) (ν' j) ≤ M * p := by
      dsimp [e, p]
      simpa [Nat.mul_comm] using Nat.mul_le_mul (hpow i j hij) (hdiff_le j)
    have hsum :
        (∑ j, if i < j then e j * natDifference (ν j) (ν' j) else 0) ≤
          (Finset.univ.filter (fun j : Fin n => i < j)).card * (M * p) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_card_nsmul
      intro j hj
      exact hterm j (by simpa using (Finset.mem_filter.mp hj).2)
    have hcard : (Finset.univ.filter (fun j : Fin n => i < j)).card ≤ n := by
      calc
        (Finset.univ.filter (fun j : Fin n => i < j)).card ≤ Finset.univ.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = n := by simp
    have hsum' :
        (∑ j, if i < j then e j * natDifference (ν j) (ν' j) else 0) ≤
          n * (M * p) :=
      hsum.trans (Nat.mul_le_mul_right _ hcard)
    have hexp : n - i.1 = n - i.1 - 1 + 1 := by omega
    have hsmall : n * (M * p) < e i := by
      calc
        n * (M * p) = (n * M) * p := by ac_rfl
        _ < (n * M + 2) * p := by
          exact Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) _)
        _ = B * p := by dsimp [B]
        _ = e i := by
          dsimp [e, p]
          rw [show n - i.1 = n - i.1 - 1 + 1 by omega, pow_succ]
          simp [Nat.mul_comm]
    calc
      (∑ j, if i < j then e j * natDifference (ν j) (ν' j) else 0) ≤
          n * (M * p) := hsum'
      _ < e i := hsmall
      _ ≤ e i * natDifference (ν i) (ν' i) := by
        simpa using Nat.mul_le_mul_left (e i) (Nat.succ_le_iff.mpr hdiff_pos)

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
  classical
  obtain ⟨d, hd⟩ := exists_multiIndexDominates N
  rw [multiIndexDominates] at hd
  let e : Fin n → ℕ := fun i => d i.castSucc
  refine ⟨e, ?_⟩
  rw [multiIndexDominates]
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [lastVariableWeight]
    · simpa [lastVariableWeight, e] using hd.1 j.castSucc
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro ν ν' hν hν' hbefore hdiff
      have hdiff' : ν (Fin.last n) ≠ ν' (Fin.last n) := by simpa using hdiff
      have hdiff_pos : 0 < natDifference (ν (Fin.last n)) (ν' (Fin.last n)) := by
        simp [natDifference]
        split_ifs <;> omega
      have hsum0 :
          (∑ j : Fin (n + 1), if Fin.last n < j then
              lastVariableWeight e j *
                natDifference (ν j) (ν' j) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        by_cases h : Fin.last n < j
        · change n < j.1 at h
          have : False := by omega
          exact this.elim
        · simp [h]
      rw [hsum0]
      simpa [lastVariableWeight] using hdiff_pos
    · intro ν ν' hν hν' hbefore hdiff
      have hdom := hd.2 hν hν' hbefore hdiff
      have hweight (j : Fin (n + 1)) : lastVariableWeight e j ≤ d j := by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · have hpos := hd.1 (Fin.last n)
          simp [lastVariableWeight]
          omega
        · simp [lastVariableWeight, e]
      have hsum_le :
          (∑ j, if i.castSucc < j then lastVariableWeight e j *
              natDifference (ν j) (ν' j) else 0) ≤
            ∑ j, if i.castSucc < j then d j * natDifference (ν j) (ν' j) else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i.castSucc < j
        · simp [hij]
          exact Nat.mul_le_mul_right _ (hweight j)
        · simp [hij]
      simpa [lastVariableWeight, e] using (lt_of_le_of_lt hsum_le hdom)

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
  simp [weightedMultiIndex, lastVariableWeight, Fin.sum_univ_castSucc, add_comm]
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
      simp [hz]
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
  classical
  cases n with
  | zero =>
      obtain ⟨f, hf, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hInonzero
      have hfC : f = MvPolynomial.C (f.coeff 0) := MvPolynomial.eq_C_of_isEmpty f
      have ha : f.coeff 0 ≠ 0 := by
        intro ha
        apply hfne
        rw [hfC, ha]
        simp
      have hone : (1 : MvPolynomial (Fin 0) k) ∈ I := by
        let c : k := f.coeff 0
        have hc : c ≠ 0 := by simpa [c] using ha
        have hfC' : f = MvPolynomial.C c := by simpa [c] using hfC
        have hmul := I.mul_mem_left (MvPolynomial.C c⁻¹) hf
        rw [hfC', ← MvPolynomial.C_mul, inv_mul_cancel₀ hc, MvPolynomial.C_1] at hmul
        exact hmul
      exact (hIproper ((Ideal.eq_top_iff_one I).2 hone)).elim
  | succ n =>
      obtain ⟨f, hf, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hInonzero
      have hf_nonconst : f ∉ Set.range (fun a : k => MvPolynomial.C a) := by
        rintro ⟨a, rfl⟩
        by_cases ha : a = 0
        · exact hfne (by simp [ha])
        · have hone : (1 : MvPolynomial (Fin (n + 1)) k) ∈ I := by
            have hmul := I.mul_mem_left (MvPolynomial.C a⁻¹) hf
            rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ha, MvPolynomial.C_1] at hmul
            exact hmul
          exact hIproper ((Ideal.eq_top_iff_one I).2 hone)
      obtain ⟨e, he⟩ := exists_lastVariableWeights f.support
      obtain ⟨d, a, hd, ha, ν, hν, hcoeff, hdeg, hLC⟩ :=
        helper_polynomial_leading_term f hf_nonconst e he
      let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
        fun i => MvPolynomial.X i.castSucc - MvPolynomial.X (Fin.last n) ^ e i
      let Q := (MvPolynomial (Fin (n + 1)) k) ⧸ I
      have : Nontrivial Q := by
        dsimp [Q]
        exact Ideal.Quotient.nontrivial_iff.mpr hIproper
      let q : MvPolynomial (Fin (n + 1)) k →ₐ[k] Q := Ideal.Quotient.mkₐ k I
      let A : Subalgebra k Q := quotientGeneratorSubalgebra I y
      have hX (i : Fin (n + 1)) :
          MvPolynomial.X i ∈ integerPolynomialSubalgebra k (n + 1) := by
        exact Algebra.subset_adjoin ⟨i, rfl⟩
      have hy : ∀ i, y i ∈ integerPolynomialSubalgebra k (n + 1) := by
        intro i
        dsimp [y]
        exact Subalgebra.sub_mem _ (hX i.castSucc)
          (Subalgebra.pow_mem _ (hX (Fin.last n)) _)
      let φ : MvPolynomial (Fin n) k →ₐ[k] A :=
        MvPolynomial.aeval (fun i =>
          ⟨q (y i), by
            change Ideal.Quotient.mk I (y i) ∈ quotientGeneratorSubalgebra I y
            exact Algebra.subset_adjoin ⟨i, rfl⟩⟩)
      let x : Q := q (MvPolynomial.X (Fin.last n))
      let P : Polynomial (MvPolynomial (Fin n) k) :=
        noetherPolynomialSubstitution f e
      let pA : Polynomial A := P.map φ
      let hφ : MvPolynomial (Fin n) k →+* Q := A.val.toRingHom.comp φ.toRingHom
      let qp : Polynomial (MvPolynomial (Fin n) k) →+* Q :=
        Polynomial.eval₂RingHom hφ x
      have hrootP : qp P = q f := by
        change qp (noetherPolynomialSubstitution f e) = q f
        rw [noetherPolynomialSubstitution]
        change qp (MvPolynomial.eval₂ _ _ f) = q f
        rw [MvPolynomial.hom_eval₂]
        have heval :
            MvPolynomial.eval₂Hom
                (qp.comp (Polynomial.C.comp MvPolynomial.C))
                (fun i => qp (lastVariableSubstitution n e i)) = q.toRingHom := by
          apply MvPolynomial.ringHom_ext
          · intro c
            rw [MvPolynomial.eval₂Hom_C]
            simp only [RingHom.coe_comp, Function.comp_apply]
            change qp (Polynomial.C (MvPolynomial.C c)) = q (MvPolynomial.C c)
            simp [qp, hφ, φ, q]
            rfl
          · intro i
            refine Fin.lastCases ?_ (fun i => ?_) i
            · simp [qp, q, x, lastVariableSubstitution]
            · simp [qp, hφ, φ, q, x, y, lastVariableSubstitution]
        exact congrArg (fun h => h f) heval
      have hpa_lc : pA.leadingCoeff = algebraMap k A a := by
        dsimp [pA]
        rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
        · rw [show P.leadingCoeff = MvPolynomial.C a by simpa [P] using hLC]
          simp [φ]
        · rw [show P.leadingCoeff = MvPolynomial.C a by simpa [P] using hLC]
          simpa [φ] using (isUnit_iff_ne_zero.mpr ha).map (algebraMap k A) |>.ne_zero
      have hpa_unit : IsUnit pA.leadingCoeff := by
        rw [hpa_lc]
        exact (isUnit_iff_ne_zero.mpr ha).map (algebraMap k A)
      let pmon : Polynomial A := hpa_unit.unit⁻¹ • pA
      have hpmon : pmon.Monic := by
        dsimp [pmon]
        exact Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hpa_unit
      have hroot : Polynomial.aeval x pA = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        rw [Polynomial.eval_map]
        dsimp [pA]
        rw [Polynomial.eval₂_map]
        change qp P = 0
        rw [hrootP]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hf
      have hxint : IsIntegral A x := by
        refine ⟨pmon, hpmon, ?_⟩
        dsimp [pmon]
        change Polynomial.aeval x ((↑(hpa_unit.unit⁻¹) : A) • pA) = 0
        rw [Polynomial.smul_eq_C_mul, map_mul]
        rw [hroot, mul_zero]
      have hqgen : ∀ i : Fin (n + 1), q (MvPolynomial.X i) ∈
          Algebra.adjoin A ({x} : Set Q) := by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · exact Algebra.subset_adjoin rfl
        · have hrel : q (MvPolynomial.X i.castSucc) =
              q (y i) + x ^ e i := by
            dsimp [y, x]
            rw [map_sub, map_pow]
            ring
          rw [hrel]
          apply add_mem
          · simpa using (Algebra.adjoin A ({x} : Set Q)).algebraMap_mem
              (⟨q (y i), by
              change Ideal.Quotient.mk I (y i) ∈ quotientGeneratorSubalgebra I y
              exact Algebra.subset_adjoin ⟨i, rfl⟩⟩ : A)
          · exact (Algebra.adjoin A ({x} : Set Q)).pow_mem
              (Algebra.subset_adjoin rfl) _
      have hqaeval :
          (MvPolynomial.aeval (fun i : Fin (n + 1) => q (MvPolynomial.X i))).toRingHom =
            q.toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [q]
          rfl
        · intro i
          simp [q]
      have htop : Algebra.adjoin A ({x} : Set Q) = ⊤ := by
        apply top_unique
        intro z hz
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I z
        have hsub : ∀ z, z ∈
            Algebra.adjoin k (Set.range (fun i : Fin (n + 1) => q (MvPolynomial.X i))) →
              z ∈ Algebra.adjoin A ({x} : Set Q) := by
          intro z hz
          induction hz using Algebra.adjoin_induction with
          | mem z hz =>
              obtain ⟨i, rfl⟩ := hz
              change q (MvPolynomial.X i) ∈ Algebra.adjoin A ({x} : Set Q)
              exact hqgen i
          | algebraMap c =>
              rw [IsScalarTower.algebraMap_apply k A Q]
              exact (Algebra.adjoin A ({x} : Set Q)).algebraMap_mem
                (algebraMap k A c)
          | add z w _ _ hz hw =>
              exact add_mem hz hw
          | mul z w _ _ hz hw =>
              exact mul_mem hz hw
        apply hsub
        rw [Algebra.adjoin_range_eq_range_aeval]
        exact ⟨p, congrArg (fun h => h p) hqaeval⟩
      have hInt : Algebra.IsIntegral A Q := by
        have hBint : Algebra.IsIntegral A (Algebra.adjoin A ({x} : Set Q)) :=
          Algebra.IsIntegral.adjoin (by
            intro z hz
            obtain rfl : z = x := by simpa using hz
            exact hxint)
        refine ⟨fun z => ?_⟩
        have hz : z ∈ Algebra.adjoin A ({x} : Set Q) := by
          rw [htop]
          trivial
        have hz' := hBint.isIntegral
          (⟨z, hz⟩ : Algebra.adjoin A ({x} : Set Q))
        exact (isIntegral_algHom_iff
          (Algebra.adjoin A ({x} : Set Q)).val Subtype.val_injective).mpr hz'
      have hfg : (Algebra.adjoin A ({x} : Set Q)).FG :=
        (Subalgebra.fg_iff_finiteType _).2
          (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))
      have hft : Algebra.FiniteType A Q := by
        refine ⟨?__⟩
        rw [← htop]
        exact hfg
      have hRI : A.val.toRingHom.IsIntegral := by
        intro z
        change IsIntegral A z
        exact hInt.isIntegral z
      have hfinite : RingHom.Finite A.val.toRingHom :=
        hRI.to_finite (RingHom.finiteType_algebraMap.mpr hft)
      refine ⟨y, ?_, hy⟩
      change A.val.toRingHom.Finite
      exact hfinite

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
  classical
  have integer_substitution
      {m N : ℕ} (y : Fin m → MvPolynomial (Fin N) k)
      (hy : ∀ j, y j ∈ integerPolynomialSubalgebra k N)
      (p : MvPolynomial (Fin m) k)
      (hp : p ∈ integerPolynomialSubalgebra k m) :
      MvPolynomial.aeval y p ∈ integerPolynomialSubalgebra k N := by
    rw [integerPolynomialSubalgebra] at hp ⊢
    refine Algebra.adjoin_induction
      (p := fun p _ => MvPolynomial.aeval y p ∈
        Algebra.adjoin ℤ (Set.range (fun i : Fin N => MvPolynomial.X i)))
      ?_ ?_ ?_ ?_ hp
    · intro i hi
      obtain ⟨j, rfl⟩ := hi
      simpa [integerPolynomialSubalgebra] using hy j
    · intro z
      simp
    · intro p q _ _ hp hq
      simpa using add_mem hp hq
    · intro p q _ _ hp hq
      simpa using mul_mem hp hq
  have hnorm : ∀ (m : ℕ) (J : Ideal (MvPolynomial (Fin m) k)), J ≠ ⊤ →
      ∃ r : ℕ, r ≤ m ∧
        ∃ g : MvPolynomial (Fin r) k →ₐ[k]
            ((MvPolynomial (Fin m) k) ⧸ J),
          Function.Injective g ∧
            RingHom.Finite g.toRingHom ∧
              ∃ y : Fin r → MvPolynomial (Fin m) k,
                (∀ i, g (MvPolynomial.X i) = Ideal.Quotient.mk J (y i)) ∧
                  ∀ i, y i ∈ integerPolynomialSubalgebra k m := by
    intro m
    induction m with
    | zero =>
        intro J hJ
        obtain ⟨r, hr, g, hginj, hgint⟩ :=
          noether_normalization_integral_core J hJ
        have hr0 : r = 0 := Nat.eq_zero_of_le_zero (by simpa using hr)
        subst r
        have hcomp : algebraMap k ((MvPolynomial (Fin 0) k) ⧸ J) =
            g.toRingHom.comp (algebraMap k (MvPolynomial (Fin 0) k)) := by
          ext c
          exact (g.commutes c).symm
        refine ⟨0, le_rfl, g, hginj,
          hgint.to_finite
            (hcomp ▸ RingHom.finiteType_algebraMap.mpr inferInstance).of_comp_finiteType,
          fun i => Fin.elim0 i, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
    | succ m ih =>
        intro J hJ
        by_cases hJbot : J = ⊥
        · let g : MvPolynomial (Fin (m + 1)) k →ₐ[k]
              ((MvPolynomial (Fin (m + 1)) k) ⧸ J) := Ideal.Quotient.mkₐ k J
          have hbij : Function.Bijective g := by
            dsimp [g]
            exact (Ideal.Quotient.mk_bijective_iff_eq_bot J).mpr hJbot
          have hgint : g.IsIntegral :=
            RingHom.isIntegral_of_surjective g.toRingHom hbij.2
          have hcomp : algebraMap k ((MvPolynomial (Fin (m + 1)) k) ⧸ J) =
              g.toRingHom.comp (algebraMap k (MvPolynomial (Fin (m + 1)) k)) := by
            ext c
            exact (g.commutes c).symm
          refine ⟨m + 1, le_rfl, g, hbij.1,
            hgint.to_finite
              (hcomp ▸ RingHom.finiteType_algebraMap.mpr inferInstance).of_comp_finiteType,
            fun i => MvPolynomial.X i, ?_, ?_⟩
          · intro i
            rfl
          · intro i
            exact Algebra.subset_adjoin ⟨i, rfl⟩
        · obtain ⟨y, hfiniteA, hy⟩ := one_relation J hJ hJbot
          simp only [Nat.succ_sub_one] at y hfiniteA hy
          let Q := (MvPolynomial (Fin (m + 1)) k) ⧸ J
          have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJ
          let q : MvPolynomial (Fin (m + 1)) k →ₐ[k] Q := Ideal.Quotient.mkₐ k J
          let A : Subalgebra k Q := quotientGeneratorSubalgebra J y
          let φ : MvPolynomial (Fin m) k →ₐ[k] A :=
            MvPolynomial.aeval (fun i =>
              ⟨q (y i), by
                change Ideal.Quotient.mk J (y i) ∈ quotientGeneratorSubalgebra J y
                exact Algebra.subset_adjoin ⟨i, rfl⟩⟩)
          let f : MvPolynomial (Fin m) k →ₐ[k] Q := A.val.comp φ
          have hφmap : A.val.toRingHom.comp φ.toRingHom =
              (MvPolynomial.aeval (fun i => q (y i))).toRingHom := by
            apply MvPolynomial.ringHom_ext
            · intro c
              simp [φ, q]
            · intro i
              simp [φ, q]
          have hsub :
              (MvPolynomial.aeval (fun i => q (y i))).toRingHom =
                q.toRingHom.comp
                  ((MvPolynomial.aeval (R := k) y :
                    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin (m + 1)) k).toRingHom) := by
            apply MvPolynomial.ringHom_ext
            · intro c
              simp only [RingHom.coe_comp, Function.comp_apply]
              simp [q]
              rfl
            · intro i
              simp only [RingHom.coe_comp, Function.comp_apply]
              simp [q]
          have hφsurj : Function.Surjective φ := by
            intro z
            have hz : z.1 ∈ Algebra.adjoin k (Set.range (fun i => q (y i))) := z.2
            rw [Algebra.adjoin_range_eq_range_aeval] at hz
            obtain ⟨p, hp⟩ := hz
            refine ⟨p, ?_⟩
            apply Subtype.ext
            change (A.val.toRingHom.comp φ.toRingHom) p = (z : Q)
            exact (congrArg (fun h => h p) hφmap).trans hp
          have hAint : A.val.toRingHom.IsIntegral := hfiniteA.to_isIntegral
          have hfint : f.IsIntegral := by
            change (A.val.toRingHom.comp φ.toRingHom).IsIntegral
            exact (RingHom.isIntegral_of_surjective φ.toRingHom hφsurj).trans _ _ hAint
          have hKtop : RingHom.ker f ≠ ⊤ :=
            by
              intro htop
              have h1 : (1 : MvPolynomial (Fin m) k) ∈ RingHom.ker f := by
                rw [htop]
                trivial
              change f 1 = 0 at h1
              rw [map_one] at h1
              exact one_ne_zero h1
          obtain ⟨r, hr, g₀, hg₀inj, hg₀finite, z, hg₀X, hz⟩ :=
            ih (RingHom.ker f) hKtop
          let lift :
              ((MvPolynomial (Fin m) k) ⧸ RingHom.ker f) →ₐ[k] Q :=
            Ideal.kerLiftAlg f
          have hcomp : lift.comp
                (Ideal.Quotient.mkₐ k (RingHom.ker f)) = f := by
            apply AlgHom.ext
            intro p
            change Ideal.kerLiftAlg f
              (Ideal.Quotient.mk (RingHom.ker f) p) = f p
            rw [Ideal.kerLiftAlg_mk]
          have hliftint : lift.IsIntegral := by
            exact (hcomp ▸ hfint).tower_top _ _
          let g : MvPolynomial (Fin r) k →ₐ[k] Q := lift.comp g₀
          have hgint : g.IsIntegral := by
            change (lift.toRingHom.comp g₀.toRingHom).IsIntegral
            exact hg₀finite.to_isIntegral.trans _ _ hliftint
          have hcompg : algebraMap k Q =
              g.toRingHom.comp (algebraMap k (MvPolynomial (Fin r) k)) := by
            ext c
            exact (g.commutes c).symm
          have hfiniteg : RingHom.Finite g.toRingHom := hgint.to_finite
            (hcompg ▸ RingHom.finiteType_algebraMap.mpr inferInstance).of_comp_finiteType
          refine ⟨r, by omega, g,
            (by
              change Function.Injective (lift.comp g₀)
              exact (Ideal.kerLiftAlg_injective f).comp hg₀inj),
            hfiniteg, fun i => MvPolynomial.aeval y (z i), ?_, ?_⟩
          · intro i
            rw [show g (MvPolynomial.X i) =
              lift (Ideal.Quotient.mk (RingHom.ker f) (z i)) by
                rw [← hg₀X i]
                rfl]
            change Ideal.kerLiftAlg f
              (Ideal.Quotient.mk (RingHom.ker f) (z i)) = _
            rw [Ideal.kerLiftAlg_mk]
            change (A.val.toRingHom.comp φ.toRingHom) (z i) =
              q (MvPolynomial.aeval y (z i))
            exact congrArg (fun h => h (z i)) (hφmap.trans hsub)
          · intro i
            exact integer_substitution y hy (z i) (hz i)
  obtain ⟨r, hr, g, hginj, hgfinite, y, hgX, hy⟩ := hnorm n I hI
  have hdim : ringKrullDim (MvPolynomial (Fin r) k) =
      ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
    Formalization.Books.Algebra.Unit112.integral_subring_ringKrullDim_eq
      g.toRingHom hginj hgfinite.to_isIntegral
  have hpoly : ringKrullDim (MvPolynomial (Fin r) k) = r := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    simp
  exact ⟨r, hr, g, hginj, hgfinite,
    by simpa [hpoly, Nat.card_fin] using hdim.symm, y, hgX, hy⟩

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
/-
  classical
  let x : PrimeSpectrum S := ⟨q, hq⟩
  change ∃ g : S, g ∉ x.asIdeal ∧
    ∃ d : ℕ,
      krullDimensionAt x = d ∧
        ringKrullDim (Localization.Away g) = d ∧
          ∃ φ : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g,
            Function.Injective φ ∧ RingHom.Finite φ.toRingHom
  obtain ⟨U, hUopen, hxU, hUdim⟩ := (krullDimensionAt_isLeast x).1
  obtain ⟨V, ⟨g, rfl⟩, hxV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hUopen
  have hg : g ∉ x.asIdeal := by
    exact (PrimeSpectrum.mem_basicOpen g x).mp hxV
  have hVdim : topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) =
      krullDimensionAt x := by
    apply le_antisymm
    · exact (krullDimension_mono_of_open_subset PrimeSpectrum.isOpen_basicOpen hUopen hVU).trans_eq hUdim
    · exact krullDimensionAt_le x PrimeSpectrum.isOpen_basicOpen hxV
  have hawaydim : ringKrullDim (Localization.Away g) =
      topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
    let h : Topology.IsOpenEmbedding (PrimeSpectrum.comap
        (algebraMap S (Localization.Away g))) :=
      PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g) g
    let e : PrimeSpectrum (Localization.Away g) ≃ₜ
        {p : PrimeSpectrum S // p ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))} :=
      h.isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr
          (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g))
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    change topologicalKrullDim (PrimeSpectrum (Localization.Away g)) =
      topologicalKrullDim
        {p : PrimeSpectrum S // p ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))}
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  have hg0 : g ≠ 0 := by
    intro hgzero
    apply hg
    rw [hgzero]
    exact q.zero_mem
  haveI : Nontrivial (Localization.Away g) := by
    apply (IsLocalization.toLocalizationMap (Submonoid.powers g)
      (Localization.Away g)).nontrivial
    intro hz
    obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff.mp hz
    exact (pow_ne_zero m hg0) hm
  obtain ⟨d, φ, hφinj, hφfinite⟩ :=
    exists_finite_inj_algHom_of_fg k (Localization.Away g)
  have hdimpoly : ringKrullDim (MvPolynomial (Fin d) k) =
      ringKrullDim (Localization.Away g) :=
    Formalization.Books.Algebra.Unit112.integral_subring_ringKrullDim_eq
      φ.toRingHom hφinj hφfinite.to_isIntegral
  have hdimd : ringKrullDim (MvPolynomial (Fin d) k) = d := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    simp
  refine ⟨g, hg, d, ?_, ?_, φ, hφinj, hφfinite⟩
  · calc
      krullDimensionAt x = topologicalKrullDim
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := hVdim.symm
      _ = ringKrullDim (Localization.Away g) := hawaydim.symm
      _ = ringKrullDim (MvPolynomial (Fin d) k) := hdimpoly.symm
      _ = d := hdimd
  · exact hdimpoly.symm.trans hdimd
-/

/-! ## Refined normalization -/

/-- The ideal generated by the last `n - r` variables of an `n`-variable
polynomial ring. -/
def tailVariableIdeal
    (k : Type u) [CommRing k] (n r : ℕ) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span {p | ∃ i : Fin n, r ≤ i.1 ∧ p = MvPolynomial.X i}

private theorem residueField_trdeg_of_normalization
    {k : Type u} [Field k] {n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) k)) (hq : q.IsPrime) :
    ∃ r : ℕ, r ≤ n ∧ Algebra.trdeg k q.ResidueField = r := by
  sorry
/-
  obtain ⟨r, hr, g, hginj, hfinite, _, _⟩ :=
    noether_normalization q hq.ne_top
  let Q := (MvPolynomial (Fin n) k) ⧸ q
  let K := q.ResidueField
  letI : q.IsPrime := hq
  let : IsDomain Q := Ideal.Quotient.isDomain q
  let : Algebra (MvPolynomial (Fin r) k) Q := g.toAlgebra
  let : IsScalarTower k (MvPolynomial (Fin r) k) Q :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have htrdegQ : Algebra.trdeg k Q = r := by
    have hfaith : FaithfulSMul (MvPolynomial (Fin r) k) Q :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hginj
    let : FaithfulSMul (MvPolynomial (Fin r) k) Q := hfaith
    let : Module.Finite (MvPolynomial (Fin r) k) Q := hfinite
    let : Algebra.IsAlgebraic (MvPolynomial (Fin r) k) Q :=
      Algebra.IsAlgebraic.of_finite _ _
    rw [← trdeg_add_eq k (MvPolynomial (Fin r) k)]
    simp [trdeg_eq_zero, MvPolynomial.trdeg_of_isDomain]
  have htrdegK : Algebra.trdeg k K = r := by
    let : Algebra.IsAlgebraic Q K := IsLocalization.isAlgebraic K (nonZeroDivisors Q)
    have hfaith : FaithfulSMul Q K :=
      (faithfulSmul_iff_algebraMap_injective Q K).mpr (IsFractionRing.injective Q K)
    let : FaithfulSMul Q K := hfaith
    have h := lift_trdeg_add_eq k Q K
    rw [htrdegQ, trdeg_eq_zero] at h
    simpa using h.symm
  exact ⟨r, hr, htrdegK⟩
-/

private theorem finite_triangular_substitution
    {k : Type u} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (e : Fin n → ℕ)
    (hPunit : IsUnit (noetherPolynomialSubstitution f e).leadingCoeff)
    (hPpos : 0 < (noetherPolynomialSubstitution f e).natDegree) :
    ∃ τ : MvPolynomial (Fin (n + 1)) k →+*
        MvPolynomial (Fin (n + 1)) k,
      RingHom.Finite τ ∧
        (∀ i, τ (MvPolynomial.X i.castSucc) =
          MvPolynomial.X i.castSucc - MvPolynomial.X (Fin.last n) ^ e i) ∧
          τ (MvPolynomial.X (Fin.last n)) = f ∧
            τ.comp (MvPolynomial.C : k →+*
              MvPolynomial (Fin (n + 1)) k) =
              (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k) := by
  sorry
/-
  let z : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k :=
    Fin.lastCases f (fun i =>
      MvPolynomial.X i.castSucc - MvPolynomial.X (Fin.last n) ^ e i)
  let τ : MvPolynomial (Fin (n + 1)) k →+*
      MvPolynomial (Fin (n + 1)) k := (MvPolynomial.aeval z).toRingHom
  let B : Subalgebra k (MvPolynomial (Fin (n + 1)) k) :=
    Algebra.adjoin k (Set.range z)
  let θ : MvPolynomial (Fin n) k →ₐ[k] B :=
    MvPolynomial.aeval (fun i =>
      ⟨z i.castSucc, Algebra.subset_adjoin ⟨i.castSucc, rfl⟩⟩)
  let x : MvPolynomial (Fin (n + 1)) k := MvPolynomial.X (Fin.last n)
  let P : Polynomial (MvPolynomial (Fin n) k) :=
    noetherPolynomialSubstitution f e
  let pB : Polynomial B := P.map θ
  let hθ : MvPolynomial (Fin n) k →+*
      MvPolynomial (Fin (n + 1)) k := B.val.toRingHom.comp θ.toRingHom
  let qp : Polynomial (MvPolynomial (Fin n) k) →+*
      MvPolynomial (Fin (n + 1)) k := Polynomial.eval₂RingHom hθ x
  have hrootP : qp P = f := by
    change qp (noetherPolynomialSubstitution f e) = f
    rw [noetherPolynomialSubstitution]
    change qp (MvPolynomial.eval₂ _ _ f) = f
    rw [MvPolynomial.hom_eval₂]
    have heval :
        MvPolynomial.eval₂Hom
            (qp.comp (Polynomial.C.comp MvPolynomial.C))
            (fun i => qp (lastVariableSubstitution n e i)) =
          RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [MvPolynomial.eval₂Hom_C]
        simp [qp, hθ, θ]
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [qp, x]
        · simp [qp, hθ, θ, z, x, lastVariableSubstitution]
    exact congrArg (fun h => h f) heval
  have hpBunit : IsUnit pB.leadingCoeff := by
    exact hPunit.map θ.toRingHom
  let fB : B := ⟨f, by
    change f ∈ Algebra.adjoin k (Set.range z)
    exact Algebra.subset_adjoin ⟨Fin.last n, rfl⟩⟩
  have hroot : Polynomial.aeval x pB = f := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [Polynomial.eval_map]
    dsimp [pB]
    rw [Polynomial.eval₂_map]
    change qp P = f
    exact hrootP
  have hpBpos : 0 < pB.natDegree := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero θ.toRingHom
      (hpBunit.ne_zero)]
    exact hPpos
  have hCdeg : (Polynomial.C fB).degree < pB.degree := by
    calc
      (Polynomial.C fB).degree ≤ 0 := Polynomial.degree_C_le
      _ < pB.degree := by
        rw [Polynomial.degree_eq_natDegree hpBunit.ne_zero]
        exact WithBot.coe_lt_coe.mpr hpBpos
  have hxint : IsIntegral B x := by
    let p0 : Polynomial B := pB - Polynomial.C fB
    have hp0unit : IsUnit p0.leadingCoeff := by
      dsimp [p0]
      rw [Polynomial.leadingCoeff_sub_of_degree_lt hCdeg]
      exact hpBunit
    let pmon : Polynomial B := hp0unit.unit⁻¹ • p0
    have hpmon : pmon.Monic := by
      dsimp [pmon]
      exact Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hp0unit
    refine ⟨pmon, hpmon, ?_⟩
    dsimp [pmon, p0]
    change Polynomial.aeval x
      ((↑(hp0unit.unit⁻¹) : B) • (pB - Polynomial.C fB)) = 0
    rw [Polynomial.smul_eq_C_mul, map_mul, Polynomial.aeval_sub,
      Polynomial.aeval_C, hroot]
    simp
  have hgen : Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k)) = ⊤ := by
    apply top_unique
    intro w hw
    have hw' : w ∈ Algebra.adjoin k
        (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)) := by
      rw [MvPolynomial.adjoin_range_X]
      trivial
    induction hw' using Algebra.adjoin_induction with
    | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        refine Fin.lastCases ?_ (fun i => ?_) i
        · exact Algebra.subset_adjoin rfl
        · have hzi : z i.castSucc ∈ B :=
            Algebra.subset_adjoin ⟨i.castSucc, rfl⟩
          have hmem : z i.castSucc ∈
              Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k)) := by
            exact (Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k))).algebraMap_mem hzi
          have hpow := (Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k))).pow_mem
            (Algebra.subset_adjoin rfl) (e i)
          change MvPolynomial.X i.castSucc ∈
            Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k))
          rw [show MvPolynomial.X i.castSucc = z i.castSucc + x ^ e i by
            simp [z, x]]
          exact add_mem hmem hpow
    | algebraMap c =>
        exact (Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k))).algebraMap_mem
          (algebraMap k B c)
    | add w v _ _ hw hv => exact add_mem hw hv
    | mul w v _ _ hw hv => exact mul_mem hw hv
  have hInt : Algebra.IsIntegral B (MvPolynomial (Fin (n + 1)) k) := by
    have hBint : Algebra.IsIntegral B
        (Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k))) :=
      Algebra.IsIntegral.adjoin (by
        intro w hw
        obtain rfl : w = x := by simpa using hw
        exact hxint)
    refine ⟨fun w => ?_⟩
    have hw' : w ∈ Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k)) := by
      rw [hgen]
      trivial
    have hw'' := hBint.isIntegral
      (⟨w, hw'⟩ : Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k)))
    exact (isIntegral_algHom_iff
      (Algebra.adjoin B ({x} : Set (MvPolynomial (Fin (n + 1)) k))).val
      Subtype.val_injective).mpr hw''
  have hBfg : (Algebra.adjoin k (Set.range z)).FG :=
    (Subalgebra.fg_iff_finiteType _).2
      (Algebra.FiniteType.adjoin_of_finite (Set.finite_range z))
  have hft : Algebra.FiniteType B (MvPolynomial (Fin (n + 1)) k) := by
    refine ⟨?__⟩
    rw [← hgen]
    exact (Subalgebra.fg_iff_finiteType _).mp
      (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))
  have hBint' : B.val.toRingHom.IsIntegral := by
    intro w
    change IsIntegral B w
    exact hInt.isIntegral w
  have hBfinite : RingHom.Finite B.val.toRingHom :=
    hBint'.to_finite (RingHom.finiteType_algebraMap.mpr hft)
  let τB : MvPolynomial (Fin (n + 1)) k →ₐ[k] B :=
    MvPolynomial.aeval (fun i =>
      ⟨z i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)
  have hτBsurj : Function.Surjective τB := by
    intro w
    have hw : w.1 ∈ Algebra.adjoin k (Set.range z) := w.2
    rw [Algebra.adjoin_range_eq_range_aeval] at hw
    obtain ⟨p, hp⟩ := hw
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hp
  have hτ : RingHom.Finite τ := by
    have hcomp : B.val.toRingHom.comp τB.toRingHom = τ := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [τB, τ, z]
      · intro i
        simp [τB, τ, z]
    rw [← hcomp]
    exact RingHom.Finite.comp hBfinite
      (RingHom.Finite.of_surjective τB.toRingHom hτBsurj)
  have hτC : τ.comp (MvPolynomial.C : k →+*
      MvPolynomial (Fin (n + 1)) k) =
      (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k) := by
    ext c
    simp [τ]
  refine ⟨τ, hτ, ?_, ?_, hτC⟩
  · intro i
    simp [τ, z]
  · simp [τ, z]
-/

private theorem finite_polynomial_extension
    {k : Type u} [Field k] {n : ℕ}
    (ψ : MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) k)
    (hψ : RingHom.Finite ψ) :
    ∃ β : MvPolynomial (Fin (n + 1)) k →+*
        MvPolynomial (Fin (n + 1)) k,
      RingHom.Finite β ∧
        (∀ i, β (MvPolynomial.X i.castSucc) =
          MvPolynomial.rename Fin.castSucc (ψ (MvPolynomial.X i))) ∧
          β (MvPolynomial.X (Fin.last n)) = MvPolynomial.X (Fin.last n) ∧
            β.comp (MvPolynomial.C : k →+*
              MvPolynomial (Fin (n + 1)) k) =
              (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k) := by
  sorry
/-
  let z : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k :=
    Fin.lastCases (MvPolynomial.X (Fin.last n)) (fun i =>
      MvPolynomial.rename Fin.castSucc (ψ (MvPolynomial.X i)))
  let β : MvPolynomial (Fin (n + 1)) k →+*
      MvPolynomial (Fin (n + 1)) k := (MvPolynomial.aeval z).toRingHom
  let C : Subalgebra k (MvPolynomial (Fin (n + 1)) k) :=
    Algebra.adjoin k (Set.range z)
  let ι : MvPolynomial (Fin n) k →+*
      MvPolynomial (Fin (n + 1)) k := MvPolynomial.rename Fin.castSucc
  let j : MvPolynomial (Fin n) k →ₐ[k] C :=
    MvPolynomial.aeval (fun i =>
      ⟨z i.castSucc, Algebra.subset_adjoin ⟨i.castSucc, rfl⟩⟩)
  have hj : C.val.toRingHom.comp j.toRingHom = ι.comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [j, ι, z]
    · intro i
      simp [j, ι, z]
  have hψint : ψ.IsIntegral := hψ.to_isIntegral
  have hgen : Algebra.adjoin C
      (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin (n + 1)) k)) = ⊤ := by
    apply top_unique
    intro w hw
    have hw' : w ∈ Algebra.adjoin k
        (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)) := by
      rw [MvPolynomial.adjoin_range_X]
      trivial
    induction hw' using Algebra.adjoin_induction with
    | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        refine Fin.lastCases ?_ (fun i => ?_) i
        · exact (Algebra.adjoin C
            (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin (n + 1)) k))).algebraMap_mem
            (Algebra.subset_adjoin ⟨Fin.last n, rfl⟩)
        · exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap c =>
        exact (Algebra.adjoin C
          (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin (n + 1)) k))).algebraMap_mem
          (algebraMap k C c)
    | add w v _ _ hw hv => exact add_mem hw hv
    | mul w v _ _ hw hv => exact mul_mem hw hv
  have hgen_int : ∀ i : Fin n,
      IsIntegral C (MvPolynomial.X i.castSucc) := by
    intro i
    have hi : (C.val.toRingHom.comp j.toRingHom).IsIntegralElem
        (ι (MvPolynomial.X i)) := by
      rw [hj]
      exact (hψint (MvPolynomial.X i)).map ι
    have hi' := RingHom.IsIntegralElem.of_comp hi
    simpa [ι] using hi'
  have hCint : Algebra.IsIntegral C
      (MvPolynomial (Fin (n + 1)) k) := by
    have hAint : Algebra.IsIntegral C
        (Algebra.adjoin C
          (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin (n + 1)) k))) :=
      Algebra.IsIntegral.adjoin (by
        intro w hw
        obtain ⟨i, rfl⟩ := hw
        exact hgen_int i)
    refine ⟨fun w => ?_⟩
    have hw' : w ∈ Algebra.adjoin C
        (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin (n + 1)) k)) := by
      rw [hgen]
      trivial
    have hw'' := hAint.isIntegral
      (⟨w, hw'⟩ : Algebra.adjoin C
        (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin (n + 1)) k)))
    exact (isIntegral_algHom_iff
      (Algebra.adjoin C
        (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin (n + 1)) k))).val
      Subtype.val_injective).mpr hw''
  have hft : Algebra.FiniteType C (MvPolynomial (Fin (n + 1)) k) := by
    refine ⟨?__⟩
    rw [← hgen]
    exact (Subalgebra.fg_iff_finiteType _).mp
      (Algebra.FiniteType.adjoin_of_finite (Set.finite_range
        (MvPolynomial.X : Fin n → MvPolynomial (Fin (n + 1)) k)))
  have hCint' : C.val.toRingHom.IsIntegral := by
    intro w
    exact hCint.isIntegral w
  have hCfinite : RingHom.Finite C.val.toRingHom :=
    hCint'.to_finite (RingHom.finiteType_algebraMap.mpr hft)
  let βC : MvPolynomial (Fin (n + 1)) k →ₐ[k] C :=
    MvPolynomial.aeval (fun i =>
      ⟨z i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)
  have hβCsurj : Function.Surjective βC := by
    intro w
    have hw : w.1 ∈ Algebra.adjoin k (Set.range z) := w.2
    rw [Algebra.adjoin_range_eq_range_aeval] at hw
    obtain ⟨p, hp⟩ := hw
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hp
  have hβ : RingHom.Finite β := by
    have hcomp : C.val.toRingHom.comp βC.toRingHom = β := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [βC, β, z]
      · intro i
        simp [βC, β, z]
    rw [← hcomp]
    exact RingHom.Finite.comp hCfinite
      (RingHom.Finite.of_surjective βC.toRingHom hβCsurj)
  have hβC : β.comp (MvPolynomial.C : k →+*
      MvPolynomial (Fin (n + 1)) k) =
      (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k) := by
    ext c
    simp [β]
  refine ⟨β, hβ, ?_, ?_, hβC⟩
  · intro i
    simp [β, z]
  · simp [β, z]
-/

private theorem mem_span_last_sub_projection
    {k : Type u} [Field k] {n : ℕ}
    (ρ : MvPolynomial (Fin (n + 1)) k →+*
      MvPolynomial (Fin (n + 1)) k)
    (hρ : (∀ c : k, ρ (MvPolynomial.C c) = MvPolynomial.C c) ∧
      (∀ i : Fin n, ρ (MvPolynomial.X i.castSucc) =
        MvPolynomial.X i.castSucc) ∧
      ρ (MvPolynomial.X (Fin.last n)) = 0) :
    ∀ p, p - ρ p ∈ Ideal.span
      ({MvPolynomial.X (Fin.last n)} : Set (MvPolynomial (Fin (n + 1)) k)) := by
  sorry
/-
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => rw [hρ.1 c, sub_self]; exact Ideal.zero_mem
  | add p q hp hq =>
      rw [map_add]
      simpa [sub_add_sub_comm] using
        (Ideal.add_mem _ hp hq)
  | mul_X p i hp =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [map_mul, hρ.2.2, mul_zero, sub_zero]
        exact Ideal.mul_mem_left _ (Ideal.subset_span (by simp))
      · rw [map_mul, hρ.2.1 i, sub_mul]
        exact Ideal.mul_mem_right _ hp
-/

private theorem comap_tail_of_triangular_composition
    {k : Type u} [Field k] {n r : ℕ}
    (q : Ideal (MvPolynomial (Fin (n + 1)) k))
    (α : MvPolynomial (Fin n) k →+*
      MvPolynomial (Fin (n + 1)) k)
    (ψ : MvPolynomial (Fin n) k →+*
      MvPolynomial (Fin n) k)
    (τ β : MvPolynomial (Fin (n + 1)) k →+*
      MvPolynomial (Fin (n + 1)) k)
    (f : MvPolynomial (Fin (n + 1)) k)
    (hτ : (∀ i : Fin n, τ (MvPolynomial.X i.castSucc) = α (MvPolynomial.X i)) ∧
      τ (MvPolynomial.X (Fin.last n)) = f)
    (hβ : (∀ i : Fin n, β (MvPolynomial.X i.castSucc) =
        MvPolynomial.rename Fin.castSucc (ψ (MvPolynomial.X i))) ∧
      β (MvPolynomial.X (Fin.last n)) = MvPolynomial.X (Fin.last n))
    (hf : f ∈ q)
    (hr : r ≤ n)
    (hp : (q.comap α).comap ψ = tailVariableIdeal k n r) :
    q.comap (τ.comp β) = tailVariableIdeal k (n + 1) r := by
  sorry
/-
  let qmk : MvPolynomial (Fin (n + 1)) k →+*
      (MvPolynomial (Fin (n + 1)) k) ⧸ q := Ideal.Quotient.mk q
  let ι : MvPolynomial (Fin n) k →+*
      MvPolynomial (Fin (n + 1)) k := MvPolynomial.rename Fin.castSucc
  let drop : MvPolynomial (Fin (n + 1)) k →+*
      MvPolynomial (Fin n) k := MvPolynomial.aeval
        (Fin.lastCases 0 (fun i => MvPolynomial.X i))
  let ρ : MvPolynomial (Fin (n + 1)) k →+*
      MvPolynomial (Fin (n + 1)) k := MvPolynomial.aeval
        (Fin.lastCases 0 (fun i => MvPolynomial.X i.castSucc))
  let δ : MvPolynomial (Fin (n + 1)) k →+*
      (MvPolynomial (Fin (n + 1)) k) ⧸ q := qmk.comp τ |>.comp β
  have hτι : τ.comp ι = α := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ι]
    · intro i
      simp only [RingHom.comp_apply, ι, MvPolynomial.rename_X]
      exact hτ.1 i
  have hδι : δ.comp ι = qmk.comp α |>.comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [δ, ι, qmk]
    · intro i
      simp only [RingHom.comp_apply, δ, hβ.1 i, hτι]
      rfl
  have hδlast : δ (MvPolynomial.X (Fin.last n)) = 0 := by
    rw [show δ (MvPolynomial.X (Fin.last n)) = qmk (τ (MvPolynomial.X (Fin.last n))) by
      simp [δ, hβ.2]]
    rw [hτ.2]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hδρ : δ.comp ρ = δ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [δ, ρ]
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa [ρ] using hδlast
      · simp [ρ]
  have hρ : (∀ c : k, ρ (MvPolynomial.C c) = MvPolynomial.C c) ∧
      (∀ i : Fin n, ρ (MvPolynomial.X i.castSucc) =
      MvPolynomial.X i.castSucc) ∧
      ρ (MvPolynomial.X (Fin.last n)) = 0 := by
    constructor
    · intro c
      simp [ρ]
    constructor
    · intro i
      simp [ρ]
    · simp [ρ]
  have hρcomp : ι.comp drop = ρ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ι, drop, ρ]
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [ι, drop, ρ]
      · simp [ι, drop, ρ]
  have hL : Ideal.span
      ({MvPolynomial.X (Fin.last n)} : Set (MvPolynomial (Fin (n + 1)) k)) ≤
        tailVariableIdeal k (n + 1) r := by
    apply Ideal.span_le.2
    intro z hz
    obtain rfl : z = MvPolynomial.X (Fin.last n) := by simpa using hz
    apply Ideal.subset_span
    exact ⟨Fin.last n, by simpa using hr, rfl⟩
  have hmap : Ideal.map ι (tailVariableIdeal k n r) ≤
      tailVariableIdeal k (n + 1) r := by
    apply (Ideal.map_le_iff_le_comap).2
    rw [tailVariableIdeal]
    apply Ideal.span_le.2
    intro z hz
    obtain ⟨i, hri, rfl⟩ := hz
    change ι (MvPolynomial.X i) ∈ tailVariableIdeal k (n + 1) r
    rw [show ι (MvPolynomial.X i) = MvPolynomial.X i.castSucc by simp]
    apply Ideal.subset_span
    exact ⟨i.castSucc, by simpa using hri, rfl⟩
  apply le_antisymm
  · intro h hh
    have hhρ : δ (ρ h) = 0 := by
      have := congrArg (fun u => u h) hδρ
      simpa [δ] using hh
    let a := drop h
    have hρa : ρ h = ι a := by
      change ρ h = ι (drop h)
      rw [← hρcomp]
      rfl
    have hδa : δ (ι a) = 0 := by
      rw [← hρa]
      exact hhρ
    have hqa : α (ψ a) ∈ q := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hzero := congrArg (fun u => u a) hδι
      rw [hδa] at hzero
      exact hzero.symm
    have hpa : ψ a ∈ q.comap α := hqa
    have har : a ∈ tailVariableIdeal k n r := by
      rw [← hp]
      exact hpa
    have hρtail : ρ h ∈ tailVariableIdeal k (n + 1) r := by
      rw [hρa]
      exact hmap (Ideal.mem_map_of_mem ι har)
    have hdiff := mem_span_last_sub_projection ρ hρ h
    rw [← sub_add_cancel h (ρ h)]
    exact Ideal.add_mem _ (hL hdiff) hρtail
  · intro h hh
    rw [tailVariableIdeal]
    apply Ideal.span_le.2
    intro z hz
    obtain ⟨i, hri, rfl⟩ := hz
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact hδlast
    · have hxi : MvPolynomial.X i ∈ tailVariableIdeal k n r := by
        apply Ideal.subset_span
        exact ⟨i, hri, rfl⟩
      have hψxi : ψ (MvPolynomial.X i) ∈ q.comap α := by
        rw [hp]
        exact hxi
      have hαψxi : α (ψ (MvPolynomial.X i)) ∈ q := hψxi
      change qmk (τ (β (MvPolynomial.X i.castSucc))) = 0
      rw [hβ.1 i]
      change qmk (τ (ι (ψ (MvPolynomial.X i)))) = 0
      rw [show τ (ι (ψ (MvPolynomial.X i))) =
        α (ψ (MvPolynomial.X i)) by
          exact congrArg (fun u => u (ψ (MvPolynomial.X i))) hτι]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hαψxi
-/

private theorem tailVariableIdeal_self
    {k : Type u} [CommRing k] (n : ℕ) :
    tailVariableIdeal k n n = ⊥ := by
  rw [tailVariableIdeal]
  have hset : {p : MvPolynomial (Fin n) k |
      ∃ i : Fin n, n ≤ i.1 ∧ p = MvPolynomial.X i} = ∅ := by
    ext p
    change (∃ i : Fin n, n ≤ i.1 ∧ p = MvPolynomial.X i) ↔ False
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro h
      exact h.elim
  rw [hset, Ideal.span_empty]

private theorem exists_refined_normalization_map
    {k : Type u} [Field k] {n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) k)) (hq : q.IsPrime) :
    ∃ r : ℕ, r ≤ n ∧
      ∃ φ : MvPolynomial (Fin n) k →+*
          MvPolynomial (Fin n) k,
        RingHom.Finite φ ∧ q.comap φ = tailVariableIdeal k n r ∧
          φ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin n) k) =
            (MvPolynomial.C : k →+* MvPolynomial (Fin n) k) := by
  sorry
/-
  induction n with
  | zero =>
      have hqbot : q = ⊥ := by
        apply le_antisymm
        · intro f hf
          have hfC : f = MvPolynomial.C (f.coeff 0) :=
            MvPolynomial.eq_C_of_isEmpty f
          by_cases ha : f.coeff 0 = 0
          · simpa [hfC, ha]
          · have hone : (1 : MvPolynomial (Fin 0) k) ∈ q := by
              have hmul := q.mul_mem_left (MvPolynomial.C (f.coeff 0)⁻¹) hf
              rw [hfC, ← MvPolynomial.C_mul, inv_mul_cancel₀ ha,
                MvPolynomial.C_1] at hmul
              exact hmul
            exact (hq.ne_top ((Ideal.eq_top_iff_one q).2 hone)).elim
        · exact bot_le
      subst q
      refine ⟨0, le_rfl, RingHom.id _, RingHom.Finite.id _, ?_, ?_⟩
      · rw [Ideal.comap_id, tailVariableIdeal_self]
      · rfl
  | succ n ih =>
      by_cases hqbot : q = ⊥
      · subst q
        refine ⟨n + 1, le_rfl, RingHom.id _, RingHom.Finite.id _, ?_, ?_⟩
        · rw [Ideal.comap_id, tailVariableIdeal_self]
        · rfl
      · obtain ⟨f, hf, hfne⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot hqbot
        have hf_nonconst : f ∉ Set.range (fun a : k => MvPolynomial.C a) := by
          rintro ⟨a, rfl⟩
          by_cases ha : a = 0
          · exact hfne (by simp [ha])
          · have hone : (1 : MvPolynomial (Fin (n + 1)) k) ∈ q := by
              have hmul := q.mul_mem_left (MvPolynomial.C a⁻¹) hf
              rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ha, MvPolynomial.C_1] at hmul
              exact hmul
            exact hq.ne_top ((Ideal.eq_top_iff_one q).2 hone)
        obtain ⟨e, he⟩ := exists_lastVariableWeights f.support
        obtain ⟨d, a, hd, ha, ν, hν, hcoeff, hdeg, hLC⟩ :=
          helper_polynomial_leading_term f hf_nonconst e he
        have hPunit : IsUnit
            (noetherPolynomialSubstitution f e).leadingCoeff := by
          rw [hLC]
          exact IsUnit.map (MvPolynomial.C : k →+*
            MvPolynomial (Fin (n + 1)) k) (isUnit_iff_ne_zero.mpr ha)
        let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
          fun i => MvPolynomial.X i.castSucc -
            MvPolynomial.X (Fin.last n) ^ e i
        let α : MvPolynomial (Fin n) k →+*
            MvPolynomial (Fin (n + 1)) k := (MvPolynomial.aeval y).toRingHom
        have hα : ∀ i, α (MvPolynomial.X i) = y i := by
          intro i
          simp [α]
        have hpprime : (q.comap α).IsPrime := Ideal.comap_isPrime α q
        obtain ⟨r, hr, ψ, hψfinite, hp⟩ := ih (q.comap α) hpprime
        obtain ⟨τ, hτfinite, hτcast, hτlast, hτC⟩ :=
          finite_triangular_substitution f e hPunit hdeg
        obtain ⟨β, hβfinite, hβcast, hβlast, hβC⟩ :=
          finite_polynomial_extension ψ hψfinite
        let φ : MvPolynomial (Fin (n + 1)) k →+*
            MvPolynomial (Fin (n + 1)) k := τ.comp β
        have hcomap : q.comap φ = tailVariableIdeal k (n + 1) r := by
          apply comap_tail_of_triangular_composition q α ψ τ β f
          · constructor
            · intro i
              simpa [α, y] using hτcast i
            · exact hτlast
          · constructor
            · exact hβcast
            · exact hβlast
          · exact hf
          · exact hr
          · simpa [φ] using hp
        have hφC : φ.comp (MvPolynomial.C : k →+*
            MvPolynomial (Fin (n + 1)) k) =
            (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k) := by
          calc
            φ.comp (MvPolynomial.C : k →+*
                MvPolynomial (Fin (n + 1)) k) =
                τ.comp (β.comp (MvPolynomial.C : k →+*
                  MvPolynomial (Fin (n + 1)) k)) := by rfl
            _ = τ.comp (MvPolynomial.C : k →+*
                MvPolynomial (Fin (n + 1)) k) := by rw [hβC]
            _ = (MvPolynomial.C : k →+*
                MvPolynomial (Fin (n + 1)) k) := hτC
        refine ⟨r, by omega, φ, RingHom.Finite.comp hτfinite hβfinite,
          hcomap, hφC⟩
-/

private theorem trdeg_residueField_eq_of_comap_tail
    {k : Type u} [Field k] {n r : ℕ}
    (q : Ideal (MvPolynomial (Fin n) k))
    (hq : q.IsPrime)
    (φ : MvPolynomial (Fin n) k →+*
      MvPolynomial (Fin n) k)
    (hφfinite : RingHom.Finite φ)
    (hcomap : q.comap φ = tailVariableIdeal k n r)
    (hr : r ≤ n)
    (hφC : φ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin n) k) =
      (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)) :
    Algebra.trdeg k q.ResidueField = r := by
  sorry
/-
  let emb : Fin r ↪ Fin n :=
    ⟨Fin.castLE hr, Fin.castLE_injective hr⟩
  let ι : MvPolynomial (Fin r) k →ₐ[k]
      MvPolynomial (Fin n) k := MvPolynomial.rename emb
  let κ : MvPolynomial (Fin n) k →ₐ[k]
      MvPolynomial (Fin r) k := MvPolynomial.killCompl emb.injective
  let φA : MvPolynomial (Fin n) k →ₐ[k]
      MvPolynomial (Fin n) k :=
    { toRingHom := φ
      commutes' := fun c => by
        exact congrArg (fun h => h c) hφC }
  let qmk : MvPolynomial (Fin n) k →ₐ[k] q.ResidueField :=
    Ideal.Quotient.mkₐ k q
  let g : MvPolynomial (Fin r) k →ₐ[k] q.ResidueField :=
    qmk.comp (φA.comp ι)
  have htail_kill : tailVariableIdeal k n r ≤
      RingHom.ker κ.toRingHom := by
    rw [tailVariableIdeal]
    apply Ideal.span_le.2
    intro z hz
    obtain ⟨i, hri, rfl⟩ := hz
    apply Ideal.mem_ker.mpr
    have hi : i ∉ Set.range emb := by
      intro hi
      obtain ⟨j, hj⟩ := hi
      have hj' : i.1 = j.1 := congrArg Fin.val hj
      have : i.1 < r := by simpa [emb] using j.2
      omega
    exact MvPolynomial.killCompl_X_eq_zero emb hi
  have hginj : Function.Injective g := by
    intro a b hab
    have hz : g (a - b) = 0 := by simp [hab]
    have hmem : ι (a - b) ∈ q.comap φ := by
      change φ (ι (a - b)) ∈ q
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact hz
    rw [hcomap] at hmem
    have hk := htail_kill hmem
    have hk' : κ (ι (a - b)) = 0 := hk
    simpa [κ, MvPolynomial.killCompl_rename_app] using hk'
  have hδfactor :
      (Ideal.Quotient.mk q).comp φ = g.toRingHom.comp κ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [g, κ, qmk, φA, hφC]
    · intro i
      by_cases hi : i ∈ Set.range emb
      · obtain ⟨j, rfl⟩ := hi
        simp [g, κ, qmk, ι, φA]
      · have hri : r ≤ i.1 := by
          by_contra hnot
          have hj : (⟨i.1, hnot⟩ : Fin r) ∈ Set.range emb := by
            refine ⟨⟨i.1, hnot⟩, ?_⟩
            apply Fin.ext
            rfl
          exact hi hj
        have hXi : MvPolynomial.X i ∈ tailVariableIdeal k n r := by
          apply Ideal.subset_span
          exact ⟨i, hri, rfl⟩
        have hφXi : φ (MvPolynomial.X i) ∈ q := by
          rw [← hcomap]
          exact hXi
        have hqXi : (Ideal.Quotient.mk q) (φ (MvPolynomial.X i)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hφXi
        simpa [g, κ, qmk, φA, ι, hi] using hqXi
  have hδfinite : RingHom.Finite
      ((Ideal.Quotient.mk q).comp φ) :=
    RingHom.Finite.comp
      (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hφfinite
  have hgfinite : RingHom.Finite g.toRingHom := by
    apply RingHom.Finite.of_comp_finite
    rw [hδfactor]
    exact hδfinite
  let Q := (MvPolynomial (Fin n) k) ⧸ q
  let K := q.ResidueField
  let : IsDomain Q := Ideal.Quotient.isDomain q hq
  let : Algebra (MvPolynomial (Fin r) k) Q := g.toAlgebra
  let : IsScalarTower k (MvPolynomial (Fin r) k) Q :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have htrdegQ : Algebra.trdeg k Q = r := by
    have hfaith : FaithfulSMul (MvPolynomial (Fin r) k) Q :=
      (faithfulSmul_iff_algebraMap_injective _ _).mpr hginj
    let : FaithfulSMul (MvPolynomial (Fin r) k) Q := hfaith
    let : Module.Finite (MvPolynomial (Fin r) k) Q := hgfinite
    let : Algebra.IsAlgebraic (MvPolynomial (Fin r) k) Q :=
      Algebra.IsAlgebraic.of_finite _ _
    rw [← trdeg_add_eq k (MvPolynomial (Fin r) k)]
    rw [trdeg_eq_zero, add_zero]
    simp [MvPolynomial.trdeg_of_isDomain]
  have htrdegK : Algebra.trdeg k K = r := by
    let : Algebra.IsAlgebraic Q K := IsLocalization.isAlgebraic K (nonZeroDivisors Q)
    have hfaith : FaithfulSMul Q K :=
      (faithfulSmul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective Q K)
    let : FaithfulSMul Q K := hfaith
    have h := lift_trdeg_add_eq k Q K
    rw [htrdegQ, trdeg_eq_zero] at h
    simpa using h.symm
  exact htrdegK
-/

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
  classical
  let _ : q.IsPrime := hq
  obtain ⟨r, hr, φ, hφfinite, hcomap, hφC⟩ :=
    exists_refined_normalization_map q hq
  have htrdeg := trdeg_residueField_eq_of_comap_tail
    q hq φ hφfinite hcomap hr hφC
  exact ⟨r, hr, htrdeg, φ, hφfinite, hcomap⟩

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
