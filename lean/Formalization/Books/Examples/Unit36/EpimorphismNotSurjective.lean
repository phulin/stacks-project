import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.PNat.Notation
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Examples, Chapter 36: An epimorphism of zero-dimensional rings which is not surjective

This file records the two countable polynomial presentations in the source and
the ring map between their quotients.  The omitted computations showing that
the target variables are nilpotent and that the first `y` is nonzero are left
as theorem interfaces, as are the local/zero-dimensional and epimorphism
claims.

The positive-natural indexing below implements the textbook's 1-based indices.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory

namespace Formalization.Books.Examples.Unit36

/-! ## The two polynomial presentations -/

/-- The variables in the source presentation, with the left summand naming `x`
and the right summand naming `z`. -/
abbrev sourceVariable := ℕ+ ⊕ ℕ+

/-- The variables in the target presentation, with the left summand naming `x`
and the right summand naming `y`. -/
abbrev targetVariable := ℕ+ ⊕ ℕ+

/-- The countable polynomial ring on the source variables. -/
abbrev sourcePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial sourceVariable k

/-- The countable polynomial ring on the target variables. -/
abbrev targetPolynomialRing (k : Type u) [Field k] :=
  MvPolynomial targetVariable k

/-- The exponent `4ⁱ` occurring in the source, with `i : ℕ+`. -/
def nilpotenceExponent (i : ℕ+) : ℕ :=
  4 ^ (i : ℕ)

/-- The source polynomial variable `xᵢ`. -/
def sourceX (k : Type u) [Field k] (i : ℕ+) : sourcePolynomialRing k :=
  MvPolynomial.X (.inl i)

/-- The source polynomial variable `zᵢ`. -/
def sourceZ (k : Type u) [Field k] (i : ℕ+) : sourcePolynomialRing k :=
  MvPolynomial.X (.inr i)

/-- The target polynomial variable `xᵢ`. -/
def targetX (k : Type u) [Field k] (i : ℕ+) : targetPolynomialRing k :=
  MvPolynomial.X (.inl i)

/-- The target polynomial variable `yᵢ`. -/
def targetY (k : Type u) [Field k] (i : ℕ+) : targetPolynomialRing k :=
  MvPolynomial.X (.inr i)

/-- The generators `(xᵢ⁴ⁱ, zᵢ⁴ⁱ)` of the source relation ideal. -/
def sourceRelationGenerators (k : Type u) [Field k] :
    Set (sourcePolynomialRing k) :=
  Set.range (fun i : ℕ+ => sourceX k i ^ nilpotenceExponent i) ∪
    Set.range (fun i : ℕ+ => sourceZ k i ^ nilpotenceExponent i)

/-- The source relation ideal `(xᵢ⁴ⁱ, zᵢ⁴ⁱ)`. -/
def sourceRelationIdeal (k : Type u) [Field k] :
    Ideal (sourcePolynomialRing k) :=
  Ideal.span (sourceRelationGenerators k)

/-- The generators `(xᵢ⁴ⁱ, yᵢ - xᵢ₊₁ yᵢ₊₁²)` of the target relation ideal. -/
def targetRelationGenerators (k : Type u) [Field k] :
    Set (targetPolynomialRing k) :=
  Set.range (fun i : ℕ+ => targetX k i ^ nilpotenceExponent i) ∪
    Set.range (fun i : ℕ+ =>
      targetY k i - targetX k (i + 1) * targetY k (i + 1) ^ 2)

/-- The target relation ideal `(xᵢ⁴ⁱ, yᵢ - xᵢ₊₁ yᵢ₊₁²)`. -/
def targetRelationIdeal (k : Type u) [Field k] :
    Ideal (targetPolynomialRing k) :=
  Ideal.span (targetRelationGenerators k)

/-- The source quotient ring in the example. -/
abbrev sourceRing (k : Type u) [Field k] :=
  sourcePolynomialRing k ⧸ sourceRelationIdeal k

/-- The target quotient ring in the example. -/
abbrev targetRing (k : Type u) [Field k] :=
  targetPolynomialRing k ⧸ targetRelationIdeal k

/-- The source quotient element represented by `xᵢ`. -/
def sourceXElement (k : Type u) [Field k] (i : ℕ+) : sourceRing k :=
  Ideal.Quotient.mk (sourceRelationIdeal k) (sourceX k i)

/-- The source quotient element represented by `zᵢ`. -/
def sourceZElement (k : Type u) [Field k] (i : ℕ+) : sourceRing k :=
  Ideal.Quotient.mk (sourceRelationIdeal k) (sourceZ k i)

/-- The target quotient element represented by `xᵢ`. -/
def targetXElement (k : Type u) [Field k] (i : ℕ+) : targetRing k :=
  Ideal.Quotient.mk (targetRelationIdeal k) (targetX k i)

/-- The target quotient element represented by `yᵢ`. -/
def targetYElement (k : Type u) [Field k] (i : ℕ+) : targetRing k :=
  Ideal.Quotient.mk (targetRelationIdeal k) (targetY k i)

/-! ## The polynomial map and its quotient -/

/-- The polynomial-ring map sending `xᵢ ↦ xᵢ` and `zᵢ ↦ xᵢyᵢ`. -/
def sourcePolynomialMap (k : Type u) [Field k] :
    sourcePolynomialRing k →+* targetPolynomialRing k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* targetPolynomialRing k) fun v =>
    match v with
    | .inl i => targetX k i
    | .inr i => targetX k i * targetY k i

@[simp]
theorem sourcePolynomialMap_x (k : Type u) [Field k] (i : ℕ+) :
    sourcePolynomialMap k (sourceX k i) = targetX k i := by
  simp [sourcePolynomialMap, sourceX]

@[simp]
theorem sourcePolynomialMap_z (k : Type u) [Field k] (i : ℕ+) :
    sourcePolynomialMap k (sourceZ k i) = targetX k i * targetY k i := by
  simp [sourcePolynomialMap, sourceZ]

/-- The polynomial map followed by the target quotient map. -/
def sourcePolynomialMapToTarget (k : Type u) [Field k] :
    sourcePolynomialRing k →+* targetRing k :=
  (Ideal.Quotient.mk (targetRelationIdeal k)).comp (sourcePolynomialMap k)

lemma sourceRelationGenerators_map_to_zero (k : Type u) [Field k]
    {p : sourcePolynomialRing k} (hp : p ∈ sourceRelationGenerators k) :
    sourcePolynomialMapToTarget k p = 0 := by
  change p ∈
      (Set.range (fun i : ℕ+ => sourceX k i ^ nilpotenceExponent i) ∪
        Set.range (fun i : ℕ+ => sourceZ k i ^ nilpotenceExponent i)) at hp
  rcases hp with hp | hp
  · rcases hp with ⟨i, rfl⟩
    rw [sourcePolynomialMapToTarget, RingHom.comp_apply, map_pow,
        sourcePolynomialMap_x]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
      Ideal.subset_span (Or.inl (Set.mem_range_self i))
  · rcases hp with ⟨i, rfl⟩
    rw [sourcePolynomialMapToTarget, RingHom.comp_apply, map_pow,
        sourcePolynomialMap_z]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hx : targetX k i ^ nilpotenceExponent i ∈ targetRelationIdeal k :=
      Ideal.subset_span (Or.inl (Set.mem_range_self i))
    simpa [mul_pow, mul_comm, mul_left_comm, mul_assoc] using
      (targetRelationIdeal k).mul_mem_left (targetY k i ^ nilpotenceExponent i) hx

lemma sourceRelationIdeal_le_map_kernel (k : Type u) [Field k] :
    sourceRelationIdeal k ≤ RingHom.ker (sourcePolynomialMapToTarget k) := by
  change Ideal.span (sourceRelationGenerators k) ≤
    RingHom.ker (sourcePolynomialMapToTarget k)
  refine Ideal.span_le.mpr ?_
  intro p hp
  exact sourceRelationGenerators_map_to_zero k hp

/-- The quotient map of the displayed polynomial map. -/
noncomputable def sourceToTarget (k : Type u) [Field k] :
    sourceRing k →+* targetRing k :=
  Ideal.Quotient.lift (sourceRelationIdeal k) (sourcePolynomialMapToTarget k)
    (sourceRelationIdeal_le_map_kernel k)

@[simp]
theorem sourceToTarget_x (k : Type u) [Field k] (i : ℕ+) :
    sourceToTarget k (sourceXElement k i) = targetXElement k i := by
  simp [sourceToTarget, sourceXElement, targetXElement, sourcePolynomialMapToTarget]

@[simp]
theorem sourceToTarget_z (k : Type u) [Field k] (i : ℕ+) :
    sourceToTarget k (sourceZElement k i) =
      targetXElement k i * targetYElement k i := by
  simp [sourceToTarget, sourceZElement, targetXElement, targetYElement,
    sourcePolynomialMapToTarget]

/-! ## Nilpotence, grading, and failure of surjectivity -/

/-- The target relation gives `yᵢ = xᵢ₊₁ yᵢ₊₁²`. -/
theorem target_y_relation (k : Type u) [Field k] (i : ℕ+) :
    targetYElement k i =
      targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2 := by
  apply sub_eq_zero.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Or.inr (Set.mem_range_self i))

/-- The displayed `xᵢ⁴ⁱ = 0` relations hold in the target quotient. -/
theorem target_x_power_eq_zero (k : Type u) [Field k] (i : ℕ+) :
    targetXElement k i ^ nilpotenceExponent i = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa [targetRelationIdeal, targetXElement, map_pow] using
    (Ideal.subset_span (Or.inl (Set.mem_range_self i)) :
      targetX k i ^ nilpotenceExponent i ∈ targetRelationIdeal k)

/-- Every `yᵢ` is nilpotent with the exponent forced by the next `x` relation. -/
theorem target_y_power_eq_zero (k : Type u) [Field k] (i : ℕ+) :
    targetYElement k i ^ nilpotenceExponent (i + 1) = 0 := by
  rw [target_y_relation, mul_pow, target_x_power_eq_zero, zero_mul]

private def targetEvaluationXExponent (N i : ℕ+) : ℕ :=
  2 * 4 ^ ((N : ℕ) + 1 - (i : ℕ))

private def targetEvaluationYExponent (N i : ℕ+) : ℕ :=
  4 ^ ((N : ℕ) + 1 - (i : ℕ))

private def targetEvaluationPolynomialMap (k : Type u) [Field k] (N : ℕ+) :
    targetPolynomialRing k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C fun v =>
    match v with
    | .inl i => Polynomial.X ^ targetEvaluationXExponent N i
    | .inr i => Polynomial.X ^ targetEvaluationYExponent N i

private lemma targetEvaluationYExponent_relation (N i : ℕ+) (hi : i ≤ N) :
    targetEvaluationYExponent N i =
      targetEvaluationXExponent N (i + 1) +
        2 * targetEvaluationYExponent N (i + 1) := by
  have hjs : (i : ℕ) ≤ (N : ℕ) := by exact_mod_cast hi
  dsimp [targetEvaluationXExponent, targetEvaluationYExponent]
  simp only [Nat.add_sub_add_right]
  rw [Nat.sub_add_comm hjs, pow_succ]
  ring

private lemma targetEvaluation_map_x_power (k : Type u) [Field k] (N i : ℕ+)
    (hi : i ≤ N) :
    targetEvaluationPolynomialMap k N (targetX k i ^ nilpotenceExponent i) =
      Polynomial.X ^ (2 * 4 ^ ((N : ℕ) + 1)) := by
  have hjs : (i : ℕ) ≤ (N : ℕ) := by exact_mod_cast hi
  rw [map_pow]
  simp only [targetEvaluationPolynomialMap, targetX, MvPolynomial.eval₂Hom_X',
    targetEvaluationXExponent, nilpotenceExponent]
  rw [← pow_mul]
  congr 1
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_succ_of_le hjs)]

private lemma targetEvaluation_map_relation (k : Type u) [Field k] (N i : ℕ+)
    (hi : i ≤ N) :
    targetEvaluationPolynomialMap k N
        (targetY k i - targetX k (i + 1) * targetY k (i + 1) ^ 2) = 0 := by
  rw [map_sub, map_mul, map_pow]
  simp only [targetEvaluationPolynomialMap, targetY, targetX,
    MvPolynomial.eval₂Hom_X']
  rw [← pow_mul, ← pow_add]
  rw [show targetEvaluationYExponent N i =
      targetEvaluationXExponent N (i + 1) +
        targetEvaluationYExponent N (i + 1) * 2 by
    rw [targetEvaluationYExponent_relation N i hi]
    ring]
  exact sub_self _

private lemma targetEvaluation_map_generator_mem (k : Type u) [Field k] (N : ℕ+)
    {p : targetPolynomialRing k}
    (hp : ∃ i : ℕ+, i ≤ N ∧
      (p = targetX k i ^ nilpotenceExponent i ∨
        p = targetY k i - targetX k (i + 1) * targetY k (i + 1) ^ 2)) :
    targetEvaluationPolynomialMap k N p ∈
      Ideal.span ({Polynomial.X ^ (2 * 4 ^ ((N : ℕ) + 1))} : Set (Polynomial k)) := by
  rcases hp with ⟨i, hi, rfl | rfl⟩
  · rw [targetEvaluation_map_x_power k N i hi]
    exact Ideal.subset_span (by simp)
  · rw [targetEvaluation_map_relation k N i hi]
    exact (Ideal.span ({Polynomial.X ^ (2 * 4 ^ ((N : ℕ) + 1))} : Set (Polynomial k))).zero_mem

private lemma exists_target_relation_index_bound (k : Type u) [Field k]
    {T : Finset (targetPolynomialRing k)}
    (hT : (↑T : Set (targetPolynomialRing k)) ⊆ targetRelationGenerators k) :
    ∃ N : ℕ+, ∀ p ∈ T, ∃ i : ℕ+, i ≤ N ∧
      (p = targetX k i ^ nilpotenceExponent i ∨
        p = targetY k i - targetX k (i + 1) * targetY k (i + 1) ^ 2) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      simp
  | @insert p T hp ih =>
      have hpgen : p ∈ targetRelationGenerators k := hT (by simp)
      have hTgen : (↑T : Set (targetPolynomialRing k)) ⊆ targetRelationGenerators k :=
        fun q hq => hT (by simp [hq])
      obtain ⟨N, hN⟩ := ih hTgen
      change p ∈
        Set.range (fun i : ℕ+ => targetX k i ^ nilpotenceExponent i) ∪
          Set.range (fun i : ℕ+ =>
            targetY k i - targetX k (i + 1) * targetY k (i + 1) ^ 2) at hpgen
      rcases hpgen with hpgen | hpgen
      · rcases hpgen with ⟨j, hj⟩
        refine ⟨max N j, ?_⟩
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact ⟨j, le_max_right _ _, Or.inl hj.symm⟩
        · obtain ⟨l, hlN, hlp⟩ := hN q hq
          exact ⟨l, le_trans hlN (le_max_left _ _), hlp⟩
      · rcases hpgen with ⟨j, hj⟩
        refine ⟨max N j, ?_⟩
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact ⟨j, le_max_right _ _, Or.inr hj.symm⟩
        · obtain ⟨l, hlN, hlp⟩ := hN q hq
          exact ⟨l, le_trans hlN (le_max_left _ _), hlp⟩

/-- The first target `y` is nonzero, as in the source (the coefficient
computation proving this is omitted there). -/
theorem target_y_one_ne_zero (k : Type u) [Field k] :
    targetYElement k 1 ≠ 0 := by
  intro hzero
  have hp : targetY k 1 ∈ Ideal.span (targetRelationGenerators k) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  obtain ⟨T, hT, hmem⟩ :=
    Submodule.mem_span_finite_of_mem_span hp
  obtain ⟨N, hN⟩ := exists_target_relation_index_bound k hT
  let P : Ideal (Polynomial k) :=
    Ideal.span ({Polynomial.X ^ (2 * 4 ^ ((N : ℕ) + 1))} : Set (Polynomial k))
  let J : Ideal (targetPolynomialRing k) :=
    Ideal.comap (targetEvaluationPolynomialMap k N) P
  have hTJ : Ideal.span (↑T : Set (targetPolynomialRing k)) ≤ J := by
    refine Ideal.span_le.mpr ?_
    intro p hpT
    exact targetEvaluation_map_generator_mem k N (hN p hpT)
  change targetY k 1 ∈ Ideal.span (↑T : Set (targetPolynomialRing k)) at hmem
  have hYJ : targetY k 1 ∈ J := hTJ hmem
  have hY : targetEvaluationPolynomialMap k N (targetY k 1) ∈ P := hYJ
  change targetEvaluationPolynomialMap k N (targetY k 1) ∈
    Ideal.span ({Polynomial.X ^ (2 * 4 ^ ((N : ℕ) + 1))} : Set (Polynomial k)) at hY
  simp only [targetEvaluationPolynomialMap, targetY, MvPolynomial.eval₂Hom_X',
    targetEvaluationYExponent] at hY
  change (Polynomial.X : Polynomial k) ^ (4 ^ (N : ℕ)) ∈
    Ideal.span ({Polynomial.X ^ (2 * 4 ^ ((N : ℕ) + 1))} : Set (Polynomial k)) at hY
  rw [Ideal.mem_span_singleton'] at hY
  obtain ⟨q, hq⟩ := hY
  have hdiv : (Polynomial.X : Polynomial k) ^ (2 * 4 ^ ((N : ℕ) + 1)) ∣
      (Polynomial.X : Polynomial k) ^ (4 ^ (N : ℕ)) := by
    exact ⟨q, by simpa [mul_comm] using hq.symm⟩
  have hlt : 4 ^ (N : ℕ) < 2 * 4 ^ ((N : ℕ) + 1) := by
    have h : 4 ^ (N : ℕ) < 8 * 4 ^ (N : ℕ) :=
      lt_mul_of_one_lt_left (pow_pos (by decide : 0 < (4 : ℕ)) (N : ℕ))
        (by decide : 1 < (8 : ℕ))
    rw [pow_succ]
    convert h using 1 <;> ring
  exact Polynomial.not_dvd_of_natDegree_lt (by simp) (by simpa using hlt) hdiv

/-- The degree assigned to a source variable: `deg(xᵢ) = -1` and
`deg(zᵢ) = 0`. -/
def sourceVariableDegree : sourceVariable → ℤ
  | .inl _ => -1
  | .inr _ => 0

/-- The degree assigned to a target variable: `deg(xᵢ) = -1` and
`deg(yᵢ) = 1`. -/
def targetVariableDegree : targetVariable → ℤ
  | .inl _ => -1
  | .inr _ => 1

theorem source_degree_assignment (i : ℕ+) :
    sourceVariableDegree (.inl i) = targetVariableDegree (.inl i) ∧
      sourceVariableDegree (.inr i) =
        targetVariableDegree (.inl i) + targetVariableDegree (.inr i) := by
  simp [sourceVariableDegree, targetVariableDegree]

/-- The target `y₁` is not in the image; the source uses the displayed
`ℤ`-grading to see this. -/
theorem target_y_one_not_mem_range (k : Type u) [Field k] :
    targetYElement k 1 ∉ Set.range (sourceToTarget k) := by
  let nonpositive : LaurentPolynomial (targetRing k) → Prop :=
    fun f => ∀ n ∈ f.coeff.support, n ≤ 0
  have nonpositive_add : ∀ f g, nonpositive f → nonpositive g →
      nonpositive (f + g) := by
    intro f g hf hg n hn
    rcases Finset.mem_union.mp (Finsupp.support_add hn) with hn | hn
    · exact hf n hn
    · exact hg n hn
  have nonpositive_mul : ∀ f g, nonpositive f → nonpositive g →
      nonpositive (f * g) := by
    intro f g hf hg n hn
    rcases Finset.mem_add.1
      (AddMonoidAlgebra.support_coeff_mul_subset f g hn) with ⟨a, ha, b, hb, rfl⟩
    exact add_nonpos (hf a ha) (hg b hb)
  have nonpositive_single (n : ℤ) (hn : n ≤ 0) (r : targetRing k) :
      nonpositive (AddMonoidAlgebra.single n r) := by
    intro m hm
    have hm' : m ∈ ({n} : Finset ℤ) :=
      Finsupp.support_single_subset hm
    exact Finset.mem_singleton.mp hm' ▸ hn
  let coeffMap : k →+* LaurentPolynomial (targetRing k) :=
    (LaurentPolynomial.C : targetRing k →+*
      LaurentPolynomial (targetRing k)).comp
      ((Ideal.Quotient.mk (targetRelationIdeal k)).comp
        (MvPolynomial.C : k →+* targetPolynomialRing k))
  let targetEval : targetPolynomialRing k →+* LaurentPolynomial (targetRing k) :=
    MvPolynomial.eval₂Hom coeffMap (fun v : targetVariable =>
      match v with
      | Sum.inl i => AddMonoidAlgebra.single (-1) (targetXElement k i)
      | Sum.inr i => AddMonoidAlgebra.single 1 (targetYElement k i))
  have targetEval_X (i : ℕ+) :
      targetEval (targetX k i) =
        AddMonoidAlgebra.single (-1) (targetXElement k i) := by
    simp [targetEval, targetX]
  have targetEval_Y (i : ℕ+) :
      targetEval (targetY k i) =
        AddMonoidAlgebra.single 1 (targetYElement k i) := by
    simp [targetEval, targetY]
  have targetEval_x_power (i : ℕ+) :
      targetEval (targetX k i ^ nilpotenceExponent i) = 0 := by
    rw [map_pow, targetEval_X, AddMonoidAlgebra.single_pow]
    simp [target_x_power_eq_zero]
  have targetEval_relation (i : ℕ+) :
      targetEval (targetY k i - targetX k (i + 1) *
        targetY k (i + 1) ^ 2) = 0 := by
    rw [map_sub, map_mul, map_pow, targetEval_Y, targetEval_X, targetEval_Y]
    rw [target_y_relation, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single]
    have hdeg : (-1 : ℤ) + 2 • 1 = 1 := by decide
    rw [hdeg]
    exact sub_self _
  have htarget_kernel : targetRelationIdeal k ≤ RingHom.ker targetEval := by
    change Ideal.span (targetRelationGenerators k) ≤ RingHom.ker targetEval
    refine Ideal.span_le.mpr ?_
    intro p hp
    change p ∈
        (Set.range (fun i : ℕ+ => targetX k i ^ nilpotenceExponent i) ∪
          Set.range (fun i : ℕ+ =>
            targetY k i - targetX k (i + 1) * targetY k (i + 1) ^ 2)) at hp
    change targetEval p = 0
    rcases hp with hp | hp
    · rcases hp with ⟨i, rfl⟩
      exact targetEval_x_power i
    · rcases hp with ⟨i, rfl⟩
      exact targetEval_relation i
  let targetLift : targetRing k →+* LaurentPolynomial (targetRing k) :=
    Ideal.Quotient.lift (targetRelationIdeal k) targetEval htarget_kernel
  have targetLift_X (i : ℕ+) :
      targetLift (targetXElement k i) =
        AddMonoidAlgebra.single (-1) (targetXElement k i) := by
    simp [targetLift, targetXElement, targetX, targetEval]
  have targetLift_Y (i : ℕ+) :
      targetLift (targetYElement k i) =
        AddMonoidAlgebra.single 1 (targetYElement k i) := by
    simp [targetLift, targetYElement, targetY, targetEval]
  let sourceEval : sourceRing k →+* LaurentPolynomial (targetRing k) :=
    targetLift.comp (sourceToTarget k)
  let sourcePolyEval : sourcePolynomialRing k →+*
      LaurentPolynomial (targetRing k) :=
    targetEval.comp (sourcePolynomialMap k)
  have sourcePolyEval_X (i : ℕ+) :
      nonpositive (sourcePolyEval (sourceX k i)) := by
    change nonpositive (targetEval (sourcePolynomialMap k (sourceX k i)))
    rw [sourcePolynomialMap_x, targetEval_X]
    exact nonpositive_single (-1) (by decide) _
  have sourcePolyEval_Z (i : ℕ+) :
      nonpositive (sourcePolyEval (sourceZ k i)) := by
    change nonpositive (targetEval (sourcePolynomialMap k (sourceZ k i)))
    rw [sourcePolynomialMap_z, map_mul, targetEval_X, targetEval_Y,
      AddMonoidAlgebra.single_mul_single]
    have hdeg : (-1 : ℤ) + 1 = 0 := by decide
    rw [hdeg]
    exact nonpositive_single 0 (by decide) _
  have sourcePolyEval_C (r : k) :
      nonpositive (sourcePolyEval (MvPolynomial.C r)) := by
    have hc :
        sourcePolyEval (MvPolynomial.C r) =
          AddMonoidAlgebra.single 0 (algebraMap k (targetRing k) r) := by
      simp [sourcePolyEval, sourcePolynomialMap, targetEval, coeffMap]
      congr 1
    rw [hc]
    exact nonpositive_single 0 (by decide) _
  have sourcePolyEval_nonpositive :
      ∀ p : sourcePolynomialRing k, nonpositive (sourcePolyEval p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
        exact sourcePolyEval_C r
    | add p q hp hq =>
        rw [map_add]
        exact nonpositive_add _ _ hp hq
    | mul_X p v hp =>
        rw [map_mul]
        cases v with
        | inl i => exact nonpositive_mul _ _ hp (sourcePolyEval_X i)
        | inr i => exact nonpositive_mul _ _ hp (sourcePolyEval_Z i)
  have sourceEval_mk (p : sourcePolynomialRing k) :
      sourceEval (Ideal.Quotient.mk (sourceRelationIdeal k) p) =
        sourcePolyEval p := by
    change targetEval (sourcePolynomialMap k p) =
      targetEval (sourcePolynomialMap k p)
    rfl
  intro h
  obtain ⟨a, ha⟩ := h
  have hnon : nonpositive (sourceEval a) := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [sourceEval_mk]
    exact sourcePolyEval_nonpositive p
  change nonpositive (targetLift (sourceToTarget k a)) at hnon
  rw [ha, targetLift_Y] at hnon
  have hmem :
      (1 : ℤ) ∈
        (AddMonoidAlgebra.single 1 (targetYElement k 1)).coeff.support := by
    change (1 : ℤ) ∈
      (Finsupp.single (1 : ℤ) (targetYElement k 1)).support
    rw [Finsupp.mem_support_iff]
    simpa only [Finsupp.single_eq_same] using target_y_one_ne_zero k
  have hle : (1 : ℤ) ≤ 0 := hnon 1 hmem
  have hnot : ¬ ((1 : ℤ) ≤ 0) := by decide
  exact hnot hle

/-- The quotient map in the example is not surjective. -/
theorem sourceToTarget_not_surjective (k : Type u) [Field k] :
    ¬ Function.Surjective (sourceToTarget k) := by
  intro h
  rcases h (targetYElement k 1) with ⟨a, ha⟩
  exact target_y_one_not_mem_range k ⟨a, ha⟩

/-! ## The tensor identities proving epimorphy -/

/- The `A`-algebra structure on the target induced by the displayed map. -/
@[instance_reducible]
def sourceTargetAlgebra (k : Type u) [Field k] : Algebra (sourceRing k) (targetRing k) :=
  RingHom.toAlgebra (sourceToTarget k)

/-- Register the displayed map as the algebra map used by the tensor product. -/
noncomputable instance sourceTargetAlgebra_inst (k : Type u) [Field k] :
    Algebra (sourceRing k) (targetRing k) :=
  sourceTargetAlgebra k

/-- The tensor product `B ⊗ₐ B`, where `A` acts on `B` through the example map. -/
abbrev sourceTargetTensorProduct (k : Type u) [Field k] :=
  targetRing k ⊗[sourceRing k] targetRing k

/-- A convenient name for a pure tensor in the tensor product above. -/
def sourceTargetTensor (k : Type u) [Field k] (a b : targetRing k) :
    sourceTargetTensorProduct k :=
  a ⊗ₜ[sourceRing k] b

theorem source_tensor_identity_first (k : Type u) [Field k] (i : ℕ+) :
    sourceTargetTensor k (targetYElement k i) 1 =
      sourceTargetTensor k
        (targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2) 1 := by
  rw [target_y_relation]

theorem source_tensor_identity_middle_left (k : Type u) [Field k] (i : ℕ+) :
    sourceTargetTensor k
        (targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2) 1 =
      sourceTargetTensor k (targetYElement k (i + 1))
        (targetXElement k (i + 1) * targetYElement k (i + 1)) := by
  have hz : algebraMap (sourceRing k) (targetRing k) (sourceZElement k (i + 1)) =
      targetXElement k (i + 1) * targetYElement k (i + 1) := by
    change sourceToTarget k (sourceZElement k (i + 1)) = _
    exact sourceToTarget_z k (i + 1)
  simpa [sourceTargetTensor, Algebra.smul_def, hz, pow_two, mul_assoc, mul_comm,
    mul_left_comm] using
    (TensorProduct.smul_tmul (R := sourceRing k) (R' := sourceRing k)
      (M := targetRing k) (N := targetRing k) (sourceZElement k (i + 1))
      (targetYElement k (i + 1)) (1 : targetRing k))

theorem source_tensor_identity_middle_right (k : Type u) [Field k] (i : ℕ+) :
    sourceTargetTensor k (targetYElement k (i + 1))
        (targetXElement k (i + 1) * targetYElement k (i + 1)) =
      sourceTargetTensor k
        (targetXElement k (i + 1) * targetYElement k (i + 1))
        (targetYElement k (i + 1)) := by
  have hx : algebraMap (sourceRing k) (targetRing k) (sourceXElement k (i + 1)) =
      targetXElement k (i + 1) := by
    change sourceToTarget k (sourceXElement k (i + 1)) = _
    exact sourceToTarget_x k (i + 1)
  simpa [sourceTargetTensor, Algebra.smul_def, hx, mul_assoc, mul_comm,
    mul_left_comm] using
    (TensorProduct.smul_tmul (R := sourceRing k) (R' := sourceRing k)
      (M := targetRing k) (N := targetRing k) (sourceXElement k (i + 1))
      (targetYElement k (i + 1)) (targetYElement k (i + 1))).symm

theorem source_tensor_identity_last (k : Type u) [Field k] (i : ℕ+) :
    sourceTargetTensor k
        (targetXElement k (i + 1) * targetYElement k (i + 1))
        (targetYElement k (i + 1)) =
      sourceTargetTensor k 1
        (targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2) := by
  have hz : algebraMap (sourceRing k) (targetRing k) (sourceZElement k (i + 1)) =
      targetXElement k (i + 1) * targetYElement k (i + 1) := by
    change sourceToTarget k (sourceZElement k (i + 1)) = _
    exact sourceToTarget_z k (i + 1)
  simpa [sourceTargetTensor, Algebra.smul_def, hz, pow_two, mul_assoc, mul_comm,
    mul_left_comm] using
    (TensorProduct.smul_tmul (R := sourceRing k) (R' := sourceRing k)
      (M := targetRing k) (N := targetRing k) (sourceZElement k (i + 1))
      (1 : targetRing k) (targetYElement k (i + 1)))

/-- The complete tensor identity displayed in the source. -/
theorem source_tensor_identity (k : Type u) [Field k] (i : ℕ+) :
    sourceTargetTensor k (targetYElement k i) 1 =
      sourceTargetTensor k 1
        (targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2) := by
  calc
    sourceTargetTensor k (targetYElement k i) 1 =
        sourceTargetTensor k
          (targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2) 1 :=
      source_tensor_identity_first k i
    _ = sourceTargetTensor k (targetYElement k (i + 1))
        (targetXElement k (i + 1) * targetYElement k (i + 1)) :=
      source_tensor_identity_middle_left k i
    _ = sourceTargetTensor k
        (targetXElement k (i + 1) * targetYElement k (i + 1))
        (targetYElement k (i + 1)) :=
      source_tensor_identity_middle_right k i
    _ = sourceTargetTensor k 1
        (targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2) :=
      source_tensor_identity_last k i

/-- The tensor identities yield the algebraic epimorphism property. -/
theorem sourceToTarget_isAlgebraEpi (k : Type u) [Field k] :
    Algebra.IsEpi (sourceRing k) (targetRing k) := by
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hvar : ∀ v : targetVariable,
      (1 : targetRing k) ⊗ₜ[sourceRing k]
          Ideal.Quotient.mk (targetRelationIdeal k) (MvPolynomial.X v) =
        Ideal.Quotient.mk (targetRelationIdeal k) (MvPolynomial.X v) ⊗ₜ[sourceRing k]
          (1 : targetRing k) := by
    intro v
    rcases v with i | i
    · have hx : algebraMap (sourceRing k) (targetRing k) (sourceXElement k i) =
          Ideal.Quotient.mk (targetRelationIdeal k) (MvPolynomial.X (.inl i)) := by
        change sourceToTarget k (sourceXElement k i) = _
        exact sourceToTarget_x k i
      rw [← hx]
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := sourceRing k) (A := targetRing k) (B := targetRing k)
        (sourceXElement k i)).symm
    · calc
        (1 : targetRing k) ⊗ₜ[sourceRing k] targetYElement k i =
            (1 : targetRing k) ⊗ₜ[sourceRing k]
              (targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2) := by
                rw [target_y_relation k i]
        _ = targetYElement k i ⊗ₜ[sourceRing k] (1 : targetRing k) :=
          (source_tensor_identity k i).symm
  have hmul : ∀ a b : targetRing k,
      ((1 : targetRing k) ⊗ₜ[sourceRing k] a = a ⊗ₜ[sourceRing k] (1 : targetRing k)) →
      ((1 : targetRing k) ⊗ₜ[sourceRing k] b = b ⊗ₜ[sourceRing k] (1 : targetRing k)) →
      (1 : targetRing k) ⊗ₜ[sourceRing k] (a * b) =
        (a * b) ⊗ₜ[sourceRing k] (1 : targetRing k) := by
    intro a b ha hb
    calc
      (1 : targetRing k) ⊗ₜ[sourceRing k] (a * b) =
          ((1 : targetRing k) ⊗ₜ[sourceRing k] a) *
            ((1 : targetRing k) ⊗ₜ[sourceRing k] b) := by
              simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      _ = (a ⊗ₜ[sourceRing k] (1 : targetRing k)) *
            (b ⊗ₜ[sourceRing k] (1 : targetRing k)) := by rw [ha, hb]
      _ = (a * b) ⊗ₜ[sourceRing k] (1 : targetRing k) := by
              simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  induction p using MvPolynomial.induction_on with
  | C r =>
      have hs := Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := sourceRing k) (A := targetRing k) (B := targetRing k)
        (Ideal.Quotient.mk (sourceRelationIdeal k) (MvPolynomial.C r))
      have hc : algebraMap (sourceRing k) (targetRing k)
            (Ideal.Quotient.mk (sourceRelationIdeal k) (MvPolynomial.C r)) =
          Ideal.Quotient.mk (targetRelationIdeal k) (MvPolynomial.C r) := by
        change sourceToTarget k
            (Ideal.Quotient.mk (sourceRelationIdeal k) (MvPolynomial.C r)) = _
        simp [sourceToTarget, sourcePolynomialMapToTarget, sourcePolynomialMap]
      rw [← hc]
      exact hs.symm
  | add p q hp hq =>
      simp only [map_add, TensorProduct.tmul_add, TensorProduct.add_tmul]
      rw [hp, hq]
  | mul_X p v hp =>
      exact hmul _ _ hp (hvar v)

/-- Multiplication is the canonical map from the tensor product to the target. -/
noncomputable def sourceTargetTensorMultiplication (k : Type u) [Field k] :
    sourceTargetTensorProduct k →ₐ[sourceRing k] targetRing k :=
  Algebra.TensorProduct.lmul' (sourceRing k)

/-- The tensor product of the target over the source is isomorphic to the
target, as used in the source's epimorphism argument. -/
theorem sourceTargetTensorProduct_isomorphic_to_target (k : Type u) [Field k] :
    Nonempty (sourceTargetTensorProduct k ≃ₐ[sourceRing k] targetRing k) := by
  refine ⟨AlgEquiv.ofBijective (sourceTargetTensorMultiplication k) ?_⟩
  constructor
  · exact (sourceToTarget_isAlgebraEpi k).injective_lift_mul
  · intro b
    exact ⟨1 ⊗ₜ[sourceRing k] b, by simp [sourceTargetTensorMultiplication]⟩

/-- The displayed ring map is an epimorphism in `CommRingCat`. -/
theorem sourceToTarget_is_epi (k : Type u) [Field k] :
    Epi (CommRingCat.ofHom (sourceToTarget k)) := by
  exact CommRingCat.epi_iff_epi.mpr (sourceToTarget_isAlgebraEpi k)

/-! ## Local zero-dimensional conclusion -/

private lemma polynomial_sub_constant_mem_nilradical
    {k Q σ : Type*} [Field k] [CommRing Q] [Algebra k Q]
    (f : MvPolynomial σ k →+* Q)
    (hf : f.comp (MvPolynomial.C : k →+* MvPolynomial σ k) = algebraMap k Q)
    (hX : ∀ v : σ, IsNilpotent (f (MvPolynomial.X v))) :
    ∀ p : MvPolynomial σ k,
      f p - algebraMap k Q (MvPolynomial.constantCoeff p) ∈ nilradical Q := by
  have hC (r : k) : f (MvPolynomial.C r) = algebraMap k Q r := by
    exact RingHom.congr_fun hf r
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp [hC]
  | add p q hp hq =>
      rw [map_add, map_add]
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (nilradical Q).add_mem hp hq
  | mul_X p v hp =>
      rw [map_mul, map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero,
        sub_zero]
      exact (nilradical Q).mul_mem_left _ (mem_nilradical.mpr (hX v))

private lemma local_zero_dimensional_of_polynomial_quotient
    {k Q σ : Type*} [Field k] [CommRing Q] [Algebra k Q]
    [Nontrivial Q] (f : MvPolynomial σ k →+* Q)
    (hf : f.comp (MvPolynomial.C : k →+* MvPolynomial σ k) = algebraMap k Q)
    (hX : ∀ v : σ, IsNilpotent (f (MvPolynomial.X v)))
    (hsurj : Function.Surjective f) :
    IsLocalRing Q ∧ ringKrullDim Q = 0 := by
  have hnil : ∀ x : Q, ¬ IsUnit x → IsNilpotent x := by
    intro x hx
    obtain ⟨p, rfl⟩ := hsurj x
    by_cases hc : MvPolynomial.constantCoeff p = 0
    · have hp := polynomial_sub_constant_mem_nilradical f hf hX p
      rw [hc, map_zero, sub_zero] at hp
      exact mem_nilradical.mp hp
    · have hp := polynomial_sub_constant_mem_nilradical f hf hX p
      have hu : IsUnit (algebraMap k Q (MvPolynomial.constantCoeff p)) :=
        (isUnit_iff_ne_zero.mpr hc).map (algebraMap k Q)
      have hu' : IsUnit (f p) := by
        have hnil' : IsNilpotent
            (f p - algebraMap k Q (MvPolynomial.constantCoeff p)) :=
          mem_nilradical.mp hp
        have := hnil'.isUnit_add_right_of_commute hu (Commute.all _ _)
        simpa [sub_add_cancel] using this
      exact (hx hu').elim
  have hlocal : IsLocalRing Q := by
    apply IsLocalRing.of_nonunits_add
    intro a b ha hb hab
    exact ((Commute.all _ _).isNilpotent_add (hnil a ha) (hnil b hb)).not_isUnit hab
  have hnil_iff : ∀ x : Q, IsNilpotent x ↔ ¬ IsUnit x := by
    intro x
    exact ⟨fun hx => hx.not_isUnit, hnil x⟩
  have hmax : (nilradical Q).IsMaximal :=
    ((Ring.krullDimLE_zero_and_isLocalRing_tfae Q).out 2 3 rfl rfl).mp hnil_iff
  let _ : (nilradical Q).IsMaximal := hmax
  have hdimLE : Ring.KrullDimLE 0 Q := Ring.KrullDimLE.of_isMaximal_nilradical Q
  exact ⟨hlocal, (ringKrullDimZero_iff_ringKrullDim_eq_zero).mp hdimLE⟩

/-- The source quotient is a local ring of Krull dimension zero. -/
theorem sourceRing_is_local_zero_dimensional (k : Type u) [Field k] :
    IsLocalRing (sourceRing k) ∧ ringKrullDim (sourceRing k) = 0 := by
  let _ : Nontrivial (targetRing k) :=
    ⟨⟨targetYElement k 1, 0, target_y_one_ne_zero k⟩⟩
  let _ : Nontrivial (sourceRing k) := (sourceToTarget k).domain_nontrivial
  apply local_zero_dimensional_of_polynomial_quotient
    (Q := sourceRing k) (σ := sourceVariable)
    (Ideal.Quotient.mk (sourceRelationIdeal k))
  · ext r
    rfl
  · intro v
    rcases v with i | i
    · refine ⟨nilpotenceExponent i, ?_⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa [sourceXElement, sourceX, sourceRelationIdeal] using
        (Ideal.subset_span (Or.inl (Set.mem_range_self i)) :
          sourceX k i ^ nilpotenceExponent i ∈ sourceRelationIdeal k)
    · refine ⟨nilpotenceExponent i, ?_⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa [sourceZElement, sourceZ, sourceRelationIdeal] using
        (Ideal.subset_span (Or.inr (Set.mem_range_self i)) :
          sourceZ k i ^ nilpotenceExponent i ∈ sourceRelationIdeal k)
  · exact Ideal.Quotient.mk_surjective

/-- The target quotient is a local ring of Krull dimension zero. -/
theorem targetRing_is_local_zero_dimensional (k : Type u) [Field k] :
    IsLocalRing (targetRing k) ∧ ringKrullDim (targetRing k) = 0 := by
  let _ : Nontrivial (targetRing k) :=
    ⟨⟨targetYElement k 1, 0, target_y_one_ne_zero k⟩⟩
  apply local_zero_dimensional_of_polynomial_quotient
    (Q := targetRing k) (σ := targetVariable)
    (Ideal.Quotient.mk (targetRelationIdeal k))
  · ext r
    rfl
  · intro v
    rcases v with i | i
    · exact ⟨nilpotenceExponent i, target_x_power_eq_zero k i⟩
    · exact ⟨nilpotenceExponent (i + 1), target_y_power_eq_zero k i⟩
  · exact Ideal.Quotient.mk_surjective

/-- The chapter's example: an epimorphism of local zero-dimensional rings
which is not a surjection. -/
theorem chapter36_epimorphism_of_local_zero_dimensional_rings_not_surjective
    (k : Type u) [Field k] :
    IsLocalRing (sourceRing k) ∧ IsLocalRing (targetRing k) ∧
      ringKrullDim (sourceRing k) = 0 ∧ ringKrullDim (targetRing k) = 0 ∧
      Epi (CommRingCat.ofHom (sourceToTarget k)) ∧
        ¬ Function.Surjective (sourceToTarget k) := by
  rcases sourceRing_is_local_zero_dimensional k with ⟨hsourceLocal, hsourceDim⟩
  rcases targetRing_is_local_zero_dimensional k with ⟨htargetLocal, htargetDim⟩
  exact ⟨hsourceLocal, htargetLocal, hsourceDim, htargetDim,
    sourceToTarget_is_epi k, sourceToTarget_not_surjective k⟩

/-- The final existential statement in the source, instantiated at `ℚ`. -/
theorem exists_epimorphism_of_local_zero_dimensional_rings_not_surjective :
    ∃ f : sourceRing ℚ →+* targetRing ℚ,
      IsLocalRing (sourceRing ℚ) ∧ IsLocalRing (targetRing ℚ) ∧
        ringKrullDim (sourceRing ℚ) = 0 ∧ ringKrullDim (targetRing ℚ) = 0 ∧
        Epi (CommRingCat.ofHom f) ∧ ¬ Function.Surjective f := by
  refine ⟨sourceToTarget ℚ, ?_⟩
  exact chapter36_epimorphism_of_local_zero_dimensional_rings_not_surjective ℚ

end Formalization.Books.Examples.Unit36
