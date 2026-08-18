import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.PNat.Notation
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

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
  sorry

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
  sorry

theorem source_tensor_identity_last (k : Type u) [Field k] (i : ℕ+) :
    sourceTargetTensor k
        (targetXElement k (i + 1) * targetYElement k (i + 1))
        (targetYElement k (i + 1)) =
      sourceTargetTensor k 1
        (targetXElement k (i + 1) * targetYElement k (i + 1) ^ 2) := by
  sorry

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
  sorry

/-- Multiplication is the canonical map from the tensor product to the target. -/
noncomputable def sourceTargetTensorMultiplication (k : Type u) [Field k] :
    sourceTargetTensorProduct k →ₐ[sourceRing k] targetRing k :=
  Algebra.TensorProduct.lmul' (sourceRing k)

/-- The tensor product of the target over the source is isomorphic to the
target, as used in the source's epimorphism argument. -/
theorem sourceTargetTensorProduct_isomorphic_to_target (k : Type u) [Field k] :
    Nonempty (sourceTargetTensorProduct k ≃ₐ[sourceRing k] targetRing k) := by
  sorry

/-- The displayed ring map is an epimorphism in `CommRingCat`. -/
theorem sourceToTarget_is_epi (k : Type u) [Field k] :
    Epi (CommRingCat.ofHom (sourceToTarget k)) := by
  exact CommRingCat.epi_iff_epi.mpr (sourceToTarget_isAlgebraEpi k)

/-! ## Local zero-dimensional conclusion -/

/-- The source quotient is a local ring of Krull dimension zero. -/
theorem sourceRing_is_local_zero_dimensional (k : Type u) [Field k] :
    IsLocalRing (sourceRing k) ∧ ringKrullDim (sourceRing k) = 0 := by
  sorry

/-- The target quotient is a local ring of Krull dimension zero. -/
theorem targetRing_is_local_zero_dimensional (k : Type u) [Field k] :
    IsLocalRing (targetRing k) ∧ ringKrullDim (targetRing k) = 0 := by
  sorry

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
