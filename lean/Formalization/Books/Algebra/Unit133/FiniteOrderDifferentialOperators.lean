import Formalization.Books.Algebra.Unit132.DeRhamComplex

set_option genSizeOf false
set_option linter.all false

/-!
# Commutative Algebra, Chapter 133: Finite order differential operators

The source's `Diff^k_{S/R}(M, N)` is represented by the submodule of
`R`-linear maps whose iterated commutators with multiplication by elements of
`S` have the prescribed order.  The module of principal parts is represented
by the quotient of the free `S`-module on `M` by the source's generators and
relations.  Statements whose proof is the substantial mathematical content of
the chapter are intentionally left as theorem interfaces at this stage.
-/

namespace Formalization.Books.Algebra.Unit133

open scoped TensorProduct
open Formalization.Books.Algebra.Unit131
open Formalization.Books.Algebra.Unit132

attribute [local instance] SMulCommClass.of_commMonoid

noncomputable section

universe u v w u' v' w'

private abbrev LinearMapOver
    (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] := M →ₗ[R] N

/-! ## Differential operators and their filtration -/

section DifferentialOperators

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module S N] [Module R M] [Module R N]
  [IsScalarTower R S M] [IsScalarTower R S N]

/- The commutator with multiplication by `s`. -/
def differentialOperatorCommutator (D : LinearMapOver R M N) (s : S) : LinearMapOver R M N :=
  D.comp (DistribSMul.toLinearMap R M s) -
    (DistribSMul.toLinearMap R N s).comp D

/- The source's inductive predicate, with the order-zero clause made
   explicit instead of referring to `k - 1`. -/
def IsDifferentialOperator
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N] :
    ℕ → (LinearMapOver R M N) → Prop
  | 0, D => ∀ (s : S) (m : M), D (s • m) = s • D m
  | k + 1, D => ∀ (s : S),
      IsDifferentialOperator (R := R) (S := S) (M := M) (N := N) k
        (differentialOperatorCommutator D s)

theorem isDifferentialOperator_zero (k : ℕ) :
    IsDifferentialOperator (R := R) (S := S) k (0 : LinearMapOver R M N) := by
  induction k with
  | zero =>
      intro s m
      simp
  | succ k ih =>
      intro s
      simpa [differentialOperatorCommutator] using ih

theorem isDifferentialOperator_add (k : ℕ) (D E : LinearMapOver R M N)
    (hD : IsDifferentialOperator (R := R) (S := S) k D)
    (hE : IsDifferentialOperator (R := R) (S := S) k E) :
    IsDifferentialOperator (R := R) (S := S) k (D + E) := by
  revert D E
  induction k with
  | zero =>
      intro D E hD hE s m
      simp only [LinearMap.add_apply, hD s m, hE s m, smul_add]
  | succ k ih =>
      intro D E hD hE s
      have hcomm :
          differentialOperatorCommutator (D + E) s =
            differentialOperatorCommutator D s + differentialOperatorCommutator E s := by
        ext m
        simp [differentialOperatorCommutator, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      rw [hcomm]
      exact ih _ _ (hD s) (hE s)

theorem isDifferentialOperator_smul (k : ℕ) (c : S) (D : LinearMapOver R M N)
    (hD : IsDifferentialOperator (R := R) (S := S) k D) :
    IsDifferentialOperator (R := R) (S := S) k (c • D) := by
  revert D
  induction k with
  | zero =>
      intro D hD s m
      simp [hD s m, smul_smul, mul_comm]
  | succ k ih =>
      intro D hD s
      have hcomp :
          DistribSMul.toLinearMap R N s ∘ₗ (c • D) =
            c • DistribSMul.toLinearMap R N s ∘ₗ D := by
        ext m
        simp [smul_smul, mul_comm]
      rw [show differentialOperatorCommutator (c • D) s =
        c • differentialOperatorCommutator D s by
        simp [differentialOperatorCommutator, LinearMap.smul_comp, LinearMap.comp_smul,
          smul_sub, hcomp]]
      exact ih _ (hD s)

/- The space `Diff^k_{S/R}(M, N)`, as an actual `S`-submodule. -/
def differentialOperatorSubmodule (k : ℕ) : Submodule S (LinearMapOver R M N) where
  carrier := {D | IsDifferentialOperator (R := R) (S := S) k D}
  zero_mem' := isDifferentialOperator_zero (R := R) (S := S) k
  add_mem' := by
    intro D E hD hE
    change IsDifferentialOperator (R := R) (S := S) k D at hD
    change IsDifferentialOperator (R := R) (S := S) k E at hE
    change IsDifferentialOperator (R := R) (S := S) k (D + E)
    exact isDifferentialOperator_add (R := R) (S := S) k D E hD hE
  smul_mem' := by
    intro c D hD
    change IsDifferentialOperator (R := R) (S := S) k D at hD
    change IsDifferentialOperator (R := R) (S := S) k (c • D)
    exact isDifferentialOperator_smul (R := R) (S := S) k c D hD

/-- Differential operators of order `k`, with their underlying `R`-linear map. -/
abbrev DifferentialOperator (k : ℕ) : Submodule S (LinearMapOver R M N) :=
  differentialOperatorSubmodule (R := R) (S := S) k

theorem mem_differentialOperatorSubmodule_iff (k : ℕ) (D : LinearMapOver R M N) :
    D ∈ differentialOperatorSubmodule (R := R) (S := S) k ↔
      IsDifferentialOperator (R := R) (S := S) k D :=
  Iff.rfl

theorem differentialOperatorSubmodule_mono (k : ℕ) :
    differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k ≤
      differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) (k + 1) := by
  change ∀ D, IsDifferentialOperator (R := R) (S := S) k D →
    IsDifferentialOperator (R := R) (S := S) (k + 1) D
  induction k with
  | zero =>
      intro D hD
      intro s
      have hzero :
          differentialOperatorCommutator D s = 0 := by
        ext m
        simp [differentialOperatorCommutator, hD s m]
      rw [hzero]
      exact isDifferentialOperator_zero (R := R) (S := S) (M := M) (N := N) 0
  | succ k ih =>
      intro D hD s
      exact ih _ (hD s)

theorem differentialOperatorSubmodule_zero_iff (D : LinearMapOver R M N) :
    D ∈ differentialOperatorSubmodule (R := R) (S := S) 0 ↔
      ∀ (s : S) (m : M), D (s • m) = s • D m :=
  Iff.rfl

theorem differentialOperator_subtype_coe (k : ℕ)
    (D : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k) :
    IsDifferentialOperator (R := R) (S := S) k D.1 :=
  D.2

theorem differentialOperator_comp_isDifferentialOperator
    {L : Type*} [AddCommGroup L] [Module S L] [Module R L]
    [IsScalarTower R S L]
    (k k' : ℕ) (D : LinearMapOver R M N) (D' : LinearMapOver R N L)
    (hD : IsDifferentialOperator (R := R) (S := S) k D)
    (hD' : IsDifferentialOperator (R := R) (S := S) k' D') :
    IsDifferentialOperator (R := R) (S := S) (k + k') (D'.comp D) := by
  revert k' D D' hD hD'
  induction k with
  | zero =>
      intro k'
      induction k' with
      | zero =>
          intro D D' hD hD' s m
          simp [hD s m, hD' s (D m)]
      | succ k' ih =>
          intro D D' hD hD' s
          have hcomm :
              differentialOperatorCommutator (D'.comp D) s =
                D'.comp (differentialOperatorCommutator D s) +
                  (differentialOperatorCommutator D' s).comp D := by
            ext m
            simp [differentialOperatorCommutator, sub_eq_add_neg,
              add_assoc, add_comm, add_left_comm]
          have hzero : differentialOperatorCommutator D s = 0 := by
            ext m
            simp [differentialOperatorCommutator, hD s m]
          rw [hcomm, hzero, LinearMap.comp_zero, zero_add]
          convert (ih D (differentialOperatorCommutator D' s) hD (hD' s)) using 1 <;>
            simp
  | succ k ih =>
      intro k'
      induction k' with
      | zero =>
          intro D D' hD hD' s
          have hcomm :
              differentialOperatorCommutator (D'.comp D) s =
                D'.comp (differentialOperatorCommutator D s) +
                  (differentialOperatorCommutator D' s).comp D := by
            ext m
            simp [differentialOperatorCommutator, sub_eq_add_neg,
              add_assoc, add_comm, add_left_comm]
          have hzero : differentialOperatorCommutator D' s = 0 := by
            ext m
            simp [differentialOperatorCommutator, hD' s m]
          rw [hcomm, hzero]
          simp only [LinearMap.zero_comp, add_zero]
          simpa only [Nat.add_zero] using
            (ih 0 (differentialOperatorCommutator D s) D' (hD s) hD')
      | succ k' ih' =>
          intro D D' hD hD' s
          have hcomm :
              differentialOperatorCommutator (D'.comp D) s =
                D'.comp (differentialOperatorCommutator D s) +
                  (differentialOperatorCommutator D' s).comp D := by
            ext m
            simp [differentialOperatorCommutator, sub_eq_add_neg,
              add_assoc, add_comm, add_left_comm]
          rw [hcomm]
          apply isDifferentialOperator_add (R := R) (S := S) ((k + 1) + k')
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (ih (k' + 1) (differentialOperatorCommutator D s) D'
                (hD s) hD')
          · exact ih' D (differentialOperatorCommutator D' s) hD (hD' s)

theorem differentialOperator_postcompose_isDifferentialOperator
    {N' : Type*} [AddCommGroup N'] [Module S N'] [Module R N']
    [IsScalarTower R S N'] (k : ℕ) (D : LinearMapOver R M N)
    (f : LinearMapOver S N N')
    (hD : IsDifferentialOperator (R := R) (S := S) k D) :
    IsDifferentialOperator (R := R) (S := S) k
      ((f.restrictScalars R).comp D) := by
  revert D hD
  induction k with
  | zero =>
      intro D hD
      intro s m
      simp [hD s m]
  | succ k ih =>
      intro D hD
      intro s
      have hcomm :
          differentialOperatorCommutator ((f.restrictScalars R).comp D) s =
            (f.restrictScalars R).comp (differentialOperatorCommutator D s) := by
        ext m
        simp [differentialOperatorCommutator]
      rw [hcomm]
      exact ih (differentialOperatorCommutator D s) (hD s)

/- Bundled versions of the two operations used repeatedly below. -/
def differentialOperatorComp
    {L : Type*} [AddCommGroup L] [Module S L] [Module R L]
    [IsScalarTower R S L]
    {k k' : ℕ}
    (D' : DifferentialOperator (R := R) (S := S) (M := N) (N := L) k')
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k) :
    differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := L) (k + k') :=
  ⟨D'.1.comp D.1,
    differentialOperator_comp_isDifferentialOperator (R := R) (S := S)
      k k' D.1 D'.1 D.2 D'.2⟩

def differentialOperatorPostcompose
    {N' : Type*} [AddCommGroup N'] [Module S N'] [Module R N']
    [IsScalarTower R S N'] {k : ℕ}
    (f : LinearMapOver S N N')
    (D : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k) :
    differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N') k :=
  ⟨(f.restrictScalars R).comp D.1,
    differentialOperator_postcompose_isDifferentialOperator
      (R := R) (S := S) k D.1 f D.2⟩

theorem differentialOperator_comp_order_add
    {L : Type*} [AddCommGroup L] [Module S L] [Module R L]
    [IsScalarTower R S L]
    {k k' : ℕ}
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k)
    (D' : DifferentialOperator (R := R) (S := S) (M := N) (N := L) k') :
    IsDifferentialOperator (R := R) (S := S) (k + k') (D'.1.comp D.1) :=
  (differentialOperatorComp D' D).2

end DifferentialOperators

/-! ## The module of principal parts -/

section PrincipalParts

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M]

include R

def principalPartsAddRelation (m m' : M) : M →₀ S :=
  Finsupp.single (m + m') 1 - Finsupp.single m 1 - Finsupp.single m' 1

def principalPartsScalarRelation (r : R) (m : M) : M →₀ S :=
  (algebraMap R S r) • Finsupp.single m 1 - Finsupp.single (r • m) 1

def principalPartsHigherRelation (k : ℕ) (g : Fin (k + 1) → S) (m : M) : M →₀ S := by
  classical
  exact (Finset.univ : Finset (Finset (Fin (k + 1)))).sum (fun t =>
    ((-1 : S) ^ t.card) •
      (((Finset.univ \ t).prod g) •
        Finsupp.single ((t.prod g) • m) 1))

def principalPartsRelationSet (k : ℕ) : Set (M →₀ S) :=
  Set.range (fun p : M × M => principalPartsAddRelation p.1 p.2) ∪
    Set.range (fun p : R × M => principalPartsScalarRelation p.1 p.2) ∪
    Set.range (fun p : (Fin (k + 1) → S) × M =>
      principalPartsHigherRelation k p.1 p.2)

def principalPartsRelationSubmodule (k : ℕ) : Submodule S (M →₀ S) :=
  Submodule.span S (principalPartsRelationSet (R := R) (S := S) (M := M) k)

/-- The quotient construction of the module of principal parts. -/
abbrev PrincipalParts (k : ℕ) : Type _ :=
  (M →₀ S) ⧸ principalPartsRelationSubmodule (R := R) (S := S) (M := M) k

private theorem principalPartsHigherRelation_succ_eq (k : ℕ)
    (g : Fin (k + 1 + 1) → S) (m : M) :
    principalPartsHigherRelation (k + 1) g m =
      g (Fin.last (k + 1)) •
          principalPartsHigherRelation k (fun i => g i.castSucc) m -
        principalPartsHigherRelation k (fun i => g i.castSucc)
          (g (Fin.last (k + 1)) • m) := by
  let g₀ : Fin (k + 1) → S := fun i => g i.castSucc
  let a : S := g (Fin.last (k + 1))
  let embed : Finset (Fin (k + 1)) × Bool →
      Finset (Fin (k + 1 + 1)) := fun p =>
    match p.2 with
    | false => p.1.map Fin.castSuccEmb
    | true => insert (Fin.last (k + 1)) (p.1.map Fin.castSuccEmb)
  have hembed : Function.Bijective embed := by
    constructor
    · rintro ⟨p, b⟩ ⟨q, c⟩ h
      cases b <;> cases c
      · simp only [embed] at h
        exact Prod.ext (Finset.map_injective Fin.castSuccEmb h) rfl
      · exfalso
        have hm := congrArg (fun t => Fin.last (k + 1) ∈ t) h
        simpa [embed] using hm
      · exfalso
        have hm := congrArg (fun t => Fin.last (k + 1) ∈ t) h
        simpa [embed] using hm
      · simp only [embed] at h
        apply Prod.ext
        · apply Finset.ext
          intro i
          have hi := congrArg (fun t => i.castSucc ∈ t) h
          simpa using hi
        · rfl
    · intro u
      by_cases hu : Fin.last (k + 1) ∈ u
      · let p := (u.erase (Fin.last (k + 1))).preimage
            Fin.castSucc (Fin.castSucc_injective _).injOn
        refine ⟨(p, true), ?_⟩
        apply Finset.ext
        intro i
        cases i using Fin.lastCases with
        | last => simp [embed, p, hu]
        | cast i => simp [embed, p, hu]
      · let p := u.preimage Fin.castSucc (Fin.castSucc_injective _).injOn
        refine ⟨(p, false), ?_⟩
        apply Finset.ext
        intro i
        cases i using Fin.lastCases with
        | last => simp [embed, p, hu]
        | cast i => simp [embed, p, hu]
  let F : Finset (Fin (k + 1 + 1)) → M →₀ S := fun t =>
    ((-1 : S) ^ t.card) •
      (((Finset.univ \ t).prod g) •
        Finsupp.single ((t.prod g) • m) 1)
  have hcompFalse (x : Finset (Fin (k + 1))) :
      (Finset.univ \ x.map Fin.castSuccEmb) =
        insert (Fin.last (k + 1))
          ((Finset.univ \ x).map Fin.castSuccEmb) := by
    ext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i => simp
  have hcompTrue (x : Finset (Fin (k + 1))) :
      (Finset.univ \ insert (Fin.last (k + 1)) (x.map Fin.castSuccEmb)) =
        (Finset.univ \ x).map Fin.castSuccEmb := by
    ext i
    cases i using Fin.lastCases with
    | last => simp
    | cast i => simp
  have hsum := Fintype.sum_bijective embed hembed
    (fun p => F (embed p)) F (fun _ => rfl)
  have hfalse : (∑ x : Finset (Fin (k + 1)), F (embed (x, false))) =
      a • principalPartsHigherRelation k g₀ m := by
    simp [F, embed, principalPartsHigherRelation, g₀, a, hcompFalse,
      Finset.smul_sum, Finsupp.smul_single', mul_assoc, mul_comm, mul_left_comm]
  have htrue : (∑ x : Finset (Fin (k + 1)), F (embed (x, true))) =
      -principalPartsHigherRelation k g₀ (a • m) := by
    change (∑ x : Finset (Fin (k + 1)), F (embed (x, true))) =
      -(∑ x : Finset (Fin (k + 1)), ((-1 : S) ^ x.card) •
        (((Finset.univ \ x).prod g₀) •
          Finsupp.single ((x.prod g₀) • (a • m)) 1))
    rw [← Finset.sum_neg_distrib]
    simp [F, embed, principalPartsHigherRelation, g₀, a, hcompTrue,
      Finsupp.smul_single', pow_succ', smul_smul, mul_assoc, mul_comm,
      mul_left_comm]
  have hsum' := hsum.symm
  rw [← Finset.univ_product_univ, Finset.sum_product] at hsum'
  simp_rw [Fintype.sum_bool] at hsum'
  rw [Finset.sum_add_distrib] at hsum'
  rw [htrue, hfalse] at hsum'
  simpa [F, principalPartsHigherRelation, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm, g₀, a] using hsum'

theorem principalParts_relation_succ_le (k : ℕ) :
    principalPartsRelationSubmodule (R := R) (S := S) (M := M) (k + 1) ≤
      principalPartsRelationSubmodule (R := R) (S := S) (M := M) k := by
  apply Submodule.span_le.2
  intro x hx
  rcases hx with hx | ⟨⟨g, m⟩, rfl⟩
  · rcases hx with ⟨p, rfl⟩ | ⟨⟨r, m⟩, rfl⟩
    · apply Submodule.subset_span
      change principalPartsAddRelation p.1 p.2 ∈
        principalPartsRelationSet (R := R) (S := S) (M := M) k
      apply Or.inl
      apply Or.inl
      exact ⟨p, rfl⟩
    · apply Submodule.subset_span
      change principalPartsScalarRelation r m ∈
        principalPartsRelationSet (R := R) (S := S) (M := M) k
      apply Or.inl
      apply Or.inr
      exact ⟨(r, m), rfl⟩
  · let g₀ : Fin (k + 1) → S := fun i => g i.castSucc
    let a : S := g (Fin.last (k + 1))
    have h₁ : principalPartsHigherRelation k g₀ m ∈
        principalPartsRelationSubmodule (R := R) (S := S) (M := M) k := by
      apply Submodule.subset_span
      change principalPartsHigherRelation k g₀ m ∈
        principalPartsRelationSet (R := R) (S := S) (M := M) k
      apply Or.inr
      exact ⟨(g₀, m), rfl⟩
    have h₂ : principalPartsHigherRelation k g₀ (a • m) ∈
        principalPartsRelationSubmodule (R := R) (S := S) (M := M) k := by
      apply Submodule.subset_span
      change principalPartsHigherRelation k g₀ (a • m) ∈
        principalPartsRelationSet (R := R) (S := S) (M := M) k
      apply Or.inr
      exact ⟨(g₀, a • m), rfl⟩
    have hmem : a • principalPartsHigherRelation k g₀ m -
          principalPartsHigherRelation k g₀ (a • m) ∈
        principalPartsRelationSubmodule (R := R) (S := S) (M := M) k := by
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ h₁) h₂
    let embed : Finset (Fin (k + 1)) × Bool →
        Finset (Fin (k + 1 + 1)) := fun p =>
      match p.2 with
      | false => p.1.map Fin.castSuccEmb
      | true => insert (Fin.last (k + 1)) (p.1.map Fin.castSuccEmb)
    have hembed : Function.Bijective embed := by
      constructor
      · rintro ⟨p, b⟩ ⟨q, c⟩ h
        cases b <;> cases c
        · simp only [embed] at h
          exact Prod.ext (Finset.map_injective Fin.castSuccEmb h) rfl
        · exfalso
          have hm := congrArg (fun t => Fin.last (k + 1) ∈ t) h
          simpa [embed] using hm
        · exfalso
          have hm := congrArg (fun t => Fin.last (k + 1) ∈ t) h
          simpa [embed] using hm
        · simp only [embed] at h
          apply Prod.ext
          · apply Finset.ext
            intro i
            have hi := congrArg (fun t => i.castSucc ∈ t) h
            simpa using hi
          · rfl
      · intro u
        by_cases hu : Fin.last (k + 1) ∈ u
        · let p := (u.erase (Fin.last (k + 1))).preimage
              Fin.castSucc (Fin.castSucc_injective _).injOn
          refine ⟨(p, true), ?_⟩
          apply Finset.ext
          intro i
          cases i using Fin.lastCases with
          | last => simp [embed, p, hu]
          | cast i => simp [embed, p, hu]
        · let p := u.preimage Fin.castSucc (Fin.castSucc_injective _).injOn
          refine ⟨(p, false), ?_⟩
          apply Finset.ext
          intro i
          cases i using Fin.lastCases with
          | last => simp [embed, p, hu]
          | cast i => simp [embed, p, hu]
    have hEq : principalPartsHigherRelation (k + 1) g m =
        a • principalPartsHigherRelation k g₀ m -
          principalPartsHigherRelation k g₀ (a • m) := by
      let F : Finset (Fin (k + 1 + 1)) → M →₀ S := fun t =>
        ((-1 : S) ^ t.card) •
          (((Finset.univ \ t).prod g) •
            Finsupp.single ((t.prod g) • m) 1)
      have hcompFalse (x : Finset (Fin (k + 1))) :
          (Finset.univ \ x.map Fin.castSuccEmb) =
            insert (Fin.last (k + 1))
              ((Finset.univ \ x).map Fin.castSuccEmb) := by
        ext i
        cases i using Fin.lastCases with
        | last => simp
        | cast i => simp
      have hcompTrue (x : Finset (Fin (k + 1))) :
          (Finset.univ \ insert (Fin.last (k + 1)) (x.map Fin.castSuccEmb)) =
            (Finset.univ \ x).map Fin.castSuccEmb := by
        ext i
        cases i using Fin.lastCases with
        | last => simp
        | cast i => simp
      have hsum := Fintype.sum_bijective embed hembed
        (fun p => F (embed p)) F (fun _ => rfl)
      have hfalse : (∑ x : Finset (Fin (k + 1)), F (embed (x, false))) =
          a • principalPartsHigherRelation k g₀ m := by
        simp [F, embed, principalPartsHigherRelation, g₀, a, hcompFalse,
          Finset.smul_sum, Finsupp.smul_single', mul_assoc, mul_comm, mul_left_comm]
      have htrue : (∑ x : Finset (Fin (k + 1)), F (embed (x, true))) =
          -principalPartsHigherRelation k g₀ (a • m) := by
        change (∑ x : Finset (Fin (k + 1)), F (embed (x, true))) =
          -(∑ x : Finset (Fin (k + 1)), ((-1 : S) ^ x.card) •
            (((Finset.univ \ x).prod g₀) •
              Finsupp.single ((x.prod g₀) • (a • m)) 1))
        rw [← Finset.sum_neg_distrib]
        simp [F, embed, principalPartsHigherRelation, g₀, a, hcompTrue,
          Finsupp.smul_single', pow_succ', smul_smul, mul_assoc, mul_comm,
          mul_left_comm]
      have hsum' := hsum.symm
      rw [← Finset.univ_product_univ, Finset.sum_product] at hsum'
      simp_rw [Fintype.sum_bool] at hsum'
      rw [Finset.sum_add_distrib] at hsum'
      rw [htrue, hfalse] at hsum'
      simpa [F, principalPartsHigherRelation, sub_eq_add_neg, add_assoc,
        add_comm, add_left_comm] using hsum'
    change principalPartsHigherRelation (k + 1) g m ∈
      principalPartsRelationSubmodule (R := R) (S := S) (M := M) k
    rw [hEq]
    exact hmem

noncomputable def principalPartsTransition (k : ℕ) :
    PrincipalParts (R := R) (S := S) (M := M) (k + 1) →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) k :=
  Submodule.factor (principalParts_relation_succ_le (R := R) (S := S) (M := M) k)

theorem principalPartsTransition_on_generator (k : ℕ) (m : M) :
    principalPartsTransition (R := R) (S := S) (M := M) k
        (Submodule.mkQ _ (Finsupp.single m 1)) =
      Submodule.mkQ _ (Finsupp.single m 1) := by
  rfl

def principalPartsGenerator (k : ℕ) (m : M) :
    PrincipalParts (R := R) (S := S) (M := M) k :=
  Submodule.mkQ _ (Finsupp.single m 1)

private def principalPartsHigherEvaluation
    {Q : Type*} [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q] (k : ℕ) (D : M →ₗ[R] Q)
    (g : Fin (k + 1) → S) (m : M) : Q :=
  ∑ t : Finset (Fin (k + 1)), ((-1 : S) ^ t.card) •
    (((Finset.univ \ t).prod g) • D ((t.prod g) • m))

private def principalPartsHigherEvaluationMap
    {Q : Type*} [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q] (D : M →ₗ[R] Q) : (M →₀ S) →ₗ[S] Q :=
  Finsupp.lsum S (fun x : M => (LinearMap.id : S →ₗ[S] S).smulRight (D x))

private theorem principalPartsHigherEvaluation_eq_map
    {Q : Type*} [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q] (k : ℕ) (D : M →ₗ[R] Q)
    (g : Fin (k + 1) → S) (m : M) :
    principalPartsHigherEvaluation (R := R) (S := S) k D g m =
      principalPartsHigherEvaluationMap (R := R) (S := S) D
        (principalPartsHigherRelation k g m) := by
  simp [principalPartsHigherEvaluation, principalPartsHigherEvaluationMap,
    principalPartsHigherRelation, Finsupp.lsum_apply, Finset.smul_sum,
    Finsupp.smul_single', smul_smul, mul_assoc, mul_comm, mul_left_comm]

private theorem principalPartsHigherEvaluation_succ
    {Q : Type*} [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q] (k : ℕ) (D : M →ₗ[R] Q) (s : S)
    (g : Fin (k + 1) → S) (m : M) :
    principalPartsHigherEvaluation (R := R) (S := S) (k + 1) D
        (fun i => Fin.lastCases s g i) m =
      s • principalPartsHigherEvaluation (R := R) (S := S) k D g m -
        principalPartsHigherEvaluation (R := R) (S := S) k D g (s • m) := by
  rw [principalPartsHigherEvaluation_eq_map,
    principalPartsHigherRelation_succ_eq (R := R) (S := S) (M := M)]
  simp only [map_sub, map_smul]
  simp [principalPartsHigherEvaluation_eq_map]

private theorem principalPartsHigherEvaluation_zero
    {Q : Type*} [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q] (D : M →ₗ[R] Q) (s : S) (m : M) :
    principalPartsHigherEvaluation (R := R) (S := S) 0 D (fun _ => s) m =
      s • D m - D (s • m) := by
  let embed : Bool → Finset (Fin 1) := fun b =>
    if b then {0} else ∅
  have hembed : Function.Bijective embed := by
    constructor
    · intro b c h
      cases b <;> cases c <;> simp [embed] at h ⊢
    · intro t
      by_cases ht : (0 : Fin 1) ∈ t
      · refine ⟨true, ?_⟩
        apply Finset.ext
        intro i
        cases i using Fin.lastCases with
        | last => simp [embed, ht]
        | cast i => exact Fin.elim0 i
      · refine ⟨false, ?_⟩
        apply Finset.ext
        intro i
        cases i using Fin.lastCases with
        | last => simp [embed, ht]
        | cast i => exact Fin.elim0 i
  let F : Finset (Fin 1) → Q := fun t =>
    ((-1 : S) ^ t.card) •
      (((Finset.univ \ t).prod (fun _ => s)) •
        D ((t.prod (fun _ => s)) • m))
  have hsum := Fintype.sum_bijective embed hembed
    (fun b => F (embed b)) F (fun _ => rfl)
  have hsum' := hsum.symm
  simp_rw [Fintype.sum_bool] at hsum'
  simpa [F, embed, principalPartsHigherEvaluation, Finset.prod_const,
    Finset.card_singleton, smul_smul, mul_assoc, mul_comm, mul_left_comm,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'

private theorem isDifferentialOperator_of_principalPartsHigherEvaluation
    {Q : Type*} [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q] (k : ℕ) (D : M →ₗ[R] Q)
    (hD : ∀ (g : Fin (k + 1) → S) (m : M),
      principalPartsHigherEvaluation (R := R) (S := S) k D g m = 0) :
    IsDifferentialOperator (R := R) (S := S) k D := by
  induction k generalizing D with
  | zero =>
      intro s m
      have h := hD (fun _ => s) m
      rw [principalPartsHigherEvaluation_zero] at h
      exact (sub_eq_zero.mp h).symm
  | succ k ih =>
      intro s
      apply ih
      intro g m
      have hcomm :
          principalPartsHigherEvaluation (R := R) (S := S) k
              (differentialOperatorCommutator D s) g m =
            principalPartsHigherEvaluation (R := R) (S := S) k D g (s • m) -
              s • principalPartsHigherEvaluation (R := R) (S := S) k D g m := by
        simp [principalPartsHigherEvaluation, differentialOperatorCommutator,
          Finset.smul_sum, smul_sub, smul_smul, mul_assoc, mul_comm, mul_left_comm]
      have h := principalPartsHigherEvaluation_succ (R := R) (S := S) k D s g m
      rw [hcomm, ← neg_sub, ← h, hD (fun i => Fin.lastCases s g i) m,
        neg_zero]

theorem principalParts_universal_linear_map_exists (k : ℕ) :
    ∃ u : M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) k,
      (∀ m, u m = principalPartsGenerator (R := R) (S := S) (M := M) k m) ∧
      IsDifferentialOperator (R := R) (S := S) k u := by
  let q : (M →₀ S) →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) k :=
    Submodule.mkQ _
  let u : M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) k :=
    { toFun := fun m => q (Finsupp.single m 1)
      map_add' := by
        intro m m'
        rw [← q.map_add, eq_comm, ← sub_eq_zero, ← q.map_sub,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        have hrel : principalPartsAddRelation m m' ∈
            principalPartsRelationSubmodule (R := R) (S := S) (M := M) k := by
          apply Submodule.subset_span
          change principalPartsAddRelation m m' ∈
            principalPartsRelationSet (R := R) (S := S) (M := M) k
          exact Or.inl (Or.inl ⟨(m, m'), rfl⟩)
        simpa [principalPartsAddRelation, sub_eq_add_neg, add_assoc, add_comm,
          add_left_comm] using (Submodule.neg_mem _ hrel)
      map_smul' := by
        intro r m
        rw [← q.map_smul_of_tower, eq_comm, ← sub_eq_zero,
          ← q.map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        have hrel : principalPartsScalarRelation r m ∈
            principalPartsRelationSubmodule (R := R) (S := S) (M := M) k := by
          apply Submodule.subset_span
          change principalPartsScalarRelation r m ∈
            principalPartsRelationSet (R := R) (S := S) (M := M) k
          exact Or.inl (Or.inr ⟨(r, m), rfl⟩)
        simpa [principalPartsScalarRelation, sub_eq_add_neg, add_assoc, add_comm,
          add_left_comm] using hrel }
  have hq : principalPartsHigherEvaluationMap (R := R) (S := S) u = q := by
    ext z
    classical
    simp [principalPartsHigherEvaluationMap, Finsupp.lsum_apply, u, q,
      Finsupp.smul_single', smul_smul, mul_assoc, mul_comm, mul_left_comm]
  refine ⟨u, ?_, ?_⟩
  · intro m
    rfl
  · apply isDifferentialOperator_of_principalPartsHigherEvaluation
    intro g m
    rw [principalPartsHigherEvaluation_eq_map, hq]
    change Submodule.mkQ _ (principalPartsHigherRelation k g m) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply Submodule.subset_span
    change principalPartsHigherRelation k g m ∈
      principalPartsRelationSet (R := R) (S := S) (M := M) k
    exact Or.inr ⟨(g, m), rfl⟩

noncomputable def principalPartsUniversalLinearMap (k : ℕ) :
    M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) k :=
  Classical.choose (principalParts_universal_linear_map_exists (R := R) (S := S) (M := M) k)

theorem principalPartsUniversalLinearMap_apply (k : ℕ) (m : M) :
    principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k m =
      principalPartsGenerator (R := R) (S := S) (M := M) k m :=
  (Classical.choose_spec
    (principalParts_universal_linear_map_exists (R := R) (S := S) (M := M) k)).1 m

theorem principalPartsUniversalLinearMap_isDifferentialOperator (k : ℕ) :
    IsDifferentialOperator (R := R) (S := S) k
      (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) :=
  (Classical.choose_spec
    (principalParts_universal_linear_map_exists (R := R) (S := S) (M := M) k)).2

abbrev principalPartsUniversal (k : ℕ) :
    differentialOperatorSubmodule (R := R) (S := S) (M := M)
      (N := PrincipalParts (R := R) (S := S) (M := M) k) k :=
  ⟨principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k,
    principalPartsUniversalLinearMap_isDifferentialOperator (R := R) (S := S) (M := M) k⟩

private theorem principalParts_factorization_unique_aux (k : ℕ) (N : Type*)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k) :
    ∃! α : PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N,
      (α.restrictScalars R).comp
          (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) = D.1 := by
  classical
  let L : (M →₀ S) →ₗ[S] N :=
    Finsupp.lsum S (fun m : M =>
      ((LinearMap.id : S →ₗ[S] S).smulRight (D.1 m)))
  have hEval : ∀ (j : ℕ) (E : M →ₗ[R] N),
      IsDifferentialOperator (R := R) (S := S) j E →
        ∀ (g : Fin (j + 1) → S) (m : M),
          principalPartsHigherEvaluation (R := R) (S := S) j E g m = 0 := by
    intro j
    induction j with
    | zero =>
        intro E hE g m
        have hg : g = fun _ => g 0 := by
          funext i
          exact congrArg g (Fin.eq_zero i)
        rw [hg, principalPartsHigherEvaluation_zero]
        exact sub_eq_zero.mpr (hE (g 0) m).symm
    | succ j ih =>
        intro E hE g m
        let s : S := g (Fin.last (j + 1))
        let g₀ : Fin (j + 1) → S := fun i => g i.castSucc
        have hg : g = fun i => Fin.lastCases s g₀ i := by
          funext i
          cases i using Fin.lastCases with
          | last => simp [s]
          | cast i => simp [g₀]
        rw [hg, principalPartsHigherEvaluation_succ]
        have hcomm :
            principalPartsHigherEvaluation (R := R) (S := S) j
                (differentialOperatorCommutator E s) g₀ m =
              principalPartsHigherEvaluation (R := R) (S := S) j E g₀ (s • m) -
                s • principalPartsHigherEvaluation (R := R) (S := S) j E g₀ m := by
          simp [principalPartsHigherEvaluation, differentialOperatorCommutator,
            Finset.smul_sum, smul_sub, smul_smul, mul_assoc, mul_comm, mul_left_comm]
        have hz := ih (differentialOperatorCommutator E s) (hE s) g₀ m
        rw [hcomm] at hz
        exact sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
  have hL : principalPartsRelationSubmodule (R := R) (S := S) (M := M) k ≤
      LinearMap.ker L := by
    apply Submodule.span_le.2
    intro x hx
    rcases hx with hx | ⟨⟨g, m⟩, rfl⟩
    · rcases hx with ⟨p, rfl⟩ | ⟨⟨r, m⟩, rfl⟩
      · change L (principalPartsAddRelation p.1 p.2) = 0
        change (Finsupp.lsum S (fun m : M =>
          ((LinearMap.id : S →ₗ[S] S).smulRight (D.1 m))))
          (Finsupp.single (p.1 + p.2) 1 - Finsupp.single p.1 1 -
            Finsupp.single p.2 1) = 0
        rw [map_sub, map_sub, Finsupp.lsum_single, Finsupp.lsum_single,
          Finsupp.lsum_single]
        simp [D.1.map_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      · change L (principalPartsScalarRelation r m) = 0
        change (Finsupp.lsum S (fun m : M =>
          ((LinearMap.id : S →ₗ[S] S).smulRight (D.1 m))))
          ((algebraMap R S r) • Finsupp.single m 1 - Finsupp.single (r • m) 1) = 0
        rw [map_sub, map_smul, Finsupp.lsum_single, Finsupp.lsum_single]
        simp only [LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]
        rw [IsScalarTower.algebraMap_smul S r (D.1 m), D.1.map_smul]
        exact sub_self _
    · change L (principalPartsHigherRelation k g m) = 0
      change principalPartsHigherEvaluationMap (R := R) (S := S) D.1
          (principalPartsHigherRelation k g m) = 0
      rw [← principalPartsHigherEvaluation_eq_map (R := R) (S := S) k D.1 g m]
      exact hEval k D.1 D.2 g m
  have hex : ∃ α : PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N,
      (α.restrictScalars R).comp
          (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) = D.1 := by
    refine ⟨Submodule.liftQ _ L hL, ?_⟩
    ext m
    rw [LinearMap.comp_apply, principalPartsUniversalLinearMap_apply,
      principalPartsGenerator]
    change (Submodule.liftQ _ L hL)
      (Submodule.mkQ _ (Finsupp.single m 1)) = D.1 m
    have hm := congrArg (fun F : (M →₀ S) →ₗ[S] N => F (Finsupp.single m 1))
      (Submodule.liftQ_mkQ
        (p := principalPartsRelationSubmodule (R := R) (S := S) (M := M) k)
        (f := L) hL)
    simpa [LinearMap.comp_apply, L, Finsupp.lsum_single] using hm
  rcases hex with ⟨α, hα⟩
  refine ⟨α, hα, ?_⟩
  intro β hβ
  let q : (M →₀ S) →ₗ[S] PrincipalParts (R := R) (S := S) (M := M) k :=
    Submodule.mkQ _
  have hgen : ∀ m : M,
      β (principalPartsGenerator (R := R) (S := S) (M := M) k m) =
        α (principalPartsGenerator (R := R) (S := S) (M := M) k m) := by
    intro m
    have hβm := congrArg (fun E => E m) hβ
    have hαm := congrArg (fun E => E m) hα
    change β (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k m) = D.1 m at hβm
    change α (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k m) = D.1 m at hαm
    simpa [principalPartsUniversalLinearMap_apply, principalPartsGenerator] using
      hβm.trans hαm.symm
  have hmaps : β.comp q = α.comp q := by
    apply LinearMap.ext
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add]; rw [hx, hy]
    | single m s =>
        change β (q (Finsupp.single m s)) = α (q (Finsupp.single m s))
        calc
          β (q (Finsupp.single m s)) =
              β (s • q (Finsupp.single m 1)) := by
                rw [← Finsupp.smul_single_one m s, q.map_smul]
          _ = s • β (q (Finsupp.single m 1)) := by rw [map_smul]
          _ = s • α (q (Finsupp.single m 1)) := by
            simpa [q, principalPartsGenerator] using
              congrArg (fun z => s • z) (hgen m)
          _ = α (s • q (Finsupp.single m 1)) := by rw [map_smul]
          _ = α (q (Finsupp.single m s)) := by
            congr 1
            rw [← q.map_smul, Finsupp.smul_single_one]
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg (fun z => z y) hmaps

theorem principalParts_universal_property_exists (k : ℕ) (N : Type*)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    ∃ e :
        ↥(differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k)
          ≃ₗ[S]
          (PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N),
      ∀ D,
        ((e D).restrictScalars R).comp
            (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) = D.1 := by
  classical
  let backward :
      (PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N) →ₗ[S]
        differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k :=
    { toFun := fun α => differentialOperatorPostcompose α
        (principalPartsUniversal (R := R) (S := S) (M := M) k)
      map_add' := by
        intro α β
        apply Subtype.ext
        ext m
        rfl
      map_smul' := by
        intro c α
        apply Subtype.ext
        ext m
        rfl }
  have hinj : Function.Injective backward := by
    intro α β h
    rcases principalParts_factorization_unique_aux (R := R) (S := S) (M := M) k N
        (backward α) with ⟨γ, hγ, huniq⟩
    apply (huniq α ?_).trans (huniq β ?_).symm
    · change (α.restrictScalars R).comp
          (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) =
        (backward α).1
      rfl
    · change (β.restrictScalars R).comp
          (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) =
        (backward α).1
      have h' := congrArg (fun E => E.1) h
      change (backward α).1 = (backward β).1 at h'
      exact h'.symm
  have hsurj : Function.Surjective backward := by
    intro D
    rcases principalParts_factorization_unique_aux (R := R) (S := S) (M := M) k N D with
      ⟨α, hα, _⟩
    refine ⟨α, ?_⟩
    apply Subtype.ext
    exact hα
  let e := LinearEquiv.ofBijective backward ⟨hinj, hsurj⟩
  refine ⟨e.symm, ?_⟩
  intro D
  change (backward (e.symm D)).1 = D.1
  exact congrArg Subtype.val (e.apply_symm_apply D)

noncomputable def principalPartsHomEquiv (k : ℕ)
    (N : Type*) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k ≃ₗ[S]
      (PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N) :=
  Classical.choose
    (principalParts_universal_property_exists (S := S) (M := M) k N)

theorem principalPartsHomEquiv_factorization (k : ℕ) (N : Type*)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k) :
    ((principalPartsHomEquiv (R := R) (S := S) (M := M) k N D).restrictScalars R).comp
        (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) = D.1 :=
  by
    simpa [principalPartsHomEquiv] using
      (Classical.choose_spec
        (principalParts_universal_property_exists (R := R) (S := S) (M := M) k N)) D

theorem principalParts_factorization_unique (k : ℕ) (N : Type*)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k) :
    ∃! α : PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] N,
      (α.restrictScalars R).comp
          (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) = D.1 := by
  exact principalParts_factorization_unique_aux (R := R) (S := S) (M := M) k N D

theorem principalPartsHomEquiv_natural (k : ℕ)
    {N N' : Type*} [AddCommGroup N] [AddCommGroup N']
    [Module S N] [Module S N'] [Module R N] [Module R N']
    [IsScalarTower R S N] [IsScalarTower R S N'] (f : LinearMapOver S N N')
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := M) (N := N) k) :
    principalPartsHomEquiv (R := R) (S := S) (M := M) k N'
        (differentialOperatorPostcompose f D) =
      f.comp (principalPartsHomEquiv (R := R) (S := S) (M := M) k N D) := by
  rcases principalParts_factorization_unique (R := R) (S := S) (M := M) k N'
      (differentialOperatorPostcompose f D) with ⟨α, hα, huniq⟩
  have hleft := principalPartsHomEquiv_factorization
    (R := R) (S := S) (M := M) k N' (differentialOperatorPostcompose f D)
  have hright :
      ((f.comp (principalPartsHomEquiv (R := R) (S := S) (M := M) k N D)).restrictScalars R).comp
          (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k) =
        (differentialOperatorPostcompose f D).1 := by
    ext m
    have hD := principalPartsHomEquiv_factorization
      (R := R) (S := S) (M := M) k N D
    have hDm := congrArg (fun L : M →ₗ[R] N => L m) hD
    change f ((principalPartsHomEquiv (R := R) (S := S) (M := M) k N D)
      (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) k m)) = f (D.1 m)
    apply congrArg f
    simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using hDm
  exact (huniq _ hleft).trans (huniq _ hright).symm

/- The map to `M` obtained by sending `[m]` to `m`. -/
noncomputable def principalPartsFreeEvaluation : (M →₀ S) →ₗ[S] M :=
  Finsupp.lsum S (α := M) (M := S) (N := M)
    (fun m : M => ((LinearMap.id : S →ₗ[S] S).smulRight m))

theorem principalParts_relation_le_ker_evaluation (k : ℕ) :
    principalPartsRelationSubmodule (R := R) (S := S) (M := M) k ≤
      LinearMap.ker (principalPartsFreeEvaluation (S := S) (M := M)) := by
  classical
  have hHigher : ∀ (j : ℕ) (g : Fin (j + 1) → S) (m : M),
      principalPartsHigherEvaluation (R := R) (S := S) j
          (LinearMap.id : M →ₗ[R] M) g m = 0 := by
    intro j
    induction j with
    | zero =>
        intro g m
        have hg : g = fun _ => g 0 := by
          funext i
          exact congrArg g (Fin.eq_zero i)
        rw [hg, principalPartsHigherEvaluation_zero]
        simp
    | succ j ih =>
        intro g m
        let s : S := g (Fin.last (j + 1))
        let g₀ : Fin (j + 1) → S := fun i => g i.castSucc
        have hg : g = fun i => Fin.lastCases s g₀ i := by
          funext i
          cases i using Fin.lastCases with
          | last => simp [s]
          | cast i => simp [g₀]
        rw [hg, principalPartsHigherEvaluation_succ, ih, ih]
        simp
  apply Submodule.span_le.2
  intro x hx
  rcases hx with hx | ⟨⟨g, m⟩, rfl⟩
  · rcases hx with ⟨p, rfl⟩ | ⟨⟨r, m⟩, rfl⟩
    · change principalPartsFreeEvaluation (S := S) (M := M)
          (principalPartsAddRelation p.1 p.2) = 0
      change (Finsupp.lsum S (fun m : M =>
        ((LinearMap.id : S →ₗ[S] S).smulRight m)))
          (Finsupp.single (p.1 + p.2) 1 - Finsupp.single p.1 1 -
            Finsupp.single p.2 1) = 0
      rw [map_sub, map_sub, Finsupp.lsum_single, Finsupp.lsum_single,
        Finsupp.lsum_single]
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    · change principalPartsFreeEvaluation (S := S) (M := M)
          (principalPartsScalarRelation r m) = 0
      change (Finsupp.lsum S (fun m : M =>
        ((LinearMap.id : S →ₗ[S] S).smulRight m)))
          ((algebraMap R S r) • Finsupp.single m 1 - Finsupp.single (r • m) 1) = 0
      rw [map_sub, map_smul, Finsupp.lsum_single, Finsupp.lsum_single]
      simp only [LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]
      rw [IsScalarTower.algebraMap_smul S r m]
      exact sub_self _
  · change principalPartsFreeEvaluation (S := S) (M := M)
        (principalPartsHigherRelation k g m) = 0
    change principalPartsHigherEvaluationMap (R := R) (S := S)
        (LinearMap.id : M →ₗ[R] M) (principalPartsHigherRelation k g m) = 0
    rw [← principalPartsHigherEvaluation_eq_map (R := R) (S := S) k
      (LinearMap.id : M →ₗ[R] M) g m]
    exact hHigher k g m

noncomputable def principalPartsProjection (k : ℕ) :
    PrincipalParts (R := R) (S := S) (M := M) k →ₗ[S] M :=
  Submodule.liftQ _ (principalPartsFreeEvaluation (S := S) (M := M))
    (principalParts_relation_le_ker_evaluation (R := R) (S := S) (M := M) k)

theorem principalPartsProjection_on_generator (k : ℕ) (m : M) :
    principalPartsProjection (R := R) (S := S) (M := M) k
        (principalPartsGenerator (R := R) (S := S) (M := M) k m) = m := by
  change (principalPartsFreeEvaluation (S := S) (M := M))
      (Finsupp.single m 1) = m
  simp [principalPartsFreeEvaluation]

theorem principalParts_zero_equiv_exists :
    ∃ e : PrincipalParts (R := R) (S := S) (M := M) 0 ≃ₗ[S] M,
      e.toLinearMap = principalPartsProjection (R := R) (S := S) (M := M) 0 := by
  classical
  let u : M →ₗ[S] PrincipalParts (R := R) (S := S) (M := M) 0 :=
    { toFun := principalPartsUniversalLinearMap (R := R) (S := S) (M := M) 0
      map_add' :=
        (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) 0).map_add
      map_smul' := by
        intro s m
        exact (principalPartsUniversalLinearMap_isDifferentialOperator
          (R := R) (S := S) (M := M) 0) s m }
  have hright : ∀ m : M,
      principalPartsProjection (R := R) (S := S) (M := M) 0 (u m) = m := by
    intro m
    change principalPartsProjection (R := R) (S := S) (M := M) 0
      (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) 0 m) = m
    rw [principalPartsUniversalLinearMap_apply,
      principalPartsProjection_on_generator]
  have hleft : ∀ x : PrincipalParts (R := R) (S := S) (M := M) 0,
      u (principalPartsProjection (R := R) (S := S) (M := M) 0 x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
      (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 0) x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
        simp only [map_add]
        rw [hx, hy]
    | single m s =>
        change u (principalPartsProjection (R := R) (S := S) (M := M) 0
          (Submodule.mkQ _ (Finsupp.single m s))) =
          Submodule.mkQ _ (Finsupp.single m s)
        rw [← Finsupp.smul_single_one m s, map_smul, map_smul]
        change u (s • principalPartsProjection (R := R) (S := S) (M := M) 0
          (principalPartsGenerator (R := R) (S := S) (M := M) 0 m)) =
          s • principalPartsGenerator (R := R) (S := S) (M := M) 0 m
        rw [map_smul, principalPartsProjection_on_generator]
        have hu : u m = principalPartsGenerator (R := R) (S := S) (M := M) 0 m := by
          change principalPartsUniversalLinearMap (R := R) (S := S) (M := M) 0 m =
            principalPartsGenerator (R := R) (S := S) (M := M) 0 m
          rw [principalPartsUniversalLinearMap_apply]
        rw [hu]
  have hbij : Function.Bijective
      (principalPartsProjection (R := R) (S := S) (M := M) 0) := by
    constructor
    · intro x y hxy
      have h := congrArg u hxy
      rw [hleft x, hleft y] at h
      exact h
    · intro m
      exact ⟨u m, hright m⟩
  exact ⟨LinearEquiv.ofBijective
    (principalPartsProjection (R := R) (S := S) (M := M) 0) hbij, rfl⟩

noncomputable def principalPartsZeroEquiv :
    PrincipalParts (R := R) (S := S) (M := M) 0 ≃ₗ[S] M :=
  Classical.choose (principalParts_zero_equiv_exists (R := R) (S := S) (M := M))

theorem principalParts_zero_equiv_agrees_with_projection :
    (principalPartsZeroEquiv (R := R) (S := S) (M := M)).toLinearMap =
      principalPartsProjection (R := R) (S := S) (M := M) 0 := by
  simpa [principalPartsZeroEquiv] using
    (Classical.choose_spec
      (principalParts_zero_equiv_exists (R := R) (S := S) (M := M)))

end PrincipalParts

/-! ## Derivations and the order-one example -/

section OrderOneExample

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

def scalarValueLinearMap (x : N) : S →ₗ[S] N :=
  (LinearMap.id : S →ₗ[S] S).smulRight x

def differentialOperatorDerivationFormula
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1) (g : S) : N :=
  D.1 g - g • D.1 1

theorem differentialOperator_order_one_derivation_decomposition
    (D : differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1) :
    ∃ σ : Derivation R S N,
      (∀ g, σ g = differentialOperatorDerivationFormula (R := R) (S := S) D g) ∧
      (∀ g, D.1 g = σ g + scalarValueLinearMap (S := S) (N := N) (D.1 1) g) := by
  let σ : Derivation R S N :=
    { toLinearMap := D.1 -
        (scalarValueLinearMap (S := S) (N := N) (D.1 1)).restrictScalars R
      map_one_eq_zero' := by
        change D.1 1 - (scalarValueLinearMap (S := S) (N := N) (D.1 1)) 1 = 0
        simp [scalarValueLinearMap]
      leibniz' := by
        intro g h
        have hc := D.2 g
        have hc' := hc h 1
        have hc'' : D.1 (g * h) - g • D.1 h =
            h • (D.1 g - g • D.1 1) := by
          simpa [differentialOperatorCommutator] using hc'
        change D.1 (g * h) - (g * h) • D.1 1 =
            g • (D.1 h - h • D.1 1) + h • (D.1 g - g • D.1 1)
        rw [← hc'']
        simp [smul_sub, smul_smul, mul_assoc, mul_comm, mul_left_comm,
          sub_eq_add_neg, add_assoc, add_comm, add_left_comm] }
  refine ⟨σ, ?_⟩
  constructor
  · intro g
    rfl
  · intro g
    change D.1 g = (D.1 g - g • D.1 1) + g • D.1 1
    rw [sub_add_cancel]

theorem differentialOperator_order_one_ring_equiv_exists :
    Nonempty
      (differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1 ≃ₗ[S]
        (Derivation R S N × N)) := by
  classical
  let sigmaOf :
      differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1 →
        Derivation R S N :=
    fun D => Classical.choose
      (differentialOperator_order_one_derivation_decomposition (R := R) (S := S) D)
  have sigmaOf_spec :
      ∀ (D : differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1)
        (g : S), sigmaOf D g =
          differentialOperatorDerivationFormula (R := R) (S := S) D g := by
    intro D g
    exact (Classical.choose_spec
      (differentialOperator_order_one_derivation_decomposition (R := R) (S := S) D)).1 g
  let forward :
      differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1 →ₗ[S]
        (Derivation R S N × N) :=
    { toFun := fun D => (sigmaOf D, D.1 1)
      map_add' := by
        intro D E
        apply Prod.ext
        · change sigmaOf (D + E) = sigmaOf D + sigmaOf E
          apply Derivation.ext
          intro g
          change sigmaOf (D + E) g = sigmaOf D g + sigmaOf E g
          rw [sigmaOf_spec (D + E) g, sigmaOf_spec D g, sigmaOf_spec E g]
          simp [differentialOperatorDerivationFormula, sub_eq_add_neg,
            smul_add, add_assoc, add_comm, add_left_comm]
        · simp
      map_smul' := by
        intro c D
        apply Prod.ext
        · change sigmaOf (c • D) = c • sigmaOf D
          apply Derivation.ext
          intro g
          change sigmaOf (c • D) g = c • sigmaOf D g
          rw [sigmaOf_spec (c • D) g, sigmaOf_spec D g]
          simp [differentialOperatorDerivationFormula, sub_eq_add_neg,
            smul_sub, smul_smul, mul_assoc, mul_comm, mul_left_comm]
        · simp }
  let op : (Derivation R S N × N) → (S →ₗ[R] N) :=
    fun p => p.1.toLinearMap.restrictScalars R +
      (scalarValueLinearMap (S := S) (N := N) p.2).restrictScalars R
  have hop :
      ∀ p : Derivation R S N × N,
        IsDifferentialOperator (R := R) (S := S) 1 (op p) := by
    intro p
    intro g
    have hcomm :
        differentialOperatorCommutator (op p) g =
          scalarValueLinearMap (S := S) (N := N) (p.1 g) := by
      ext m
      change ((p.1 : S → N) (g * m) + (g * m) • p.2) -
          g • ((p.1 : S → N) m + m • p.2) = m • p.1 g
      rw [p.1.leibniz, smul_add, mul_smul, sub_eq_add_neg, neg_add_rev]
      simp [add_assoc, add_comm, add_left_comm]
    rw [hcomm]
    intro s m
    exact mul_smul s m (p.1 g)
  let backward :
      (Derivation R S N × N) →ₗ[S]
        differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1 :=
    { toFun := fun p => ⟨op p, hop p⟩
      map_add' := by
        intro p q
        apply Subtype.ext
        ext g
        simp [op, scalarValueLinearMap, add_smul, add_assoc, add_comm, add_left_comm]
      map_smul' := by
        intro c p
        apply Subtype.ext
        ext g
        simp [op, scalarValueLinearMap, smul_smul, mul_assoc, mul_comm, mul_left_comm] }
  have hback :
      ∀ D : differentialOperatorSubmodule (R := R) (S := S) (M := S) (N := N) 1,
        backward (forward D) = D := by
    intro D
    apply Subtype.ext
    ext g
    have h := (Classical.choose_spec
      (differentialOperator_order_one_derivation_decomposition (R := R) (S := S) D)).2 g
    change sigmaOf D g + g • D.1 1 = D.1 g
    simpa [sigmaOf, scalarValueLinearMap] using h.symm
  have hforward :
      ∀ p : Derivation R S N × N, forward (backward p) = p := by
    intro p
    apply Prod.ext
    · apply Derivation.ext
      intro g
      change sigmaOf (backward p) g = p.1 g
      have h := sigmaOf_spec (backward p) g
      rw [h]
      change op p g - g • op p 1 = p.1 g
      simp [op, differentialOperatorDerivationFormula, scalarValueLinearMap,
        Derivation.map_one_eq_zero, sub_eq_add_neg, smul_add, smul_sub,
        smul_smul, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
        mul_left_comm]
    · change op p 1 = p.2
      simp [op, scalarValueLinearMap, Derivation.map_one_eq_zero]
  have hbij : Function.Bijective backward := ⟨
    fun p q h => by
      have h' := congrArg forward h
      rw [hforward p, hforward q] at h'
      exact h',
    fun D => ⟨forward D, hback D⟩⟩
  exact ⟨(LinearEquiv.ofBijective backward hbij).symm⟩

theorem principalParts_one_equiv_differentials_prod :
    Nonempty
      (PrincipalParts (R := R) (S := S) 1 (M := S) ≃ₗ[S]
        (ModuleOfDifferentials R S × S)) := by
  classical
  let dprod : S →ₗ[R] (ModuleOfDifferentials R S × S) :=
    { toFun := fun g => (universalDifferential R S g, g)
      map_add' := by
        intro g h
        apply Prod.ext
        · exact (universalDifferential R S).map_add g h
        · rfl
      map_smul' := by
        intro r g
        simp [universalDifferential] }
  have hdprod :
      IsDifferentialOperator (R := R) (S := S) 1 dprod := by
    intro g
    let commRight : S →ₗ[R] (ModuleOfDifferentials R S × S) :=
      { toFun := fun m => (m • universalDifferential R S g, 0)
        map_add' := by
          intro m n
          apply Prod.ext
          · change (m + n) • universalDifferential R S g =
              m • universalDifferential R S g + n • universalDifferential R S g
            rw [add_smul]
          · simp
        map_smul' := by
          intro r m
          simp [smul_smul, mul_smul] }
    have hcomm :
        differentialOperatorCommutator dprod g = commRight := by
      apply LinearMap.ext
      intro m
      change
        ((universalDifferential R S (g * m), g * m) -
            g • (universalDifferential R S m, m)) =
          (m • universalDifferential R S g, 0)
      apply Prod.ext
      · simp [Derivation.leibniz, smul_sub, smul_add, smul_smul, mul_smul,
          add_assoc, add_comm, add_left_comm, sub_eq_add_neg]
      · simp
    rw [hcomm]
    intro s m
    change ((s • m) • universalDifferential R S g, 0) =
      s • (m • universalDifferential R S g, 0)
    apply Prod.ext
    · exact smul_assoc s m (universalDifferential R S g)
    · simp
  let Dprod :
      differentialOperatorSubmodule (R := R) (S := S) (M := S)
        (N := ModuleOfDifferentials R S × S) 1 :=
    ⟨dprod, hdprod⟩
  let α : PrincipalParts (R := R) (S := S) (M := S) 1 →ₗ[S]
      (ModuleOfDifferentials R S × S) :=
    principalPartsHomEquiv (R := R) (S := S) (M := S) 1
      (ModuleOfDifferentials R S × S) Dprod
  have hα :
      (α.restrictScalars R).comp
          (principalPartsUniversalLinearMap (R := R) (S := S) (M := S) 1) =
        dprod :=
    principalPartsHomEquiv_factorization (R := R) (S := S) (M := S) 1
      (ModuleOfDifferentials R S × S) Dprod
  let Ulinear :
      S →ₗ[R] PrincipalParts (R := R) (S := S) (M := S) 1 :=
    principalPartsUniversalLinearMap (R := R) (S := S) (M := S) 1
  let U : differentialOperatorSubmodule (R := R) (S := S) (M := S)
      (N := PrincipalParts (R := R) (S := S) (M := S) 1) 1 :=
    principalPartsUniversal (R := R) (S := S) (M := S) 1
  let sigmaU : Derivation R S (PrincipalParts (R := R) (S := S) (M := S) 1) :=
    Classical.choose
      (differentialOperator_order_one_derivation_decomposition (R := R) (S := S) U)
  have sigmaU_spec (g : S) :
      sigmaU g = differentialOperatorDerivationFormula (R := R) (S := S) U g :=
    (Classical.choose_spec
      (differentialOperator_order_one_derivation_decomposition (R := R) (S := S) U)).1 g
  let l : ModuleOfDifferentials R S →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := S) 1 :=
    (derivationsEquivLinearMaps (R := R) (S := S)
      (M := PrincipalParts (R := R) (S := S) (M := S) 1)).symm sigmaU
  have hl (g : S) :
      l (universalDifferential R S g) = sigmaU g := by
    exact congrArg (fun d : Derivation R S
      (PrincipalParts (R := R) (S := S) (M := S) 1) => d g)
      ((derivationsEquivLinearMaps (R := R) (S := S)
        (M := PrincipalParts (R := R) (S := S) (M := S) 1)).apply_symm_apply sigmaU)
  let beta :
      (ModuleOfDifferentials R S × S) →ₗ[S]
        PrincipalParts (R := R) (S := S) (M := S) 1 :=
    { toFun := fun p => l p.1 + p.2 • Ulinear 1
      map_add' := by
        intro p q
        change l (p.1 + q.1) + (p.2 + q.2) • Ulinear 1 =
          (l p.1 + p.2 • Ulinear 1) + (l q.1 + q.2 • Ulinear 1)
        rw [map_add, add_smul]
        ac_rfl
      map_smul' := by
        intro c p
        simp [smul_smul, smul_assoc, mul_assoc, mul_comm, mul_left_comm] }
  have hbeta :
      (beta.restrictScalars R).comp dprod = Ulinear := by
    apply LinearMap.ext
    intro g
    change beta (dprod g) = Ulinear g
    change l (universalDifferential R S g) + g • Ulinear 1 = Ulinear g
    rw [hl g]
    have hs := sigmaU_spec g
    change sigmaU g = Ulinear g - g • Ulinear 1 at hs
    rw [hs]
    exact sub_add_cancel _ _
  have hba :
      beta.comp α = LinearMap.id := by
    rcases principalParts_factorization_unique (R := R) (S := S)
      (M := S) 1 (PrincipalParts (R := R) (S := S) (M := S) 1) U
      with ⟨f, hf, huniq⟩
    have hid :
        ((LinearMap.id :
          PrincipalParts (R := R) (S := S) (M := S) 1 →ₗ[S]
            PrincipalParts (R := R) (S := S) (M := S) 1).restrictScalars R).comp
          Ulinear = Ulinear := by
      rfl
    have hcomp :
        ((beta.comp α).restrictScalars R).comp Ulinear = Ulinear := by
      apply LinearMap.ext
      intro g
      change beta (α (Ulinear g)) = Ulinear g
      have ha := congrArg (fun F : S →ₗ[R]
          (ModuleOfDifferentials R S × S) => F g) hα
      change α (Ulinear g) = dprod g at ha
      have hb := congrArg (fun F : S →ₗ[R]
          PrincipalParts (R := R) (S := S) (M := S) 1 => F g) hbeta
      change beta (dprod g) = Ulinear g at hb
      rw [ha]
      exact hb
    apply (huniq (beta.comp α) hcomp).trans
      (huniq (LinearMap.id) hid).symm
  let inj : ModuleOfDifferentials R S →ₗ[S]
      (ModuleOfDifferentials R S × S) :=
    { toFun := fun ω => (ω, 0)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  have hal : α.comp l = inj := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro g
    change α (l (universalDifferential R S g)) = inj (universalDifferential R S g)
    rw [hl g]
    have hs := sigmaU_spec g
    change sigmaU g = Ulinear g - g • Ulinear 1 at hs
    rw [hs, map_sub]
    have ha := congrArg (fun F : S →ₗ[R]
        (ModuleOfDifferentials R S × S) => F g) hα
    change α (Ulinear g) = dprod g at ha
    rw [ha]
    have ha1 := congrArg (fun F : S →ₗ[R]
        (ModuleOfDifferentials R S × S) => F 1) hα
    change α (Ulinear 1) = dprod 1 at ha1
    rw [map_smul, ha1]
    simp [inj, dprod, universalDifferential]
  have hab :
      α.comp beta = LinearMap.id := by
    apply LinearMap.ext
    intro p
    change α (l p.1 + p.2 • Ulinear 1) = p
    rw [map_add, map_smul]
    have hlp := congrArg (fun F : ModuleOfDifferentials R S →ₗ[S]
        (ModuleOfDifferentials R S × S) => F p.1) hal
    have ha1 := congrArg (fun F : S →ₗ[R]
        (ModuleOfDifferentials R S × S) => F 1) hα
    change α (l p.1) = inj p.1 at hlp
    change α (Ulinear 1) = dprod 1 at ha1
    rw [hlp, ha1]
    simp [inj, dprod, universalDifferential]
  have hinj : Function.Injective α := by
    intro x y h
    have h' := congrArg beta h
    change (beta.comp α) x = (beta.comp α) y at h'
    rw [hba] at h'
    exact h'
  have hsurj : Function.Surjective α := by
    intro y
    refine ⟨beta y, ?_⟩
    change (α.comp beta) y = y
    rw [hab]
    rfl
  exact ⟨LinearEquiv.ofBijective α ⟨hinj, hsurj⟩⟩

end OrderOneExample

/-! ## The sequence of principal parts -/

section PrincipalPartsSequence

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

private theorem principalPartsHigherRelation_one_explicit
    {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (g : Fin 2 → S) (m : M) :
    principalPartsHigherRelation 1 g m =
      (g 0 * g 1) • Finsupp.single m (1 : S) -
        g 1 • Finsupp.single (g 0 • m) (1 : S) -
        g 0 • Finsupp.single (g 1 • m) (1 : S) +
        Finsupp.single ((g 0 * g 1) • m) (1 : S) := by
  classical
  have huniv : (Finset.univ : Finset (Finset (Fin 2))) =
      {∅, {0}, {1}, {0, 1}} := by decide
  have hd0 : (Finset.univ : Finset (Fin 2)) \ ∅ = {0, 1} := by decide
  have hd1 : (Finset.univ : Finset (Fin 2)) \ {0} = {1} := by decide
  have hd2 : (Finset.univ : Finset (Fin 2)) \ {1} = {0} := by decide
  have hd3 : (Finset.univ : Finset (Fin 2)) \ {0, 1} = ∅ := by decide
  rw [principalPartsHigherRelation, huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hd0, hd1, hd2, hd3]
  simp only [Finset.card_empty, Finset.card_singleton, Finset.card_pair,
    Finset.prod_empty, Finset.prod_singleton, Finset.prod_insert,
    pow_zero, pow_one, one_smul, neg_one_smul, Finsupp.smul_single',
    sub_eq_add_neg]
  simp [Finset.prod_pair, Finset.card_pair, pow_two, mul_one, one_mul,
    mul_assoc]
  abel

private theorem principalParts_sequence_K_higher
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (K : (M →₀ S) →ₗ[R] (ModuleOfDifferentials R S) ⊗[S] M)
    (hK_single : ∀ m s, K (Finsupp.single m s) =
      -(universalDifferential R S s ⊗ₜ[S] m))
    (hK_single_smul : ∀ c m, K (c • Finsupp.single m (1 : S)) =
      -(universalDifferential R S c ⊗ₜ[S] m))
    (g : Fin 2 → S) (m : M) :
    K (principalPartsHigherRelation 1 g m) = 0 := by
  let a : S := g 0
  let b : S := g 1
  have hrel : principalPartsHigherRelation 1 g m =
      (a * b) • Finsupp.single m 1 -
        b • Finsupp.single (a • m) 1 -
        a • Finsupp.single (b • m) 1 +
        Finsupp.single ((a * b) • m) 1 := by
    simpa [a, b] using principalPartsHigherRelation_one_explicit g m
  let f₀ : M →₀ S := Finsupp.single m (1 : S)
  let f₁ : M →₀ S := Finsupp.single ((a : S) • m) (1 : S)
  let f₂ : M →₀ S := Finsupp.single ((b : S) • m) (1 : S)
  let f₃ : M →₀ S := Finsupp.single (((a * b : S)) • m) (1 : S)
  let F₀ : M →₀ S := (a * b) • f₀ - b • f₁ - a • f₂ + f₃
  have hrelK : K (principalPartsHigherRelation 1 g m) = K F₀ := by
    apply congrArg (fun F : M →₀ S => K F)
    simpa [F₀, f₀, f₁, f₂, f₃] using hrel
  calc
    K (principalPartsHigherRelation 1 g m) = K F₀ := hrelK
    _ = 0 := by
      dsimp [F₀, f₀, f₁, f₂, f₃]
      rw [map_add, map_sub, map_sub]
      have hk0 := hK_single_smul (a * b) m
      have hk1 := hK_single_smul b (a • m)
      have hk2 := hK_single_smul a (b • m)
      simp only [hk0, hk1, hk2, hK_single ((a * b) • m) 1]
      simp [Derivation.map_one_eq_zero]
      rw [TensorProduct.add_tmul, neg_add]
      simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul,
        smul_neg, sub_eq_add_neg]
      abel

private theorem principalParts_sequence_formula
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (i : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) 1)
    (u : M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) 1)
    (eval : (M →₀ S) →ₗ[S] M)
    (K : (M →₀ S) →ₗ[R] (ModuleOfDifferentials R S) ⊗[S] M)
    (hugen : ∀ m, Submodule.mkQ
        (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1)
          (Finsupp.single m (1 : S)) = u m)
    (hsingle : ∀ m s, K (Finsupp.single m s) =
      -(universalDifferential R S s ⊗ₜ[S] m))
    (heval_single : ∀ m s, eval (Finsupp.single m s) = s • m)
    (hi : ∀ g m, i (universalDifferential R S g ⊗ₜ[S] m) =
      u (g • m) - g • u m) :
    ∀ F, Submodule.mkQ
        (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1) F =
      u (eval F) + i (K F) := by
  let q : (M →₀ S) →ₗ[S]
      (M →₀ S) ⧸ principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1 :=
    Submodule.mkQ
      (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1)
  intro F
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG =>
      rw [map_add, map_add, map_add, map_add, hF, hG]
      rw [map_add]
      abel
  | single m s =>
      have hqsmul : q (Finsupp.single m s) = s • q (Finsupp.single m (1 : S)) := by
        rw [← Finsupp.smul_single_one m s, q.map_smul]
      rw [hqsmul, hugen m, heval_single m s, hsingle m s, map_neg, hi]
      rw [sub_eq_add_neg]
      abel

private theorem principalParts_sequence_exact_of_data
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (i : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) 1)
    (u : M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) 1)
    (eval : (M →₀ S) →ₗ[S] M)
    (K : (M →₀ S) →ₗ[R] (ModuleOfDifferentials R S) ⊗[S] M)
    (hformula : ∀ F, Submodule.mkQ
        (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1) F =
      u (eval F) + i (K F))
    (hKrel : ∀ F, F ∈ principalPartsRelationSubmodule
        (R := R) (S := S) (M := M) 1 → K F = 0)
    (hproj : ∀ F, principalPartsProjection (R := R) (S := S) (M := M) 1
        (Submodule.mkQ
          (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1) F) =
      eval F)
    (hrep : ∀ z, ∃ F, Submodule.mkQ
        (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1) F =
          i z ∧ K F = z ∧ eval F = 0)
    (hsurj : Function.Surjective
      (principalPartsProjection (R := R) (S := S) (M := M) 1)) :
    Function.Exact i (principalPartsProjection (R := R) (S := S) (M := M) 1) ∧
      Function.Injective i ∧
      Function.Surjective (principalPartsProjection (R := R) (S := S) (M := M) 1) := by
  let q := Submodule.mkQ
    (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1)
  have hpi : ∀ z, principalPartsProjection (R := R) (S := S) (M := M) 1 (i z) = 0 := by
    intro z
    obtain ⟨F, hq, hK, heval⟩ := hrep z
    rw [← hq]
    rw [hproj]
    exact heval
  have hex : Function.Exact i
      (principalPartsProjection (R := R) (S := S) (M := M) 1) := by
    intro x
    constructor
    · intro hx
      obtain ⟨F, rfl⟩ := Submodule.mkQ_surjective
        (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1) x
      have heval : eval F = 0 := by
        exact (hproj F).symm.trans hx
      refine ⟨K F, ?_⟩
      rw [hformula F, heval, map_zero, zero_add]
    · rintro ⟨z, rfl⟩
      exact hpi z
  have hinj : Function.Injective i := by
    intro z z' hzz'
    obtain ⟨F, hq, hK, heval⟩ := hrep (z - z')
    have hq0 : q F = 0 := by
      rw [hq, map_sub, hzz', sub_self]
    have hrel : F ∈ principalPartsRelationSubmodule
        (R := R) (S := S) (M := M) 1 := by
      exact (Submodule.Quotient.mk_eq_zero _).mp hq0
    exact sub_eq_zero.mp (hK.symm.trans (hKrel F hrel))
  exact ⟨hex, hinj, hsurj⟩

private theorem moduleOfDifferentials_zero_tmul_neg
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (m : M) :
    -((0 : ModuleOfDifferentials R S) ⊗ₜ[S] m) = 0 := by
  rw [TensorProduct.zero_tmul, neg_zero]

private theorem moduleOfDifferentials_zero_tmul_sub_neg
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (m : M) (x : (ModuleOfDifferentials R S) ⊗[S] M) :
    -((0 : ModuleOfDifferentials R S) ⊗ₜ[S] m) - -x = x := by
  have hzero : -((0 : ModuleOfDifferentials R S) ⊗ₜ[S] m) = 0 :=
    moduleOfDifferentials_zero_tmul_neg (R := R) (S := S) (M := M) m
  calc
    -((0 : ModuleOfDifferentials R S) ⊗ₜ[S] m) - -x = 0 - -x :=
      congrArg (fun z : (ModuleOfDifferentials R S) ⊗[S] M => z - -x) hzero
    _ = x := (zero_sub (-x)).trans (neg_neg x)

private theorem principalParts_eval_sub_smul
    {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (eval : (M →₀ S) →ₗ[S] M)
    (heval_single : ∀ m s, eval (Finsupp.single m s) = s • m)
    (g : S) (m : M) :
    eval (Finsupp.single (g • m) (1 : S) -
      g • Finsupp.single m (1 : S)) = 0 := by
  rw [eval.map_sub, heval_single (g • m) 1, eval.map_smul,
    heval_single m 1]
  change (1 : S) • (g • m) - g • ((1 : S) • m) = 0
  rw [one_smul, one_smul, sub_self]

private theorem principalParts_sequence_span
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (i : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) 1)
    (u : M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) 1)
    (eval : (M →₀ S) →ₗ[S] M)
    (K : (M →₀ S) →ₗ[R] (ModuleOfDifferentials R S) ⊗[S] M)
    (q : (M →₀ S) →ₗ[S]
      (M →₀ S) ⧸ principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1)
    (hformula : ∀ F, q F = u (eval F) + i (K F))
    (hsingle : ∀ m s, K (Finsupp.single m s) =
      -(universalDifferential R S s ⊗ₜ[S] m))
    (hK_single_smul : ∀ c m,
      K (c • Finsupp.single m (1 : S)) =
        -(universalDifferential R S c ⊗ₜ[S] m))
    (hK_smul : ∀ c F, K (c • F) = c • K F -
      universalDifferential R S c ⊗ₜ[S] eval F)
    (heval_single : ∀ m s, eval (Finsupp.single m s) = s • m) :
    ∀ (ω : ModuleOfDifferentials R S) (m : M),
      ∃ F, q F = i (ω ⊗ₜ[S] m) ∧ K F = ω ⊗ₜ[S] m ∧ eval F = 0 := by
  intro ω m
  have hmem : ω ∈ Submodule.span S (Set.range (universalDifferential R S)) := by
    change ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction (p := fun ω _ =>
    ∃ F, q F = i (ω ⊗ₜ[S] m) ∧ K F = ω ⊗ₜ[S] m ∧ eval F = 0) ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨g, rfl⟩
    have hKF : K (Finsupp.single (g • m) (1 : S) -
        g • Finsupp.single m (1 : S)) =
        universalDifferential R S g ⊗ₜ[S] m := by
      rw [map_sub, hsingle (g • m) 1, hK_single_smul g m]
      have hd1 : universalDifferential R S 1 = 0 :=
        (universalDifferential R S).map_one_eq_zero
      rw [hd1]
      exact moduleOfDifferentials_zero_tmul_sub_neg (R := R) (S := S) (M := M)
        (g • m) (universalDifferential R S g ⊗ₜ[S] m)
    have hEvalF := principalParts_eval_sub_smul eval heval_single g m
    refine ⟨Finsupp.single (g • m) (1 : S) -
      g • Finsupp.single m (1 : S), ?_, hKF, hEvalF⟩
    calc
      q (Finsupp.single (g • m) (1 : S) -
          g • Finsupp.single m (1 : S)) =
          u (eval (Finsupp.single (g • m) (1 : S) -
            g • Finsupp.single m (1 : S))) +
            i (K (Finsupp.single (g • m) (1 : S) -
              g • Finsupp.single m (1 : S))) :=
        hformula _
      _ = i (universalDifferential R S g ⊗ₜ[S] m) := by
        rw [hEvalF, map_zero, zero_add, hKF]
  · refine ⟨0, ?_, ?_, ?_⟩
    · simp only [map_zero, TensorProduct.zero_tmul]
    · simpa only [TensorProduct.zero_tmul] using map_zero K
    · exact map_zero eval
  · intro x y hx hy ⟨F, hFq, hFK, hFe⟩ ⟨G, hGq, hGK, hGe⟩
    refine ⟨F + G, ?_, ?_, ?_⟩
    · calc
        q (F + G) = q F + q G := q.map_add _ _
        _ = i (x ⊗ₜ[S] m) + i (y ⊗ₜ[S] m) := by rw [hFq, hGq]
        _ = i ((x + y) ⊗ₜ[S] m) := by
          have ht :
              (x ⊗ₜ[S] m) + (y ⊗ₜ[S] m) =
                (x + y) ⊗ₜ[S] m :=
            (TensorProduct.add_tmul x y m).symm
          calc
            i (x ⊗ₜ[S] m) + i (y ⊗ₜ[S] m) =
                i ((x ⊗ₜ[S] m) + (y ⊗ₜ[S] m)) := (i.map_add _ _).symm
            _ = i ((x + y) ⊗ₜ[S] m) :=
              congrArg (fun z : (ModuleOfDifferentials R S) ⊗[S] M => i z) ht
    · calc
        K (F + G) = K F + K G := K.map_add _ _
        _ = (x ⊗ₜ[S] m) + (y ⊗ₜ[S] m) := by rw [hFK, hGK]
        _ = (x + y) ⊗ₜ[S] m := (TensorProduct.add_tmul x y m).symm
    · rw [eval.map_add, hFe, hGe, add_zero]
  · intro c x _ ⟨F, hFq, hFK, hFe⟩
    refine ⟨c • F, ?_, ?_, ?_⟩
    · calc
        q (c • F) = c • q F := q.map_smul _ _
        _ = c • i (x ⊗ₜ[S] m) := by rw [hFq]
        _ = i ((c • x) ⊗ₜ[S] m) := by
          rw [← i.map_smul, TensorProduct.smul_tmul']
    · rw [hK_smul, hFK, hFe, TensorProduct.tmul_zero, sub_zero]
      rw [TensorProduct.smul_tmul']
    · rw [eval.map_smul, hFe, smul_zero]

private theorem principalParts_sequence_surjective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    :
    Function.Surjective (principalPartsProjection (R := R) (S := S) (M := M) 1) := by
  intro m
  refine ⟨principalPartsUniversalLinearMap (R := R) (S := S) (M := M) 1 m, ?_⟩
  change principalPartsProjection (R := R) (S := S) (M := M) 1
    (principalPartsUniversalLinearMap (R := R) (S := S) (M := M) 1 m) = m
  rw [principalPartsUniversalLinearMap_apply,
    principalPartsProjection_on_generator]

private theorem principalParts_sequence_tensor_representation
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (i : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) 1)
    (q : (M →₀ S) →ₗ[S]
      (M →₀ S) ⧸ principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1)
    (K : (M →₀ S) →ₗ[R] (ModuleOfDifferentials R S) ⊗[S] M)
    (eval : (M →₀ S) →ₗ[S] M)
    (hspan : ∀ (ω : ModuleOfDifferentials R S) (m : M),
      ∃ F, q F = i (ω ⊗ₜ[S] m) ∧ K F = ω ⊗ₜ[S] m ∧ eval F = 0) :
    ∀ z : (ModuleOfDifferentials R S) ⊗[S] M,
      ∃ F, q F = i z ∧ K F = z ∧ eval F = 0 := by
  intro z
  refine TensorProduct.induction_on z ?_ (fun ω m => hspan ω m) ?_
  · refine ⟨0, ?_, ?_, ?_⟩
    · simp only [map_zero, TensorProduct.zero_tmul]
    · simpa only [TensorProduct.zero_tmul] using map_zero K
    · exact map_zero eval
  · intro x y ⟨F, hFq, hFK, hFe⟩ ⟨G, hGq, hGK, hGe⟩
    refine ⟨F + G, ?_, ?_, ?_⟩
    · rw [q.map_add, hFq, hGq, i.map_add]
    · rw [K.map_add, hFK, hGK]
    · rw [eval.map_add, hFe, hGe, add_zero]

theorem principalParts_sequence_left_exists :
    ∃ i : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
          PrincipalParts (R := R) (S := S) (M := M) 1,
      Function.Exact i (principalPartsProjection (R := R) (S := S) (M := M) 1) ∧
        Function.Injective i ∧
        Function.Surjective (principalPartsProjection (R := R) (S := S) (M := M) 1) := by
  classical
  let u : M →ₗ[R] PrincipalParts (R := R) (S := S) (M := M) 1 :=
    principalPartsUniversalLinearMap (R := R) (S := S) (M := M) 1
  let deltaLinear (m : M) : S →ₗ[R]
      PrincipalParts (R := R) (S := S) (M := M) 1 :=
    { toFun := fun g => u (g • m) - g • u m
      map_add' := by
        intro g h
        rw [add_smul, map_add, sub_eq_add_neg]
        rw [show (g + h) • u m = g • u m + h • u m by
          exact add_smul g h (u m)]
        abel
      map_smul' := by
        intro r g
        change u ((r • g) • m) - (r • g) • u m =
          r • (u (g • m) - g • u m)
        rw [smul_assoc, map_smul, smul_assoc, smul_sub] }
  let delta (m : M) : Derivation R S
      (PrincipalParts (R := R) (S := S) (M := M) 1) :=
    { toLinearMap := deltaLinear m
      map_one_eq_zero' := by dsimp [deltaLinear]; simp
      leibniz' := by
        intro g h
        have hc := (principalPartsUniversal (R := R) (S := S) (M := M) 1).2 g h m
        change u (g • (h • m)) - g • u (h • m) =
          h • (u (g • m) - g • u m) at hc
        change u ((g * h) • m) - (g * h) • u m =
          g • (u (h • m) - h • u m) + h • (u (g • m) - g • u m)
        rw [mul_smul, ← hc, smul_sub, smul_smul]
        rw [show (g * h) • u m = g • h • u m by exact mul_smul g h (u m)]
        simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] }
  have hdelta_add (m n : M) : delta (m + n) = delta m + delta n := by
    apply Derivation.ext
    intro g
    change u (g • (m + n)) - g • u (m + n) =
      (u (g • m) - g • u m) + (u (g • n) - g • u n)
    rw [smul_add, u.map_add (g • m) (g • n), u.map_add m n]
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  have hdelta_smul (c : S) (m : M) : delta (c • m) = c • delta m := by
    apply Derivation.ext
    intro g
    have hc := (principalPartsUniversal (R := R) (S := S) (M := M) 1).2 g c m
    change u (g • (c • m)) - g • u (c • m) =
      c • (u (g • m) - g • u m) at hc
    exact hc
  let lOf (m : M) : ModuleOfDifferentials R S →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) 1 :=
    (derivationsEquivLinearMaps (R := R) (S := S)
      (M := PrincipalParts (R := R) (S := S) (M := M) 1)).symm (delta m)
  have hlOf (m : M) (g : S) :
      lOf m (universalDifferential R S g) = delta m g := by
    exact congrArg (fun d : Derivation R S
        (PrincipalParts (R := R) (S := S) (M := M) 1) => d g)
      ((derivationsEquivLinearMaps (R := R) (S := S)
        (M := PrincipalParts (R := R) (S := S) (M := M) 1)).apply_symm_apply
          (delta m))
  have hlOf_add (m n : M) : lOf (m + n) = lOf m + lOf n := by
    simpa [lOf] using congrArg
      (fun d : Derivation R S
          (PrincipalParts (R := R) (S := S) (M := M) 1) =>
        (derivationsEquivLinearMaps (R := R) (S := S)
          (M := PrincipalParts (R := R) (S := S) (M := M) 1)).symm d)
      (hdelta_add m n)
  have hlOf_smul (c : S) (m : M) : lOf (c • m) = c • lOf m := by
    simpa [lOf] using congrArg
      (fun d : Derivation R S
          (PrincipalParts (R := R) (S := S) (M := M) 1) =>
        (derivationsEquivLinearMaps (R := R) (S := S)
          (M := PrincipalParts (R := R) (S := S) (M := M) 1)).symm d)
      (hdelta_smul c m)
  let phi : ModuleOfDifferentials R S →ₗ[S]
      (M →ₗ[S] PrincipalParts (R := R) (S := S) (M := M) 1) :=
    { toFun := fun ω =>
        { toFun := fun m => lOf m ω
          map_add' := by
            intro m n
            rw [hlOf_add]
            simp
          map_smul' := by
            intro c m
            rw [hlOf_smul]
            simp }
      map_add' := by
        intro ω η
        ext m
        change lOf m (ω + η) = lOf m ω + lOf m η
        rw [map_add]
      map_smul' := by
        intro c ω
        ext m
        change lOf m (c • ω) = c • lOf m ω
        rw [map_smul] }
  let i : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) 1 :=
    TensorProduct.AlgebraTensorModule.lift phi
  have hi (g : S) (m : M) :
      i (universalDifferential R S g ⊗ₜ[S] m) =
        u (g • m) - g • u m := by
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]
    change lOf m (universalDifferential R S g) = _
    rw [hlOf]
    rfl
  let coeff (m : M) : S →ₗ[R] (ModuleOfDifferentials R S) ⊗[S] M :=
    { toFun := fun s => -(universalDifferential R S s ⊗ₜ[S] m)
      map_add' := by
        intro s t
        rw [map_add, TensorProduct.add_tmul, neg_add]
      map_smul' := by
        intro r s
        change -(universalDifferential R S (r • s) ⊗ₜ[S] m) =
          r • -(universalDifferential R S s ⊗ₜ[S] m)
        have hds : universalDifferential R S (r • s) =
            r • universalDifferential R S s :=
          (universalDifferential R S).toLinearMap.map_smul r s
        rw [hds]
        simp [TensorProduct.smul_tmul', smul_neg] }
  let K : (M →₀ S) →ₗ[R] (ModuleOfDifferentials R S) ⊗[S] M :=
    Finsupp.lsum R coeff
  have hK_single (m : M) (s : S) : K (Finsupp.single m s) = coeff m s := by
    simp [K]
  let eval : (M →₀ S) →ₗ[S] M :=
    principalPartsFreeEvaluation (S := S) (M := M)
  have hK_smul (c : S) (F : M →₀ S) :
      K (c • F) = c • K F -
        universalDifferential R S c ⊗ₜ[S] eval F := by
    induction F using Finsupp.induction_linear with
    | zero => simp
    | add F G hF hG =>
        rw [smul_add, map_add, hF, hG, map_add]
        rw [eval.map_add, TensorProduct.tmul_add, smul_add]
        rw [sub_eq_add_neg]
        abel
    | single m s =>
        rw [show c • Finsupp.single m s = Finsupp.single m (c * s) by
          ext x
          by_cases hx : x = m <;> simp [hx]]
        rw [hK_single m (c * s), hK_single m s]
        change -(universalDifferential R S (c * s) ⊗ₜ[S] m) = _
        rw [(universalDifferential R S).leibniz]
        rw [TensorProduct.add_tmul, neg_add]
        simp only [eval, principalPartsFreeEvaluation, Finsupp.lsum_single,
          LinearMap.smulRight_apply, LinearMap.id_apply, one_smul,
          TensorProduct.tmul_smul]
        change -(c • universalDifferential R S s) ⊗ₜ[S] m +
            -(s • universalDifferential R S c) ⊗ₜ[S] m =
          c • (-(universalDifferential R S s ⊗ₜ[S] m)) -
            (s • universalDifferential R S c) ⊗ₜ[S] m
        have hct : -(c • universalDifferential R S s) ⊗ₜ[S] m =
            c • (-(universalDifferential R S s ⊗ₜ[S] m)) := by
          simp only [TensorProduct.smul_tmul', smul_neg]
        rw [hct, sub_eq_add_neg]
  have hevalrel (F : M →₀ S)
      (hF : F ∈ principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1) :
      eval F = 0 := by
    apply LinearMap.mem_ker.mp
    simpa [eval] using
      (principalParts_relation_le_ker_evaluation (R := R) (S := S) (M := M) 1 hF)
  have hK_single_smul (c : S) (m : M) :
      K (c • Finsupp.single m (1 : S)) =
        -(universalDifferential R S c ⊗ₜ[S] m) := by
    rw [show c • Finsupp.single m (1 : S) = Finsupp.single m c by
      ext x
      by_cases hx : x = m <;> simp [hx]]
    rw [hK_single]
    simp [coeff, Derivation.map_one_eq_zero]
  have hK_relation_set (F : M →₀ S)
      (hF : F ∈ principalPartsRelationSet (R := R) (S := S) (M := M) 1) :
      K F = 0 := by
    rcases hF with hF | ⟨⟨g, m⟩, rfl⟩
    · rcases hF with ⟨⟨m, n⟩, rfl⟩ | ⟨⟨r, m⟩, rfl⟩
      · change K (principalPartsAddRelation m n) = 0
        rw [principalPartsAddRelation, map_sub, map_sub,
          hK_single, hK_single, hK_single]
        simp [principalPartsAddRelation, coeff]
      · change K (principalPartsScalarRelation r m) = 0
        have hs : (algebraMap R S r) • (Finsupp.single m (1 : S)) =
            (r • (Finsupp.single m (1 : S)) : M →₀ S) := by
          ext x
          by_cases hx : x = m <;> simp [hx, IsScalarTower.algebraMap_smul S r]
        rw [principalPartsScalarRelation, hs, map_sub, map_smul,
          hK_single, hK_single]
        simp [coeff]
    · exact principalParts_sequence_K_higher K hK_single hK_single_smul g m
  have hugen (m : M) :
      Submodule.mkQ (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1)
          (Finsupp.single m (1 : S)) = u m := by
    change principalPartsGenerator (R := R) (S := S) (M := M) 1 m = u m
    rw [← principalPartsUniversalLinearMap_apply]
  have hsingle (m : M) (s : S) :
      K (Finsupp.single m s) =
        -(universalDifferential R S s ⊗ₜ[S] m) := by
    rw [hK_single]
    rfl
  have heval_single (m : M) (s : S) : eval (Finsupp.single m s) = s • m := by
    change principalPartsFreeEvaluation (S := S) (M := M)
      (Finsupp.single m s) = s • m
    simp [principalPartsFreeEvaluation]
  let q : (M →₀ S) →ₗ[S]
      (M →₀ S) ⧸ principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1 :=
    Submodule.mkQ
      (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1)
  have hformula (F : M →₀ S) : q F = u (eval F) + i (K F) := by
    change Submodule.mkQ
        (principalPartsRelationSubmodule (R := R) (S := S) (M := M) 1) F = _
    exact principalParts_sequence_formula i u eval K hugen hsingle
      heval_single hi F
  have hspan : ∀ (ω : ModuleOfDifferentials R S) (m : M),
      ∃ F, q F = i (ω ⊗ₜ[S] m) ∧ K F = ω ⊗ₜ[S] m ∧ eval F = 0 :=
    principalParts_sequence_span i u eval K q hformula hsingle
      hK_single_smul hK_smul heval_single
  have hrep : ∀ z : (ModuleOfDifferentials R S) ⊗[S] M,
      ∃ F, q F = i z ∧ K F = z ∧ eval F = 0 :=
    principalParts_sequence_tensor_representation i q K eval hspan
  have hKrel : ∀ F, F ∈ principalPartsRelationSubmodule
      (R := R) (S := S) (M := M) 1 → K F = 0 := by
    intro F hF
    change F ∈ Submodule.span S (principalPartsRelationSet
      (R := R) (S := S) (M := M) 1) at hF
    refine Submodule.span_induction (p := fun F _ => K F = 0) ?_ ?_ ?_ ?_ hF
    · intro F hF
      exact hK_relation_set F hF
    · exact map_zero K
    · intro F G hF hG ihF ihG
      rw [K.map_add, ihF, ihG, add_zero]
    · intro c F hF ihF
      have hevalF : eval F = 0 := hevalrel F (by exact hF)
      rw [hK_smul, ihF, hevalF, smul_zero, TensorProduct.tmul_zero, sub_zero]
  have hproj (F : M →₀ S) :
      principalPartsProjection (R := R) (S := S) (M := M) 1 (q F) = eval F := by
    rfl
  have hsurj : Function.Surjective
      (principalPartsProjection (R := R) (S := S) (M := M) 1) :=
    principalParts_sequence_surjective
  exact ⟨i, principalParts_sequence_exact_of_data i u eval K hformula
    hKrel hproj hrep hsurj⟩

noncomputable def principalPartsSequenceLeft :
    (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
      PrincipalParts (R := R) (S := S) (M := M) 1 :=
  Classical.choose (principalParts_sequence_left_exists (R := R) (S := S) (M := M))

theorem principalParts_sequence_exact :
    Function.Exact (principalPartsSequenceLeft (R := R) (S := S) (M := M))
      (principalPartsProjection (R := R) (S := S) (M := M) 1) :=
  (Classical.choose_spec (principalParts_sequence_left_exists (R := R) (S := S) (M := M))).1

theorem principalParts_sequence_left_injective :
    Function.Injective (principalPartsSequenceLeft (R := R) (S := S) (M := M)) :=
  (Classical.choose_spec (principalParts_sequence_left_exists (R := R) (S := S) (M := M))).2.1

theorem principalParts_sequence_right_surjective :
    Function.Surjective (principalPartsProjection (R := R) (S := S) (M := M) 1) :=
  (Classical.choose_spec (principalParts_sequence_left_exists (R := R) (S := S) (M := M))).2.2

structure PrincipalPartsShortExactSequence where
  left : (ModuleOfDifferentials R S) ⊗[S] M →ₗ[S]
    PrincipalParts (R := R) (S := S) (M := M) 1
  right : PrincipalParts (R := R) (S := S) (M := M) 1 →ₗ[S] M
  left_eq : left = principalPartsSequenceLeft (R := R) (S := S) (M := M)
  right_eq : right = principalPartsProjection (R := R) (S := S) (M := M) 1
  exact : Function.Exact left right
  left_injective : Function.Injective left
  right_surjective : Function.Surjective right

noncomputable def principalPartsSequence : PrincipalPartsShortExactSequence
    (R := R) (S := S) (M := M) :=
  { left := principalPartsSequenceLeft (R := R) (S := S) (M := M)
    right := principalPartsProjection (R := R) (S := S) (M := M) 1
    left_eq := rfl
    right_eq := rfl
    exact := principalParts_sequence_exact (R := R) (S := S) (M := M)
    left_injective := principalParts_sequence_left_injective (R := R) (S := S) (M := M)
    right_surjective := principalParts_sequence_right_surjective (R := R) (S := S) (M := M) }

end PrincipalPartsSequence

/-! ## Functoriality and base change -/

section PrincipalPartsFunctoriality

variable {A A' B B' M M' : Type*}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B']
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  [AddCommGroup M'] [Module B' M'] [Module A' M'] [IsScalarTower A' B' M']

/-- The data carried by the functoriality statement for principal parts.

The source calls the map on `M` `B`-linear.  Since the target has its
`B`-action induced through `B → B'`, `f_smul` records that statement
without requiring a second, potentially ambiguous `Module B M'` instance.
-/
structure PrincipalPartsFunctoriality where
  f : M →+ M'
  f_smul : ∀ b m, f (b • m) = algebraMap B B' b • f m
  commutes :
    (algebraMap A' B').comp (algebraMap A A') =
      (algebraMap B B').comp (algebraMap A B)
  map : ∀ k, PrincipalParts (R := A) (S := B) (M := M) k →+
    PrincipalParts (R := A') (S := B') (M := M') k
  map_zero : ∀ k, map k 0 = 0
  map_add : ∀ k x y, map k (x + y) = map k x + map k y
  map_smul : ∀ k b x, map k (b • x) = algebraMap B B' b • map k x
  map_generator : ∀ k m,
    map k (principalPartsGenerator (R := A) (S := B) k m) =
      principalPartsGenerator (R := A') (S := B') k (f m)
  map_transition : ∀ k x,
    map k (principalPartsTransition (R := A) (S := B) k x) =
      principalPartsTransition (R := A') (S := B') k (map (k + 1) x)

theorem principalParts_functoriality_exists
    (f : M →+ M')
    (hf : ∀ b m, f (b • m) = algebraMap B B' b • f m)
    (hcomm :
      (algebraMap A' B').comp (algebraMap A A') =
        (algebraMap B B').comp (algebraMap A B)) :
    Nonempty (PrincipalPartsFunctoriality (A := A) (A' := A') (B := B) (B' := B')
      (M := M) (M' := M')) := by
  classical
  let q : (M →₀ B) →ₗ[B] (M' →₀ B') :=
    { toFun := fun z =>
        Finsupp.mapRange (algebraMap B B') (by simp)
          (Finsupp.mapDomain f z)
      map_add' := by
        intro x y
        rw [Finsupp.mapDomain_add]
        rw [Finsupp.mapRange_add (map_add (algebraMap B B'))]
      map_smul' := by
        intro b z
        rw [Finsupp.mapDomain_smul]
        rw [Finsupp.mapRange_smul' (f := algebraMap B B') b
          (algebraMap B B' b) _ (by intro c; simp [smul_eq_mul])]
        ext i
        simp [Algebra.smul_def] }
  have hqsingle (m : M) (c : B) :
      q (Finsupp.single m c) =
        Finsupp.single (f m) (algebraMap B B' c) := by
    simp [q]
  have hc (a : A) :
      (algebraMap B B') ((algebraMap A B) a) =
        (algebraMap A' B') ((algebraMap A A') a) := by
    simpa using (DFunLike.congr_fun hcomm a).symm
  have hfA (a : A) (m : M) :
      f (a • m) = algebraMap A A' a • f m := by
    rw [← IsScalarTower.algebraMap_smul B a m, hf]
    rw [← IsScalarTower.algebraMap_smul B' (algebraMap A A' a) (f m)]
    rw [hc]
  have hqadd (m₁ m₂ : M) :
      q (principalPartsAddRelation m₁ m₂) =
        principalPartsAddRelation (f m₁) (f m₂) := by
    change q (Finsupp.single (m₁ + m₂) 1 -
      Finsupp.single m₁ 1 - Finsupp.single m₂ 1) = _
    rw [map_sub, map_sub]
    simp [q]
    rfl
  have hqscalar (a : A) (m : M) :
      q (principalPartsScalarRelation a m) =
        principalPartsScalarRelation (algebraMap A A' a) (f m) := by
    change q ((algebraMap A B a) • Finsupp.single m 1 -
      Finsupp.single (a • m) 1) = _
    rw [map_sub, map_smul, hqsingle, hqsingle, hfA]
    simp only [map_one]
    change (algebraMap A B a) • Finsupp.single (f m) (1 : B') -
        Finsupp.single (algebraMap A A' a • f m) (1 : B') =
      (algebraMap A' B' (algebraMap A A' a)) •
          Finsupp.single (f m) (1 : B') -
        Finsupp.single (algebraMap A A' a • f m) (1 : B')
    congr 1
    ext i
    by_cases hi : f m = i <;> simp [hi, Algebra.smul_def, hc]
  have hqhigher (k : ℕ) (g : Fin (k + 1) → B) (m : M) :
      q (principalPartsHigherRelation k g m) =
        principalPartsHigherRelation k (fun i => algebraMap B B' (g i)) (f m) := by
    unfold principalPartsHigherRelation
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ext i
    simp [q, Finsupp.mapDomain, Finsupp.mapRange, hf, Finset.prod_map]
    by_cases hidx : (t.prod (fun x => algebraMap B B' (g x))) • f m = i
    · simp [Finsupp.single_apply, hidx]
    · simp [Finsupp.single_apply, hidx]
  let L (k : ℕ) : (M →₀ B) →ₗ[B]
      PrincipalParts (R := A') (S := B') (M := M') k :=
    ((Submodule.mkQ (principalPartsRelationSubmodule
      (R := A') (S := B') (M := M') k)).restrictScalars B).comp q
  have hrel (k : ℕ) :
      principalPartsRelationSubmodule (R := A) (S := B) (M := M) k ≤
        LinearMap.ker (L k) := by
    apply Submodule.span_le.2
    intro x hx
    rcases hx with hx | ⟨⟨g, m⟩, rfl⟩
    · rcases hx with ⟨p, rfl⟩ | ⟨⟨a, m⟩, rfl⟩
      · change L k (principalPartsAddRelation p.1 p.2) = 0
        change Submodule.mkQ _ (q (principalPartsAddRelation p.1 p.2)) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hqadd]
        apply Submodule.subset_span
        change principalPartsAddRelation (f p.1) (f p.2) ∈
          principalPartsRelationSet (R := A') (S := B') (M := M') k
        exact Or.inl (Or.inl ⟨(f p.1, f p.2), rfl⟩)
      · change L k (principalPartsScalarRelation a m) = 0
        change Submodule.mkQ _ (q (principalPartsScalarRelation a m)) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hqscalar]
        apply Submodule.subset_span
        change principalPartsScalarRelation (algebraMap A A' a) (f m) ∈
          principalPartsRelationSet (R := A') (S := B') (M := M') k
        exact Or.inl (Or.inr ⟨(algebraMap A A' a, f m), rfl⟩)
    · change L k (principalPartsHigherRelation k g m) = 0
      change Submodule.mkQ _ (q (principalPartsHigherRelation k g m)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hqhigher]
      apply Submodule.subset_span
      change principalPartsHigherRelation k
          (fun i => algebraMap B B' (g i)) (f m) ∈
        principalPartsRelationSet (R := A') (S := B') (M := M') k
      exact Or.inr ⟨((fun i => algebraMap B B' (g i)), f m), rfl⟩
  let mapLinear (k : ℕ) :
      PrincipalParts (R := A) (S := B) (M := M) k →ₗ[B]
        PrincipalParts (R := A') (S := B') (M := M') k :=
    Submodule.liftQ _ (L k) (hrel k)
  have hmap_generator (k : ℕ) (m : M) :
      mapLinear k (principalPartsGenerator (R := A) (S := B) k m) =
        principalPartsGenerator (R := A') (S := B') k (f m) := by
    change mapLinear k (Submodule.mkQ _ (Finsupp.single m 1)) = _
    simp [mapLinear, L, q]
    rfl
  have hmap_transition (k : ℕ) (x :
      PrincipalParts (R := A) (S := B) (M := M) (k + 1)) :
      mapLinear k (principalPartsTransition (R := A) (S := B) k x) =
        principalPartsTransition (R := A') (S := B') k
          (mapLinear (k + 1) x) := by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    change mapLinear k (principalPartsTransition (R := A) (S := B) k
        (Submodule.mkQ _ z)) = _
    rfl
  have htarget_smul (k : ℕ) (b : B)
      (y : PrincipalParts (R := A') (S := B') (M := M') k) :
      b • y = algebraMap B B' b • y := by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z w hz hw =>
        calc
          b • Submodule.mkQ _ (z + w) =
              b • (Submodule.mkQ _ z + Submodule.mkQ _ w) := by rw [map_add]
          _ = b • Submodule.mkQ _ z + b • Submodule.mkQ _ w := smul_add _ _ _
          _ = algebraMap B B' b • Submodule.mkQ _ z +
              algebraMap B B' b • Submodule.mkQ _ w :=
            congrArg₂ (· + ·) hz hw
          _ = algebraMap B B' b • (Submodule.mkQ _ z + Submodule.mkQ _ w) :=
            (smul_add _ _ _).symm
          _ = algebraMap B B' b • Submodule.mkQ _ (z + w) := by rw [map_add]
    | single m c =>
        simp [Algebra.smul_def]
  have hmap_smul (k : ℕ) (b : B)
      (x : PrincipalParts (R := A) (S := B) (M := M) k) :
      mapLinear k (b • x) =
        algebraMap B B' b • mapLinear k x := by
    rw [(mapLinear k).map_smul]
    exact htarget_smul k b (mapLinear k x)
  refine ⟨{
    f := f
    f_smul := hf
    commutes := hcomm
    map := fun k => (mapLinear k).toAddMonoidHom
    map_zero := by
      intro k
      exact (mapLinear k).map_zero
    map_add := by
      intro k x y
      exact (mapLinear k).map_add x y
    map_smul := by
      intro k b x
      exact hmap_smul k b x
    map_generator := by
      intro k m
      exact hmap_generator k m
    map_transition := by
      intro k x
      exact hmap_transition k x
  }⟩

def principalPartsFunctorialitySequenceCompatible
    (F : PrincipalPartsFunctoriality (A := A) (A' := A') (B := B) (B' := B')
      (M := M) (M' := M')) : Prop :=
  ∃ φ : (ModuleOfDifferentials A B) ⊗[B] M →+
      (ModuleOfDifferentials A' B') ⊗[B'] M',
    (∀ x,
      F.map 1 (principalPartsSequenceLeft (R := A) (S := B) (M := M) x) =
        principalPartsSequenceLeft (R := A') (S := B') (M := M') (φ x)) ∧
    (∀ x,
      principalPartsProjection (R := A') (S := B') (M := M') 1
          (F.map 1 x) =
        F.f (principalPartsProjection (R := A) (S := B) (M := M) 1 x))

theorem principalParts_functoriality_sequence_compatible
    (F : PrincipalPartsFunctoriality (A := A) (A' := A') (B := B) (B' := B')
      (M := M) (M' := M')) :
    principalPartsFunctorialitySequenceCompatible F := by
  have hprojection (x :
      PrincipalParts (R := A) (S := B) (M := M) 1) :
      principalPartsProjection (R := A') (S := B') (M := M') 1
          (F.map 1 x) =
        F.f (principalPartsProjection (R := A) (S := B) (M := M) 1 x) := by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    induction z using Finsupp.induction_linear with
    | zero =>
        simp [F.map_zero]
    | add z w hz hw =>
        simp only [map_add, F.map_add, hz, hw]
    | single m c =>
        rw [← Finsupp.smul_single_one m c]
        rw [(Submodule.mkQ _).map_smul]
        rw [F.map_smul]
        change principalPartsProjection (R := A') (S := B') (M := M') 1
            ((algebraMap B B') c •
              F.map 1 (principalPartsGenerator (R := A) (S := B) 1 m)) =
          F.f (principalPartsProjection (R := A) (S := B) (M := M) 1
            (c • principalPartsGenerator (R := A) (S := B) 1 m))
        rw [F.map_generator]
        rw [map_smul, principalPartsProjection_on_generator]
        rw [map_smul, principalPartsProjection_on_generator, F.f_smul]
  have hpreimage (x :
      (ModuleOfDifferentials A B) ⊗[B] M) :
      ∃ y : (ModuleOfDifferentials A' B') ⊗[B'] M',
        principalPartsSequenceLeft (R := A') (S := B') (M := M') y =
          F.map 1 (principalPartsSequenceLeft (R := A) (S := B) (M := M) x) := by
    apply (principalParts_sequence_exact (R := A') (S := B') (M := M')
      (F.map 1 (principalPartsSequenceLeft
        (R := A) (S := B) (M := M) x))).mp
    rw [hprojection]
    have hzero :
        principalPartsProjection (R := A) (S := B) (M := M) 1
            (principalPartsSequenceLeft (R := A) (S := B) (M := M) x) = 0 :=
      (principalParts_sequence_exact (R := A) (S := B) (M := M)
        (principalPartsSequenceLeft (R := A) (S := B) (M := M) x)).2 ⟨x, rfl⟩
    rw [hzero, map_zero]
  let chosen :
      (ModuleOfDifferentials A B) ⊗[B] M →
        (ModuleOfDifferentials A' B') ⊗[B'] M' :=
    fun x => Classical.choose (hpreimage x)
  have hchosen (x : (ModuleOfDifferentials A B) ⊗[B] M) :
      principalPartsSequenceLeft (R := A') (S := B') (M := M') (chosen x) =
        F.map 1 (principalPartsSequenceLeft (R := A) (S := B) (M := M) x) :=
    Classical.choose_spec (hpreimage x)
  let φ : (ModuleOfDifferentials A B) ⊗[B] M →+
      (ModuleOfDifferentials A' B') ⊗[B'] M' :=
    { toFun := chosen
      map_zero' := by
        apply principalParts_sequence_left_injective
          (R := A') (S := B') (M := M')
        have hzero := hchosen (0 :
          (ModuleOfDifferentials A B) ⊗[B] M)
        calc
          principalPartsSequenceLeft (R := A') (S := B') (M := M') (chosen 0) =
              F.map 1 (principalPartsSequenceLeft (R := A) (S := B) (M := M) 0) := hzero
          _ = F.map 1 0 := by rw [map_zero]
          _ = 0 := F.map_zero 1
          _ = principalPartsSequenceLeft (R := A') (S := B') (M := M') 0 :=
            (principalPartsSequenceLeft (R := A') (S := B') (M := M')).map_zero.symm
      map_add' := by
        intro x y
        apply principalParts_sequence_left_injective
          (R := A') (S := B') (M := M')
        have hxy := hchosen (x + y)
        have hx := hchosen x
        have hy := hchosen y
        calc
          principalPartsSequenceLeft (R := A') (S := B') (M := M') (chosen (x + y)) =
              F.map 1 (principalPartsSequenceLeft (R := A) (S := B) (M := M) (x + y)) := hxy
          _ = F.map 1
              (principalPartsSequenceLeft (R := A) (S := B) (M := M) x +
                principalPartsSequenceLeft (R := A) (S := B) (M := M) y) := by
              rw [map_add]
          _ = F.map 1 (principalPartsSequenceLeft
              (R := A) (S := B) (M := M) x) +
              F.map 1 (principalPartsSequenceLeft
                (R := A) (S := B) (M := M) y) := F.map_add 1 _ _
          _ = principalPartsSequenceLeft (R := A') (S := B') (M := M') (chosen x) +
              principalPartsSequenceLeft (R := A') (S := B') (M := M') (chosen y) :=
            congrArg₂ (· + ·) hx.symm hy.symm
          _ = principalPartsSequenceLeft (R := A') (S := B') (M := M')
              (chosen x + chosen y) := ((principalPartsSequenceLeft
                (R := A') (S := B') (M := M')).map_add _ _).symm }
  have hφ (x : (ModuleOfDifferentials A B) ⊗[B] M) :
      principalPartsSequenceLeft (R := A') (S := B') (M := M') (φ x) =
        F.map 1 (principalPartsSequenceLeft (R := A) (S := B) (M := M) x) := by
    simpa [φ] using hchosen x
  refine ⟨φ, ?_, hprojection⟩
  intro x
  exact (hφ x).symm

end PrincipalPartsFunctoriality

section PrincipalPartsFunctorialityComposition

variable {A A' A'' B B' B'' M M' M'' : Type*}
  [CommRing A] [CommRing A'] [CommRing A'']
  [CommRing B] [CommRing B'] [CommRing B'']
  [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B']
  [Algebra A' A''] [Algebra B' B''] [Algebra A'' B'']
  [Algebra A A''] [Algebra B B'']
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  [AddCommGroup M'] [Module B' M'] [Module A' M'] [IsScalarTower A' B' M']
  [AddCommGroup M''] [Module B'' M''] [Module A'' M'']
  [IsScalarTower A'' B'' M'']

/-- Composition of two compatible principal-parts systems, including the
source-level map and the maps in every order. -/
structure PrincipalPartsFunctorialityComposition
    (F : PrincipalPartsFunctoriality
      (A := A) (A' := A') (B := B) (B' := B') (M := M) (M' := M'))
    (G : PrincipalPartsFunctoriality
      (A := A') (A' := A'') (B := B') (B' := B'') (M := M') (M' := M'')) where
  composed : PrincipalPartsFunctoriality
    (A := A) (A' := A'') (B := B) (B' := B'') (M := M) (M' := M'')
  f_eq : composed.f =
    (G.f.comp F.f)
  map_eq : ∀ k x, composed.map k x = G.map k (F.map k x)

theorem principalParts_functoriality_composition_exists
    (F : PrincipalPartsFunctoriality
      (A := A) (A' := A') (B := B) (B' := B') (M := M) (M' := M'))
    (G : PrincipalPartsFunctoriality
      (A := A') (A' := A'') (B := B') (B' := B'') (M := M') (M' := M'')) :
    Nonempty (PrincipalPartsFunctorialityComposition
      (A := A) (A' := A') (A'' := A'') (B := B) (B' := B') (B'' := B'')
      (M := M) (M' := M') (M'' := M'') F G) := by
  sorry

theorem principalParts_functoriality_composition_sequence_compatible
    (C : PrincipalPartsFunctorialityComposition
      (A := A) (A' := A') (A'' := A'') (B := B) (B' := B') (B'' := B'')
      (M := M) (M' := M') (M'' := M'') F G) :
    principalPartsFunctorialitySequenceCompatible C.composed := by
  exact principalParts_functoriality_sequence_compatible C.composed

end PrincipalPartsFunctorialityComposition

section PrincipalPartsBaseChange

variable {A A' B M : Type*}
  [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B]
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]

/-- The base-change statement for principal parts, with the tensor-product
convention used by Mathlib (`B ⊗[A] A'`).  The required target module
structures are explicit parameters because Mathlib deliberately does not
install all tensor-product algebra actions globally.
-/
structure PrincipalPartsBaseChangeData (k : ℕ) where
  B' : Type u'
  M' : Type u'
  [commRing_B' : CommRing B']
  [algebra_A'_B' : Algebra A' B']
  [addCommGroup_M' : AddCommGroup M']
  [module_B'_M' : Module B' M']
  [module_A'_M' : Module A' M']
  [module_A_M' : Module A M']
  [tower_A'_B'_M' : IsScalarTower A' B' M']
  [module_B'_left : Module B' (PrincipalParts (R := A) (S := B) (M := M) k ⊗[A] A')]
  identify_B' : B' ≃+* (B ⊗[A] A')
  identify_M' : M' ≃ₗ[A] (M ⊗[A] A')
  equivalence :
    PrincipalParts (R := A) (S := B) (M := M) k ⊗[A] A' ≃ₗ[B']
      PrincipalParts (R := A') (S := B') (M := M') k

theorem principalParts_base_change (k : ℕ) :
    Nonempty (PrincipalPartsBaseChangeData (A := A) (A' := A') (B := B) (M := M) k) := by
  sorry

end PrincipalPartsBaseChange

/-! ## The diagonal presentation -/

section PrincipalPartsDiagonal

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M]

def diagonalMultiplication : S ⊗[R] S →ₐ[R] S :=
  Algebra.TensorProduct.lmul' R

def diagonalIdeal : Ideal (S ⊗[R] S) :=
  RingHom.ker (diagonalMultiplication (R := R) (S := S)).toRingHom

def diagonalGenerator (g : S) : S ⊗[R] S :=
  g ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] g

theorem diagonalIdeal_eq_span_generators :
    diagonalIdeal (R := R) (S := S) =
      Ideal.span (Set.range (diagonalGenerator (R := R) (S := S))) := by
  sorry

def diagonalHigherRelation (k : ℕ) (g : Fin (k + 1) → S) (m : M) : S ⊗[R] M := by
  classical
  exact (Finset.univ : Finset (Finset (Fin (k + 1)))).sum (fun t =>
    ((-1 : S) ^ t.card) •
      (((Finset.univ \ t).prod g) ⊗ₜ[R] ((t.prod g) • m)))

def diagonalPowerSubmodule (k : ℕ) : Submodule S (S ⊗[R] M) :=
  Submodule.span S (Set.range (fun p : (Fin (k + 1) → S) × M =>
    diagonalHigherRelation (R := R) (S := S) k p.1 p.2))

abbrev DiagonalPrincipalParts (k : ℕ) : Type _ :=
  (S ⊗[R] M) ⧸ diagonalPowerSubmodule (R := R) (S := S) k

noncomputable def diagonalUniversalLinearMap (k : ℕ) :
    M →ₗ[R] DiagonalPrincipalParts (R := R) (S := S) (M := M) k :=
  (Submodule.mkQ (diagonalPowerSubmodule (R := R) (S := S) k)).restrictScalars R |>.comp
    (TensorProduct.AlgebraTensorModule.mk R S S M 1)

theorem principalParts_diagonal_equiv_exists (k : ℕ) :
    ∃ e : PrincipalParts (R := R) (S := S) (M := M) k ≃ₗ[S]
        DiagonalPrincipalParts (R := R) (S := S) (M := M) k,
      ∀ m,
        e (principalPartsGenerator (R := R) (S := S) k m) =
          diagonalUniversalLinearMap (R := R) (S := S) (M := M) k m := by
  sorry

noncomputable def principalPartsDiagonalEquiv (k : ℕ) :
    PrincipalParts (R := R) (S := S) (M := M) k ≃ₗ[S]
      DiagonalPrincipalParts (R := R) (S := S) (M := M) k :=
  Classical.choose (principalParts_diagonal_equiv_exists (R := R) (S := S) (M := M) k)

theorem principalPartsDiagonalEquiv_on_generator (k : ℕ) (m : M) :
    principalPartsDiagonalEquiv (R := R) (S := S) (M := M) k
        (principalPartsGenerator (R := R) (S := S) (M := M) k m) =
      diagonalUniversalLinearMap (R := R) (S := S) (M := M) k m :=
  (Classical.choose_spec
    (principalParts_diagonal_equiv_exists (R := R) (S := S) (M := M) k)) m

end PrincipalPartsDiagonal

/-! ## Differential forms, generators, localization, and tensor products -/

section DifferentialFormsAndGenerators

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem deRham_differential_is_differentialOperator (i : ℕ) :
    @IsDifferentialOperator A B (deRhamTerm A B i) (deRhamTerm A B (i + 1))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (deRhamTerm.moduleA (A := A) (B := B) i)
      (deRhamTerm.moduleA (A := A) (B := B) (i + 1))
      (deRhamTerm.isScalarTower (A := A) (B := B) i)
      (deRhamTerm.isScalarTower (A := A) (B := B) (i + 1))
      1 (deRhamDifferential (A := A) (B := B) i) := by
  sorry

theorem differentialOperator_check_on_algebra_generators
    {I : Type*} (g : I → B)
    (hg : Algebra.adjoin A (Set.range g) = ⊤)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] [Module A M] [Module A N]
    [IsScalarTower A B M] [IsScalarTower A B N]
    (k : ℕ) (hk : 1 ≤ k) (D : M →ₗ[A] N)
    (hD : ∀ i, IsDifferentialOperator (R := A) (S := B) (k - 1)
      (differentialOperatorCommutator (R := A) (S := B) D (g i))) :
    IsDifferentialOperator (R := A) (S := B) k D := by
  sorry

end DifferentialFormsAndGenerators

section DifferentialOperatorLocalization

variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [AddCommGroup N]
  [Module B M] [Module B N] [Module A M] [Module A N]
  [IsScalarTower A B M] [IsScalarTower A B N]

theorem differentialOperator_localization_unique (T : Submonoid B) (k : ℕ)
    (D : differentialOperatorSubmodule (R := A) (S := B) (M := M) (N := N) k) :
    ∃! E : differentialOperatorSubmodule (R := A) (S := B) k
        (M := LocalizedModule T M) (N := LocalizedModule T N),
      ∀ m,
        E.1 (LocalizedModule.mkLinearMap T M m) =
          LocalizedModule.mkLinearMap T N (D.1 m) := by
  sorry

noncomputable def localizedDifferentialOperator (T : Submonoid B) (k : ℕ)
    (D : differentialOperatorSubmodule (R := A) (S := B) (M := M) (N := N) k) :
    differentialOperatorSubmodule (R := A) (S := B) k
      (M := LocalizedModule T M) (N := LocalizedModule T N) :=
  Classical.choose (differentialOperator_localization_unique (A := A) (B := B)
    (M := M) (N := N) T k D)

theorem localizedDifferentialOperator_extends (T : Submonoid B) (k : ℕ)
    (D : differentialOperatorSubmodule (R := A) (S := B) (M := M) (N := N) k) (m : M) :
    (localizedDifferentialOperator (A := A) (B := B) (M := M) (N := N) T k D).1
        (LocalizedModule.mkLinearMap T M m) =
      LocalizedModule.mkLinearMap T N (D.1 m) :=
  (Classical.choose_spec (differentialOperator_localization_unique (A := A) (B := B)
    (M := M) (N := N) T k D)).1 m

end DifferentialOperatorLocalization

section DifferentialOperatorTensorProduct

variable {R A B M M' N : Type*}
  [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
  [Module A M] [Module A M'] [Module R M] [Module R M']
  [IsScalarTower R A M] [IsScalarTower R A M']
  [Module B N] [Module R N] [IsScalarTower R B N]

def tensorProductDifferentialOperator (D : M →ₗ[R] M') :
    M ⊗[R] N →ₗ[R] M' ⊗[R] N :=
  TensorProduct.map D (LinearMap.id : N →ₗ[R] N)

theorem differentialOperator_tensor_product_base_change
    (k : ℕ) (D : differentialOperatorSubmodule (R := R) (S := A) k
      (M := M) (N := M'))
    [Module (A ⊗[R] B) (M ⊗[R] N)]
    [Module (A ⊗[R] B) (M' ⊗[R] N)]
    [IsScalarTower R (A ⊗[R] B) (M ⊗[R] N)]
    [IsScalarTower R (A ⊗[R] B) (M' ⊗[R] N)] :
    IsDifferentialOperator (R := R) (S := A ⊗[R] B) k
      (tensorProductDifferentialOperator (R := R) (M := M) (M' := M')
        (N := N) D.1) := by
  sorry

end DifferentialOperatorTensorProduct

end
end Formalization.Books.Algebra.Unit133
