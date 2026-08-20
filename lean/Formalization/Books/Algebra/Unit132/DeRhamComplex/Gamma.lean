import Formalization.Books.Algebra.Unit132.DeRhamComplex.Core

namespace Formalization.Books.Algebra.Unit132

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section
/-! ## The factorization construction in positive degrees -/

/-- The product of a finite family of degree-one exterior terms. -/
def deRhamPureWedgeTerms
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
    (p : ℕ) → (Fin p → deRhamTerm A B 1) → deRhamTerm A B p
  | 0, _ => ⟨1, SetLike.GradedOne.one_mem⟩
  | n + 1, ω => by
      simpa [Nat.add_comm] using
        deRhamWedge (A := A) (B := B) 1 n (ω 0)
          (deRhamPureWedgeTerms (A := A) (B := B) n (Matrix.vecTail ω))

/-- Insert the degree-one differential in the `i`th position of a pure wedge. -/
def deRhamWedgeWithDifferential
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
    (p : ℕ) → (Fin p → deRhamTerm A B 1) → Fin p → deRhamTerm A B (p + 1)
  | 0, _, i => Fin.elim0 i
  | n + 1, ω, i =>
      Fin.cases
        (by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            deRhamWedge (A := A) (B := B) 2 n
              (deRhamDifferential (A := A) (B := B) 1 (ω 0))
              (deRhamPureWedgeTerms (A := A) (B := B) n (Matrix.vecTail ω)))
        (fun j => by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            deRhamWedge (A := A) (B := B) 1 (n + 1) (ω 0)
              (deRhamWedgeWithDifferential (A := A) (B := B) n
                (Matrix.vecTail ω) j))
        i

/-- The alternating formula for the map `γ` in the source. -/
def deRhamGammaPureFormula
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) (ω : Fin p → deRhamTerm A B 1) : deRhamTerm A B (p + 1) :=
  ∑ i : Fin p, (-1 : A) ^ i.1 •
    deRhamWedgeWithDifferential (A := A) (B := B) p ω i

private theorem deRhamGamma_sum_smul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) [DecidableEq (Fin p)] (ω : Fin p → deRhamTerm A B 1)
    (i : Fin p) (c : A) (x : deRhamTerm A B 1) :
    (∑ j : Fin p, (-1 : A) ^ j.1 •
      (c • deRhamWedgeWithDifferential (A := A) (B := B) p
        (Function.update ω i x) j)) =
      c • (∑ j : Fin p, (-1 : A) ^ j.1 •
        deRhamWedgeWithDifferential (A := A) (B := B) p
          (Function.update ω i x) j) := by
  calc
    (∑ j : Fin p, (-1 : A) ^ j.1 •
        (c • deRhamWedgeWithDifferential (A := A) (B := B) p
          (Function.update ω i x) j)) =
      ∑ j : Fin p, c • ((-1 : A) ^ j.1 •
        deRhamWedgeWithDifferential (A := A) (B := B) p
          (Function.update ω i x) j) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (-1 : A) ^ j.1 •
              (c • deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j) =
            ((-1 : A) ^ j.1 * c) •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j := smul_smul _ _ _
          _ = (c * (-1 : A) ^ j.1) •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j := by rw [mul_comm]
          _ = c • ((-1 : A) ^ j.1 •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j) := (smul_smul _ _ _).symm
    _ = c • (∑ j : Fin p, (-1 : A) ^ j.1 •
          deRhamWedgeWithDifferential (A := A) (B := B) p
            (Function.update ω i x) j) := by
      exact (Finset.smul_sum (r := c)
        (f := fun j : Fin p => (-1 : A) ^ j.1 •
          deRhamWedgeWithDifferential (A := A) (B := B) p
            (Function.update ω i x) j) (s := Finset.univ)).symm

private theorem tail_update_zero
    {X : Type*} (n : ℕ) (ω : Fin (n + 1) → X) (x : X) :
    Matrix.vecTail (Function.update ω 0 x) = Matrix.vecTail ω := by
  funext i
  simp [Matrix.vecTail]

private theorem tail_update_succ
    {X : Type*} (n : ℕ) (ω : Fin (n + 1) → X) (i : Fin n) (x : X) :
    Matrix.vecTail (Function.update ω i.succ x) =
      Function.update (Matrix.vecTail ω) i x := by
  funext j
  by_cases h : i = j
  · subst h
    simp [Matrix.vecTail]
  · simp [Matrix.vecTail, Ne.symm h]

private theorem deRhamTerm_coe_cast
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {n m : ℕ} (h : n = m) (x : deRhamTerm A B n) :
    ((cast (congrArg (fun k => (deRhamTerm A B k : Type _)) h) x :
      deRhamTerm A B m) : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  cases h
  rfl

private theorem coe_smul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (c : B) (x : deRhamTerm A B n) :
    ((c • x : deRhamTerm A B n) :
      ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      c • (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  rfl

private theorem pure_succ_val
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1) :
    (deRhamPureWedgeTerms (A := A) (B := B) (n + 1) ω :
        ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      (deRhamWedge (A := A) (B := B) 1 n (ω 0)
        (deRhamPureWedgeTerms (A := A) (B := B) n (Matrix.vecTail ω)) :
        ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  simp only [deRhamPureWedgeTerms]
  apply deRhamTerm_coe_cast (Nat.add_comm 1 n)

private theorem pure_add
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
  ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
    (i : Fin n) (x y : deRhamTerm A B 1),
    deRhamPureWedgeTerms (A := A) (B := B) n
        (Function.update ω i (x + y)) =
      deRhamPureWedgeTerms (A := A) (B := B) n
          (Function.update ω i x) +
        deRhamPureWedgeTerms (A := A) (B := B) n
          (Function.update ω i y) := by
  intro n
  induction n with
  | zero => intro ω i; exact Fin.elim0 i
  | succ n ih =>
      intro ω i x y
      refine Fin.cases ?_ (fun j => ?_) i
      · apply Subtype.ext
        change (↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
            (Function.update ω 0 (x + y))) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (Function.update ω 0 x)) : ExteriorAlgebra B (ModuleOfDifferentials A B)) +
          ↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (Function.update ω 0 y))
        rw [pure_succ_val, pure_succ_val, pure_succ_val,
          tail_update_zero, tail_update_zero, tail_update_zero]
        simp [deRhamWedge, Function.update]
      ·
        apply Subtype.ext
        change (↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
            (Function.update ω j.succ (x + y))) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (Function.update ω j.succ x)) : ExteriorAlgebra B (ModuleOfDifferentials A B)) +
          ↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (Function.update ω j.succ y))
        rw [pure_succ_val, pure_succ_val, pure_succ_val,
          tail_update_succ, tail_update_succ, tail_update_succ,
          ih (Matrix.vecTail ω) j x y]
        have hzero : (0 : Fin (n + 1)) ≠ j.succ := by
          intro h
          exact Fin.succ_ne_zero j h.symm
        simp [deRhamWedge, Function.update, hzero]
        rw [mul_add]

private theorem pure_smul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
  ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
    (i : Fin n) (c : A) (x : deRhamTerm A B 1),
    deRhamPureWedgeTerms (A := A) (B := B) n
        (Function.update ω i (c • x)) =
      c • deRhamPureWedgeTerms (A := A) (B := B) n
        (Function.update ω i x) := by
  intro n
  induction n with
  | zero => intro ω i; exact Fin.elim0 i
  | succ n ih =>
      intro ω i c x
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [← IsScalarTower.algebraMap_smul B c
          (deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
            (Function.update ω 0 x))]
        apply Subtype.ext
        change (↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
            (Function.update ω 0 (c • x))) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (↑((algebraMap A B c) • deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (Function.update ω 0 x)) : ExteriorAlgebra B (ModuleOfDifferentials A B))
        rw [coe_smul, pure_succ_val, pure_succ_val, tail_update_zero, tail_update_zero]
        simp [deRhamWedge, Function.update]
      ·
        rw [← IsScalarTower.algebraMap_smul B c
          (deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
            (Function.update ω j.succ x))]
        apply Subtype.ext
        change (↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
            (Function.update ω j.succ (c • x))) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (↑((algebraMap A B c) • deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (Function.update ω j.succ x)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B))
        rw [coe_smul, pure_succ_val, pure_succ_val, tail_update_succ, tail_update_succ,
          ih (Matrix.vecTail ω) j c x]
        have hzero : (0 : Fin (n + 1)) ≠ j.succ := by
          intro h
          exact Fin.succ_ne_zero j h.symm
        simp [deRhamWedge, Function.update, hzero]

private theorem diff_zero_val
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1) :
    (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1) ω 0 :
        ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      (deRhamWedge (A := A) (B := B) 2 n
        (deRhamDifferential (A := A) (B := B) 1 (ω 0))
        (deRhamPureWedgeTerms (A := A) (B := B) n (Matrix.vecTail ω)) :
        ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  simp only [deRhamWedgeWithDifferential]
  apply deRhamTerm_coe_cast (Nat.add_comm 2 n)

private theorem diff_succ_val
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1) (j : Fin n) :
    (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1) ω j.succ :
        ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      (deRhamWedge (A := A) (B := B) 1 (n + 1) (ω 0)
        (deRhamWedgeWithDifferential (A := A) (B := B) n
          (Matrix.vecTail ω) j) :
        ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  simp only [deRhamWedgeWithDifferential]
  apply deRhamTerm_coe_cast (by simp [Nat.add_left_comm])

private theorem diff_add
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
  ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
    (i : Fin n) (x y : deRhamTerm A B 1) (j : Fin n),
    deRhamWedgeWithDifferential (A := A) (B := B) n
        (Function.update ω i (x + y)) j =
      deRhamWedgeWithDifferential (A := A) (B := B) n
          (Function.update ω i x) j +
        deRhamWedgeWithDifferential (A := A) (B := B) n
          (Function.update ω i y) j := by
  intro n
  induction n with
  | zero => intro ω i; exact Fin.elim0 i
  | succ n ih =>
      intro ω i x y j
      refine Fin.cases ?_ (fun k => ?_) i
      · refine Fin.cases ?_ (fun l => ?_) j
        · apply Subtype.ext
          change (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω 0 (x + y)) 0) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
                (Function.update ω 0 x) 0) : ExteriorAlgebra B (ModuleOfDifferentials A B)) +
            ↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
                (Function.update ω 0 y) 0)
          rw [diff_zero_val, diff_zero_val, diff_zero_val]
          simp [deRhamWedge, Function.update, tail_update_zero]
        · apply Subtype.ext
          change (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω 0 (x + y)) l.succ) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
                (Function.update ω 0 x) l.succ) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) +
            ↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
                (Function.update ω 0 y) l.succ)
          rw [diff_succ_val, diff_succ_val, diff_succ_val]
          simp [deRhamWedge, Function.update, tail_update_zero]
      · refine Fin.cases ?_ (fun l => ?_) j
        · apply Subtype.ext
          change (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω k.succ (x + y)) 0) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
                (Function.update ω k.succ x) 0) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) +
            ↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
                (Function.update ω k.succ y) 0)
          rw [diff_zero_val, diff_zero_val, diff_zero_val]
          rw [tail_update_succ, tail_update_succ, tail_update_succ]
          have hzero : (0 : Fin (n + 1)) ≠ k.succ := by
            intro h
            exact Fin.succ_ne_zero k h.symm
          simp [deRhamWedge, Function.update, hzero, pure_add]
          rw [mul_add]
        · apply Subtype.ext
          change (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω k.succ (x + y)) l.succ) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
                (Function.update ω k.succ x) l.succ) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) +
            ↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
                (Function.update ω k.succ y) l.succ)
          rw [diff_succ_val, diff_succ_val, diff_succ_val]
          rw [tail_update_succ, tail_update_succ, tail_update_succ]
          rw [ih (Matrix.vecTail ω) k x y]
          have hzero : (0 : Fin (n + 1)) ≠ k.succ := by
            intro h
            exact Fin.succ_ne_zero k h.symm
          simp [deRhamWedge, Function.update, hzero]
          rw [mul_add]

private theorem wedge_smul_A_coe
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (r s : ℕ) (u : deRhamTerm A B r) (c : A) (v : deRhamTerm A B s) :
    ((deRhamWedge (A := A) (B := B) r s u (c • v) :
        deRhamTerm A B (r + s)) :
        ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      (algebraMap A B c) •
        ((deRhamWedge (A := A) (B := B) r s u v :
          deRhamTerm A B (r + s)) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  rw [← IsScalarTower.algebraMap_smul B c v, map_smul, coe_smul]

private theorem wedge_smul_A_coe_left
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (r s : ℕ) (u : deRhamTerm A B r) (c : A) (v : deRhamTerm A B s) :
    ((deRhamWedge (A := A) (B := B) r s (c • u) v :
        deRhamTerm A B (r + s)) :
        ExteriorAlgebra B (ModuleOfDifferentials A B)) =
      (algebraMap A B c) •
        ((deRhamWedge (A := A) (B := B) r s u v :
          deRhamTerm A B (r + s)) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
  rw [← IsScalarTower.algebraMap_smul B c u, map_smul]
  rfl

private theorem diff_smul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
  ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
    (i : Fin n) (c : A) (x : deRhamTerm A B 1) (j : Fin n),
    deRhamWedgeWithDifferential (A := A) (B := B) n
        (Function.update ω i (c • x)) j =
      c • deRhamWedgeWithDifferential (A := A) (B := B) n
        (Function.update ω i x) j := by
  intro n
  induction n with
  | zero => intro ω i; exact Fin.elim0 i
  | succ n ih =>
      intro ω i c x j
      refine Fin.cases ?_ (fun k => ?_) i
      · refine Fin.cases ?_ (fun l => ?_) j
        · apply Subtype.ext
          rw [← IsScalarTower.algebraMap_smul B c
            (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω 0 x) 0)]
          change (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω 0 (c • x)) 0) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑((algebraMap A B c) • deRhamWedgeWithDifferential
                (A := A) (B := B) (n + 1) (Function.update ω 0 x) 0) :
              ExteriorAlgebra B (ModuleOfDifferentials A B))
          rw [coe_smul, diff_zero_val n (Function.update ω 0 (c • x)),
            diff_zero_val n (Function.update ω 0 x)]
          have hhead_c0 : Function.update ω 0 (c • x) 0 = c • x := by
            simp [Function.update]
          have hhead_x0 : Function.update ω 0 x 0 = x := by
            simp [Function.update]
          have htail_c0 : Matrix.vecTail (Function.update ω 0 (c • x)) =
              Matrix.vecTail ω := tail_update_zero n ω (c • x)
          have htail_x0 : Matrix.vecTail (Function.update ω 0 x) =
              Matrix.vecTail ω := tail_update_zero n ω x
          rw [hhead_c0, hhead_x0, htail_c0, htail_x0]
          rw [map_smul]
          rw [← IsScalarTower.algebraMap_smul B c
            ((deRhamDifferential (A := A) (B := B) 1) x)]
          exact wedge_smul_A_coe_left 2 n
            ((deRhamDifferential (A := A) (B := B) 1) x) c
            (deRhamPureWedgeTerms (A := A) (B := B) n
              (Matrix.vecTail ω))
        · apply Subtype.ext
          rw [← IsScalarTower.algebraMap_smul B c
            (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω 0 x) l.succ)]
          change (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω 0 (c • x)) l.succ) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑((algebraMap A B c) • deRhamWedgeWithDifferential
                (A := A) (B := B) (n + 1) (Function.update ω 0 x) l.succ) :
              ExteriorAlgebra B (ModuleOfDifferentials A B))
          rw [coe_smul, diff_succ_val n (Function.update ω 0 (c • x)) l,
            diff_succ_val n (Function.update ω 0 x) l]
          have hhead_c0 : Function.update ω 0 (c • x) 0 = c • x := by
            simp [Function.update]
          have hhead_x0 : Function.update ω 0 x 0 = x := by
            simp [Function.update]
          have htail_c0 : Matrix.vecTail (Function.update ω 0 (c • x)) =
              Matrix.vecTail ω := tail_update_zero n ω (c • x)
          have htail_x0 : Matrix.vecTail (Function.update ω 0 x) =
              Matrix.vecTail ω := tail_update_zero n ω x
          rw [hhead_c0, hhead_x0, htail_c0, htail_x0]
          exact wedge_smul_A_coe_left 1 (n + 1) x c
            (deRhamWedgeWithDifferential (A := A) (B := B) n
              (Matrix.vecTail ω) l)
      · refine Fin.cases ?_ (fun l => ?_) j
        · apply Subtype.ext
          rw [← IsScalarTower.algebraMap_smul B c
            (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω k.succ x) 0)]
          change (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω k.succ (c • x)) 0) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑((algebraMap A B c) • deRhamWedgeWithDifferential
                (A := A) (B := B) (n + 1) (Function.update ω k.succ x) 0) :
              ExteriorAlgebra B (ModuleOfDifferentials A B))
          rw [coe_smul]
          rw [diff_zero_val n (Function.update ω k.succ (c • x))]
          rw [diff_zero_val n (Function.update ω k.succ x)]
          have htail_c : Matrix.vecTail (Function.update ω k.succ (c • x)) =
              Function.update (Matrix.vecTail ω) k (c • x) :=
            tail_update_succ n ω k (c • x)
          have htail_x : Matrix.vecTail (Function.update ω k.succ x) =
              Function.update (Matrix.vecTail ω) k x :=
            tail_update_succ n ω k x
          have hzero : (0 : Fin (n + 1)) ≠ k.succ := by
            intro h
            exact Fin.succ_ne_zero k h.symm
          have hzero' : k.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero k
          have hhead_c : Function.update ω k.succ (c • x) 0 = ω 0 := by
            simp [Function.update, hzero]
          have hhead_x : Function.update ω k.succ x 0 = ω 0 := by
            simp [Function.update, hzero]
          have hpure_c : deRhamPureWedgeTerms (A := A) (B := B) n
              (Matrix.vecTail (Function.update ω k.succ (c • x))) =
              deRhamPureWedgeTerms (A := A) (B := B) n
                (Function.update (Matrix.vecTail ω) k (c • x)) :=
            congrArg (deRhamPureWedgeTerms (A := A) (B := B) n) htail_c
          have hpure_x : deRhamPureWedgeTerms (A := A) (B := B) n
              (Matrix.vecTail (Function.update ω k.succ x)) =
              deRhamPureWedgeTerms (A := A) (B := B) n
                (Function.update (Matrix.vecTail ω) k x) :=
            congrArg (deRhamPureWedgeTerms (A := A) (B := B) n) htail_x
          simp only [hhead_c, hhead_x, hpure_c, hpure_x, pure_smul]
          exact wedge_smul_A_coe 2 n
            ((deRhamDifferential (A := A) (B := B) 1) (ω 0)) c
            (deRhamPureWedgeTerms (A := A) (B := B) n
              (Function.update (Matrix.vecTail ω) k x))
        · apply Subtype.ext
          rw [← IsScalarTower.algebraMap_smul B c
            (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω k.succ x) l.succ)]
          change (↑(deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
              (Function.update ω k.succ (c • x)) l.succ) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑((algebraMap A B c) • deRhamWedgeWithDifferential
                (A := A) (B := B) (n + 1) (Function.update ω k.succ x) l.succ) :
              ExteriorAlgebra B (ModuleOfDifferentials A B))
          rw [coe_smul, diff_succ_val n (Function.update ω k.succ (c • x)) l,
            diff_succ_val n (Function.update ω k.succ x) l,
            tail_update_succ n ω k (c • x), tail_update_succ n ω k x]
          rw [ih (Matrix.vecTail ω) k c x l]
          have hzero : (0 : Fin (n + 1)) ≠ k.succ := by
            intro h
            exact Fin.succ_ne_zero k h.symm
          have hhead_c : Function.update ω k.succ (c • x) 0 = ω 0 := by
            simp [Function.update, hzero]
          have hhead_x : Function.update ω k.succ x 0 = ω 0 := by
            simp [Function.update, hzero]
          simp only [hhead_c, hhead_x]
          exact wedge_smul_A_coe 1 (n + 1) (ω 0) c
            (deRhamWedgeWithDifferential (A := A) (B := B) n
              (Function.update (Matrix.vecTail ω) k x) l)

theorem deRhamGamma_exists
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Nonempty
      {γ : PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1) →ₗ[A]
          deRhamTerm A B (p + 1) //
        ∀ ω, γ (PiTensorProduct.tprod A ω) =
      deRhamGammaPureFormula (A := A) (B := B) p ω} := by
  classical
  let f : MultilinearMap A (fun _ : Fin p => deRhamTerm A B 1)
      (deRhamTerm A B (p + 1)) :=
    { toFun := deRhamGammaPureFormula (A := A) (B := B) p
      map_update_add' := by
        intro _ ω i x y
        have update_eq_update : ∀ z : deRhamTerm A B 1,
            Function.update ω i z =
              @Function.update (Fin p) (fun _ => deRhamTerm A B 1)
                (instDecidableEqFin p) ω i z := by
          intro z
          funext k
          by_cases h : k = i <;> simp [Function.update, h]
        simp only [deRhamGammaPureFormula]
        calc
          (∑ j : Fin p, (-1 : A) ^ j.1 •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i (x + y)) j) =
            ∑ j : Fin p, (-1 : A) ^ j.1 •
              (deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j +
               deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i y) j) := by
              apply Finset.sum_congr rfl
              intro j hj
              apply congrArg (fun z => (-1 : A) ^ j.1 • z)
              rw [update_eq_update, update_eq_update, update_eq_update]
              exact diff_add p ω i x y j
          _ = (∑ j : Fin p, (-1 : A) ^ j.1 •
                deRhamWedgeWithDifferential (A := A) (B := B) p
                  (Function.update ω i x) j) +
              ∑ j : Fin p, (-1 : A) ^ j.1 •
                deRhamWedgeWithDifferential (A := A) (B := B) p
                  (Function.update ω i y) j := by
            calc
              (∑ j : Fin p, (-1 : A) ^ j.1 •
                  (deRhamWedgeWithDifferential (A := A) (B := B) p
                    (Function.update ω i x) j +
                   deRhamWedgeWithDifferential (A := A) (B := B) p
                    (Function.update ω i y) j)) =
                ∑ j : Fin p, ((-1 : A) ^ j.1 •
                  deRhamWedgeWithDifferential (A := A) (B := B) p
                    (Function.update ω i x) j +
                  (-1 : A) ^ j.1 •
                    deRhamWedgeWithDifferential (A := A) (B := B) p
                      (Function.update ω i y) j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    exact smul_add ((-1 : A) ^ j.1)
                      (deRhamWedgeWithDifferential (A := A) (B := B) p
                        (Function.update ω i x) j)
                      (deRhamWedgeWithDifferential (A := A) (B := B) p
                        (Function.update ω i y) j)
              _ = (∑ j : Fin p, (-1 : A) ^ j.1 •
                    deRhamWedgeWithDifferential (A := A) (B := B) p
                      (Function.update ω i x) j) +
                  ∑ j : Fin p, (-1 : A) ^ j.1 •
                    deRhamWedgeWithDifferential (A := A) (B := B) p
                      (Function.update ω i y) j := by
                    exact Finset.sum_add_distrib
      map_update_smul' := by
        intro _ ω i c x
        have update_eq_update : ∀ z : deRhamTerm A B 1,
            Function.update ω i z =
              @Function.update (Fin p) (fun _ => deRhamTerm A B 1)
                (instDecidableEqFin p) ω i z := by
          intro z
          funext k
          by_cases h : k = i <;> simp [Function.update, h]
        simp only [deRhamGammaPureFormula]
        calc
          (∑ j : Fin p, (-1 : A) ^ j.1 •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i (c • x)) j) =
            ∑ j : Fin p, (-1 : A) ^ j.1 •
              (c • deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j) := by
              apply Finset.sum_congr rfl
              intro j hj
              apply congrArg (fun z => (-1 : A) ^ j.1 • z)
              rw [update_eq_update, update_eq_update]
              exact diff_smul p ω i c x j
          _ = c • (∑ j : Fin p, (-1 : A) ^ j.1 •
                deRhamWedgeWithDifferential (A := A) (B := B) p
                  (Function.update ω i x) j) := by
            exact deRhamGamma_sum_smul (A := A) (B := B) p ω i c x }
  refine ⟨⟨PiTensorProduct.lift f, ?_⟩⟩
  intro ω
  simp [f]

/-- The alternating map `γ` from the source's tensor product construction. -/
noncomputable def deRhamGamma
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1) →ₗ[A]
      deRhamTerm A B (p + 1) :=
  (Classical.choice (deRhamGamma_exists (A := A) (B := B) p)).1

theorem deRhamGamma_on_pure_tensor
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ)
    (ω : Fin p → deRhamTerm A B 1) :
    deRhamGamma (A := A) (B := B) p (PiTensorProduct.tprod A ω) =
      deRhamGammaPureFormula (A := A) (B := B) p ω := by
  exact (Classical.choice (deRhamGamma_exists (A := A) (B := B) p)).2 ω

theorem deRhamGamma_alternating
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) (_hp : 2 ≤ p) (ω : Fin p → deRhamTerm A B 1)
    {i j : Fin p} (hij : i ≠ j) (hω : ω i = ω j) :
    deRhamGamma (A := A) (B := B) p (PiTensorProduct.tprod A ω) = 0 := by
  sorry

/-- The scalar-moving relations used to identify the tensor product with an
exterior power. -/
def deRhamWedgeRelations
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Set (PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1)) :=
  {z | ∃ (ω : Fin p → deRhamTerm A B 1) (i j : Fin p),
      i ≠ j ∧ ω i = ω j ∧ z = PiTensorProduct.tprod A ω} ∪
    {z | ∃ (ω : Fin p → deRhamTerm A B 1) (i j : Fin p) (f : B),
      i ≠ j ∧ z =
        PiTensorProduct.tprod A (Function.update ω i (f • ω i)) -
          PiTensorProduct.tprod A (Function.update ω j (f • ω j))}

theorem deRhamGamma_balanced
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) (_hp : 2 ≤ p) (ω : Fin p → deRhamTerm A B 1)
    {i j : Fin p} (hij : i ≠ j) (f : B) :
    deRhamGamma (A := A) (B := B) p
        (PiTensorProduct.tprod A (Function.update ω i (f • ω i))) =
      deRhamGamma (A := A) (B := B) p
        (PiTensorProduct.tprod A (Function.update ω j (f • ω j))) := by
  sorry

/-- The natural tensor-to-exterior-power map on pure tensors. -/
theorem deRhamExteriorPowerTensorMap_exists
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Nonempty
      {q : PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1) →ₗ[A]
          deRhamTerm A B p //
        ∀ ω, q (PiTensorProduct.tprod A ω) =
      deRhamPureWedgeTerms (A := A) (B := B) p ω} := by
  classical
  let f : MultilinearMap A (fun _ : Fin p => deRhamTerm A B 1)
      (deRhamTerm A B p) :=
    { toFun := deRhamPureWedgeTerms (A := A) (B := B) p
      map_update_add' := by
        intro _ ω i x y
        have update_eq_update : ∀ z : deRhamTerm A B 1,
            Function.update ω i z =
              @Function.update (Fin p) (fun _ => deRhamTerm A B 1)
                (instDecidableEqFin p) ω i z := by
          intro z
          funext k
          by_cases h : k = i <;> simp [Function.update, h]
        rw [update_eq_update, update_eq_update, update_eq_update]
        exact pure_add p ω i x y
      map_update_smul' := by
        intro _ ω i c x
        have update_eq_update : ∀ z : deRhamTerm A B 1,
            Function.update ω i z =
              @Function.update (Fin p) (fun _ => deRhamTerm A B 1)
                (instDecidableEqFin p) ω i z := by
          intro z
          funext k
          by_cases h : k = i <;> simp [Function.update, h]
        rw [update_eq_update, update_eq_update]
        exact pure_smul p ω i c x }
  refine ⟨⟨PiTensorProduct.lift f, ?_⟩⟩
  intro ω
  simp [f]

noncomputable def deRhamExteriorPowerTensorMap
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1) →ₗ[A]
      deRhamTerm A B p :=
  (Classical.choice
    (deRhamExteriorPowerTensorMap_exists (A := A) (B := B) p)).1

theorem deRhamExteriorPowerTensorMap_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ)
    (hp : 1 ≤ p) :
    Function.Surjective (deRhamExteriorPowerTensorMap (A := A) (B := B) p) := by
  classical
  cases p with
  | zero => omega
  | succ n =>
      have coe_cast : ∀ {r s : ℕ} (h : r = s) (x : deRhamTerm A B r),
          ((cast (congrArg (fun k => (deRhamTerm A B k : Type _)) h) x :
            deRhamTerm A B s) : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
        intro r s h x
        cases h
        rfl
      have pure_succ_val : ∀ (r : ℕ) (ω : Fin (r + 1) → deRhamTerm A B 1),
          (deRhamPureWedgeTerms (A := A) (B := B) (r + 1) ω :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (deRhamWedge (A := A) (B := B) 1 r (ω 0)
              (deRhamPureWedgeTerms (A := A) (B := B) r (Matrix.vecTail ω)) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
        intro r ω
        simp only [deRhamPureWedgeTerms]
        apply coe_cast (Nat.add_comm 1 r)
      have pure_cons_smul : ∀ (r : ℕ) (c : B) (x : deRhamTerm A B 1)
          (ω : Fin r → deRhamTerm A B 1),
          (deRhamPureWedgeTerms (A := A) (B := B) (r + 1)
            (Fin.cons (c • x) ω) : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            c • (deRhamPureWedgeTerms (A := A) (B := B) (r + 1)
              (Fin.cons x ω) : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
        intro r c x ω
        rw [pure_succ_val, pure_succ_val]
        change (↑(deRhamWedge (A := A) (B := B) 1 r (c • x)
            (deRhamPureWedgeTerms (A := A) (B := B) r ω)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          c • (↑(deRhamWedge (A := A) (B := B) 1 r x
            (deRhamPureWedgeTerms (A := A) (B := B) r ω)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B))
        rw [map_smul]
        rfl
      have pure_univ : ∀ (r : ℕ) (b : Fin r → B),
          (deRhamPureWedgeTerms (A := A) (B := B) r
            (fun i => deRhamUniversalDifferential A B (b i)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (exteriorPower.ιMulti B r
              (fun i => universalDifferentialLinearMap A B (b i)) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
        intro r
        induction r with
        | zero =>
            intro b
            simp [deRhamPureWedgeTerms, ExteriorAlgebra.ιMulti_zero_apply]
        | succ r ih =>
            intro b
            rw [pure_succ_val]
            have htail : Matrix.vecTail (fun i =>
                deRhamUniversalDifferential A B (b i)) =
                (fun i => deRhamUniversalDifferential A B ((Matrix.vecTail b) i)) := by
              rfl
            rw [htail]
            have hpure : deRhamPureWedgeTerms (A := A) (B := B) r
                (fun i => deRhamUniversalDifferential A B ((Matrix.vecTail b) i)) =
                exteriorPower.ιMulti B r
                  (fun i => universalDifferentialLinearMap A B ((Matrix.vecTail b) i)) := by
              apply Subtype.ext
              exact ih (Matrix.vecTail b)
            rw [hpure]
            simp [deRhamUniversalDifferential, deRhamDegreeOneEquivA,
              deRhamDegreeOneEquiv, exteriorPower.oneEquiv, deRhamWedge,
              ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, Function.comp_apply]
            have hvec : (fun i : Fin r => universalDifferentialLinearMap A B (b i.succ)) =
                (fun i : Fin (r + 1) => universalDifferentialLinearMap A B (b i)) ∘ Fin.succ := by
              funext i
              rfl
            rw [hvec]
      have hgen : ∀ (b₀ : B) (b : Fin (n + 1) → B),
          deRhamGenerator (A := A) (B := B) (n + 1) b₀ b ∈
            LinearMap.range (deRhamExteriorPowerTensorMap (A := A) (B := B) (n + 1)) := by
        intro b₀ b
        let ω : Fin (n + 1) → deRhamTerm A B 1 :=
          Fin.cons (b₀ • deRhamUniversalDifferential A B (b 0))
            (fun i => deRhamUniversalDifferential A B (b i.succ))
        refine ⟨PiTensorProduct.tprod A ω, ?_⟩
        change (Classical.choice
          (deRhamExteriorPowerTensorMap_exists (A := A) (B := B) (n + 1))).1
            (PiTensorProduct.tprod A ω) = _
        rw [(Classical.choice
          (deRhamExteriorPowerTensorMap_exists (A := A) (B := B) (n + 1))).2]
        apply Subtype.ext
        have hfun : Fin.cons (deRhamUniversalDifferential A B (b 0))
              (fun i => deRhamUniversalDifferential A B (b i.succ)) =
            (fun i => deRhamUniversalDifferential A B (b i)) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        calc
          (deRhamPureWedgeTerms (A := A) (B := B) (n + 1) ω :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            b₀ • (deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (Fin.cons (deRhamUniversalDifferential A B (b 0))
                (fun i => deRhamUniversalDifferential A B (b i.succ))) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
                dsimp [ω]
                exact pure_cons_smul n b₀
                  (deRhamUniversalDifferential A B (b 0))
                  (fun i => deRhamUniversalDifferential A B (b i.succ))
          _ = b₀ • (deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (fun i => deRhamUniversalDifferential A B (b i)) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
                rw [hfun]
          _ = b₀ • (exteriorPower.ιMulti B (n + 1)
              (fun i => universalDifferentialLinearMap A B (b i)) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
                rw [pure_univ (n + 1) b]
          _ = (deRhamGenerator (A := A) (B := B) (n + 1) b₀ b :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
                rfl
      intro y
      have hy : y ∈ Submodule.span A
          (deRhamGenerators (A := A) (B := B) (n + 1)) := by
        rw [deRhamGenerators_span (A := A) (B := B) (n + 1)]
        exact Submodule.mem_top
      refine Submodule.span_induction (p := fun z _ =>
          z ∈ LinearMap.range
            (deRhamExteriorPowerTensorMap (A := A) (B := B) (n + 1))) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨z, rfl⟩
        rcases z with ⟨b₀, b⟩
        exact hgen b₀ b
      · exact ⟨0, by simp⟩
      · intro x y hx hy ihx ihy
        rcases ihx with ⟨u, hu⟩
        rcases ihy with ⟨v, hv⟩
        refine ⟨u + v, ?_⟩
        simp [map_add, hu, hv]
      · intro c x hx ih
        rcases ih with ⟨u, hu⟩
        refine ⟨c • u, ?_⟩
        simp [hu]

theorem deRhamExteriorPowerTensorMap_on_pure_tensor
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ)
    (ω : Fin p → deRhamTerm A B 1) :
    deRhamExteriorPowerTensorMap (A := A) (B := B) p
        (PiTensorProduct.tprod A ω) =
      deRhamPureWedgeTerms (A := A) (B := B) p ω := by
  exact (Classical.choice
    (deRhamExteriorPowerTensorMap_exists (A := A) (B := B) p)).2 ω

theorem deRhamExteriorPowerTensorMap_kernel_span
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ)
    (_hp : 2 ≤ p) :
    LinearMap.ker (deRhamExteriorPowerTensorMap (A := A) (B := B) p) =
      Submodule.span A (deRhamWedgeRelations (A := A) (B := B) p) := by
  sorry

theorem deRhamGamma_factors_through_exteriorPower
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ)
    (_hp : 2 ≤ p) :
      (deRhamDifferential (A := A) (B := B) p).comp
        (deRhamExteriorPowerTensorMap (A := A) (B := B) p) =
      deRhamGamma (A := A) (B := B) p := by
  classical
  apply PiTensorProduct.ext_of_span_eq_top
    (g := fun _ (z : B × (Fin 1 → B)) =>
      deRhamGenerator (A := A) (B := B) 1 z.1 z.2)
  · intro i
    exact deRhamGenerators_span (A := A) (B := B) 1
  · intro z
    change deRhamDifferential (A := A) (B := B) p
        (deRhamExteriorPowerTensorMap (A := A) (B := B) p
          (PiTensorProduct.tprod A
            (fun i => deRhamGenerator (A := A) (B := B) 1
              (z i).1 (z i).2))) =
      deRhamGamma (A := A) (B := B) p
        (PiTensorProduct.tprod A
          (fun i => deRhamGenerator (A := A) (B := B) 1
            (z i).1 (z i).2))
    rw [deRhamExteriorPowerTensorMap_on_pure_tensor,
      deRhamGamma_on_pure_tensor]
    have coe_cast : ∀ {r s : ℕ} (h : r = s) (x : deRhamTerm A B r),
        ((cast (congrArg (fun k => (deRhamTerm A B k : Type _)) h) x :
          deRhamTerm A B s) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro r s h x
      cases h
      rfl
    have pure_succ_coe : ∀ (n : ℕ)
        (ω : Fin (n + 1) → deRhamTerm A B 1),
        ((deRhamPureWedgeTerms (A := A) (B := B) (n + 1) ω :
            deRhamTerm A B (n + 1)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          ((deRhamWedge (A := A) (B := B) 1 n (ω 0)
            (deRhamPureWedgeTerms (A := A) (B := B) n
              (Matrix.vecTail ω)) :
              deRhamTerm A B (1 + n)) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro n ω
      simp only [deRhamPureWedgeTerms]
      apply coe_cast (Nat.add_comm 1 n)
    have pure_gen_coe : ∀ (n : ℕ) (u : Fin n → B) (v : Fin n → B),
        ((deRhamPureWedgeTerms (A := A) (B := B) n
            (fun i => deRhamGenerator (A := A) (B := B) 1
              (u i) (fun _ => v i)) :
            deRhamTerm A B n) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          ((deRhamGenerator (A := A) (B := B) n (∏ i, u i) v :
            deRhamTerm A B n) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro n
      induction n with
      | zero =>
          intro u v
          simp [deRhamPureWedgeTerms, deRhamGenerator,
            exteriorPower.ιMulti]
      | succ n ih =>
          intro u v
          rw [pure_succ_coe]
          rw [show Matrix.vecTail
              (fun i : Fin (n + 1) =>
                deRhamGenerator (A := A) (B := B) 1
                  (u i) (fun _ => v i)) =
              (fun i => deRhamGenerator (A := A) (B := B) 1
                (u i.succ) (fun _ => v i.succ)) by
                funext i
                rfl]
          change
            ((deRhamGenerator (A := A) (B := B) 1 (u 0)
                (fun _ => v 0) :
                deRhamTerm A B 1) :
                ExteriorAlgebra B (ModuleOfDifferentials A B)) *
              (((deRhamPureWedgeTerms (A := A) (B := B) n
                  (fun i => deRhamGenerator (A := A) (B := B) 1
                    (u i.succ) (fun _ => v i.succ)) :
                  deRhamTerm A B n) :
                  ExteriorAlgebra B (ModuleOfDifferentials A B))) = _
          rw [ih]
          simp [deRhamGenerator, exteriorPower.ιMulti,
            Fin.prod_univ_succ, smul_smul, Matrix.vecTail]
          rw [mul_comm]
          congr 1
    have pure_gen : ∀ (n : ℕ) (u : Fin n → B) (v : Fin n → B),
        deRhamPureWedgeTerms (A := A) (B := B) n
            (fun i => deRhamGenerator (A := A) (B := B) 1
              (u i) (fun _ => v i)) =
          deRhamGenerator (A := A) (B := B) n (∏ i, u i) v := by
      intro n u v
      apply Subtype.ext
      exact pure_gen_coe n u v
    have wedge_coe : ∀ (r s : ℕ) (u : deRhamTerm A B r)
        (v : deRhamTerm A B s),
        ((deRhamWedge (A := A) (B := B) r s u v :
            deRhamTerm A B (r + s)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (u : ExteriorAlgebra B (ModuleOfDifferentials A B)) *
            (v : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro r s u v
      rfl
    have diff_zero_coe : ∀ (n : ℕ)
        (ω : Fin (n + 1) → deRhamTerm A B 1),
        (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1) ω 0 :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (deRhamWedge (A := A) (B := B) 2 n
            (deRhamDifferential (A := A) (B := B) 1 (ω 0))
            (deRhamPureWedgeTerms (A := A) (B := B) n
              (Matrix.vecTail ω)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro n ω
      simp only [deRhamWedgeWithDifferential]
      apply coe_cast (Nat.add_comm 2 n)
    have diff_succ_coe : ∀ (n : ℕ)
        (ω : Fin (n + 1) → deRhamTerm A B 1) (j : Fin n),
        (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1) ω j.succ :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (deRhamWedge (A := A) (B := B) 1 (n + 1) (ω 0)
            (deRhamWedgeWithDifferential (A := A) (B := B) n
              (Matrix.vecTail ω) j) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro n ω j
      simp only [deRhamWedgeWithDifferential]
      exact congrArg (fun x =>
          (x : ExteriorAlgebra B (ModuleOfDifferentials A B)))
        (coe_cast (by simp [Nat.add_left_comm]) _)
    have gamma_succ_coe : ∀ (n : ℕ)
        (ω : Fin (n + 1) → deRhamTerm A B 1),
        (deRhamGammaPureFormula (A := A) (B := B) (n + 1) ω :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1) ω 0 :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) -
          (deRhamWedge (A := A) (B := B) 1 (n + 1) (ω 0)
            (deRhamGammaPureFormula (A := A) (B := B) n
              (Matrix.vecTail ω)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro n ω
      simp only [deRhamGammaPureFormula, Fin.sum_univ_succ]
      simp [pow_succ, neg_smul]
      simp_rw [diff_succ_coe, wedge_coe]
      abel
    have generator_step_coe : ∀ (n : ℕ) (u : Fin (n + 1) → B)
        (v : Fin (n + 1) → B),
        ((deRhamDifferentialGenerator (A := A) (B := B) (n + 1)
            (∏ i, u i) v :
            deRhamTerm A B (n + 2)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1)
            (fun i => deRhamGenerator (A := A) (B := B) 1
              (u i) (fun _ => v i)) 0 :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) -
          (deRhamWedge (A := A) (B := B) 1 (n + 1)
            (deRhamGenerator (A := A) (B := B) 1 (u 0)
              (fun _ => v 0))
            (deRhamDifferentialGenerator (A := A) (B := B) n
              (∏ i : Fin n, u i.succ) (fun i => v i.succ)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro n u v
      have hprod :
          universalDifferential A B (∏ i : Fin (n + 1), u i) =
            u 0 • universalDifferential A B (∏ i : Fin n, u i.succ) +
              (∏ i : Fin n, u i.succ) • universalDifferential A B (u 0) := by
        rw [Fin.prod_univ_succ]
        exact (universalDifferential A B).leibniz (u 0)
          (∏ i : Fin n, u i.succ)
      have htail :
          Matrix.vecTail (fun i : Fin (n + 1) =>
            deRhamGenerator (A := A) (B := B) 1
              (u i) (fun _ => v i)) =
            (fun i : Fin n => deRhamGenerator (A := A) (B := B) 1
              (u i.succ) (fun _ => v i.succ)) := by
        funext i
        rfl
      rw [diff_zero_coe, deRhamDifferential_on_generator 1 (by omega)]
      rw [wedge_coe, htail, pure_gen_coe]
      rw [wedge_coe]
      simp only [deRhamDifferentialGenerator, deRhamGenerator]
      have hvec :
          ((Fin.cons ((universalDifferentialLinearMap A B)
              (∏ i : Fin (n + 1), u i))
            (fun i : Fin (n + 1) => (universalDifferentialLinearMap A B)
              (v i)) :
              Fin (n + 1 + 1) → ModuleOfDifferentials A B)) =
          ((Fin.cons
            (u 0 • (universalDifferentialLinearMap A B)
                (∏ i : Fin n, u i.succ) +
              (∏ i : Fin n, u i.succ) • (universalDifferentialLinearMap A B)
                (u 0))
            (fun i : Fin (n + 1) => (universalDifferentialLinearMap A B)
              (v i)) :
              Fin (n + 1 + 1) → ModuleOfDifferentials A B)) := by
        funext i
        refine Fin.cases ?_ (fun j => rfl) i
        exact hprod
      rw [hvec]
      have hcoe : ∀ (m : ℕ) (w : Fin m → ModuleOfDifferentials A B),
          ((exteriorPower.ιMulti B m w : deRhamTerm A B m) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            ExteriorAlgebra.ιMulti B m w := by
        intro m w
        rfl
      have hcoe_smul : ∀ (m : ℕ) (c : B)
          (w : Fin m → ModuleOfDifferentials A B),
          ((c • (exteriorPower.ιMulti B m w) : deRhamTerm A B m) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            c • ExteriorAlgebra.ιMulti B m w := by
        intro m c w
        rfl
      calc
        _ = ExteriorAlgebra.ιMulti B (n + 1 + 1)
            (Fin.cons
              (u 0 • (universalDifferentialLinearMap A B)
                  (∏ i : Fin n, u i.succ) +
                (∏ i : Fin n, u i.succ) • (universalDifferentialLinearMap A B)
                  (u 0))
              (fun i : Fin (n + 1) => (universalDifferentialLinearMap A B)
                (v i))) := by rfl
        _ = _ := by
          simp only [hcoe, hcoe_smul]
          simp only [ExteriorAlgebra.ιMulti_succ_apply]
          simp only [Fin.cons_zero, Matrix.vecTail]
          simp only [ExteriorAlgebra.ιMulti_zero_apply, mul_one]
          rw [map_add, map_smul, map_smul]
          simp only [Function.comp_def, Function.comp_apply, Fin.cons_succ]
          simp only [Algebra.smul_def]
          have hswap (r : ExteriorAlgebra B (ModuleOfDifferentials A B)) :
              (ExteriorAlgebra.ι B)
                  (universalDifferentialLinearMap A B (∏ i : Fin n, u i.succ)) *
                ((ExteriorAlgebra.ι B)
                    (universalDifferentialLinearMap A B (v 0)) * r) =
              -((ExteriorAlgebra.ι B)
                  (universalDifferentialLinearMap A B (v 0)) *
                (ExteriorAlgebra.ι B)
                  (universalDifferentialLinearMap A B (∏ i : Fin n, u i.succ))) * r := by
            rw [← mul_assoc, exterior_generator_swap
              (R := B) (M := ModuleOfDifferentials A B)
              (universalDifferentialLinearMap A B (∏ i : Fin n, u i.succ))
              (universalDifferentialLinearMap A B (v 0))]
            simp only [neg_mul]
          rw [add_mul]
          simp only [mul_assoc]
          rw [hswap]
          let S : ExteriorAlgebra B (ModuleOfDifferentials A B) :=
            algebraMap B (ExteriorAlgebra B (ModuleOfDifferentials A B)) (u 0)
          let T : ExteriorAlgebra B (ModuleOfDifferentials A B) :=
            algebraMap B (ExteriorAlgebra B (ModuleOfDifferentials A B))
              (∏ i : Fin n, u i.succ)
          let a : ExteriorAlgebra B (ModuleOfDifferentials A B) :=
            ExteriorAlgebra.ι B
              (universalDifferentialLinearMap A B (∏ i : Fin n, u i.succ))
          let b : ExteriorAlgebra B (ModuleOfDifferentials A B) :=
            ExteriorAlgebra.ι B (universalDifferentialLinearMap A B (u 0))
          let c : ExteriorAlgebra B (ModuleOfDifferentials A B) :=
            ExteriorAlgebra.ι B (universalDifferentialLinearMap A B (v 0))
          let r : ExteriorAlgebra B (ModuleOfDifferentials A B) :=
            ExteriorAlgebra.ιMulti B n
              (fun i => universalDifferentialLinearMap A B (v i.succ))
          change S * (-(c * a) * r) + T * (b * (c * r)) =
            b * (c * (T * r)) - S * (c * (a * r))
          have hfirst : S * (-(c * a) * r) = -(S * (c * (a * r))) := by
            simp only [neg_mul, mul_neg, mul_assoc]
          have hsecond : T * (b * (c * r)) = b * (c * (T * r)) := by
            calc
              T * (b * (c * r)) = (T * b) * (c * r) :=
                (mul_assoc _ _ _).symm
              _ = (b * T) * (c * r) := by rw [Algebra.commutes]
              _ = b * (T * (c * r)) := mul_assoc _ _ _
              _ = b * (c * (T * r)) := by
                congr 1
                calc
                  T * (c * r) = (T * c) * r := (mul_assoc _ _ _).symm
                  _ = (c * T) * r := by rw [Algebra.commutes]
                  _ = c * (T * r) := mul_assoc _ _ _
          rw [hfirst, hsecond]
          simp only [sub_eq_add_neg]
          abel
    have gamma_one_coe (ω : Fin 1 → deRhamTerm A B 1) :
        (deRhamGammaPureFormula (A := A) (B := B) 1 ω :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (deRhamWedgeWithDifferential (A := A) (B := B) 1 ω 0 :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      simp only [deRhamGammaPureFormula, Fin.sum_univ_succ]
      simp
    have base : ∀ (u : Fin 1 → B) (v : Fin 1 → B),
        ((deRhamDifferentialGenerator (A := A) (B := B) 1
            (∏ i, u i) v : deRhamTerm A B 2) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (deRhamGammaPureFormula (A := A) (B := B) 1
            (fun i => deRhamGenerator (A := A) (B := B) 1
              (u i) (fun _ => v i)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro u v
      let ω : Fin 1 → deRhamTerm A B 1 :=
        fun i => deRhamGenerator (A := A) (B := B) 1
          (u i) (fun _ => v i)
      rw [show (fun i => deRhamGenerator (A := A) (B := B) 1
            (u i) (fun _ => v i)) = ω by rfl]
      rw [gamma_one_coe, diff_zero_coe]
      rw [deRhamDifferential_on_generator 1 (by omega), wedge_coe]
      simp [deRhamPureWedgeTerms, deRhamDifferentialGenerator,
        ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
    have generator_formula : ∀ (n : ℕ) (u : Fin n → B) (v : Fin n → B),
        1 ≤ n →
        ((deRhamDifferential (A := A) (B := B) n
            (deRhamPureWedgeTerms (A := A) (B := B) n
              (fun i => deRhamGenerator (A := A) (B := B) 1
                (u i) (fun _ => v i))) :
            deRhamTerm A B (n + 1)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) =
          (deRhamGammaPureFormula (A := A) (B := B) n
            (fun i => deRhamGenerator (A := A) (B := B) 1
              (u i) (fun _ => v i)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
      intro n
      induction n with
      | zero =>
          intro u v hn
          omega
      | succ n ih =>
          intro u v hn
          by_cases h : n = 0
          · subst n
            rw [pure_gen, deRhamDifferential_on_generator 1 (by omega)]
            exact base u v
          · have hn' : 1 ≤ n := by omega
            have ihterm :
                deRhamGammaPureFormula (A := A) (B := B) n
                    (fun i => deRhamGenerator (A := A) (B := B) 1
                      (u i.succ) (fun _ => v i.succ)) =
                  deRhamDifferentialGenerator (A := A) (B := B) n
                    (∏ i : Fin n, u i.succ) (fun i => v i.succ) := by
              apply Subtype.ext
              have hih := ih (fun i => u i.succ) (fun i => v i.succ) hn'
              rw [pure_gen, deRhamDifferential_on_generator n hn'] at hih
              exact hih.symm
            rw [pure_gen, deRhamDifferential_on_generator (n + 1) (by omega)]
            rw [gamma_succ_coe n]
            rw [show Matrix.vecTail (fun i : Fin (n + 1) =>
                deRhamGenerator (A := A) (B := B) 1
                  (u i) (fun _ => v i)) =
                (fun i : Fin n => deRhamGenerator (A := A) (B := B) 1
                  (u i.succ) (fun _ => v i.succ)) by
              funext i
              rfl]
            rw [ihterm]
            exact generator_step_coe n u v
    apply Subtype.ext
    let u : Fin p → B := fun i => (z i).1
    let v : Fin p → B := fun i => (z i).2 0
    have hz : (fun i => deRhamGenerator (A := A) (B := B) 1
        (z i).1 (z i).2) =
        (fun i => deRhamGenerator (A := A) (B := B) 1
          (u i) (fun _ => v i)) := by
      funext i
      have hzi : (z i).2 = fun _ => (z i).2 0 := by
        funext j
        exact congrArg (fun k => (z i).2 k) (Fin.eq_zero j)
      change deRhamGenerator (A := A) (B := B) 1 (z i).1 (z i).2 =
        deRhamGenerator (A := A) (B := B) 1 (z i).1 (fun _ => (z i).2 0)
      rw [hzi]
    rw [hz]
    have hp1 : 1 ≤ p := by omega
    simpa [u, v] using (generator_formula p u v hp1)

end
end Formalization.Books.Algebra.Unit132
