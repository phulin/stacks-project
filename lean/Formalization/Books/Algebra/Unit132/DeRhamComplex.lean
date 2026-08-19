import Mathlib.Algebra.Homology.HomologicalComplex
import Formalization.Books.Algebra.Unit13.TensorAlgebra
import Formalization.Books.Algebra.Unit131.Differentials

/-!
# Commutative Algebra, Chapter 132: The de Rham complex

The source's module of differentials is Mathlib's `KaehlerDifferential`.
Exterior powers are represented by the homogeneous submodules of the exterior
algebra, and the de Rham complex is represented by a cochain
`HomologicalComplex` of `ModuleCat`s.  The source identifies degrees zero and
one with `B` and `Ω[B⁄A]`; the two linear equivalences below make those
identifications explicit while retaining Mathlib's canonical exterior-power
representation in every degree.
-/

namespace Formalization.Books.Algebra.Unit132

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section

/-! ## Terms and the universal differential -/

/-- The `p`th exterior-power term of the de Rham complex. -/
abbrev deRhamTerm (A B : Type*) (p : ℕ) [CommRing A] [CommRing B]
    [Algebra A B] :=
  exteriorPower B (ModuleOfDifferentials A B) p

/-- Restriction of scalars gives every de Rham term its `A`-module structure. -/
noncomputable instance deRhamTerm.moduleA
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Module A (deRhamTerm A B p) :=
  Module.restrictScalars A B (deRhamTerm A B p)

noncomputable instance deRhamTerm.isScalarTower
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    IsScalarTower A B (deRhamTerm A B p) :=
  IsScalarTower.restrictScalars A B (deRhamTerm A B p)

/-- The canonical universal derivation as an `A`-linear map. -/
def universalDifferentialLinearMap
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    B →ₗ[A] ModuleOfDifferentials A B :=
  (universalDifferential A B).toLinearMap

/-- The canonical identifications of degree zero with `B` and degree one with
`Ω[B⁄A]`.  Mathlib exposes the homogeneous exterior powers as submodules, so
the source-facing directions are the inverses of Mathlib's canonical
`zeroEquiv` and `oneEquiv`. -/
noncomputable def deRhamDegreeZeroEquiv
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    B ≃ₗ[B] deRhamTerm A B 0 :=
  (exteriorPower.zeroEquiv B (ModuleOfDifferentials A B)).symm

noncomputable def deRhamDegreeZeroEquivA
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    B ≃ₗ[A] deRhamTerm A B 0 :=
  let f := deRhamDegreeZeroEquiv A B
  let fA : B →ₗ[A] deRhamTerm A B 0 :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro c x
        rw [← IsScalarTower.algebraMap_smul B c x, f.map_smul,
          IsScalarTower.algebraMap_smul B c (f x)]
        rfl }
  LinearEquiv.ofBijective fA f.bijective

noncomputable def deRhamDegreeOneEquiv
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleOfDifferentials A B ≃ₗ[B] deRhamTerm A B 1 :=
  (exteriorPower.oneEquiv B (ModuleOfDifferentials A B)).symm

noncomputable def deRhamDegreeOneEquivA
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleOfDifferentials A B ≃ₗ[A] deRhamTerm A B 1 :=
  let f := deRhamDegreeOneEquiv A B
  let fA : ModuleOfDifferentials A B →ₗ[A] deRhamTerm A B 1 :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro c x
        rw [← IsScalarTower.algebraMap_smul B c x, f.map_smul,
          IsScalarTower.algebraMap_smul B c (f x)]
        rfl }
  LinearEquiv.ofBijective fA f.bijective

/-- The universal differential viewed in the degree-one exterior-power term. -/
def deRhamUniversalDifferential
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
  B →ₗ[A] deRhamTerm A B 1 :=
  (deRhamDegreeOneEquivA A B).toLinearMap.comp
    (universalDifferentialLinearMap A B)

/-- A pure wedge of universal differentials, with a coefficient in front. -/
def deRhamGenerator
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (p : ℕ) (b₀ : B) (b : Fin p → B) : deRhamTerm A B p :=
  b₀ • exteriorPower.ιMulti B p (fun i => universalDifferentialLinearMap A B (b i))

/-- The pure wedge on the right side of the de Rham differential rule. -/
def deRhamDifferentialGenerator
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) (b₀ : B) (b : Fin p → B) : deRhamTerm A B (p + 1) :=
  exteriorPower.ιMulti B (p + 1)
    (Fin.cons (universalDifferentialLinearMap A B b₀)
      (fun i => universalDifferentialLinearMap A B (b i)))

/-- The generator set used in the source's uniqueness argument. -/
def deRhamGenerators
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) : Set (deRhamTerm A B p) :=
  Set.range (fun z : B × (Fin p → B) => deRhamGenerator p z.1 z.2)

theorem deRhamGenerators_span
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Submodule.span A (deRhamGenerators (A := A) (B := B) p) = ⊤ := by
  classical
  let S : Submodule A (deRhamTerm A B p) :=
    Submodule.span A (deRhamGenerators (A := A) (B := B) p)
  have hB : Submodule.span B (deRhamGenerators (A := A) (B := B) p) = ⊤ := by
    apply le_antisymm le_top
    rw [← exteriorPower.ιMulti_span_of_span B p (ModuleOfDifferentials A B)
      (KaehlerDifferential.span_range_derivation A B)]
    apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩
    let b : Fin p → B := fun i =>
      Classical.choose (hx ⟨i, rfl⟩)
    have hb : ∀ i : Fin p,
        universalDifferentialLinearMap A B (b i) = x i := by
      intro i
      exact Classical.choose_spec (hx ⟨i, rfl⟩)
    apply Submodule.subset_span
    refine ⟨(1, b), ?_⟩
    simp [deRhamGenerator, hb]
  have hBsmul : ∀ (c : B) {x : deRhamTerm A B p}, x ∈ S → c • x ∈ S := by
    intro c x hx
    refine Submodule.span_induction (p := fun x _ => c • x ∈ S) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨z, rfl⟩
      rcases z with ⟨b₀, b⟩
      apply Submodule.subset_span
      refine ⟨(c * b₀, b), ?_⟩
      simp [deRhamGenerator, smul_smul]
    · simp
    · intro x y hx hy ihx ihy
      simpa [smul_add] using S.add_mem ihx ihy
    · intro a x hx ih
      change c • (a • x) ∈ S
      rw [← IsScalarTower.algebraMap_smul B a x, smul_smul, mul_comm,
        ← smul_smul, IsScalarTower.algebraMap_smul B a (c • x)]
      exact S.smul_mem a ih
  apply le_antisymm le_top
  intro x _
  have hxB : x ∈ Submodule.span B (deRhamGenerators (A := A) (B := B) p) := by
    rw [hB]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ => x ∈ S) ?_ ?_ ?_ ?_ hxB
  · intro y hy
    exact Submodule.subset_span hy
  · exact S.zero_mem
  · intro x y hx hy ihx ihy
    exact S.add_mem ihx ihy
  · intro c x hx ih
    exact hBsmul c ih

/-! ## Exterior multiplication and the differential -/

/-- Multiplication of homogeneous exterior terms, with its degree recorded. -/
noncomputable def deRhamWedge
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p q : ℕ) : deRhamTerm A B p →ₗ[B] deRhamTerm A B q →ₗ[B]
      deRhamTerm A B (p + q) :=
  LinearMap.mk₂ B
    (fun x y =>
      ⟨(x : ExteriorAlgebra B (ModuleOfDifferentials A B)) * y,
        SetLike.GradedMul.mul_mem x.property y.property⟩)
    (by
      intro x₁ x₂ y
      ext
      simp [add_mul])
    (by
      intro c x y
      ext
      simp)
    (by
      intro x y₁ y₂
      ext
      simp [mul_add])
    (by
      intro c x y
      ext
      simp)

/-- A de Rham differential system packages the source's differential rule and
the assertion that consecutive differentials compose to zero. -/
structure DeRhamDifferentialData
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] where
  differential : ∀ p : ℕ, deRhamTerm A B p →ₗ[A] deRhamTerm A B (p + 1)
  differential_zero :
    differential 0 =
      (deRhamUniversalDifferential A B).comp
        (deRhamDegreeZeroEquivA A B).symm.toLinearMap
  generator_rule :
    ∀ (p : ℕ), 1 ≤ p → ∀ (b₀ : B) (b : Fin p → B),
      differential p (deRhamGenerator p b₀ b) =
        deRhamDifferentialGenerator p b₀ b
  square_zero :
    ∀ p : ℕ, (differential (p + 1)).comp (differential p) = 0

theorem deRhamDifferentialData_exists
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (DeRhamDifferentialData A B) := by
  sorry

/-- The source-ordered de Rham differential system. -/
noncomputable def deRhamDifferentialData
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    DeRhamDifferentialData A B :=
  Classical.choice (deRhamDifferentialData_exists (A := A) (B := B))

/-- The `A`-linear de Rham differential in degree `p`. -/
noncomputable def deRhamDifferential
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    deRhamTerm A B p →ₗ[A] deRhamTerm A B (p + 1) :=
  (deRhamDifferentialData A B).differential p

theorem deRhamDifferential_zero
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
    deRhamDifferential (A := A) (B := B) 0 =
      (deRhamUniversalDifferential A B).comp
        (deRhamDegreeZeroEquivA A B).symm.toLinearMap := by
  exact (deRhamDifferentialData A B).differential_zero

theorem deRhamDifferential_on_generator
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) (hp : 1 ≤ p) (b₀ : B) (b : Fin p → B) :
    deRhamDifferential (A := A) (B := B) p (deRhamGenerator p b₀ b) =
      deRhamDifferentialGenerator p b₀ b := by
  exact (deRhamDifferentialData A B).generator_rule p hp b₀ b

theorem deRhamDifferential_comp
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    (deRhamDifferential (A := A) (B := B) (p + 1)).comp
        (deRhamDifferential (A := A) (B := B) p) = 0 := by
  exact (deRhamDifferentialData A B).square_zero p

theorem deRhamDifferential_unique
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) (hp : 1 ≤ p)
    (d e : deRhamTerm A B p →ₗ[A] deRhamTerm A B (p + 1))
    (hd : ∀ (b₀ : B) (b : Fin p → B),
      d (deRhamGenerator p b₀ b) = deRhamDifferentialGenerator p b₀ b)
    (he : ∀ (b₀ : B) (b : Fin p → B),
      e (deRhamGenerator p b₀ b) = deRhamDifferentialGenerator p b₀ b) :
    d = e := by
  have _hp : 1 ≤ p := hp
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span A (deRhamGenerators (A := A) (B := B) p) := by
    rw [deRhamGenerators_span (A := A) (B := B) p]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ => d x = e x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, rfl⟩
    rcases z with ⟨b₀, b⟩
    rw [hd, he]
  · rw [map_zero, map_zero]
  · intro x y hx hy ihx ihy
    rw [map_add, map_add, ihx, ihy]
  · intro a x hx ih
    rw [map_smul, map_smul, ih]

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
  ∑ i : Fin p, (-1 : A) ^ (i.1 + 1) •
    deRhamWedgeWithDifferential (A := A) (B := B) p ω i

private theorem deRhamGamma_sum_smul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) [DecidableEq (Fin p)] (ω : Fin p → deRhamTerm A B 1)
    (i : Fin p) (c : A) (x : deRhamTerm A B 1) :
    (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
      (c • deRhamWedgeWithDifferential (A := A) (B := B) p
        (Function.update ω i x) j)) =
      c • (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
        deRhamWedgeWithDifferential (A := A) (B := B) p
          (Function.update ω i x) j) := by
  calc
    (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
        (c • deRhamWedgeWithDifferential (A := A) (B := B) p
          (Function.update ω i x) j)) =
      ∑ j : Fin p, c • ((-1 : A) ^ (j.1 + 1) •
        deRhamWedgeWithDifferential (A := A) (B := B) p
          (Function.update ω i x) j) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (-1 : A) ^ (j.1 + 1) •
              (c • deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j) =
            ((-1 : A) ^ (j.1 + 1) * c) •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j := smul_smul _ _ _
          _ = (c * (-1 : A) ^ (j.1 + 1)) •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j := by rw [mul_comm]
          _ = c • ((-1 : A) ^ (j.1 + 1) •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j) := (smul_smul _ _ _).symm
    _ = c • (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
          deRhamWedgeWithDifferential (A := A) (B := B) p
            (Function.update ω i x) j) := by
      exact (Finset.smul_sum (r := c)
        (f := fun j : Fin p => (-1 : A) ^ (j.1 + 1) •
          deRhamWedgeWithDifferential (A := A) (B := B) p
            (Function.update ω i x) j) (s := Finset.univ)).symm

theorem deRhamGamma_exists
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Nonempty
      {γ : PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1) →ₗ[A]
          deRhamTerm A B (p + 1) //
        ∀ ω, γ (PiTensorProduct.tprod A ω) =
      deRhamGammaPureFormula (A := A) (B := B) p ω} := by
  classical
  have tail_update_zero : ∀ (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1)
      (x : deRhamTerm A B 1),
      Matrix.vecTail (Function.update ω 0 x) = Matrix.vecTail ω := by
    intro n ω x
    funext i
    simp [Matrix.vecTail]
  have tail_update_succ : ∀ (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1)
      (i : Fin n) (x : deRhamTerm A B 1),
      Matrix.vecTail (Function.update ω i.succ x) =
        Function.update (Matrix.vecTail ω) i x := by
    intro n ω i x
    funext j
    by_cases h : i = j
    · subst h
      simp [Matrix.vecTail]
    · simp [Matrix.vecTail, Ne.symm h]
  have coe_cast : ∀ {n m : ℕ} (h : n = m) (x : deRhamTerm A B n),
      ((cast (congrArg (fun k => (deRhamTerm A B k : Type _)) h) x :
        deRhamTerm A B m) : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro n m h x
    cases h
    rfl
  have coe_smul : ∀ {n : ℕ} (c : B) (x : deRhamTerm A B n),
      ((c • x : deRhamTerm A B n) : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        c • (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro n c x
    rfl
  have pure_succ_val : ∀ (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1),
      (deRhamPureWedgeTerms (A := A) (B := B) (n + 1) ω :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (deRhamWedge (A := A) (B := B) 1 n (ω 0)
          (deRhamPureWedgeTerms (A := A) (B := B) n (Matrix.vecTail ω)) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro n ω
    simp only [deRhamPureWedgeTerms]
    apply coe_cast (Nat.add_comm 1 n)
  have diff_zero_val : ∀ (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1),
      (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1) ω 0 :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (deRhamWedge (A := A) (B := B) 2 n
          (deRhamDifferential (A := A) (B := B) 1 (ω 0))
          (deRhamPureWedgeTerms (A := A) (B := B) n (Matrix.vecTail ω)) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro n ω
    simp only [deRhamWedgeWithDifferential]
    apply coe_cast (Nat.add_comm 2 n)
  have diff_succ_val : ∀ (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1)
      (j : Fin n),
      (deRhamWedgeWithDifferential (A := A) (B := B) (n + 1) ω j.succ :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (deRhamWedge (A := A) (B := B) 1 (n + 1) (ω 0)
          (deRhamWedgeWithDifferential (A := A) (B := B) n
            (Matrix.vecTail ω) j) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro n ω j
    simp only [deRhamWedgeWithDifferential]
    apply coe_cast (by simp [Nat.add_left_comm])
  have pure_add : ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
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
  have pure_smul : ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
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
  have diff_add : ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
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
  have wedge_smul_A_coe : ∀ (r s : ℕ) (u : deRhamTerm A B r)
      (c : A) (v : deRhamTerm A B s),
      ((deRhamWedge (A := A) (B := B) r s u (c • v) :
          deRhamTerm A B (r + s)) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (algebraMap A B c) •
          ((deRhamWedge (A := A) (B := B) r s u v :
            deRhamTerm A B (r + s)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro r s u c v
    rw [← IsScalarTower.algebraMap_smul B c v, map_smul, coe_smul]
  have wedge_smul_A_coe_left : ∀ (r s : ℕ) (u : deRhamTerm A B r)
      (c : A) (v : deRhamTerm A B s),
      ((deRhamWedge (A := A) (B := B) r s (c • u) v :
          deRhamTerm A B (r + s)) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (algebraMap A B c) •
          ((deRhamWedge (A := A) (B := B) r s u v :
            deRhamTerm A B (r + s)) :
            ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro r s u c v
    rw [← IsScalarTower.algebraMap_smul B c u, map_smul]
    rfl
  have diff_smul : ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
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
  have finset_sum_add : ∀ (g h : Fin p → deRhamTerm A B (p + 1)),
      (∑ j : Fin p, (g j + h j)) = (∑ j : Fin p, g j) +
        (∑ j : Fin p, h j) := by
    intro g h
    exact Finset.sum_add_distrib
  have smul_add_term : ∀ (a : A) (u v : deRhamTerm A B (p + 1)),
      a • (u + v) = a • u + a • v := by
    intro a u v
    exact smul_add _ _ _
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
          (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i (x + y)) j) =
            ∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
              (deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j +
               deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i y) j) := by
              apply Finset.sum_congr rfl
              intro j hj
              apply congrArg (fun z => (-1 : A) ^ (j.1 + 1) • z)
              rw [update_eq_update, update_eq_update, update_eq_update]
              exact diff_add p ω i x y j
          _ = (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
                deRhamWedgeWithDifferential (A := A) (B := B) p
                  (Function.update ω i x) j) +
              ∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
                deRhamWedgeWithDifferential (A := A) (B := B) p
                  (Function.update ω i y) j := by
            calc
              (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
                  (deRhamWedgeWithDifferential (A := A) (B := B) p
                    (Function.update ω i x) j +
                   deRhamWedgeWithDifferential (A := A) (B := B) p
                    (Function.update ω i y) j)) =
                ∑ j : Fin p, ((-1 : A) ^ (j.1 + 1) •
                  deRhamWedgeWithDifferential (A := A) (B := B) p
                    (Function.update ω i x) j +
                  (-1 : A) ^ (j.1 + 1) •
                    deRhamWedgeWithDifferential (A := A) (B := B) p
                      (Function.update ω i y) j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    exact smul_add_term ((-1 : A) ^ (j.1 + 1))
                      (deRhamWedgeWithDifferential (A := A) (B := B) p
                        (Function.update ω i x) j)
                      (deRhamWedgeWithDifferential (A := A) (B := B) p
                        (Function.update ω i y) j)
              _ = (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
                    deRhamWedgeWithDifferential (A := A) (B := B) p
                      (Function.update ω i x) j) +
                  ∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
                    deRhamWedgeWithDifferential (A := A) (B := B) p
                      (Function.update ω i y) j := by
                    exact finset_sum_add
                      (fun j : Fin p => (-1 : A) ^ (j.1 + 1) •
                        deRhamWedgeWithDifferential (A := A) (B := B) p
                          (Function.update ω i x) j)
                      (fun j : Fin p => (-1 : A) ^ (j.1 + 1) •
                        deRhamWedgeWithDifferential (A := A) (B := B) p
                          (Function.update ω i y) j)
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
          (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
              deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i (c • x)) j) =
            ∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
              (c • deRhamWedgeWithDifferential (A := A) (B := B) p
                (Function.update ω i x) j) := by
              apply Finset.sum_congr rfl
              intro j hj
              apply congrArg (fun z => (-1 : A) ^ (j.1 + 1) • z)
              rw [update_eq_update, update_eq_update]
              exact diff_smul p ω i c x j
          _ = c • (∑ j : Fin p, (-1 : A) ^ (j.1 + 1) •
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
  have tail_update_zero : ∀ (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1)
      (x : deRhamTerm A B 1),
      Matrix.vecTail (Function.update ω 0 x) = Matrix.vecTail ω := by
    intro n ω x
    funext i
    simp [Matrix.vecTail]
  have tail_update_succ : ∀ (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1)
      (i : Fin n) (x : deRhamTerm A B 1),
      Matrix.vecTail (Function.update ω i.succ x) =
        Function.update (Matrix.vecTail ω) i x := by
    intro n ω i x
    funext j
    by_cases h : i = j
    · subst h
      simp [Matrix.vecTail]
    · simp [Matrix.vecTail, Ne.symm h]
  have coe_cast : ∀ {n m : ℕ} (h : n = m) (x : deRhamTerm A B n),
      ((cast (congrArg (fun k => (deRhamTerm A B k : Type _)) h) x :
        deRhamTerm A B m) : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro n m h x
    cases h
    rfl
  have coe_smul : ∀ {n : ℕ} (c : B) (x : deRhamTerm A B n),
      ((c • x : deRhamTerm A B n) : ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        c • (x : ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro n c x
    rfl
  have pure_succ_val : ∀ (n : ℕ) (ω : Fin (n + 1) → deRhamTerm A B 1),
      (deRhamPureWedgeTerms (A := A) (B := B) (n + 1) ω :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) =
        (deRhamWedge (A := A) (B := B) 1 n (ω 0)
          (deRhamPureWedgeTerms (A := A) (B := B) n (Matrix.vecTail ω)) :
          ExteriorAlgebra B (ModuleOfDifferentials A B)) := by
    intro n ω
    simp only [deRhamPureWedgeTerms]
    apply coe_cast (Nat.add_comm 1 n)
  have pure_add : ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
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
        · apply Subtype.ext
          change (↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
              (Function.update ω j.succ (x + y))) :
              ExteriorAlgebra B (ModuleOfDifferentials A B)) =
            (↑(deRhamPureWedgeTerms (A := A) (B := B) (n + 1)
                (Function.update ω j.succ x)) :
                ExteriorAlgebra B (ModuleOfDifferentials A B)) +
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
  have pure_smul : ∀ (n : ℕ) (ω : Fin n → deRhamTerm A B 1)
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
        · rw [← IsScalarTower.algebraMap_smul B c
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
  sorry

/-! ## The de Rham complex -/

/-- Cochain complexes of `A`-modules indexed by `ℕ`. -/
abbrev DeRhamComplex (A : Type*) [CommRing A] :=
  HomologicalComplex (ModuleCat A) (ComplexShape.up ℕ)

/-- The de Rham complex of `B` over `A`. -/
noncomputable def deRhamComplex
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    DeRhamComplex A where
  X p := ModuleCat.of A (deRhamTerm A B p)
  d i j := if h : i + 1 = j then
    h ▸ ModuleCat.ofHom (deRhamDifferential (A := A) (B := B) i)
  else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    have hjk' : j + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hjk
    subst j
    subst k
    simp
    apply ModuleCat.hom_ext
    change (deRhamDifferential (A := A) (B := B) (i + 1)).comp
        (deRhamDifferential (A := A) (B := B) i) = 0
    exact deRhamDifferential_comp (A := A) (B := B) i

theorem deRhamComplex_differential_comp_zero
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    (deRhamComplex A B).d p (p + 1) ≫ (deRhamComplex A B).d (p + 1) (p + 2) = 0 := by
  exact (deRhamComplex A B).d_comp_d p (p + 1) (p + 2)

/-! ## Absolute de Rham complexes -/

/-- The absolute module of differentials of a ring. -/
abbrev absoluteModuleOfDifferentials (R : Type*) [CommRing R] :=
  ModuleOfDifferentials ℤ R

/-- The absolute de Rham complex of a ring. -/
noncomputable def absoluteDeRhamComplex
    (R : Type*) [CommRing R] : DeRhamComplex ℤ :=
  deRhamComplex ℤ R

theorem absolute_universal_differential_one
    {R : Type*} [CommRing R] :
    universalDifferentialLinearMap ℤ R 1 = 0 := by
  exact (universalDifferential ℤ R).map_one_eq_zero

/-! ## Functoriality -/

/-- The degree-zero ring map in the de Rham map associated to a square of
  algebra maps. -/
def deRhamDegreeZeroRingMap
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    B →+* B' :=
  algebraMap B B'

def deRhamDegreeZeroMap
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    B →+ B' :=
  (deRhamDegreeZeroRingMap (A := A) (A' := A') (B := B) (B' := B')).toAddMonoidHom

/-- The degree-one map in the same square, using the canonical Kähler API. -/
noncomputable def deRhamDegreeOneMap
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    ModuleOfDifferentials A B →ₗ[A] ModuleOfDifferentials A' B' :=
  mapOfDifferentials (R := A) (T := A') (A := B) (B := B')

theorem deRhamDegreeOneMap_on_universal_differential
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
    (b : B) :
    deRhamDegreeOneMap (A := A) (A' := A') (B := B) (B' := B')
        (universalDifferentialLinearMap A B b) =
      universalDifferentialLinearMap A' B' (algebraMap B B' b) := by
  exact mapOfDifferentials_apply_universalDifferential
    (R := A) (T := A') (A := B) (B := B') b

/-- The degreewise `A`-linear maps and their compatibility with the de Rham
differentials.  The component formula records the induced exterior-power map
in all degrees. -/
structure DeRhamMapData
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] where
  component : ∀ p : ℕ, deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p
  component_on_generator :
    ∀ (p : ℕ) (b₀ : B) (b : Fin p → B),
      component p (deRhamGenerator p b₀ b) =
        deRhamGenerator p (algebraMap B B' b₀)
          (fun i => algebraMap B B' (b i))
  commutes :
    ∀ (p : ℕ) (ω : deRhamTerm A B p),
      component (p + 1) (deRhamDifferential (A := A) (B := B) p ω) =
        deRhamDifferential (A := A') (B := B') p (component p ω)

theorem deRhamMapData_exists
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    Nonempty (DeRhamMapData (A := A) (A' := A') (B := B) (B' := B')) := by
  classical
  let targetModule : Module B (ModuleOfDifferentials A' B') := inferInstance
  letI : Module B (ModuleOfDifferentials A' B') := targetModule
  letI : IsScalarTower B B' (ModuleOfDifferentials A' B') :=
    KaehlerDifferential.isScalarTower_of_tower
      (R := A') (S := B') (R₁ := B) (R₂ := B')
  let f : ModuleOfDifferentials A B →ₗ[B] ModuleOfDifferentials A' B' :=
    IsLinearMap.mk' (mapOfDifferentials (R := A) (T := A') (A := B) (B := B'))
      ⟨(by
        intro x y
        exact map_add _ _ _), (by
        intro c x
        have hx : x ∈ Submodule.span B (Set.range (universalDifferential A B)) := by
          change x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B))
          rw [KaehlerDifferential.span_range_derivation]
          exact Submodule.mem_top
        have h : ∀ x, x ∈ Submodule.span B (Set.range (universalDifferential A B)) → ∀ c : B,
            mapOfDifferentials (R := A) (T := A') (A := B) (B := B') (c • x) =
              c • mapOfDifferentials (R := A) (T := A') (A := B) (B := B') x := by
          intro x hx
          refine Submodule.span_induction (p := fun x _ => ∀ c : B,
              mapOfDifferentials (R := A) (T := A') (A := B) (B := B') (c • x) =
                c • mapOfDifferentials (R := A) (T := A') (A := B) (B := B') x)
            ?_ ?_ ?_ ?_ hx
          · rintro _ ⟨b, rfl⟩ c
            rw [mapOfDifferentials_smul_universalDifferential,
              mapOfDifferentials_apply_universalDifferential]
            exact IsScalarTower.algebraMap_smul (R := B) (A := B') c
              (universalDifferential A' B' (algebraMap B B' b))
          · intro c; simp
          · intro x y hx hy ihx ihy c
            simp only [map_add, smul_add]
            rw [ihx c, ihy c]
          · intro a x hx ih c
            rw [← mul_smul, ih (c * a), ih a, smul_smul]
        exact h x hx c)⟩
  have hf (x : ModuleOfDifferentials A B) :
      f x = mapOfDifferentials (R := A) (T := A') (A := B) (B := B') x := by
    rfl
  let componentData : ∀ p : ℕ,
      { C : deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p //
        ∀ (b₀ : B) (b : Fin p → B),
          C (deRhamGenerator p b₀ b) =
            deRhamGenerator p (algebraMap B B' b₀)
              (fun i => algebraMap B B' (b i)) } :=
    fun p => by
      letI : Module B (deRhamTerm A' B' p) :=
        Module.compHom (deRhamTerm A' B' p) (algebraMap B B')
      letI : IsScalarTower B B' (deRhamTerm A' B' p) :=
        IsScalarTower.of_compHom (R := B) (A := B')
          (M := deRhamTerm A' B' p)
      letI : Module A (deRhamTerm A' B' p) :=
        Module.compHom (deRhamTerm A' B' p) (algebraMap A B')
      letI : IsScalarTower A B' (deRhamTerm A' B' p) :=
        IsScalarTower.of_compHom (R := A) (A := B')
          (M := deRhamTerm A' B' p)
      let wedge : (ModuleOfDifferentials A' B') [⋀^Fin p]→ₗ[B]
          deRhamTerm A' B' p :=
        { toFun := exteriorPower.ιMulti B' p
          map_update_add' := by
            intro _ m i x y
            exact (exteriorPower.ιMulti B' p).toMultilinearMap.map_update_add m i x y
          map_update_smul' := by
            intro _ m i c x
            calc
              exteriorPower.ιMulti B' p (Function.update m i (c • x)) =
                  exteriorPower.ιMulti B' p
                    (Function.update m i ((algebraMap B B' c) • x)) := by
                congr 1
                funext j
                by_cases h : j = i <;> simp [h, IsScalarTower.algebraMap_smul]
              _ = (algebraMap B B' c) •
                    exteriorPower.ιMulti B' p (Function.update m i x) := by
                exact (exteriorPower.ιMulti B' p).toMultilinearMap.map_update_smul
                  m i (algebraMap B B' c) x
              _ = c • exteriorPower.ιMulti B' p (Function.update m i x) := by
                rw [IsScalarTower.algebraMap_smul]
          map_eq_zero_of_eq' := by
            intro v i j h hij
            exact (exteriorPower.ιMulti B' p).map_eq_zero_of_eq v h hij }
      let C : deRhamTerm A B p →ₗ[B] deRhamTerm A' B' p :=
        exteriorPower.alternatingMapLinearEquiv
          (wedge.compLinearMap f)
      let C_A : deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p :=
        { toFun := C
          map_add' := C.map_add
          map_smul' := by
            intro a x
            have hx : a • x = (algebraMap A B a) • x :=
              (IsScalarTower.algebraMap_smul B a x).symm
            calc
              C (a • x) = C ((algebraMap A B a) • x) := by
                simpa only [hx]
              _ = (algebraMap A B a) • C x := C.map_smul _ _
              _ = ((algebraMap B B').comp (algebraMap A B)) a • C x :=
                (IsScalarTower.algebraMap_smul (R := B) (A := B')
                  (algebraMap A B a) (C x)).symm
              _ = (algebraMap A B' a) • C x := by
                rw [IsScalarTower.algebraMap_eq A B B']
              _ = a • C x :=
                IsScalarTower.algebraMap_smul (R := A) (A := B') a (C x) }
      refine ⟨C_A, ?_⟩
      intro b₀ b
      change C (b₀ • exteriorPower.ιMulti B p
        (fun i => universalDifferentialLinearMap A B (b i))) = _
      rw [LinearMap.map_smul C]
      dsimp [C]
      rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      simp only [AlternatingMap.compLinearMap_apply, Function.comp_apply]
      have h : (fun i => f (universalDifferentialLinearMap A B (b i))) =
          (fun i => universalDifferentialLinearMap A' B' ((algebraMap B B') (b i))) := by
        funext i
        calc
          f (universalDifferentialLinearMap A B (b i)) =
              mapOfDifferentials (R := A) (T := A') (A := B) (B := B')
                (universalDifferentialLinearMap A B (b i)) := hf _
          _ = universalDifferentialLinearMap A' B' ((algebraMap B B') (b i)) :=
            deRhamDegreeOneMap_on_universal_differential
              (A := A) (A' := A') (B := B) (B' := B') (b i)
      rw [h]
      change b₀ • exteriorPower.ιMulti B' p
          (fun i => universalDifferentialLinearMap A' B'
            ((algebraMap B B') (b i))) =
        b₀ • exteriorPower.ιMulti B' p
          (fun i => universalDifferentialLinearMap A' B'
            ((algebraMap B B') (b i)))
      rfl
  let component : ∀ p : ℕ, deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p :=
    fun p => (componentData p).1
  refine ⟨⟨component, ?_, ?_⟩⟩
  · intro p b₀ b
    exact (componentData p).2 b₀ b
  · intro p ω
    cases p with
    | zero =>
        have hω : ω ∈ Submodule.span A (deRhamGenerators (A := A) (B := B) 0) := by
          rw [deRhamGenerators_span (A := A) (B := B) 0]
          exact Submodule.mem_top
        refine Submodule.span_induction (p := fun x _ =>
            component 1 (deRhamDifferential (A := A) (B := B) 0 x) =
              deRhamDifferential (A := A') (B := B') 0 (component 0 x))
          ?_ ?_ ?_ ?_ hω
        · rintro _ ⟨z, rfl⟩
          rcases z with ⟨b₀, b⟩
          have hzero : deRhamDegreeZeroEquivA A B b₀ =
              deRhamGenerator 0 b₀ b := by
            apply (exteriorPower.zeroEquiv B (ModuleOfDifferentials A B)).injective
            simp [deRhamDegreeZeroEquivA, deRhamDegreeZeroEquiv,
              deRhamGenerator, exteriorPower.zeroEquiv]
          have hzero' : deRhamDegreeZeroEquivA A' B' (algebraMap B B' b₀) =
              deRhamGenerator 0 (algebraMap B B' b₀)
                (fun i => algebraMap B B' (b i)) := by
            apply (exteriorPower.zeroEquiv B' (ModuleOfDifferentials A' B')).injective
            simp [deRhamDegreeZeroEquivA, deRhamDegreeZeroEquiv,
              deRhamGenerator, exteriorPower.zeroEquiv]
          have hone : deRhamUniversalDifferential A B b₀ =
              deRhamGenerator 1 1 (fun _ => b₀) := by
            apply (exteriorPower.oneEquiv B (ModuleOfDifferentials A B)).injective
            simp [deRhamUniversalDifferential, deRhamDegreeOneEquivA,
              deRhamDegreeOneEquiv, deRhamGenerator, exteriorPower.oneEquiv]
          have hone' : deRhamUniversalDifferential A' B'
                (algebraMap B B' b₀) =
              deRhamGenerator 1 1 (fun _ => algebraMap B B' b₀) := by
            apply (exteriorPower.oneEquiv B' (ModuleOfDifferentials A' B')).injective
            simp [deRhamUniversalDifferential, deRhamDegreeOneEquivA,
              deRhamDegreeOneEquiv, deRhamGenerator, exteriorPower.oneEquiv]
          rw [deRhamDifferential_zero (A := A) (B := B),
            deRhamDifferential_zero (A := A') (B := B')]
          rw [(componentData 0).2 b₀ b]
          change component 1
              (deRhamUniversalDifferential A B
                ((deRhamDegreeZeroEquivA A B).symm
                  (deRhamGenerator 0 b₀ b))) =
            deRhamUniversalDifferential A' B'
              ((deRhamDegreeZeroEquivA A' B').symm
                (deRhamGenerator 0 (algebraMap B B' b₀)
                  (fun i => algebraMap B B' (b i))))
          rw [← hzero, ← hzero',
            (deRhamDegreeZeroEquivA A B).symm_apply_apply,
            (deRhamDegreeZeroEquivA A' B').symm_apply_apply, hone,
            (componentData 1).2 1 (fun _ => b₀)]
          simp only [map_one, one_smul]
          rw [← hone']
        · simp
        · intro x y hx hy ihx ihy
          simp only [map_add, ihx, ihy]
        · intro a x hx ih
          have hscalar (q : ℕ) (a : A) (y : deRhamTerm A' B' q) :
              a • y = (algebraMap A A' a) • y := by
            change (algebraMap A B' a) • y =
              (algebraMap A' B' (algebraMap A A' a)) • y
            rw [show algebraMap A B' a =
                algebraMap A' B' (algebraMap A A' a) by
              exact (congrArg (fun f : A →+* B' => f a)
                (IsScalarTower.algebraMap_eq A A' B'))]
          calc
            component 1 (deRhamDifferential (A := A) (B := B) 0 (a • x)) =
                component 1 (a • deRhamDifferential (A := A) (B := B) 0 x) := by
              exact congrArg (component 1)
                ((deRhamDifferential (A := A) (B := B) 0).map_smul a x)
            _ = a • component 1 (deRhamDifferential (A := A) (B := B) 0 x) :=
              (component 1).map_smul _ _
            _ = (algebraMap A A' a) • component 1
                (deRhamDifferential (A := A) (B := B) 0 x) := by
              exact hscalar 1 a _
            _ = (algebraMap A A' a) •
                deRhamDifferential (A := A') (B := B') 0 (component 0 x) := by
              rw [ih]
            _ = deRhamDifferential (A := A') (B := B') 0
                ((algebraMap A A' a) • component 0 x) := by
              exact ((deRhamDifferential (A := A') (B := B') 0).map_smul
                (algebraMap A A' a) (component 0 x)).symm
            _ = deRhamDifferential (A := A') (B := B') 0
                (a • component 0 x) := by
              exact congrArg (deRhamDifferential (A := A') (B := B') 0)
                (hscalar 0 a _).symm
            _ = deRhamDifferential (A := A') (B := B') 0
                (component 0 (a • x)) := by
              exact congrArg (deRhamDifferential (A := A') (B := B') 0)
                ((component 0).map_smul a x).symm
    | succ p =>
        have hω : ω ∈ Submodule.span A (deRhamGenerators (A := A) (B := B) (p + 1)) := by
          rw [deRhamGenerators_span (A := A) (B := B) (p + 1)]
          exact Submodule.mem_top
        refine Submodule.span_induction (p := fun x _ =>
            component (p + 2) (deRhamDifferential (A := A) (B := B) (p + 1) x) =
              deRhamDifferential (A := A') (B := B') (p + 1) (component (p + 1) x))
          ?_ ?_ ?_ ?_ hω
        · rintro _ ⟨z, rfl⟩
          rcases z with ⟨b₀, b⟩
          rw [deRhamDifferential_on_generator (p + 1)
            (Nat.succ_le_succ (Nat.zero_le p))]
          simp only [Prod.fst, Prod.snd]
          rw [show deRhamDifferentialGenerator (p + 1) b₀ b =
              deRhamGenerator (p + 2) 1 (Fin.cons b₀ b) by
            simp only [deRhamDifferentialGenerator, deRhamGenerator, one_smul]
            congr 1
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> rfl]
          rw [(componentData (p + 2)).2 1 (Fin.cons b₀ b)]
          rw [(componentData (p + 1)).2 b₀ b]
          rw [deRhamDifferential_on_generator (p + 1)
            (Nat.succ_le_succ (Nat.zero_le p))]
          simp only [deRhamGenerator, deRhamDifferentialGenerator, one_smul]
          simp only [map_one, one_smul]
          congr 1
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        · simp
        · intro x y hx hy ihx ihy
          simp only [map_add, ihx, ihy]
        · intro a x hx ih
          have hscalar (q : ℕ) (a : A) (y : deRhamTerm A' B' q) :
              a • y = (algebraMap A A' a) • y := by
            change (algebraMap A B' a) • y =
              (algebraMap A' B' (algebraMap A A' a)) • y
            rw [show algebraMap A B' a =
                algebraMap A' B' (algebraMap A A' a) by
              exact (congrArg (fun f : A →+* B' => f a)
                (IsScalarTower.algebraMap_eq A A' B'))]
          calc
            component (p + 2)
                (deRhamDifferential (A := A) (B := B) (p + 1) (a • x)) =
                component (p + 2)
                  (a • deRhamDifferential (A := A) (B := B) (p + 1) x) := by
                    exact congrArg (component (p + 2))
                      ((deRhamDifferential (A := A) (B := B) (p + 1)).map_smul a x)
            _ = a • component (p + 2)
                (deRhamDifferential (A := A) (B := B) (p + 1) x) :=
              (component (p + 2)).map_smul _ _
            _ = (algebraMap A A') a • component (p + 2)
                (deRhamDifferential (A := A) (B := B) (p + 1) x) := by
              exact hscalar (p + 2) a _
            _ = (algebraMap A A') a •
                deRhamDifferential (A := A') (B := B') (p + 1)
                  (component (p + 1) x) := by rw [ih]
            _ = deRhamDifferential (A := A') (B := B') (p + 1)
                ((algebraMap A A') a • component (p + 1) x) := by
              exact ((deRhamDifferential (A := A') (B := B') (p + 1)).map_smul
                (algebraMap A A' a) (component (p + 1) x)).symm
            _ = deRhamDifferential (A := A') (B := B') (p + 1)
                (a • component (p + 1) x) := by
              exact congrArg (deRhamDifferential (A := A') (B := B') (p + 1))
                (hscalar (p + 1) a _).symm
            _ = deRhamDifferential (A := A') (B := B') (p + 1)
                (component (p + 1) (a • x)) := by
              exact congrArg (deRhamDifferential (A := A') (B := B') (p + 1))
                ((component (p + 1)).map_smul a x).symm

noncomputable def deRhamMapData
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    DeRhamMapData (A := A) (A' := A') (B := B) (B' := B') :=
  Classical.choice (deRhamMapData_exists (A := A) (A' := A') (B := B) (B' := B'))

noncomputable def deRhamMapComponent
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
    (p : ℕ) : deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p :=
  (deRhamMapData (A := A) (A' := A') (B := B) (B' := B')).component p

theorem deRhamMapComponent_on_generator
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
    (p : ℕ) (b₀ : B) (b : Fin p → B) :
    deRhamMapComponent (A := A) (A' := A') (B := B) (B' := B') p
        (deRhamGenerator p b₀ b) =
      deRhamGenerator p (algebraMap B B' b₀)
        (fun i => algebraMap B B' (b i)) := by
  exact (deRhamMapData (A := A) (A' := A') (B := B) (B' := B')).component_on_generator
    p b₀ b

theorem deRhamMapComponent_commutes
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
    (p : ℕ) (ω : deRhamTerm A B p) :
    deRhamMapComponent (A := A) (A' := A') (B := B) (B' := B') (p + 1)
        (deRhamDifferential (A := A) (B := B) p ω) =
      deRhamDifferential (A := A') (B := B') p
        (deRhamMapComponent (A := A) (A' := A') (B := B) (B' := B') p ω) := by
  exact (deRhamMapData (A := A) (A' := A') (B := B) (B' := B')).commutes p ω

/-! ## Base change -/

/-- Mathlib's tensor-product convention for the source's `B ⊗[A] A'` is
`A' ⊗[A] B`. -/
abbrev deRhamBaseChangeRing (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A B] :=
  A' ⊗[A] B

abbrev deRhamBaseChangeTerm
    (A A' B : Type*) [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] (p : ℕ) :=
  A' ⊗[A] deRhamTerm A B p

/-- The differential obtained by tensoring a de Rham differential with the
base-change algebra. -/
noncomputable def deRhamBaseChangeDifferential
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] (p : ℕ) :
    deRhamBaseChangeTerm A A' B p →ₗ[A'] deRhamBaseChangeTerm A A' B (p + 1) :=
  (TensorProduct.AlgebraTensorModule.lTensor (R := A) A' A')
    (deRhamDifferential (A := A) (B := B) p)

theorem deRhamBaseChangeIso_exists
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] :
    Nonempty
      {e : ∀ p : ℕ,
          deRhamBaseChangeTerm A A' B p ≃ₗ[A']
            deRhamTerm A' (deRhamBaseChangeRing A A' B) p //
        ∀ (p : ℕ) (x : deRhamBaseChangeTerm A A' B p),
          e (p + 1) (deRhamBaseChangeDifferential (A := A) (A' := A') (B := B) p x) =
            deRhamDifferential (A := A')
              (B := deRhamBaseChangeRing A A' B) p (e p x)} := by
  sorry

/-- The degreewise isomorphism of de Rham complexes after arbitrary base
change. -/
noncomputable def deRhamBaseChangeIso
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] :
    ∀ p : ℕ,
      deRhamBaseChangeTerm A A' B p ≃ₗ[A']
        deRhamTerm A' (deRhamBaseChangeRing A A' B) p :=
  (Classical.choice
    (deRhamBaseChangeIso_exists (A := A) (A' := A') (B := B))).1

theorem deRhamBaseChangeIso_commutes
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B]
    (p : ℕ) (x : deRhamBaseChangeTerm A A' B p) :
    deRhamBaseChangeIso (A := A) (A' := A') (B := B) (p + 1)
        (deRhamBaseChangeDifferential (A := A) (A' := A') (B := B) p x) =
      deRhamDifferential (A := A')
        (B := deRhamBaseChangeRing A A' B) p
        (deRhamBaseChangeIso (A := A) (A' := A') (B := B) p x) := by
  exact (Classical.choice
    (deRhamBaseChangeIso_exists (A := A) (A' := A') (B := B))).2 p x

/-! ## Quotients of the module of differentials -/

/-- A type synonym retaining the `B` parameter needed to infer restriction of
scalars on an arbitrary quotient module. -/
def quotientModule (A B Ω : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup Ω] [Module B Ω] := Ω

def quotientModuleEquiv
    (A B Ω : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] : quotientModule A B Ω ≃ Ω :=
  { toFun := fun x => x
    invFun := fun x => x
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }

instance quotientModule.addCommGroup
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] : AddCommGroup (quotientModule A B Ω) := by
  exact Equiv.addCommGroup (quotientModuleEquiv A B Ω)

def quotientModuleAddEquiv
    (A B Ω : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] : quotientModule A B Ω ≃+ Ω :=
  { toEquiv := quotientModuleEquiv A B Ω
    map_add' := by intro x y; rfl }

instance quotientModule.moduleB
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] : Module B (quotientModule A B Ω) := by
  exact AddEquiv.module B (quotientModuleAddEquiv A B Ω)

noncomputable instance quotientModule.moduleA
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] : Module A (quotientModule A B Ω) :=
  letI : Module A Ω := Module.restrictScalars A B Ω
  AddEquiv.module A (quotientModuleAddEquiv A B Ω)

/-- Exterior-power terms formed from a quotient module of differentials. -/
abbrev quotientDeRhamTerm
    (A B Ω : Type*) (p : ℕ) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup Ω] [Module B Ω] :=
  exteriorPower B (quotientModule A B Ω) p

noncomputable instance quotientDeRhamTerm.moduleA
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] (p : ℕ) :
    Module A (quotientDeRhamTerm A B Ω p) :=
  Module.restrictScalars A B (quotientDeRhamTerm A B Ω p)

def quotientModuleLinearMap
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω) :
    ModuleOfDifferentials A B →ₗ[B] quotientModule A B Ω :=
  { toFun := π
    map_add' := π.map_add
    map_smul' := by
      intro b ω
      change π (b • ω) = b • π ω
      exact π.map_smul b ω }

/-- The degreewise exterior map in the quotient diagram. -/
def quotientDeRhamProjection
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω) (p : ℕ) :
    deRhamTerm A B p →ₗ[B] quotientDeRhamTerm A B Ω p :=
  exteriorPower.map p (quotientModuleLinearMap π)

theorem quotientDeRhamProjection_surjective
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π) (p : ℕ) :
    Function.Surjective (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p) := by
  exact exteriorPower.map_surjective hπ

/-- The differential on the quotient module induced by the universal one. -/
def quotientUniversalDifferential
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω) :
    B →ₗ[A] quotientModule A B Ω :=
  { toFun := fun x => π (universalDifferentialLinearMap A B x)
    map_add' := by
      intro x y
      change π (universalDifferentialLinearMap A B (x + y)) =
        π (universalDifferentialLinearMap A B x) +
          π (universalDifferentialLinearMap A B y)
      rw [(universalDifferentialLinearMap A B).map_add, π.map_add]
    map_smul' := by
      intro a x
      change π (universalDifferentialLinearMap A B (a • x)) =
        (quotientModule.moduleA (A := A) (B := B) (Ω := Ω)).smul a
          (π (universalDifferentialLinearMap A B x))
      rw [(universalDifferentialLinearMap A B).map_smul]
      change π (a • universalDifferentialLinearMap A B x) =
        (algebraMap A B a) • π (universalDifferentialLinearMap A B x)
      rw [← IsScalarTower.algebraMap_smul B a
        (universalDifferentialLinearMap A B x)]
      exact π.map_smul (algebraMap A B a) (universalDifferentialLinearMap A B x) }

/-- The source's differential `Ω[B⁄A] → Ω²[B⁄A]`, expressed using the
degree-one bridge to Mathlib's homogeneous exterior term. -/
def deRhamOneDifferential
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
    ModuleOfDifferentials A B →ₗ[A] deRhamTerm A B 2 :=
  (deRhamDifferential (A := A) (B := B) 1).comp
    (deRhamDegreeOneEquivA A B).toLinearMap

/-- The source's closed generators for the quotient construction. -/
def quotientClosedOneForms
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω) : Set (ModuleOfDifferentials A B) :=
  {ω | ω ∈ LinearMap.ker π ∧ exteriorPower.map 2 π
      (deRhamOneDifferential (A := A) (B := B) ω) = 0}

/-- The source-facing rule for a quotient de Rham differential. -/
def quotientDifferentialGenerator
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (q : B →ₗ[A] quotientModule A B Ω) (p : ℕ) (b₀ : B) (b : Fin p → B) :
    quotientDeRhamTerm A B Ω (p + 1) :=
  exteriorPower.ιMulti B (p + 1)
    (Fin.cons (q b₀) (fun i => q (b i)))

def quotientGenerator
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (q : B →ₗ[A] quotientModule A B Ω) (p : ℕ) (b₀ : B) (b : Fin p → B) :
    quotientDeRhamTerm A B Ω p :=
  b₀ • exteriorPower.ιMulti B p (fun i => q (b i))

/-- The data whose existence is asserted by the quotient de Rham lemma. -/
structure QuotientDeRhamDifferentialData
    (A B Ω : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (q : B →ₗ[A] quotientModule A B Ω) where
  differential : ∀ p : ℕ,
    quotientDeRhamTerm A B Ω p →ₗ[A] quotientDeRhamTerm A B Ω (p + 1)
  generator_rule :
    ∀ (p : ℕ) (b₀ : B) (b : Fin p → B),
      differential p (quotientGenerator q p b₀ b) =
        quotientDifferentialGenerator q p b₀ b
  square_zero :
    ∀ p : ℕ, (differential (p + 1)).comp (differential p) = 0

/-- The kernel condition in the source, stated using the already constructed
de Rham differential on `Ω[B⁄A]`. -/
def QuotientDifferentialsKernelCondition
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω) : Prop :=
  LinearMap.ker π =
  Submodule.span B (quotientClosedOneForms (A := A) (B := B) (Ω := Ω) π)

theorem quotientDeRhamDifferentialData_exists
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : QuotientDifferentialsKernelCondition (A := A) (B := B) (Ω := Ω) π) :
    Nonempty (QuotientDeRhamDifferentialData A B Ω
      (quotientUniversalDifferential π)) := by
  sorry

noncomputable def quotientDeRhamDifferentialData
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : QuotientDifferentialsKernelCondition (A := A) (B := B) (Ω := Ω) π) :
    QuotientDeRhamDifferentialData A B Ω (quotientUniversalDifferential π) :=
  Classical.choice (quotientDeRhamDifferentialData_exists π hπ hker)

/-- The differential supplied by the quotient-module de Rham construction. -/
noncomputable def quotientDeRhamDifferential
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : QuotientDifferentialsKernelCondition (A := A) (B := B) (Ω := Ω) π)
    (p : ℕ) : quotientDeRhamTerm A B Ω p →ₗ[A]
      quotientDeRhamTerm A B Ω (p + 1) :=
  (quotientDeRhamDifferentialData π hπ hker).differential p

theorem quotientDeRhamDifferential_on_generator
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : QuotientDifferentialsKernelCondition (A := A) (B := B) (Ω := Ω) π)
    (p : ℕ) (b₀ : B) (b : Fin p → B) :
    quotientDeRhamDifferential π hπ hker p (quotientGenerator
      (quotientUniversalDifferential π) p b₀ b) =
      quotientDifferentialGenerator (quotientUniversalDifferential π) p b₀ b := by
  exact (quotientDeRhamDifferentialData π hπ hker).generator_rule p b₀ b

theorem quotientDeRhamDifferential_comp
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : QuotientDifferentialsKernelCondition (A := A) (B := B) (Ω := Ω) π)
    (p : ℕ) :
    (quotientDeRhamDifferential π hπ hker (p + 1)).comp
        (quotientDeRhamDifferential π hπ hker p) = 0 := by
  exact (quotientDeRhamDifferentialData π hπ hker).square_zero p

theorem quotientDeRhamProjection_commutes
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : QuotientDifferentialsKernelCondition (A := A) (B := B) (Ω := Ω) π)
    (p : ℕ) (ω : deRhamTerm A B p) :
    quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π (p + 1)
        (deRhamDifferential (A := A) (B := B) p ω) =
    quotientDeRhamDifferential π hπ hker p
        (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p ω) := by
  have hgen : ∀ (n : ℕ) (b₀ : B) (b : Fin n → B),
      quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π n
          (deRhamGenerator n b₀ b) =
        quotientGenerator (quotientUniversalDifferential π) n b₀ b := by
    intro n b₀ b
    simp [deRhamGenerator, quotientGenerator, quotientDeRhamProjection,
      quotientModuleLinearMap]
    rfl
  have hω : ω ∈ Submodule.span A (deRhamGenerators (A := A) (B := B) p) := by
    rw [deRhamGenerators_span (A := A) (B := B) p]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ =>
      quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π (p + 1)
          (deRhamDifferential (A := A) (B := B) p x) =
        quotientDeRhamDifferential π hπ hker p
          (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p x))
    ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨z, rfl⟩
    rcases z with ⟨b₀, b⟩
    cases p with
    | zero =>
        change quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 1
            (deRhamDifferential (A := A) (B := B) 0
              (deRhamGenerator 0 b₀ b)) =
          quotientDeRhamDifferential π hπ hker 0
            (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 0
              (deRhamGenerator 0 b₀ b))
        have hzero : deRhamDegreeZeroEquivA A B b₀ =
            deRhamGenerator 0 b₀ b := by
          apply (exteriorPower.zeroEquiv B (ModuleOfDifferentials A B)).injective
          simp [deRhamDegreeZeroEquivA, deRhamDegreeZeroEquiv,
            deRhamGenerator, exteriorPower.zeroEquiv]
        have hone : deRhamUniversalDifferential A B b₀ =
            deRhamGenerator 1 1 (fun _ => b₀) := by
          apply (exteriorPower.oneEquiv B (ModuleOfDifferentials A B)).injective
          simp [deRhamUniversalDifferential, deRhamDegreeOneEquivA,
            deRhamDegreeOneEquiv, deRhamGenerator, exteriorPower.oneEquiv]
        rw [← hzero, deRhamDifferential_zero]
        simp only [LinearMap.comp_apply,
          (deRhamDegreeZeroEquivA A B).symm_apply_apply]
        have hsymm :
            (deRhamDegreeZeroEquivA A B).symm
                ((deRhamDegreeZeroEquivA A B) b₀) = b₀ := by
          exact (deRhamDegreeZeroEquivA A B).symm_apply_apply b₀
        change quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 1
            (deRhamUniversalDifferential A B
              ((deRhamDegreeZeroEquivA A B).symm
                ((deRhamDegreeZeroEquivA A B) b₀))) =
          quotientDeRhamDifferential π hπ hker 0
            (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 0
              (deRhamDegreeZeroEquivA A B b₀))
        rw [hsymm]
        rw [hone,
          hgen 1 1 (fun _ => b₀),
          hzero,
          hgen 0 b₀ b,
          quotientDeRhamDifferential_on_generator π hπ hker 0 b₀ b]
        simp only [quotientGenerator, one_smul, quotientDifferentialGenerator]
        congr 1
        funext i
        refine Fin.cases (by rfl) (fun j => Fin.elim0 j) i
    | succ p =>
        rw [deRhamDifferential_on_generator (p + 1)
          (Nat.succ_le_succ (Nat.zero_le p))]
        rw [show deRhamDifferentialGenerator (p + 1) b₀ b =
            deRhamGenerator (p + 2) 1 (Fin.cons b₀ b) by
          simp only [deRhamDifferentialGenerator, deRhamGenerator, one_smul]
          congr 1
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl]
        rw [hgen (p + 2) 1 (Fin.cons b₀ b),
          hgen (p + 1) b₀ b,
          quotientDeRhamDifferential_on_generator π hπ hker (p + 1) b₀ b]
        simp only [quotientGenerator, one_smul, quotientDifferentialGenerator]
        congr 1
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · simp
  · intro x y hx hy ihx ihy
    simp only [map_add, ihx, ihy]
  · intro a x hx ih
    have hscalar (q : ℕ) (a : A) (y : quotientDeRhamTerm A B Ω q) :
        a • y = (algebraMap A B a) • y := by
      rfl
    have hqsmul :
        quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p (a • x) =
          a • quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p x := by
      rw [← IsScalarTower.algebraMap_smul B a x,
        (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p).map_smul,
        (hscalar p a _).symm]
    calc
      quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π (p + 1)
          (deRhamDifferential (A := A) (B := B) p (a • x)) =
            quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π (p + 1)
            (a • deRhamDifferential (A := A) (B := B) p x) := by
              exact congrArg
                (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π (p + 1))
                ((deRhamDifferential (A := A) (B := B) p).map_smul a x)
      _ = a • quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π (p + 1)
          (deRhamDifferential (A := A) (B := B) p x) := by
            rw [← IsScalarTower.algebraMap_smul B a,
              (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π (p + 1)).map_smul,
              (hscalar (p + 1) a _).symm]
      _ = a • quotientDeRhamDifferential π hπ hker p
          (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p x) := by rw [ih]
      _ = quotientDeRhamDifferential π hπ hker p
          (a • quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p x) := by
            rw [(quotientDeRhamDifferential π hπ hker p).map_smul]
      _ = quotientDeRhamDifferential π hπ hker p
          (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p (a • x)) := by
            rw [hqsmul]

/-- The quotient-module de Rham complex asserted in the source lemma. -/
abbrev QuotientDeRhamComplex (A : Type*) [CommRing A] :=
  HomologicalComplex (ModuleCat A) (ComplexShape.up ℕ)

noncomputable def quotientDeRhamComplex
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : QuotientDifferentialsKernelCondition (A := A) (B := B) (Ω := Ω) π) :
    QuotientDeRhamComplex A where
  X p := ModuleCat.of A (quotientDeRhamTerm A B Ω p)
  d i j := if h : i + 1 = j then
    h ▸ ModuleCat.ofHom (quotientDeRhamDifferential π hπ hker i)
  else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    have hjk' : j + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hjk
    subst j
    subst k
    simp
    apply ModuleCat.hom_ext
    change (quotientDeRhamDifferential π hπ hker (i + 1)).comp
        (quotientDeRhamDifferential π hπ hker i) = 0
    exact quotientDeRhamDifferential_comp π hπ hker i

end
end Formalization.Books.Algebra.Unit132
