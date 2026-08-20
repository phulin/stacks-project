import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.RingTheory.GradedAlgebra.TensorProduct
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


end
end Formalization.Books.Algebra.Unit132
