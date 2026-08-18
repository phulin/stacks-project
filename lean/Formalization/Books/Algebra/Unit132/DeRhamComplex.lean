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

theorem deRhamGamma_exists
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Nonempty
      {γ : PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1) →ₗ[A]
          deRhamTerm A B (p + 1) //
        ∀ ω, γ (PiTensorProduct.tprod A ω) =
          deRhamGammaPureFormula (A := A) (B := B) p ω} := by
  sorry

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

/-- The natural tensor-to-exterior-power quotient map. -/
theorem deRhamExteriorPowerTensorMap_exists
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Nonempty
      {q : PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1) →ₗ[A]
          deRhamTerm A B p //
        Function.Surjective q ∧
          ∀ ω, q (PiTensorProduct.tprod A ω) =
            deRhamPureWedgeTerms (A := A) (B := B) p ω} := by
  sorry

noncomputable def deRhamExteriorPowerTensorMap
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    PiTensorProduct A (fun _ : Fin p => deRhamTerm A B 1) →ₗ[A]
      deRhamTerm A B p :=
  (Classical.choice
    (deRhamExteriorPowerTensorMap_exists (A := A) (B := B) p)).1

theorem deRhamExteriorPowerTensorMap_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    Function.Surjective (deRhamExteriorPowerTensorMap (A := A) (B := B) p) := by
  exact (Classical.choice
    (deRhamExteriorPowerTensorMap_exists (A := A) (B := B) p)).2.1

theorem deRhamExteriorPowerTensorMap_on_pure_tensor
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ)
    (ω : Fin p → deRhamTerm A B 1) :
    deRhamExteriorPowerTensorMap (A := A) (B := B) p
        (PiTensorProduct.tprod A ω) =
      deRhamPureWedgeTerms (A := A) (B := B) p ω := by
  exact (Classical.choice
    (deRhamExteriorPowerTensorMap_exists (A := A) (B := B) p)).2.2 ω

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
