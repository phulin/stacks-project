import Formalization.Books.Algebra.Unit132.DeRhamComplex.Core

namespace Formalization.Books.Algebra.Unit132

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section
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
  {ω | ω ∈ LinearMap.ker π ∧ exteriorPower.map 2 (quotientModuleLinearMap π)
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

private theorem deRhamWedge_ιMulti_one_one
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (u v : ModuleOfDifferentials A B) :
    deRhamWedge (A := A) (B := B) 1 1
        (exteriorPower.ιMulti B 1 (fun _ => u))
        (exteriorPower.ιMulti B 1 (fun _ => v)) =
      exteriorPower.ιMulti B 2 (Fin.cons u (fun _ => v)) := by
  apply Subtype.ext
  simp [deRhamWedge, exteriorPower.ιMulti,
    ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

private theorem finCons_zero
    {M : Type*} (z : M) (r : Fin 0 → M) :
    Fin.cons z r = (fun _ : Fin 1 => z) := by
  funext i
  exact Fin.eq_zero i ▸ rfl

private theorem quotientDeRhamProjection_wedge_closed
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω) (b : B)
    (ω : ModuleOfDifferentials A B) (hω : π ω = 0) :
    quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 2
      (deRhamWedge (A := A) (B := B) 1 1
        (deRhamUniversalDifferential A B b)
        (exteriorPower.ιMulti B 1 (fun _ => ω))) = 0 := by
  have huniv : deRhamUniversalDifferential A B b =
      exteriorPower.ιMulti B 1 (fun _ =>
        universalDifferentialLinearMap A B b) := by
    apply Subtype.ext
    rfl
  rw [huniv, deRhamWedge_ιMulti_one_one]
  change exteriorPower.map 2 (quotientModuleLinearMap π)
    (exteriorPower.ιMulti B 2 (Fin.cons
      (universalDifferentialLinearMap A B b) (fun _ => ω))) = 0
  rw [exteriorPower.map_apply_ιMulti]
  apply Subtype.ext
  have hv0 : (quotientModuleLinearMap π ∘ Fin.cons
      (universalDifferentialLinearMap A B b) (fun _ => ω)) (1 : Fin 2) = 0 := by
    change π ω = 0
    exact hω
  exact (ExteriorAlgebra.ιMulti B 2).map_coord_zero 1 hv0

private theorem quotientDeRhamProjection_wedge_closed_finCons
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω) (b : B)
    (ω : ModuleOfDifferentials A B) (r : Fin 0 → ModuleOfDifferentials A B)
    (hω : π ω = 0) :
    quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 2
      (deRhamWedge (A := A) (B := B) 1 1
        (deRhamUniversalDifferential A B b)
        (exteriorPower.ιMulti B 1 (Fin.cons ω r))) = 0 := by
  have hv := finCons_zero ω r
  rw [hv]
  exact quotientDeRhamProjection_wedge_closed π b ω hω

private theorem quotientDeRhamProjection_wedge_congr
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω) (b : B)
    (x y : deRhamTerm A B 1) (hxy : x = y) :
    quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 2
      (deRhamWedge (A := A) (B := B) 1 1
        (deRhamUniversalDifferential A B b) x) =
      quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 2
        (deRhamWedge (A := A) (B := B) 1 1
          (deRhamUniversalDifferential A B b) y) := by
  exact congrArg (fun z => quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 2
    (deRhamWedge (A := A) (B := B) 1 1
      (deRhamUniversalDifferential A B b) z)) hxy

private theorem deRhamDifferential_one_smul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
 (b : B) (x : deRhamTerm A B 1) :
    deRhamDifferential (A := A) (B := B) 1 (b • x) =
      deRhamWedge (A := A) (B := B) 1 1
          (deRhamUniversalDifferential A B b) x +
        b • deRhamDifferential (A := A) (B := B) 1 x := by
  let smulMap : deRhamTerm A B 1 →ₗ[A] deRhamTerm A B 1 :=
    { toFun := fun y => b • y
      map_add' := by intro y z; rw [smul_add]
      map_smul' := by
        intro a y
        change b • ((algebraMap A B a) • y) =
          (algebraMap A B a) • (b • y)
        rw [smul_smul, smul_smul, mul_comm] }
  let wedgeMap : deRhamTerm A B 1 →ₗ[A] deRhamTerm A B 2 :=
    { toFun := fun y => deRhamWedge (A := A) (B := B) 1 1
          (deRhamUniversalDifferential A B b) y
      map_add' := by intro y z; rw [map_add]
      map_smul' := by
        intro a y
        change deRhamWedge (A := A) (B := B) 1 1
            (deRhamUniversalDifferential A B b) ((algebraMap A B a) • y) =
          (algebraMap A B a) •
            deRhamWedge (A := A) (B := B) 1 1
              (deRhamUniversalDifferential A B b) y
        rw [map_smul] }
  let leftMap : deRhamTerm A B 2 →ₗ[A] deRhamTerm A B 2 :=
    { toFun := fun y => b • y
      map_add' := by intro y z; rw [smul_add]
      map_smul' := by
        intro a y
        change b • ((algebraMap A B a) • y) =
          (algebraMap A B a) • (b • y)
        rw [smul_smul, smul_smul, mul_comm] }
  let dMap : deRhamTerm A B 1 →ₗ[A] deRhamTerm A B 2 :=
    (deRhamDifferential (A := A) (B := B) 1).comp smulMap
  let eMap : deRhamTerm A B 1 →ₗ[A] deRhamTerm A B 2 :=
    wedgeMap + leftMap.comp (deRhamDifferential (A := A) (B := B) 1)
  have heq : dMap = eMap := by
    apply LinearMap.ext
    intro y
    have hy : y ∈ Submodule.span A (deRhamGenerators (A := A) (B := B) 1) := by
      rw [deRhamGenerators_span (A := A) (B := B) 1]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun y _ => dMap y = eMap y) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨z, rfl⟩
      rcases z with ⟨b₀, bs⟩
      simp only [dMap, smulMap, LinearMap.comp_apply]
      change deRhamDifferential (A := A) (B := B) 1
          (b • deRhamGenerator (A := A) (B := B) 1 b₀ bs) = _
      rw [show b • deRhamGenerator (A := A) (B := B) 1 b₀ bs =
          deRhamGenerator (A := A) (B := B) 1 (b * b₀) bs by
            simp [deRhamGenerator, smul_smul]]
      rw [deRhamDifferential_on_generator 1 (by omega) (b * b₀) bs]
      simp only [deRhamDifferentialGenerator, eMap, wedgeMap, leftMap,
        LinearMap.add_apply, LinearMap.comp_apply]
      rw [deRhamDifferential_on_generator 1 (by omega) b₀ bs]
      apply Subtype.ext
      have hprod : universalDifferentialLinearMap A B (b * b₀) =
          b • universalDifferentialLinearMap A B b₀ +
            b₀ • universalDifferentialLinearMap A B b := by
        exact (universalDifferential A B).leibniz b b₀
      rw [hprod]
      simp [deRhamGenerator, deRhamUniversalDifferential,
        deRhamDegreeOneEquivA, deRhamDegreeOneEquiv,
        deRhamDifferentialGenerator, deRhamWedge,
        exteriorPower.oneEquiv, exteriorPower.ιMulti, Matrix.vecTail,
        Algebra.smul_def]
      simp [add_mul, mul_assoc, Algebra.commutes]
      ac_rfl
    · simp [dMap, eMap]
    · intro y z hy hz ihy ihz
      simp only [dMap, eMap, LinearMap.add_apply, map_add, ihy, ihz]
    · intro a y hy ih
      simp [dMap, eMap, ih]
  exact LinearMap.congr_fun heq x

private theorem quotientDeRhamProjection_one_zero
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (ω : ModuleOfDifferentials A B) (hω : π ω = 0) :
    quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 1
      (deRhamDegreeOneEquivA A B ω) = 0 := by
  have hs : deRhamDegreeOneEquivA A B ω =
      exteriorPower.ιMulti B 1 (fun _ : Fin 1 => ω) := by
    apply Subtype.ext
    rfl
  rw [hs]
  change exteriorPower.map 1 (quotientModuleLinearMap π)
    (exteriorPower.ιMulti B 1 (fun _ : Fin 1 => ω)) = 0
  rw [exteriorPower.map_apply_ιMulti]
  simp only [quotientModuleLinearMap, Function.comp_def]
  apply Subtype.ext
  apply (ExteriorAlgebra.ιMulti B 1).map_coord_zero 0
  change π ω = 0
  exact hω

private theorem quotientDeRhamProjection_wedge_zero
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (b : B) (x : deRhamTerm A B 1)
    (hx : quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 1 x = 0) :
    quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 2
      (deRhamWedge (A := A) (B := B) 1 1
        (deRhamUniversalDifferential A B b) x) = 0 := by
  have hmap_one :
      (exteriorPower.oneEquiv B (quotientModule A B Ω))
          (exteriorPower.map 1 (quotientModuleLinearMap π) x) =
        quotientModuleLinearMap π
          ((exteriorPower.oneEquiv B (ModuleOfDifferentials A B)) x) := by
    rw [show x = exteriorPower.ιMulti B 1 (fun _ =>
        (exteriorPower.oneEquiv B (ModuleOfDifferentials A B)) x) by
          change x = (exteriorPower.oneEquiv B (ModuleOfDifferentials A B)).symm
            ((exteriorPower.oneEquiv B (ModuleOfDifferentials A B)) x)
          exact ((exteriorPower.oneEquiv B (ModuleOfDifferentials A B)).symm_apply_apply x).symm]
    rw [exteriorPower.map_apply_ιMulti]
    simp [exteriorPower.oneEquiv, quotientModuleLinearMap]
  have hxQ : exteriorPower.map 1 (quotientModuleLinearMap π) x = 0 := by
    exact hx
  have hy : π ((exteriorPower.oneEquiv B (ModuleOfDifferentials A B)) x) = 0 := by
    have hyQ := congrArg (exteriorPower.oneEquiv B (quotientModule A B Ω)) hxQ
    rw [hmap_one] at hyQ
    have hyQ' : (quotientModuleLinearMap π)
        ((exteriorPower.oneEquiv B (ModuleOfDifferentials A B)) x) = 0 := by
      simpa using hyQ
    change π ((exteriorPower.oneEquiv B (ModuleOfDifferentials A B)) x) = 0 at hyQ'
    exact hyQ'
  have hy_mem : (exteriorPower.oneEquiv B (ModuleOfDifferentials A B)) x ∈
      LinearMap.range ((LinearMap.ker π).subtype) :=
    (LinearMap.exact_iff.mp (LinearMap.exact_subtype_ker_map π)) ▸ hy
  obtain ⟨z, hz⟩ := hy_mem
  let r₀ : Fin 0 → ModuleOfDifferentials A B := Fin.elim0
  have hxrel' : x = exteriorPower.ιMulti B 1
      (Fin.cons ((LinearMap.ker π).subtype z) r₀) := by
    apply (exteriorPower.oneEquiv B (ModuleOfDifferentials A B)).injective
    rw [← hz]
    rw [exteriorPower.oneEquiv_ιMulti]
    rfl
  have hzero' := quotientDeRhamProjection_wedge_closed_finCons π b
    ((LinearMap.ker π).subtype z) r₀ z.property
  have heq := quotientDeRhamProjection_wedge_congr π b x _ hxrel'
  exact heq.trans hzero'

theorem quotientDeRhamDifferentialData_exists
    {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω]
    (π : ModuleOfDifferentials A B →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : QuotientDifferentialsKernelCondition (A := A) (B := B) (Ω := Ω) π) :
    Nonempty (QuotientDeRhamDifferentialData A B Ω
      (quotientUniversalDifferential π)) := by
  classical
  let q : ∀ p : ℕ, deRhamTerm A B p →ₗ[A]
      quotientDeRhamTerm A B Ω p := fun p =>
    { toFun := quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p
      map_add' := by
        intro x y
        exact (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p).map_add x y
      map_smul' := by
        intro a x
        change (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p)
            ((algebraMap A B a) • x) =
          (algebraMap A B a) •
            (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p) x
        exact (quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p).map_smul
          (algebraMap A B a) x }
  have q_apply (p : ℕ) (x : deRhamTerm A B p) :
      q p x = quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π p x := rfl
  have hclosed : ∀ (ω : ModuleOfDifferentials A B), ω ∈ LinearMap.ker π →
      q 2 (deRhamOneDifferential (A := A) (B := B) ω) = 0 := by
    intro ω hω
    rw [hker] at hω
    have hspan : ω ∈ Submodule.span B
        (quotientClosedOneForms (A := A) (B := B) (Ω := Ω) π) := hω
    have hp : ω ∈ LinearMap.ker π ∧
        q 2 (deRhamOneDifferential (A := A) (B := B) ω) = 0 := by
      refine Submodule.span_induction (p := fun η _ =>
          η ∈ LinearMap.ker π ∧
            q 2 (deRhamOneDifferential (A := A) (B := B) η) = 0)
        ?_ ?_ ?_ ?_ hspan
      · rintro η ⟨hηker, hηclosed⟩
        have hqη : q 2 (deRhamOneDifferential (A := A) (B := B) η) = 0 := by
          rw [q_apply]
          exact hηclosed
        exact ⟨hηker, hqη⟩
      · simp [deRhamOneDifferential, q]
      · intro η ξ hη hξ ihη ihξ
        exact ⟨(LinearMap.ker π).add_mem ihη.1 ihξ.1, by
          rw [(deRhamOneDifferential (A := A) (B := B)).map_add,
            (q 2).map_add, ihη.2, ihξ.2, add_zero]⟩
      · intro c η hη ih
        have he : deRhamDegreeOneEquivA A B (c • η) =
            c • deRhamDegreeOneEquivA A B η := by
          change deRhamDegreeOneEquiv A B (c • η) =
            c • deRhamDegreeOneEquiv A B η
          exact (deRhamDegreeOneEquiv A B).map_smul c η
        have hw' : quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 2
            (deRhamWedge (A := A) (B := B) 1 1
              (deRhamUniversalDifferential A B c)
              (deRhamDegreeOneEquivA A B η)) = 0 := by
          exact quotientDeRhamProjection_wedge_zero π c _
            (quotientDeRhamProjection_one_zero π η ih.1)
        have hi' : quotientDeRhamProjection (A := A) (B := B) (Ω := Ω) π 2
            (deRhamOneDifferential (A := A) (B := B) η) = 0 := by
          rw [← q_apply]
          exact ih.2
        have hq : q 2 (deRhamOneDifferential (A := A) (B := B) (c • η)) = 0 := by
          simp only [deRhamOneDifferential, LinearMap.comp_apply]
          change q 2 (deRhamDifferential (A := A) (B := B) 1
            (deRhamDegreeOneEquivA A B (c • η))) = 0
          rw [he, deRhamDifferential_one_smul, q_apply]
          rw [map_add, map_smul, hw']
          change 0 + c • quotientDeRhamProjection
            (A := A) (B := B) (Ω := Ω) π 2
              (deRhamOneDifferential (A := A) (B := B) η) = 0
          rw [hi']
          simp
        exact ⟨(LinearMap.ker π).smul_mem c ih.1, hq⟩
    exact hp.2
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
        simp only [LinearMap.comp_apply]
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
