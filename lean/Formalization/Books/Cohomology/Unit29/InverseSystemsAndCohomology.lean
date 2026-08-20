import Formalization.Books.Algebra.Unit86.MittagLefflerSystems
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Formalization.Books.Cohomology.Unit02.CohomologyOfSheaves
import Formalization.Books.Cohomology.Unit05.FirstCohomologyAndExtensions
import Formalization.Books.Cohomology.Unit28.InverseSystems
import Formalization.Books.Modules.Unit04.Sections
import Formalization.Books.MoreAlgebra.Unit88.RlimOfModules
import Formalization.Books.Sheaves.Unit26.RingedSpaceModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.FiniteLength

/-!
# Cohomology of Sheaves, Chapter 29: inverse systems and cohomology, II

This file records the principal-ideal inverse-system interfaces and the
cohomological consequences from the source section.  Kernels, cokernels,
limits, and Mittag--Leffler conditions use the canonical categorical APIs.
-/

namespace Formalization.Books.Cohomology.Unit29

/-! ## 29.1. Inverse systems and cohomology, II -/

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Algebra.Unit86
open Formalization.Books.Categories.Unit21
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit05
open Formalization.Books.Cohomology.Unit28
open Formalization.Books.Modules.Unit04
open Formalization.Books.Sheaves.Unit10

universe v

noncomputable section

abbrev RingedSpace := Formalization.Books.Sheaves.Unit25.RingedSpace

abbrev SheafModule {X : RingedSpace.{v}} := Mod X.structureSheaf

abbrev GlobalSection {X : RingedSpace.{v}} :=
  (SheafOfModules.unit X.structureSheaf).sections

abbrev globalSectionValue {X : RingedSpace.{v}}
    (f : GlobalSection (X := X)) :
    X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)) :=
  f.eval (op (⊤ : Opens X.carrier))

abbrev globalSectionValueAt {X : RingedSpace.{v}}
    (f : GlobalSection (X := X)) (U : (Opens X.carrier)ᵒᵖ) :
    (X.structureSheaf.obj.obj U : Type v) :=
  f.eval U

/-! ## The scalar action of a global section -/

noncomputable def globalSectionScalarMap
    {X : RingedSpace.{v}} (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (F : SheafModule (X := X)) : F ⟶ F := by
  let φ : F.val.presheaf ⟶ F.val.presheaf :=
    { app := fun U => (F.val.obj U).smul (globalSectionValueAt f U)
      naturality := by
        intro U V h
        have hf : (X.structureSheaf.obj.map h).hom (globalSectionValueAt f U) =
            globalSectionValueAt f V := by
          change (X.structureSheaf.obj.map h).hom (f.eval U) = f.eval V
          exact f.property h
        rw [← hf]
        exact (PresheafOfModules.smul_map F.val h (globalSectionValueAt f U)).symm }
  exact { val := PresheafOfModules.homMk φ (by
    intro U r m
    dsimp [φ]
    change globalSectionValueAt f U • (r • m) =
      r • (globalSectionValueAt f U • m)
    rw [← mul_smul, ← mul_smul]
    exact congrArg (fun a => a • m) (hcentral U r) ) }

def globalSectionScalarPower
    {X : RingedSpace.{v}} (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (n : ℕ) (F : SheafModule (X := X)) : F ⟶ F :=
  match n with
  | 0 => 𝟙 F
  | n + 1 => globalSectionScalarPower f hcentral n F ≫
      globalSectionScalarMap f hcentral F

def IsFDivisible {X : RingedSpace.{v}} (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (G : SheafModule (X := X)) : Prop :=
  Epi (globalSectionScalarMap f hcentral G)

def IsFTorsionFree {X : RingedSpace.{v}} (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (F : SheafModule (X := X)) : Prop :=
  Mono (globalSectionScalarMap f hcentral F)

abbrev fTorsionObject {X : RingedSpace.{v}} (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (n : ℕ) (G : SheafModule (X := X)) : SheafModule (X := X) :=
  kernel (globalSectionScalarPower f hcentral n G)

abbrev fAdicQuotientObject {X : RingedSpace.{v}} (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (n : ℕ) (F : SheafModule (X := X)) : SheafModule (X := X) :=
  cokernel (globalSectionScalarPower f hcentral n F)

/-! ## Principal inverse systems -/

structure PrincipalInverseSystem (X : RingedSpace.{v}) where
  f : GlobalSection (X := X)
  central : ∀ (U : (Opens X.carrier)ᵒᵖ)
    (r : (X.structureSheaf.obj.obj U : Type v)),
    globalSectionValueAt f U * r = r * globalSectionValueAt f U
  stages : InverseSystem ℕ+ (SheafModule (X := X))
  scalar : ∀ n : ℕ+, stages.obj (op n) ⟶ stages.obj (op n)
  scalar_eq : ∀ n, scalar n = globalSectionScalarMap f central (stages.obj (op n))

abbrev stageMap {X : RingedSpace.{v}} (S : PrincipalInverseSystem X)
    {n m : ℕ+} (h : n ≤ m) : S.stages.obj (op m) ⟶ S.stages.obj (op n) :=
  S.stages.map (opHomOfLE h)

theorem positive_le_succ (n : ℕ+) : n ≤ n + 1 := by
  change (n : ℕ) ≤ (n : ℕ) + 1
  exact Nat.le_succ _

structure ConditionOne {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) where
  injection : ∀ n : ℕ+, S.stages.obj (op n) ⟶ S.stages.obj (op (n + 1))
  projection : ∀ n : ℕ+, S.stages.obj (op (n + 1)) ⟶ S.stages.obj (op 1)
  zero : ∀ n, injection n ≫ projection n = 0
  exact : ∀ n, (ShortComplex.mk (injection n) (projection n) (zero n)).ShortExact
  factor : ∀ n, S.scalar (n + 1) =
    stageMap S (positive_le_succ n) ≫ injection n

structure ConditionTwo {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) where
  injection : ∀ n : ℕ+, S.stages.obj (op 1) ⟶ S.stages.obj (op (n + 1))
  factorToFirst : ∀ n : ℕ+,
    S.stages.obj (op (n + 1)) ⟶ S.stages.obj (op 1)
  projection : ∀ n : ℕ+, S.stages.obj (op (n + 1)) ⟶ S.stages.obj (op n)
  zero : ∀ n, injection n ≫ projection n = 0
  exact : ∀ n, (ShortComplex.mk (injection n) (projection n) (zero n)).ShortExact
  factor : ∀ n, globalSectionScalarPower S.f S.central n.val
      (S.stages.obj (op (n + 1))) = factorToFirst n ≫ injection n
  projection_is_transition : ∀ n,
    projection n = stageMap S (positive_le_succ n)

structure ConditionThree {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) where
  G : SheafModule (X := X)
  divisible : IsFDivisible S.f S.central G
  stageIso : ∀ n : ℕ+, Nonempty
    (S.stages.obj (op n) ≅ fTorsionObject S.f S.central n.val G)

structure ConditionFour {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) where
  F : SheafModule (X := X)
  torsionFree : IsFTorsionFree S.f S.central F
  stageIso : ∀ n : ℕ+, Nonempty
    (S.stages.obj (op n) ≅ fAdicQuotientObject S.f S.central n.val F)

def PrincipalInverseSystem.IsConditionOne
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) : Prop :=
  Nonempty (ConditionOne S)

def PrincipalInverseSystem.IsConditionTwo
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) : Prop :=
  Nonempty (ConditionTwo S)

def PrincipalInverseSystem.IsConditionThree
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) : Prop :=
  Nonempty (ConditionThree S)

def PrincipalInverseSystem.IsConditionFour
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) : Prop :=
  Nonempty (ConditionFour S)

theorem condition_four_implies_three
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) :
    S.IsConditionFour → S.IsConditionThree := by
  sorry

theorem condition_three_iff_two
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) :
    S.IsConditionThree ↔ S.IsConditionTwo := by
  sorry

theorem condition_two_iff_one
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) :
    S.IsConditionTwo ↔ S.IsConditionOne := by
  sorry

theorem condition_four_implies_three_iff_two_iff_one
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) :
    S.IsConditionFour →
      (S.IsConditionThree ↔ S.IsConditionTwo) ∧
      (S.IsConditionTwo ↔ S.IsConditionOne) := by
  sorry

/-! ## Cohomology systems and the f-adic topology -/

abbrev cohomologyRing (X : RingedSpace.{v}) : Type v :=
  X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))

abbrev cohomologyDeltaFunctor (X : RingedSpace.{v}) :=
  ringedSpaceModuleCohomologyDeltaFunctor X

abbrev cohomologySystem {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) :
    InverseSystem ℕ+ (ModuleCat.{v} (cohomologyRing X)) :=
  S.stages ⋙ (cohomologyDeltaFunctor X).functor p

abbrev cohomologyLimit {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) :
    ModuleCat.{v} (cohomologyRing X) :=
  InverseSystemLimit (cohomologySystem S p)

def moduleScalarLinearMap {R M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] (r : R)
    (hcentral : ∀ s : R, r * s = s * r) : M →ₗ[R] M :=
  { toFun := fun m => r • m
    map_add' := by intro x y; rw [smul_add]
    map_smul' := by
      intro s m
      change r • (s • m) = s • (r • m)
      rw [← mul_smul, ← mul_smul, hcentral s] }

theorem central_pow {R : Type v} [Ring R] (f : R)
    (hcentral : ∀ s : R, f * s = s * f) :
    ∀ n : ℕ, ∀ s : R, f ^ n * s = s * f ^ n := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
      intro s
      calc
        f ^ (n + 1) * s = (f ^ n * f) * s := by rw [pow_succ]
        _ = f ^ n * (f * s) := by rw [mul_assoc]
        _ = f ^ n * (s * f) := by rw [hcentral]
        _ = (f ^ n * s) * f := by rw [mul_assoc]
        _ = (s * f ^ n) * f := by rw [ih]
        _ = s * (f ^ n * f) := by rw [mul_assoc]
        _ = s * f ^ (n + 1) := by rw [pow_succ]


/-! The arbitrary-ring sheaf interface used by the first five source lemmas. -/

abbrev AModuleSheaf (A : Type v) [CommRing A] (X : TopCat.{v}) :=
  SheafOfAModules A X

structure GeneralPrincipalInverseSystem (A : Type v) [CommRing A]
    (X : TopCat.{v}) where
  f : A
  stages : InverseSystem ℕ+ (AModuleSheaf A X)
  cohomology : SheafCohomologicalDeltaFunctor A X
  globalSections : AModuleSheaf A X ⥤ ModuleCat.{v} A
  degreeZero : Nonempty (cohomology.functor 0 ≅ globalSections)
  fScalar : ∀ F : AModuleSheaf A X, F ⟶ F
  scalar : ∀ n : ℕ+, stages.obj (op n) ⟶ stages.obj (op n)
  scalar_eq : ∀ n, fScalar (stages.obj (op n)) = scalar n

abbrev generalStageMap {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) {n m : ℕ+} (h : n ≤ m) :
    S.stages.obj (op m) ⟶ S.stages.obj (op n) :=
  S.stages.map (opHomOfLE h)

def endomorphismPower {C : Type v} [Category C] {M : C}
    (u : M ⟶ M) : ℕ → (M ⟶ M)
  | 0 => 𝟙 M
  | n + 1 => endomorphismPower u n ≫ u

structure GeneralConditionOne {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) where
  injection : ∀ n : ℕ+, S.stages.obj (op n) ⟶ S.stages.obj (op (n + 1))
  projection : ∀ n : ℕ+, S.stages.obj (op (n + 1)) ⟶ S.stages.obj (op 1)
  zero : ∀ n, injection n ≫ projection n = 0
  exact : ∀ n, (ShortComplex.mk (injection n) (projection n) (zero n)).ShortExact
  factor : ∀ n, S.scalar (n + 1) =
    generalStageMap S (positive_le_succ n) ≫ injection n

structure GeneralConditionTwo {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) where
  injection : ∀ n : ℕ+, S.stages.obj (op 1) ⟶ S.stages.obj (op (n + 1))
  factorToFirst : ∀ n : ℕ+, S.stages.obj (op (n + 1)) ⟶ S.stages.obj (op 1)
  projection : ∀ n : ℕ+, S.stages.obj (op (n + 1)) ⟶ S.stages.obj (op n)
  zero : ∀ n, injection n ≫ projection n = 0
  exact : ∀ n, (ShortComplex.mk (injection n) (projection n) (zero n)).ShortExact
  factor : ∀ n, endomorphismPower (S.scalar (n + 1)) n.val =
    factorToFirst n ≫ injection n
  projection_is_transition : ∀ n,
    projection n = generalStageMap S (positive_le_succ n)

structure GeneralConditionThree {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) where
  G : AModuleSheaf A X
  divisible : Epi (S.fScalar G)
  stageIso : ∀ n : ℕ+, Nonempty
    (S.stages.obj (op n) ≅ kernel (endomorphismPower (S.fScalar G) n.val))

structure GeneralConditionFour {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) where
  F : AModuleSheaf A X
  torsionFree : Mono (S.fScalar F)
  stageIso : ∀ n : ℕ+, Nonempty
    (S.stages.obj (op n) ≅ cokernel (endomorphismPower (S.fScalar F) n.val))

def GeneralPrincipalInverseSystem.IsConditionOne
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) : Prop :=
  Nonempty (GeneralConditionOne S)

def GeneralPrincipalInverseSystem.IsConditionTwo
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) : Prop :=
  Nonempty (GeneralConditionTwo S)

def GeneralPrincipalInverseSystem.IsConditionThree
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) : Prop :=
  Nonempty (GeneralConditionThree S)

def GeneralPrincipalInverseSystem.IsConditionFour
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) : Prop :=
  Nonempty (GeneralConditionFour S)

theorem general_condition_four_implies_three
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) :
    S.IsConditionFour → S.IsConditionThree := by
  sorry

theorem general_condition_three_iff_two
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) :
    S.IsConditionThree ↔ S.IsConditionTwo := by
  sorry

theorem general_condition_two_iff_one
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) :
    S.IsConditionTwo ↔ S.IsConditionOne := by
  sorry

theorem general_condition_four_implies_three_iff_two_iff_one
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) :
    S.IsConditionFour →
      (S.IsConditionThree ↔ S.IsConditionTwo) ∧
      (S.IsConditionTwo ↔ S.IsConditionOne) := by
  sorry

abbrev generalCohomologySystem {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) :
    InverseSystem ℕ+ (ModuleCat.{v} A) :=
  S.stages ⋙ S.cohomology.functor p

abbrev generalCohomologyLimit {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) :
    ModuleCat.{v} A :=
  InverseSystemLimit (generalCohomologySystem S p)

def generalInverseLimitFiltrationAt {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ)
    (n : ℕ+) : Submodule A (generalCohomologyLimit S p : Type v) :=
  LinearMap.ker ((limit.π (generalCohomologySystem S p) (op n)).hom)

def generalModuleScalarLinearMap {A M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] (r : A) : M →ₗ[A] M :=
  moduleScalarLinearMap r (fun s => mul_comm r s)

def generalFPowerRange {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ)
    (n : ℕ+) : Submodule A (generalCohomologyLimit S p : Type v) :=
  LinearMap.range (generalModuleScalarLinearMap (M := (generalCohomologyLimit S p : Type v))
    (S.f ^ n.val))

def generalFAdicBasisSets {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) :
    Set (Set (generalCohomologyLimit S p : Type v)) :=
  {U | ∃ n : ℕ, ∃ x : (generalCohomologyLimit S p : Type v),
    U = {y | ∃ z ∈ ((LinearMap.range
      (generalModuleScalarLinearMap (M := (generalCohomologyLimit S p : Type v))
        (S.f ^ n)) : Submodule A (generalCohomologyLimit S p : Type v)) : Set _),
      y = x + z}}

def generalInverseLimitTopology {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) :
    TopologicalSpace (generalCohomologyLimit S p : Type v) :=
  ⨅ n : ℕ+, TopologicalSpace.induced
    ((limit.π (generalCohomologySystem S p) (op n)).hom)
    (⊤ : TopologicalSpace ((generalCohomologySystem S p).obj (op n) : Type v))

def generalFAdicTopology {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) :
    TopologicalSpace (generalCohomologyLimit S p : Type v) :=
  TopologicalSpace.generateFrom (generalFAdicBasisSets S p)

theorem general_topology_I_adic_f
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) (p : ℕ)
    (hS : S.IsConditionOne) :
    (∀ c : ℕ+, generalFPowerRange S p c =
      generalInverseLimitFiltrationAt S p c) ∧
      generalInverseLimitTopology S p = generalFAdicTopology S p := by
  sorry

def generalFAdicLimitQuotient {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) :
    ModuleCat.{v} A :=
  ModuleCat.of A
    ((generalCohomologyLimit S p : Type v) ⧸ generalFPowerRange S p
      ⟨1, Nat.zero_lt_succ 0⟩)

def generalFAdicLimitImageAtOne {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) :
    ModuleCat.{v} A :=
  ModuleCat.of A
    (LinearMap.range ((limit.π (generalCohomologySystem S p)
      (op (1 : ℕ+))).hom) : Type v)

theorem general_limit_finite
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X)
    [IsNoetherianRing A]
    (hcomplete : IsAdicComplete (Ideal.span ({S.f} : Set A)) A)
    (hF₁ : Module.Finite A ((S.globalSections).obj
      (S.stages.obj (op (1 : ℕ+))) : Type v))
    (hS : S.IsConditionOne) :
    Module.Finite A (generalCohomologyLimit S 0 : Type v) ∧
      Function.Injective
        (fun x : (generalCohomologyLimit S 0 : Type v) => S.f • x) ∧
      Nonempty (generalFAdicLimitQuotient S 0 ≅
        generalFAdicLimitImageAtOne S 0) := by
  sorry

def generalCohomologyImageToFirst {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ)
    (m : ℕ+) : Submodule A
      ((generalCohomologySystem S (p + 1)).obj (op (1 : ℕ+)) : Type v) :=
  LinearMap.range (((generalCohomologySystem S (p + 1)).map
    (opHomOfLE (show (1 : ℕ+) ≤ m by exact m.2))).hom)

def generalCohomologyStableImageToFirst {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) :
    Submodule A ((generalCohomologySystem S (p + 1)).obj
      (op (1 : ℕ+)) : Type v) :=
  ⨅ m : ℕ+, generalCohomologyImageToFirst S p m

def GeneralMLFirstHypothesis {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) : Prop :=
  IsFiniteLength A ((generalCohomologySystem S (p + 1)).obj
      (op (1 : ℕ+)) : Type v) ∨
    (IsNoetherianRing A ∧ Module.Finite A
      ((generalCohomologySystem S (p + 1)).obj
        (op (1 : ℕ+)) : Type v))

def GeneralMLBetterFirstHypothesis {A : Type v} [CommRing A]
    {X : TopCat.{v}} (S : GeneralPrincipalInverseSystem A X) (p : ℕ) : Prop :=
  (∃ m : ℕ+, IsFiniteLength A
      (generalCohomologyImageToFirst S p m : Type v)) ∨
    (IsNoetherianRing A ∧ Module.Finite A
      (generalCohomologyStableImageToFirst S p : Type v))

theorem general_lemma_ML
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) (p : ℕ)
    (hF : GeneralMLFirstHypothesis S p) (hS : S.IsConditionOne) :
    IsMittagLefflerModuleSystem (generalCohomologySystem S p) := by
  sorry

theorem general_lemma_ML_better
    {A : Type v} [CommRing A] {X : TopCat.{v}}
    (S : GeneralPrincipalInverseSystem A X) (p : ℕ)
    (hF : GeneralMLBetterFirstHypothesis S p) (hS : S.IsConditionOne) :
    IsMittagLefflerModuleSystem (generalCohomologySystem S p) := by
  sorry


def fPowerSubmodule {R M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    (f : R) (hcentral : ∀ s : R, f * s = s * f) (n : ℕ) : Submodule R M :=
  LinearMap.range (moduleScalarLinearMap (M := M) (f ^ n)
    (central_pow f hcentral n))

def principalIdeal {X : RingedSpace.{v}} (f : GlobalSection (X := X))
    (hcentral : ∀ s : cohomologyRing X,
      globalSectionValue f * s = s * globalSectionValue f) :
    Submodule (cohomologyRing X) (cohomologyRing X) :=
  fPowerSubmodule (globalSectionValue f) hcentral 1

def fAdicBasisSets {R M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    (f : R) (hcentral : ∀ s : R, f * s = s * f) : Set (Set M) :=
  {U | ∃ n : ℕ, ∃ x : M,
    U = {y | ∃ z ∈ (fPowerSubmodule (R := R) (M := M) f hcentral n : Set M),
      y = x + z}}

def IsFAdicallyComplete {R : Type v} [Ring R] (f : R)
    (hcentral : ∀ s : R, f * s = s * f) : Prop :=
  ∀ (x : ℕ → R),
    (∀ ⦃m n : ℕ⦄, m ≤ n →
      x m - x n ∈ fPowerSubmodule f hcentral m) →
    ∃ L : R, ∀ n : ℕ, L - x n ∈ fPowerSubmodule f hcentral n

/-! The source's ring-completeness hypothesis uses Mathlib's canonical
`IsAdicComplete` predicate for the principal ideal generated by `f`.  The
sequential predicate above is retained for the explicitly topological
formulation of the preceding lemma. -/

abbrev IsPrincipalIdealComplete {R : Type v} [CommRing R] (f : R) : Prop :=
  IsAdicComplete (Ideal.span ({f} : Set R)) R

@[instance_reducible]
def inverseLimitTopology {R : Type v} [Ring R]
    {M : InverseSystem ℕ+ (ModuleCat.{v} R)} :
    TopologicalSpace ((InverseSystemLimit M : ModuleCat.{v} R) : Type v) :=
  ⨅ n : ℕ+, TopologicalSpace.induced
    ((limit.π M (op n)).hom)
    (⊤ : TopologicalSpace (M.obj (op n) : Type v))

def fAdicTopology {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) :
    TopologicalSpace ((cohomologyLimit S p : ModuleCat.{v} (cohomologyRing X)) : Type v) :=
  TopologicalSpace.generateFrom (fAdicBasisSets
    (M := (cohomologyLimit S p : Type v)) (globalSectionValue S.f)
    (fun s => S.central (op (⊤ : Opens X.carrier)) s))

def inverseLimitFiltrationAt {R : Type v} [Ring R]
    {M : InverseSystem ℕ+ (ModuleCat.{v} R)} (n : ℕ+) :
    Submodule R ((InverseSystemLimit M : ModuleCat.{v} R) : Type v) :=
  LinearMap.ker ((limit.π M (op n)).hom)

def fPowerRange {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) (n : ℕ+) :
    Submodule (cohomologyRing X)
      ((cohomologyLimit S p : ModuleCat.{v} (cohomologyRing X)) : Type v) :=
  LinearMap.range (moduleScalarLinearMap
    (M := (cohomologyLimit S p : Type v))
    (globalSectionValue S.f ^ n.val)
    (central_pow (globalSectionValue S.f)
      (fun s => S.central (op (⊤ : Opens X.carrier)) s) n.val))

def cohomologyLimitImageAt {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) (n : ℕ+) :
    Submodule (cohomologyRing X)
      ((cohomologySystem S p).obj (op n) : Type v) :=
  LinearMap.range ((limit.π (cohomologySystem S p) (op n)).hom)

theorem topology_I_adic_f
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) (p : ℕ)
    (hS : S.IsConditionOne) :
    (∀ c : ℕ+, fPowerRange S p c =
      inverseLimitFiltrationAt (M := cohomologySystem S p) c) ∧
      inverseLimitTopology (M := cohomologySystem S p) = fAdicTopology S p := by
  sorry

/-! ## Finiteness of the inverse limit -/

def fAdicLimitQuotient {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) : ModuleCat.{v} (cohomologyRing X) :=
  ModuleCat.of (cohomologyRing X)
    ((cohomologyLimit S p : Type v) ⧸ fPowerRange S p ⟨1, Nat.zero_lt_succ 0⟩)

def fAdicLimitImageAtOne {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) : ModuleCat.{v} (cohomologyRing X) :=
  ModuleCat.of (cohomologyRing X)
    (cohomologyLimitImageAt S p ⟨1, Nat.zero_lt_succ 0⟩ : Type v)

theorem limit_finite
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X)
    [IsNoetherianRing (cohomologyRing X)]
    (hcomplete : IsFAdicallyComplete (globalSectionValue S.f)
      (fun s => S.central (op (⊤ : Opens X.carrier)) s))
    (hF₁ : Module.Finite (cohomologyRing X)
      ((ringedSpaceModuleGlobalSections X).obj
        (S.stages.obj (op (1 : ℕ+))) : Type v))
    (hS : S.IsConditionOne) :
    Module.Finite (cohomologyRing X) (cohomologyLimit S 0 : Type v) ∧
      Function.Injective (fun x : (cohomologyLimit S 0 : Type v) =>
        globalSectionValue S.f • x) ∧
      Nonempty (fAdicLimitQuotient S 0 ≅ fAdicLimitImageAtOne S 0) := by
  sorry

/-! ## Mittag--Leffler criteria -/

abbrev firstCohomologyModule {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) : Type v :=
  (cohomologySystem S p).obj (op (1 : ℕ+))

def cohomologyImageToFirst {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) (m : ℕ+) :
    Submodule (cohomologyRing X) (firstCohomologyModule S p) :=
  LinearMap.range (((cohomologySystem S p).map
    (opHomOfLE (show (1 : ℕ+) ≤ m by exact m.2))).hom)

def cohomologyStableImageToFirst {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) :
    Submodule (cohomologyRing X) (firstCohomologyModule S p) :=
  ⨅ m : ℕ+, cohomologyImageToFirst S p m

def MLFirstHypothesis {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) : Prop :=
  IsFiniteLength (cohomologyRing X) (firstCohomologyModule S (p + 1)) ∨
    (IsNoetherianRing (cohomologyRing X) ∧
      Module.Finite (cohomologyRing X) (firstCohomologyModule S (p + 1)))

def MLBetterFirstHypothesis {X : RingedSpace.{v}}
    (S : PrincipalInverseSystem X) (p : ℕ) : Prop :=
  (∃ m : ℕ+, IsFiniteLength (cohomologyRing X)
      (cohomologyImageToFirst S (p + 1) m : Type v)) ∨
    (IsNoetherianRing (cohomologyRing X) ∧
      Module.Finite (cohomologyRing X)
        (cohomologyStableImageToFirst S (p + 1) : Type v))

theorem lemma_ML
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) (p : ℕ)
    (hF : MLFirstHypothesis S p) (hS : S.IsConditionOne) :
    IsMittagLefflerModuleSystem (cohomologySystem S p) := by
  sorry

theorem lemma_ML_better
    {X : RingedSpace.{v}} (S : PrincipalInverseSystem X) (p : ℕ)
    (hF : MLBetterFirstHypothesis S p) (hS : S.IsConditionOne) :
    IsMittagLefflerModuleSystem (cohomologySystem S p) := by
  sorry

/-! ## The comparison exact sequence for a torsion-free sheaf -/

abbrev cohomologyObject {X : RingedSpace.{v}}
    (F : SheafModule (X := X)) (p : ℕ) : ModuleCat.{v} (cohomologyRing X) :=
  (cohomologyDeltaFunctor X).functor p |>.obj F

def fQuotientCohomologyStage {X : RingedSpace.{v}}
    (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (F : SheafModule (X := X)) (p : ℕ) (n : ℕ+) :
    ModuleCat.{v} (cohomologyRing X) :=
  ModuleCat.of (cohomologyRing X)
    ((cohomologyObject F p : Type v) ⧸
      fPowerSubmodule (R := cohomologyRing X)
        (M := (cohomologyObject F p : Type v)) (globalSectionValue f)
        (fun s => hcentral (op (⊤ : Opens X.carrier)) s) n.val)

def fTorsionCohomologySubmodule {X : RingedSpace.{v}}
    (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (F : SheafModule (X := X)) (p : ℕ) (n : ℕ+) :
    Submodule (cohomologyRing X) (cohomologyObject F (p + 1) : Type v) :=
  LinearMap.ker (moduleScalarLinearMap
    (M := (cohomologyObject F (p + 1) : Type v))
    (globalSectionValue f ^ n.val)
    (central_pow (globalSectionValue f)
      (fun s => hcentral (op (⊤ : Opens X.carrier)) s) n.val))

def fTorsionCohomologyStage {X : RingedSpace.{v}}
    (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (F : SheafModule (X := X)) (p : ℕ) (n : ℕ+) :
    ModuleCat.{v} (cohomologyRing X) :=
  ModuleCat.of (cohomologyRing X)
    (fTorsionCohomologySubmodule f hcentral F p n : Type v)

structure InverseSystemShortExact {R : Type v} [Ring R]
    (L M N : InverseSystem ℕ+ (ModuleCat.{v} R)) where
  inclusion : ∀ n : ℕ+, L.obj (op n) ⟶ M.obj (op n)
  projection : ∀ n : ℕ+, M.obj (op n) ⟶ N.obj (op n)
  zero : ∀ n, inclusion n ≫ projection n = 0
  exact : ∀ n, (ShortComplex.mk (inclusion n) (projection n) (zero n)).ShortExact
  inclusion_natural : ∀ {n m : ℕ+} (h : n ≤ m),
    L.map (opHomOfLE h) ≫ inclusion n = inclusion m ≫ M.map (opHomOfLE h)
  projection_natural : ∀ {n m : ℕ+} (h : n ≤ m),
    M.map (opHomOfLE h) ≫ projection n = projection m ≫ N.map (opHomOfLE h)

structure BocksteinSystemData {X : RingedSpace.{v}}
    (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (F : SheafModule (X := X)) (p : ℕ) where
  left : InverseSystem ℕ+ (ModuleCat.{v} (cohomologyRing X))
  middle : InverseSystem ℕ+ (ModuleCat.{v} (cohomologyRing X))
  right : InverseSystem ℕ+ (ModuleCat.{v} (cohomologyRing X))
  left_stage : ∀ n, Nonempty
    (left.obj (op n) ≅ fQuotientCohomologyStage f hcentral F p n)
  middle_stage : ∀ n, Nonempty
    (middle.obj (op n) ≅
      (cohomologyObject (fAdicQuotientObject f hcentral n.val F) p))
  right_stage : ∀ n, Nonempty
    (right.obj (op n) ≅ fTorsionCohomologyStage f hcentral F p n)
  left_mittag_leffler : IsMittagLefflerModuleSystem left
  short_exact : InverseSystemShortExact left middle right

theorem exists_bockstein_system {X : RingedSpace.{v}}
    (f : GlobalSection (X := X))
    (hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U)
    (F : SheafModule (X := X)) (p : ℕ)
    (hF : IsFTorsionFree f hcentral F) :
    Nonempty (BocksteinSystemData f hcentral F p) := by
  sorry

abbrev bocksteinCompletion {X : RingedSpace.{v}}
    {f : GlobalSection (X := X)} {hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U}
    {F : SheafModule (X := X)} {p : ℕ}
    (D : BocksteinSystemData f hcentral F p) :
    ModuleCat.{v} (cohomologyRing X) := InverseSystemLimit D.left

abbrev bocksteinMiddleLimit {X : RingedSpace.{v}}
    {f : GlobalSection (X := X)} {hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U}
    {F : SheafModule (X := X)} {p : ℕ}
    (D : BocksteinSystemData f hcentral F p) :
    ModuleCat.{v} (cohomologyRing X) := InverseSystemLimit D.middle

abbrev bocksteinTateModule {X : RingedSpace.{v}}
    {f : GlobalSection (X := X)} {hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U}
    {F : SheafModule (X := X)} {p : ℕ}
    (D : BocksteinSystemData f hcentral F p) :
    ModuleCat.{v} (cohomologyRing X) := InverseSystemLimit D.right

/-! These source-facing aliases make the first displayed sequence read as
completion, middle cohomology, and Tate module, while retaining the
canonical inverse-limit constructions above. -/

abbrev usualFAdicCompletion {X : RingedSpace.{v}}
    {f : GlobalSection (X := X)} {hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U}
    {F : SheafModule (X := X)} {p : ℕ}
    (D : BocksteinSystemData f hcentral F p) :
    ModuleCat.{v} (cohomologyRing X) := bocksteinCompletion D

abbrev fAdicTateModule {X : RingedSpace.{v}}
    {f : GlobalSection (X := X)} {hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U}
    {F : SheafModule (X := X)} {p : ℕ}
    (D : BocksteinSystemData f hcentral F p) :
    ModuleCat.{v} (cohomologyRing X) := bocksteinTateModule D

structure ModuleShortExact {R : Type v} [Ring R]
    {L M N : ModuleCat.{v} R} where
  inclusion : L ⟶ M
  projection : M ⟶ N
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact

theorem bockstein_limit_exact {X : RingedSpace.{v}}
    {f : GlobalSection (X := X)}
    {hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U}
    {F : SheafModule (X := X)} {p : ℕ}
    (D : BocksteinSystemData f hcentral F p) :
    Nonempty (ModuleShortExact (L := usualFAdicCompletion D)
      (M := bocksteinMiddleLimit D) (N := fAdicTateModule D)) := by
  sorry

noncomputable abbrev firstDerivedLimit {R : Type v} [Ring R]
    [HasInjectiveResolutions (ℕ+ᵒᵖ ⥤ ModuleCat.{v} R)]
    [(lim : (ℕ+ᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R).Additive]
    (M : InverseSystem ℕ+ (ModuleCat.{v} R)) : ModuleCat.{v} R :=
  ((lim : (ℕ+ᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R).rightDerived 1).obj M

theorem bockstein_first_derived_limit_iso {X : RingedSpace.{v}}
    {f : GlobalSection (X := X)}
    {hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U}
    {F : SheafModule (X := X)} {p : ℕ}
    [HasInjectiveResolutions
      ((ℕ+ᵒᵖ ⥤ ModuleCat.{v} (cohomologyRing X)))]
    [(lim : (ℕ+ᵒᵖ ⥤ ModuleCat.{v} (cohomologyRing X)) ⥤
      ModuleCat.{v} (cohomologyRing X)).Additive]
    (D : BocksteinSystemData f hcentral F p) :
    Nonempty (firstDerivedLimit D.middle ≅ firstDerivedLimit D.right) := by
  sorry

theorem bockstein_torsion_mittag_leffler_iff {X : RingedSpace.{v}}
    {f : GlobalSection (X := X)}
    {hcentral : ∀ (U : (Opens X.carrier)ᵒᵖ)
      (r : (X.structureSheaf.obj.obj U : Type v)),
      globalSectionValueAt f U * r = r * globalSectionValueAt f U}
    {F : SheafModule (X := X)} {p : ℕ}
    (D : BocksteinSystemData f hcentral F p) :
    IsMittagLefflerModuleSystem D.right ↔
      IsMittagLefflerModuleSystem D.middle := by
  sorry

end

end Formalization.Books.Cohomology.Unit29
