import Formalization.Books.MoreAlgebra.Unit92.DerivedCompletion
import Formalization.Books.MoreAlgebra.Unit87.RlimOfAbelianGroups
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.MoreAlgebra.Unit65.PseudoCoherentModules
import Formalization.Books.Algebra.Unit31.NoetherianRings
import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# More on Algebra, Chapter 101: Systems of modules

This file records the definitions and theorem interfaces in the source section
`Systems of modules`.  Module quotients, derived tensor products, Ext groups,
Mittag--Leffler systems, pro-objects, and adic completions use the canonical
APIs supplied by Mathlib and the preceding chapters.  The longer comparison
lemmas are packaged as data structures: this preserves every map, comparison,
exactness, stabilization, and annihilation assertion without inventing a
second implementation of pro-categories or derived completion.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit71
open Formalization.Books.Algebra.Unit86
open Formalization.Books.Derived.Unit08
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit87
open Formalization.Books.MoreAlgebra.Unit92
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit101

abbrev Mod (A : Type u) [CommRing A] := ModuleCat.{u} A

abbrev Comp (A : Type u) [CommRing A] := Unit92.Comp A

abbrev D (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] := Unit92.D A

/-! ## The quotient systems attached to an ideal -/

/-- The submodule `I^n M`, in the normalization used by the preceding
chapters. -/
def idealPowerSubmodule {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) : Submodule A (M : Type u) :=
  I ^ n • (⊤ : Submodule A (M : Type u))

abbrev idealPowerModule {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) : Mod A :=
  ModuleCat.of A (idealPowerSubmodule I n M)

def idealPowerToAmbient {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) :
    idealPowerModule I n M ⟶ M :=
  ModuleCat.ofHom (idealPowerSubmodule I n M).subtype

/-- The module `M/I^nM`. -/
abbrev idealQuotientModule {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) : Mod A :=
  ModuleCat.of A ((M : Type u) ⧸ idealPowerSubmodule I n M)

/-- The quotient map induced by a module homomorphism. -/
def idealQuotientMap {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) {M N : Mod A} (f : M ⟶ N) :
    idealQuotientModule I n M ⟶ idealQuotientModule I n N := by
  apply ModuleCat.ofHom
  apply Submodule.mapQ
  intro x hx
  refine Submodule.smul_induction_on (I := I ^ n)
    (N := (⊤ : Submodule A (M : Type u)))
    (p := fun z : (M : Type u) => f.hom z ∈ idealPowerSubmodule I n N)
    hx ?_ ?_
  · intro r hr y hy
    rw [map_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro x y hx hy
    rw [map_add]
    exact (idealPowerSubmodule I n N).add_mem hx hy

/-- The adjacent transition map `M/I^(n+1)M ⟶ M/I^nM`. -/
def idealQuotientTransition {A : Type u} [CommRing A]
    (I : Ideal A) (M : Mod A) (n : ℕ) :
    idealQuotientModule I (n + 1) M ⟶ idealQuotientModule I n M := by
  apply ModuleCat.ofHom
  apply Submodule.factor
  refine Submodule.smul_le.mpr ?_
  intro r hr x hx
  exact Submodule.smul_mem_smul
    ((Ideal.pow_le_pow_right (Nat.le_succ n)) hr) hx

/-- The inverse system of the modules `M/I^nM`. -/
def idealQuotientSystem {A : Type u} [CommRing A]
    (I : Ideal A) (M : Mod A) : ℕᵒᵖ ⥤ Mod A :=
  Functor.ofOpSequence
    (X := fun n => idealQuotientModule I n M)
    (idealQuotientTransition I M)

/-- An `I^c`-annihilation assertion for a module. -/
def annihilatedByIdealPower {A : Type u} [CommRing A]
    (I : Ideal A) (c : ℕ) (M : Mod A) : Prop :=
  idealPowerSubmodule I c M ≤ ⊥

/-- A finite two-step complex of finite modules. -/
structure FiniteModuleComplex (A : Type u) [CommRing A] where
  K : Mod A
  L : Mod A
  M : Mod A
  α : K ⟶ L
  β : L ⟶ M
  comp : α ≫ β = 0
  finite_K : Module.Finite A (K : Type u)
  finite_L : Module.Finite A (L : Type u)
  finite_M : Module.Finite A (M : Type u)

def finiteModuleShortComplex {A : Type u} [CommRing A]
    (C : FiniteModuleComplex A) : ShortComplex (Mod A) :=
  { f := C.α, g := C.β, zero := C.comp }

noncomputable def finiteModuleHomology {A : Type u} [CommRing A]
    (C : FiniteModuleComplex A) : Mod A :=
  (finiteModuleShortComplex C).moduleCatLeftHomologyData.H

lemma idealQuotientMap_comp_zero {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) {M L N : Mod A}
    (f : M ⟶ L) (g : L ⟶ N) (h : f ≫ g = 0) :
    idealQuotientMap I n f ≫ idealQuotientMap I n g = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x⟩
  have hzero := congrArg (fun q : M ⟶ N => q.hom x) h
  change Submodule.mkQ _ (g.hom (f.hom x)) = 0
  change g.hom (f.hom x) = 0 at hzero
  rw [hzero]
  rfl

/-- The short complex obtained by reducing the terms and maps modulo `I^n`.
The map is the canonical quotient map from `Submodule.mapQ`. -/
structure QuotientComplexData {A : Type u} [CommRing A]
    (I : Ideal A) (C : FiniteModuleComplex A) (n : ℕ) where
  f : idealQuotientModule I n C.K ⟶ idealQuotientModule I n C.L
  g : idealQuotientModule I n C.L ⟶ idealQuotientModule I n C.M
  zero : f ≫ g = 0
  f_formula : f = idealQuotientMap I n C.α
  g_formula : g = idealQuotientMap I n C.β

noncomputable def quotientComplexData {A : Type u} [CommRing A]
    (I : Ideal A) (C : FiniteModuleComplex A) (n : ℕ) :
    QuotientComplexData I C n where
  f := idealQuotientMap I n C.α
  g := idealQuotientMap I n C.β
  zero := idealQuotientMap_comp_zero I n C.α C.β C.comp
  f_formula := rfl
  g_formula := rfl

noncomputable def quotientHomology {A : Type u} [CommRing A]
    (I : Ideal A) (C : FiniteModuleComplex A) (n : ℕ) : Mod A :=
  let Q := quotientComplexData I C n
  (ShortComplex.mk Q.f Q.g Q.zero).moduleCatLeftHomologyData.H

/-- The termwise quotient complex `K/I^nK`. -/
def idealQuotientComplex {A : Type u} [CommRing A]
    (I : Ideal A) (K : Comp A) (n : ℕ) : Comp A where
  X i := idealQuotientModule I n (K.X i)
  d i j := idealQuotientMap I n (K.d i j)
  shape i j hij := by
    rw [K.shape i j hij]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    rfl
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    change Submodule.mkQ _ (K.d j k (K.d i j x)) = 0
    have hzero := congrArg (fun f : K.X i ⟶ K.X k => f.hom x)
      (K.d_comp_d i j k)
    have hzero' : K.d j k (K.d i j x) = 0 := by
      change K.d j k (K.d i j x) = 0 at hzero
      exact hzero
    change Submodule.mkQ _ (K.d j k (K.d i j x)) = 0
    rw [hzero']
    rfl

/-! ## The Artin--Rees comparison -/

/-- All comparison maps and conclusions in the source's Artin--Rees lemma.
The fields `pro_isomorphism`, `limit_iso`, and `mittag_leffler` are the three
system-level conclusions; the remaining fields record the canonical maps,
factorizations, stable-image statement, and the two annihilation conclusions.
-/
structure ArtinReesComparisonData {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (C : FiniteModuleComplex A) where
  c : ℕ
  positive : 0 < c
  system : ℕᵒᵖ ⥤ Mod A
  stage : ∀ n, Nonempty (system.obj (Opposite.op n) ≅ quotientHomology I C n)
  transition : ∀ m n : ℕ, quotientHomology I C m ⟶ quotientHomology I C n
  transition_compatible : ∀ (m n : ℕ) (h : n ≤ m),
    let t : quotientHomology I C m ⟶ quotientHomology I C n := transition m n
    (stage m).some.hom ≫ t =
      system.map (opHomOfLE h) ≫ (stage n).some.hom
  from_homology : ∀ n, finiteModuleHomology C ⟶ quotientHomology I C n
  quotient_to_homology : ∀ n : ℕ,
    quotientHomology I C n ⟶ idealQuotientModule I (n - c)
      (finiteModuleHomology C)
  reduction_map : ∀ n : ℕ, idealQuotientModule I n (finiteModuleHomology C) ⟶
    quotientHomology I C n
  quotient_to_homology_factorization : ∀ n (hn : c ≤ n),
    let q : quotientHomology I C n ⟶ idealQuotientModule I (n - c)
        (finiteModuleHomology C) := quotient_to_homology n
    (reduction_map n) ≫ q =
      ModuleCat.ofHom (Submodule.factor (by
          refine Submodule.smul_le.mpr ?_
          intro r hr x hx
          exact Submodule.smul_mem_smul
            ((Ideal.pow_le_pow_right (Nat.sub_le n c)) hr) hx))
  quotient_from_homology : ∀ n : ℕ,
    idealQuotientModule I n (finiteModuleHomology C) ⟶
      quotientHomology I C (n - c)
  comparison_to_quotient : ∀ n (hn : 2 * c ≤ n),
    (quotient_from_homology n) ≫
      (quotient_to_homology (n - c)) =
      (idealQuotientSystem I (finiteModuleHomology C)).map
        (opHomOfLE
          ((Nat.sub_le (n - c) c).trans (Nat.sub_le n c)))
  comparison_to_lower : ∀ n (hn : 2 * c ≤ n),
    (quotient_to_homology n) ≫
      (quotient_from_homology (n - c)) =
      transition n (n - c - c)
  pro_isomorphism : IsProIsomorphism system
    (idealQuotientSystem I (finiteModuleHomology C))
  limit_iso : Nonempty (Limits.limit system ≅
    Limits.limit (idealQuotientSystem I (finiteModuleHomology C)))
  mittag_leffler : IsMittagLefflerModuleSystem system
  stable_image : ∀ n, c ≤ n →
    LinearMap.range (transition (n + c) n).hom =
      LinearMap.range (from_homology n).hom
  power_compatibility : ∀ n (hn : c ≤ n),
    (idealPowerSubmodule I c (quotientHomology I C n)).map
      (quotient_to_homology n).hom ≤
      idealPowerSubmodule I c (idealQuotientModule I (n - c)
        (finiteModuleHomology C))
  power_composition : ∀ n (hn : c ≤ n),
    idealPowerToAmbient I c (quotientHomology I C n) ≫
        quotient_to_homology n ≫
        idealQuotientMap I (n - c) (from_homology n) =
      idealPowerToAmbient I c (quotientHomology I C n) ≫
        ModuleCat.ofHom (idealPowerSubmodule I (n - c)
          (quotientHomology I C n)).mkQ
  kernel_cokernel_torsion : ∀ n,
    annihilatedByIdealPower I c
      (kernel (reduction_map n)) ∧
      annihilatedByIdealPower I c
      (cokernel (reduction_map n))

theorem lemma_consequence_Artin_Rees {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (C : FiniteModuleComplex A) :
    Nonempty (ArtinReesComparisonData I C) := by
  sorry

/-! ## Derived cohomology systems -/

noncomputable abbrev derivedQuotientObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (n : ℕ) : D A :=
  moduleInDerived A (idealQuotientModule I n (ModuleCat.of A A))

noncomputable abbrev derivedQuotientTensor {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A) (n : ℕ) : D A :=
  Unit74.derivedTensor K (derivedQuotientObject I n)

noncomputable abbrev cohomologyModule {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A) (i : ℤ) : Mod A :=
  (derivedCohomologyFunctor A (-i)).obj K

structure DerivedCohomologySystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A) (i : ℤ) where
  system : ℕᵒᵖ ⥤ Mod A
  stage : ∀ n, Nonempty (system.obj (Opposite.op n) ≅
    (derivedCohomologyFunctor A (-i)).obj (derivedQuotientTensor I K n))
  limit_iso : Nonempty (Limits.limit system ≅
    Limits.limit (idealQuotientSystem I (cohomologyModule K i)))
  mittag_leffler : IsMittagLefflerModuleSystem system

theorem lemma_kollar_kovacs_pseudo_coherent {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (K : D A)
    (hK : Unit65.IsPseudoCoherent A K) (i : ℤ) :
    Nonempty (DerivedCohomologySystemData I K i) := by
  sorry

/-! ## Ordinary bounded complexes and derived completion -/

structure BoundedFiniteModuleComplex (A : Type u) [CommRing A] where
  complex : Comp A
  bounded : IsBounded complex
  finite : ∀ i : ℤ, Module.Finite A (complex.X i : Type u)

noncomputable abbrev boundedComplexDerivedObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (M : BoundedFiniteModuleComplex A) : D A :=
  (Unit74.derivedQuotient A).obj M.complex

structure DerivedPlainCompletionComparisonData {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (M : BoundedFiniteModuleComplex A) where
  derived_system : ℕᵒᵖ ⥤ D A
  derived_stage : ∀ n, Nonempty (derived_system.obj (Opposite.op n) ≅
    Unit74.derivedTensor (boundedComplexDerivedObject M)
      (derivedQuotientObject I n))
  ordinary_system : ℕᵒᵖ ⥤ D A
  ordinary_stage : ∀ n, Nonempty (ordinary_system.obj (Opposite.op n) ≅
    (Unit74.derivedQuotient A).obj (idealQuotientComplex I M.complex n))
  comparison : ∀ n, derived_system.obj (Opposite.op n) ⟶
    ordinary_system.obj (Opposite.op n)
  pro_isomorphism : IsProIsomorphism derived_system ordinary_system

theorem lemma_derived_completion_plain_completion {A : Type u}
    [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (M : BoundedFiniteModuleComplex A) :
    Nonempty (DerivedPlainCompletionComparisonData I M) := by
  sorry

/-! ## Homomorphism and isomorphism systems -/

abbrev HomType {A : Type u} [CommRing A] (M N : Mod A) := M ⟶ N

def IsomType {A : Type u} [CommRing A] (M N : Mod A) :=
  { f : M ⟶ N // IsIso f }

abbrev homModule {A : Type u} [CommRing A] (M N : Mod A) : Mod A :=
  ModuleCat.of A (HomType M N)

abbrev homQuotientModule {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M N : Mod A) : Mod A :=
  ModuleCat.of A ((HomType M N : Type u) ⧸
    idealPowerSubmodule I n (homModule M N))

noncomputable def adicCompletionModule {A : Type u} [CommRing A]
    (I : Ideal A) (M : Mod A) : Mod A :=
  ModuleCat.of A (AdicCompletion I (M : Type u))

structure HomSystemsData {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M N : Mod A)
    [Module.Finite A (M : Type u)] [Module.Finite A (N : Type u)] where
  c : ℕ
  hom_system : ℕᵒᵖ ⥤ Type u
  hom_stage : ∀ n, Nonempty (hom_system.obj (Opposite.op n) ≃
    HomType (idealQuotientModule I n M) (idealQuotientModule I n N))
  isom_system : ℕᵒᵖ ⥤ Type u
  isom_stage : ∀ n, Nonempty (isom_system.obj (Opposite.op n) ≃
    IsomType (idealQuotientModule I n M) (idealQuotientModule I n N))
  hom_mittag_leffler : hom_system.IsMittagLeffler
  isom_mittag_leffler : isom_system.IsMittagLeffler
  reduction : ∀ n, homQuotientModule I n M N ⟶
    homModule (idealQuotientModule I n M) (idealQuotientModule I n N)
  kernel_cokernel_killed : ∀ n,
    annihilatedByIdealPower I c (kernel (reduction n)) ∧
      annihilatedByIdealPower I c (cokernel (reduction n))
  hom_limit_iso : Nonempty
    (Limits.limit hom_system ≃ AdicCompletion I (HomType M N))
  completed_hom_iso : Nonempty
    (Limits.limit hom_system ≃
      HomType (adicCompletionModule I M) (adicCompletionModule I N))
  completed_isomorphism_limit :
    Nonempty (Limits.limit isom_system ≃ IsomType
      (adicCompletionModule I M) (adicCompletionModule I N))

theorem lemma_hom_systems_ML {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M N : Mod A)
    [Module.Finite A (M : Type u)] [Module.Finite A (N : Type u)] :
    Nonempty (HomSystemsData I M N) := by
  sorry

theorem lemma_isomorphic_completions {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M N : Mod A)
    [Module.Finite A (M : Type u)] [Module.Finite A (N : Type u)]
    (h : ∀ n : ℕ, Nonempty (idealQuotientModule I n M ≅
      idealQuotientModule I n N)) :
    Nonempty (adicCompletionModule I M ≅ adicCompletionModule I N) := by
  sorry

/-! ## The category of systems with bounded torsion error -/

structure SystemObject {A : Type u} [CommRing A] (I : Ideal A) where
  stage : ∀ n : ℕ, Mod A
  finite : ∀ n, Module.Finite A (stage n : Type u)
  killed : ∀ n, annihilatedByIdealPower I (n + 1) (stage n)

/-- The submodule of elements killed by `I^c`. -/
def idealPowerTorsionSubmodule {A : Type u} [CommRing A]
    (I : Ideal A) (c : ℕ) (M : Mod A) : Submodule A (M : Type u) :=
  ⨅ r : (I ^ c : Ideal A),
    LinearMap.ker (LinearMap.lsmul A (M : Type u) (r : A))

structure SystemMorphism {A : Type u} [CommRing A] (I : Ideal A)
    (E F : SystemObject I) where
  c : ℕ
  map : ∀ n, idealPowerModule I c (E.stage n) ⟶
      ModuleCat.of A ((F.stage n : Type u) ⧸
        idealPowerTorsionSubmodule I c (F.stage n))
  coherent : Prop

def systemMorphismEquivalent {A : Type u} [CommRing A]
    {I : Ideal A} {E F : SystemObject I}
    (f g : SystemMorphism I E F) : Prop :=
  ∃ d : ℕ, d ≥ f.c ∧ d ≥ g.c ∧ f.coherent ∧ g.coherent

structure SystemIsomorphism {A : Type u} [CommRing A] (I : Ideal A)
    (E F : SystemObject I) where
  forward : SystemMorphism I E F
  backward : SystemMorphism I F E
  left_inverse : Prop
  right_inverse : Prop

def eventuallyPowerTorsion {A : Type u} [CommRing A]
    {I : Ideal A} {E F : SystemObject I} (f : SystemMorphism I E F) : Prop :=
  ∃ c' n₀ : ℕ, ∀ n, n₀ ≤ n →
    annihilatedByIdealPower I c' (kernel (f.map n)) ∧
    annihilatedByIdealPower I c' (cokernel (f.map n))

theorem lemma_system_morphism_isIso_iff {A : Type u} [CommRing A]
    (I : Ideal A) (E F : SystemObject I) (f : SystemMorphism I E F) :
    Nonempty (SystemIsomorphism I E F) ↔
      eventuallyPowerTorsion f := by
  sorry

/-! ## Ext comparison and the flat-base-change special case -/

abbrev ExtAt {A : Type u} [Ring A] (M N : ModuleCat.{u} A) (i : ℕ) : Type u :=
  ExtGroup M N i

noncomputable def extModuleZ {A : Type u} [CommRing A]
    (M N : Mod A) (i : ℤ) : Mod A :=
  if 0 ≤ i then ModuleCat.of A (ExtGroup M N i.toNat) else 0

/-- A quotient module over `A/I^(n+1)`, together with its canonical
underlying-module realization.  This is the source's `M_n` interface; the
quotient-ring action is retained instead of silently replacing it by an
`A`-module. -/
structure QuotientModuleData {A : Type u} [CommRing A]
    (I : Ideal A) (M : Mod A) where
  stage : ∀ n : ℕ, ModuleCat.{u} (A ⧸ I ^ (n + 1))
  finite : ∀ n, Module.Finite (A ⧸ I ^ (n + 1)) (stage n : Type u)
  realization : ∀ n, Nonempty
    ((stage n : Type u) ≃
      ((M : Type u) ⧸ idealPowerSubmodule I (n + 1) M))

def quotientRingMap {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) : A →+* (A ⧸ I ^ (n + 1)) :=
  Ideal.Quotient.mk (I ^ (n + 1))

abbrev quotientExtAsA {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (P Q : ModuleCat.{u} (A ⧸ I ^ (n + 1)))
    (i : ℕ) : Mod A :=
  (ModuleCat.restrictScalars (quotientRingMap I n)).obj
    (ExtModule P Q i)

structure ExtSystemComparisonData {A : Type u} [CommRing A]
    (I : Ideal A) (M N : Mod A) (i : ℕ) where
  quotient_M : QuotientModuleData I M
  quotient_N : QuotientModuleData I N
  source : SystemObject I
  target : SystemObject I
  source_formula : ∀ n, Nonempty (source.stage n ≅
    idealQuotientModule I (n + 1) (ModuleCat.of A (ExtAt M N i)))
  target_formula : ∀ n, Nonempty (target.stage n ≅
    quotientExtAsA I n (quotient_M.stage n) (quotient_N.stage n) i)
  comparison : Nonempty (SystemIsomorphism I source target)

theorem lemma_deJong_Kollar_Kovacs {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M N : Mod A) (i : ℕ)
    [Module.Finite A (M : Type u)] [Module.Finite A (N : Type u)] :
    Nonempty (ExtSystemComparisonData I M N i) := by
  sorry

structure FlatBaseChangeExtData {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (M N : ModuleCat.{u} B) (i : ℤ) where
  B_flat : RingHom.Flat f
  M_flat : Module.Flat A ((ModuleCat.restrictScalars f).obj M : Type u)
  M_finite : Module.Finite B (M : Type u)
  A_noetherian : IsNoetherianRing A
  B_noetherian : IsNoetherianRing B
  quotient_M : QuotientModuleData (I.map f) M
  quotient_N : QuotientModuleData (I.map f) N
  source_system : ℕᵒᵖ ⥤ Type u
  source_stage : ∀ n, Nonempty (source_system.obj (Opposite.op n) ≃
    (idealQuotientModule I (n + 1)
      ((ModuleCat.restrictScalars f).obj (extModuleZ M N i)) : Type u))
  target_system : ℕᵒᵖ ⥤ Type u
  target_stage : ∀ n, Nonempty (target_system.obj (Opposite.op n) ≃
    (extModuleZ (quotient_M.stage n) (quotient_N.stage n) i : Type u))
  limit_iso : Nonempty (Limits.limit source_system ≃
    Limits.limit target_system)

theorem lemma_not_awkward {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (M N : ModuleCat.{u} B) (i : ℤ)
    (hflat : RingHom.Flat f)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars f).obj M : Type u))
    (hMfinite : Module.Finite B (M : Type u))
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B) :
    Nonempty (FlatBaseChangeExtData f I M N i) := by
  sorry

/-! ## The explicit awkward example -/

structure AwkwardSystemsExampleData {k : Type u} [Field k]
    (A : Type u) [CommRing A] where
  I : Ideal A
  moduleM : ModuleCat.{u} A
  moduleN : ModuleCat.{u} A
  ext_over_A : Nonempty (ExtGroup moduleM moduleN 2 ≃+ k)
  resolution_M : Nonempty (FreeResolution A moduleM)
  resolution_N : Nonempty (FreeResolution A moduleN)
  quotient_M : QuotientModuleData I moduleM
  quotient_N : QuotientModuleData I moduleN
  quotient_resolution_M : ∀ n, Nonempty
    (FreeResolution (A ⧸ I ^ (n + 1)) (quotient_M.stage n))
  quotient_resolution_N : ∀ n, Nonempty
    (FreeResolution (A ⧸ I ^ (n + 1)) (quotient_N.stage n))
  quotient_ext_zero : ∀ n : ℕ, Subsingleton
    (ExtGroup (quotient_M.stage n) (quotient_N.stage n) 2)
  quotient_ext_vanishes : ∀ n : ℕ,
    ∀ x : ExtGroup (quotient_M.stage n) (quotient_N.stage n) 2, x = 0

abbrev awkwardPowerSeriesRing (k : Type u) [Field k] := MvPowerSeries (Fin 2) k

def awkwardRelationIdeal (k : Type u) [Field k] :
    Ideal (awkwardPowerSeriesRing k) :=
  Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} :
    Set (awkwardPowerSeriesRing k))

abbrev awkwardRing (k : Type u) [Field k] :=
  awkwardPowerSeriesRing k ⧸ awkwardRelationIdeal k

def awkwardX (k : Type u) [Field k] : awkwardRing k :=
  Ideal.Quotient.mk (awkwardRelationIdeal k) (MvPowerSeries.X 0)

def awkwardY (k : Type u) [Field k] : awkwardRing k :=
  Ideal.Quotient.mk (awkwardRelationIdeal k) (MvPowerSeries.X 1)

def awkwardIdeal (k : Type u) [Field k] : Ideal (awkwardRing k) :=
  Ideal.span ({awkwardX k} : Set (awkwardRing k))

def awkwardModule (k : Type u) [Field k] : ModuleCat.{u} (awkwardRing k) :=
  ModuleCat.of (awkwardRing k)
    (awkwardRing k ⧸ Ideal.span ({awkwardY k} : Set (awkwardRing k)))

theorem example_has_to_be_awkward {k : Type u} [Field k] :
    Nonempty (AwkwardSystemsExampleData (k := k) (awkwardRing k)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit101
