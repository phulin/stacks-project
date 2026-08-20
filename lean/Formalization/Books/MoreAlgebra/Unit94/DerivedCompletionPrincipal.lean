import Formalization.Books.MoreAlgebra.Unit92
import Formalization.Books.MoreAlgebra.Unit87
import Formalization.Books.MoreAlgebra.Unit88
import Formalization.Books.MoreAlgebra.Unit11
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# More on Algebra, Chapter 94: Derived completion for a principal ideal

This file records the definitions and theorem interfaces in the chapter.
Derived-completion objects and pro-isomorphisms reuse the canonical interfaces
from Chapters 87 and 92. The few inverse-limit presentations whose module
level transition-map API is not exposed by the current project are packaged
as explicit data, so their source-facing stages and exact sequences remain
available to later formalization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.MoreAlgebra.Unit11
open Formalization.Books.MoreAlgebra.Unit53
open Formalization.Books.MoreAlgebra.Unit87
open Formalization.Books.MoreAlgebra.Unit89
open Formalization.Books.MoreAlgebra.Unit92
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.Derived.Unit34
open Formalization.Books.MoreAlgebra.Unit88
open scoped BigOperators CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u w

namespace Formalization.Books.MoreAlgebra.Unit94

abbrev Mod (A : Type u) [CommRing A] := ModuleCat.{u} A

abbrev Comp (A : Type u) [CommRing A] := Unit92.Comp A

abbrev D (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] := Unit92.D A

/-! ## 94.1. Principal powers, Koszul stages, and pro-isomorphisms -/

/-- The principal ideal used throughout the section. -/
def principalIdeal (A : Type u) [CommRing A] (f : A) : Ideal A :=
  Ideal.span ({f} : Set A)

/-- A principal ideal is finitely generated. -/
theorem principalIdeal_finitelyGenerated (A : Type u) [CommRing A] (f : A) :
    (principalIdeal A f).FG := by
  sorry

/-- The f^n-torsion submodule of the ring, in the canonical ideal-power form. -/
def principalPowerTorsionAt (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    Submodule A A :=
  idealPowerTorsionSubmodule (principalIdeal A f) n

/-- Stabilization of the principal-power torsion, i.e. the hypothesis
A[f^c] = A[f^(c+1)] = ... in the source. -/
def PrincipalPowerTorsionStabilizes (A : Type u) [CommRing A]
    (f : A) (c : ℕ) : Prop :=
  0 < c ∧ ∀ n : ℕ, c ≤ n →
    principalPowerTorsionAt A f n = principalPowerTorsionAt A f c

theorem principalPowerTorsionStabilizes_of_isNoetherian
    (A : Type u) [CommRing A] [IsNoetherianRing A] (f : A) :
    ∃ c : ℕ, PrincipalPowerTorsionStabilizes A f c := by
  sorry

/-- The map of copies of A given by multiplication by f^n. -/
noncomputable def principalMultiplicationMap (A : Type u) [CommRing A]
    (f : A) (n : ℕ) : ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.mulLeft A (f ^ n))

/-- A complex realization of the two-term complex
(A \xrightarrow{f^n} A). -/
structure PrincipalTwoTermComplexData (A : Type u) [CommRing A]
    (f : A) (n : ℕ) where
  complex : Comp A
  supported : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (complex.X i)
  degree_zero : complex.X 0 ≅ ModuleCat.of A A
  degree_one : complex.X 1 ≅ ModuleCat.of A A
  differential :
    degree_zero.inv ≫ complex.d 0 1 ≫ degree_one.hom =
      principalMultiplicationMap A f n

theorem exists_principalTwoTermComplexData (A : Type u) [CommRing A]
    (f : A) (n : ℕ) : Nonempty (PrincipalTwoTermComplexData A f n) := by
  sorry

noncomputable def principalTwoTermComplexData (A : Type u) [CommRing A]
    (f : A) (n : ℕ) : PrincipalTwoTermComplexData A f n :=
  Classical.choice (exists_principalTwoTermComplexData A f n)

noncomputable abbrev principalKoszulObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (n : ℕ) : D A :=
  (DerivedCategory.Q : Comp A ⥤ D A).obj
    (principalTwoTermComplexData A f n).complex

/-- The quotient module A/(f^n), with the positive-index convention used
by the inverse systems below. -/
def principalQuotientModule (A : Type u) [CommRing A] (f : A) (n : ℕ) : Mod A :=
  ModuleCat.of A (A ⧸ (principalIdeal A f) ^ n)

noncomputable abbrev principalQuotientObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (n : ℕ) : D A :=
  moduleInDerived A (principalQuotientModule A f n)

/-- A chosen derived inverse system together with its source-facing stages. -/
structure PrincipalDerivedSystemData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (stage : ℕ → D A) where
  system : DerivedInverseSystem (D A)
  stage_iso : ∀ n : ℕ,
    Nonempty (system.obj (Opposite.op n) ≅ stage n)
  hasProduct : HasProduct (fun n : ℕ => system.obj (Opposite.op n))

def principalQuotientStage {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (n : ℕ) : D A :=
  principalQuotientObject f (n + 1)

theorem exists_principalQuotientSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) :
    Nonempty (PrincipalDerivedSystemData A (principalQuotientStage f)) := by
  sorry

noncomputable def principalQuotientSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) :
    PrincipalDerivedSystemData A (principalQuotientStage f) :=
  Classical.choice (exists_principalQuotientSystemData f)

def principalKoszulStage {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (n : ℕ) : D A :=
  principalKoszulObject f (n + 1)

theorem exists_principalKoszulSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) :
    Nonempty (PrincipalDerivedSystemData A (principalKoszulStage f)) := by
  sorry

noncomputable def principalKoszulSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) :
    PrincipalDerivedSystemData A (principalKoszulStage f) :=
  Classical.choice (exists_principalKoszulSystemData f)

/- The maps and pro-isomorphism asserted by Lemma 94.1. -/
structure PrincipalLiftUniversallyData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (c : ℕ) where
  to_quotient : ∀ n : ℕ, 0 < n →
    (principalKoszulObject f n ⟶ principalQuotientObject f n)
  from_quotient : ∀ n : ℕ, 0 < n →
    (principalQuotientObject f (n + c) ⟶ principalKoszulObject f n)
  pro_isomorphism :
    IsProIsomorphism
      (principalQuotientSystemData f).system
      (principalKoszulSystemData f).system

theorem principal_lift_universally {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A)
    (hstable : ∃ c : ℕ, PrincipalPowerTorsionStabilizes A f c) :
    ∃ c : ℕ, 0 < c ∧ Nonempty (PrincipalLiftUniversallyData A f c) := by
  sorry

/-! ## 94.2. Naive versus Koszul derived completion -/

/-- Bounded f-power torsion of the ring. This is the source condition
f^(n-1) A[f^n] = 0, written elementwise. -/
def PrincipalPowerTorsionBounded (A : Type u) [CommRing A] (f : A) : Prop :=
  ∃ n : ℕ, 0 < n ∧
    principalPowerTorsionAt A f n = principalPowerTorsionAt A f (n + 1)

/- The product needed after tensoring the quotient system is not supplied by
   the product of the quotient stages alone.  It is therefore recorded once
   as the precise existence datum used by the naive completion. -/
structure PrincipalNaiveCompletionProductData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) where
  hasProduct : ∀ K : D A,
    HasProduct (fun n : ℕ =>
      (derivedTensorInverseSystem K (principalQuotientSystemData f).system).obj
        (Opposite.op n))

theorem exists_principalNaiveCompletionProductData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) :
    Nonempty (PrincipalNaiveCompletionProductData A f) := by
  sorry

noncomputable def principalNaiveCompletionProductData {A : Type u}
    [CommRing A] [HasDerivedCategory.{w} (Mod A)] (f : A) :
    PrincipalNaiveCompletionProductData A f :=
  Classical.choice (exists_principalNaiveCompletionProductData f)

noncomputable def naivePrincipalCompletion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) : D A :=
  let S := principalNaiveCompletionProductData f
  letI := S.hasProduct K
  derivedLimitWithProduct
    (derivedTensorInverseSystem K (principalQuotientSystemData f).system)
    (S.hasProduct K)

structure PrincipalNaiveCompletionFunctorData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) where
  naive : D A ⥤ D A
  stage_formula : ∀ K : D A,
    Nonempty (naive.obj K ≅ naivePrincipalCompletion f K)

theorem exists_principalNaiveCompletionFunctorData {A : Type u}
    [CommRing A] [HasDerivedCategory.{w} (Mod A)] (f : A) :
    Nonempty (PrincipalNaiveCompletionFunctorData A f) := by
  sorry

noncomputable def principalNaiveCompletionFunctor {A : Type u}
    [CommRing A] [HasDerivedCategory.{w} (Mod A)] (f : A) : D A ⥤ D A :=
  (Classical.choice (exists_principalNaiveCompletionFunctorData f)).naive

noncomputable abbrev principalDerivedCompletionFunctor
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A) : D A ⥤ D A :=
  derivedCompletion (principalIdeal A f) (principalIdeal_finitelyGenerated A f)

noncomputable abbrev principalDerivedCompletion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) : D A :=
  (principalDerivedCompletionFunctor f).obj K

structure PrincipalCompletionComparisonData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) where
  comparison : principalDerivedCompletionFunctor f ⟶
    principalNaiveCompletionFunctor f
  stage_identification : ∀ K : D A,
    Nonempty ((principalNaiveCompletionFunctor f).obj K ≅
      naivePrincipalCompletion f K)

theorem exists_principalCompletionComparisonData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) :
    Nonempty (PrincipalCompletionComparisonData A f) := by
  sorry

theorem principal_completion_is_naive_iff {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) :
    ∃ C : PrincipalCompletionComparisonData A f,
      ((∀ K : D A, IsIso (C.comparison.app K)) ↔
        PrincipalPowerTorsionBounded A f) := by
  sorry

/-! ## 94.3. Derived-complete modules over a nonzerodivisor -/

def PrincipalTorsionFree {A : Type u} [CommRing A] (f : A) (M : Mod A) : Prop :=
  ∀ x : (M : Type u), f • x = 0 → x = 0

structure PrincipalDerivedCompletePresentation (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (M : Mod A) where
  K : Mod A
  L : Mod A
  left : K ⟶ L
  right : L ⟶ M
  zero : left ≫ right = 0
  exact : (CategoryTheory.ShortComplex.mk left right zero).ShortExact
  K_complete : IsAdicComplete (principalIdeal A f) (K : Type u)
  L_complete : IsAdicComplete (principalIdeal A f) (L : Type u)
  K_torsion_free : PrincipalTorsionFree f K
  L_torsion_free : PrincipalTorsionFree f L

theorem derived_complete_module_iff_principal_presentation
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A) (hf : ∀ x : A, f * x = 0 → x = 0) (M : Mod A) :
    derivedCompleteModule (principalIdeal A f) M ↔
      Nonempty (PrincipalDerivedCompletePresentation A f M) := by
  sorry

/-! ## 94.4. A derived-complete module which is not adically complete -/

noncomputable def padicPolynomialMap (p : ℕ) [Fact p.Prime] :
    Polynomial (PadicInt p) →+* Polynomial (PadicInt p) :=
  Polynomial.eval₂RingHom (Polynomial.C : PadicInt p →+* Polynomial (PadicInt p))
    (Polynomial.C (p : PadicInt p) * Polynomial.X)

noncomputable def padicPolynomialIdeal (p : ℕ) [Fact p.Prime] :
    Ideal (PadicInt p) :=
  Ideal.span ({(p : PadicInt p)} : Set (PadicInt p))

abbrev padicPolynomialCompletion (p : ℕ) [Fact p.Prime] :=
  AdicCompletion (padicPolynomialIdeal p) (Polynomial (PadicInt p))

/-- Data for the induced map on ordinary completions in the polynomial example.
The completion map is retained as a module morphism so its cokernel is the
source's module M. -/
structure PadicPolynomialCompletionData (p : ℕ) [Fact p.Prime] where
  completionMap :
    ModuleCat.of (PadicInt p)
        (padicPolynomialCompletion p) ⟶
      ModuleCat.of (PadicInt p)
        (padicPolynomialCompletion p)
  induced_by : ∀ x : Polynomial (PadicInt p),
    completionMap.hom (AdicCompletion.of (padicPolynomialIdeal p)
      (Polynomial (PadicInt p)) x) =
      AdicCompletion.of (padicPolynomialIdeal p) (Polynomial (PadicInt p))
        (padicPolynomialMap p x)

theorem exists_padicPolynomialCompletionData (p : ℕ) [Fact p.Prime] :
    Nonempty (PadicPolynomialCompletionData p) := by
  sorry

noncomputable def padicPolynomialCompletionData (p : ℕ) [Fact p.Prime] :
    PadicPolynomialCompletionData p :=
  Classical.choice (exists_padicPolynomialCompletionData p)

noncomputable def padicPolynomialCokernel (p : ℕ) [Fact p.Prime] :
    ModuleCat (PadicInt p) :=
  cokernel (padicPolynomialCompletionData p).completionMap

def PadicCokernelWitness (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ ξ : (padicPolynomialCokernel p : Type), ξ ≠ 0 ∧
    ∀ n : ℕ,
      ξ ∈ (principalIdeal (PadicInt p) (p : PadicInt p) ^ n) •
        (⊤ : Submodule (PadicInt p) (padicPolynomialCokernel p : Type))

theorem padic_polynomial_cokernel_is_derived_complete_not_adic_complete
    (p : ℕ) [Fact p.Prime] :
    derivedCompleteModule
        (principalIdeal (PadicInt p) (p : PadicInt p))
        (padicPolynomialCokernel p) ∧
      ¬ IsAdicComplete (principalIdeal (PadicInt p) (p : PadicInt p))
        (padicPolynomialCokernel p : Type) ∧
      PadicCokernelWitness p := by
  sorry

/-! ## 94.5. The principal spectral sequence -/

def principalPowerTorsionAtModule {A : Type u} [CommRing A]
    (f : A) (M : Mod A) (n : ℕ) : Submodule A (M : Type u) :=
  idealPowerTorsionSubmodule (M := (M : Type u)) (principalIdeal A f) n

def principalTateStage {A : Type u} [CommRing A]
    (f : A) (M : Mod A) (n : ℕ) : Mod A :=
  ModuleCat.of A (principalPowerTorsionAtModule f M (n + 1))

structure PrincipalTateSystemData (A : Type u) [CommRing A] (f : A)
    (M : Mod A) where
  system : ℕᵒᵖ ⥤ Mod A
  stage_iso : ∀ n : ℕ,
    system.obj (Opposite.op n) ≅ principalTateStage f M n
  transition : ∀ n : ℕ,
    system.obj (Opposite.op (n + 1)) ⟶ system.obj (Opposite.op n)
  multiplication : ∀ n : ℕ,
    principalTateStage f M (n + 1) ⟶ principalTateStage f M n
  transition_is_multiplication : ∀ n : ℕ,
    transition n ≫ (stage_iso n).hom =
      (stage_iso (n + 1)).hom ≫ multiplication n
  multiplication_formula : ∀ (n : ℕ)
    (x : (principalTateStage f M (n + 1) : Type u)),
    ((multiplication n).hom x).val = f • x.val
  hasLimit : HasLimit system

theorem exists_principalTateSystemData {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : Nonempty (PrincipalTateSystemData A f M) := by
  sorry

noncomputable def principalTateSystemData {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : PrincipalTateSystemData A f M :=
  Classical.choice (exists_principalTateSystemData f M)

noncomputable def principalTateModule {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : Mod A :=
  let S := principalTateSystemData f M
  letI := S.hasLimit
  limit S.system

noncomputable def principalModuleInDerivedFunctor {A : Type u}
    [CommRing A] [HasDerivedCategory.{w} (Mod A)] : Mod A ⥤ D A :=
  (CochainComplex.singleFunctor (Mod A) 0) ⋙
    (DerivedCategory.Q : Comp A ⥤ D A)

def principalDerivedModuleSystem {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (S : ℕᵒᵖ ⥤ Mod A) :
    DerivedInverseSystem (D A) :=
  S ⋙ principalModuleInDerivedFunctor

structure PrincipalRlimModuleData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (S : ℕᵒᵖ ⥤ Mod A) where
  hasProduct : HasProduct (fun n : ℕ =>
    (principalDerivedModuleSystem S).obj (Opposite.op n))

noncomputable def principalROneLimit {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (S : ℕᵒᵖ ⥤ Mod A)
    (hS : HasProduct (fun n : ℕ =>
      (principalDerivedModuleSystem S).obj (Opposite.op n))) : Mod A :=
  letI := hS
  (derivedCohomologyFunctor A 1).obj
    (derivedLimitWithProduct (principalDerivedModuleSystem S) hS)

structure PrincipalShortExactData (A : Type u) [CommRing A]
    (X Y Z : Mod A) where
  left : X ⟶ Y
  right : Y ⟶ Z
  zero : left ≫ right = 0
  exact : (CategoryTheory.ShortComplex.mk left right zero).ShortExact

def principalQuotientSubmodule {A : Type u} [CommRing A]
    (f : A) (M : Mod A) (n : ℕ) : Submodule A (M : Type u) :=
  (principalIdeal A f) ^ n • (⊤ : Submodule A (M : Type u))

def principalQuotientModuleStage {A : Type u} [CommRing A]
    (f : A) (M : Mod A) (n : ℕ) : Mod A :=
  ModuleCat.of A ((M : Type u) ⧸ principalQuotientSubmodule f M (n + 1))

theorem principalQuotientSubmodule_succ_le {A : Type u} [CommRing A]
    (f : A) (M : Mod A) (n : ℕ) :
    principalQuotientSubmodule f M (n + 2) ≤
      principalQuotientSubmodule f M (n + 1) := by
  sorry

structure PrincipalQuotientModuleSystemData (A : Type u) [CommRing A]
    (f : A) (M : Mod A) where
  system : ℕᵒᵖ ⥤ Mod A
  stage_iso : ∀ n : ℕ,
    system.obj (Opposite.op n) ≅ principalQuotientModuleStage f M n
  transition : ∀ n : ℕ,
    system.obj (Opposite.op (n + 1)) ⟶ system.obj (Opposite.op n)
  transition_is_quotient : ∀ (n : ℕ) (x : (system.obj
    (Opposite.op (n + 1)) : Type u)),
    (stage_iso n).hom.hom ((transition n).hom x) =
      Submodule.factor (principalQuotientSubmodule_succ_le f M n)
        ((stage_iso (n + 1)).hom.hom x)
  hasLimit : HasLimit system

theorem exists_principalQuotientModuleSystemData {A : Type u}
    [CommRing A] (f : A) (M : Mod A) :
    Nonempty (PrincipalQuotientModuleSystemData A f M) := by
  sorry

noncomputable def principalQuotientModuleSystemData {A : Type u}
    [CommRing A] (f : A) (M : Mod A) :
    PrincipalQuotientModuleSystemData A f M :=
  Classical.choice (exists_principalQuotientModuleSystemData f M)

noncomputable def principalQuotientLimitModule {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : Mod A :=
  let S := principalQuotientModuleSystemData f M
  letI := S.hasLimit
  limit S.system

noncomputable def principalHZeroModule {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (M : Mod A) : Mod A :=
  (derivedCohomologyFunctor A 0).obj
    (principalDerivedCompletion f (moduleInDerived A M))

structure PrincipalHZeroSequenceData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (M : Mod A) where
  r_one_torsion : PrincipalRlimModuleData A
    (principalTateSystemData f M).system
  r_one_quotient : PrincipalRlimModuleData A
    (principalQuotientModuleSystemData f M).system
  sequence : PrincipalShortExactData A
    (principalROneLimit _ r_one_torsion.hasProduct)
    (principalHZeroModule f M)
    (principalQuotientLimitModule f M)

structure PrincipalCohomologyShortExactData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (p : ℤ) where
  sequence : PrincipalShortExactData A
    ((derivedCohomologyFunctor A 0).obj
      (principalDerivedCompletion f
        (moduleInDerived A
          ((derivedCohomologyFunctor A p).obj K))))
    ((derivedCohomologyFunctor A p).obj
      (principalDerivedCompletion f K))
    (principalTateModule f
      ((derivedCohomologyFunctor A (p + 1)).obj K))

structure PrincipalSpectralSequenceData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (M : Mod A) where
  h_minus_one :
    Nonempty ((derivedCohomologyFunctor A (-1)).obj
      (principalDerivedCompletion f (moduleInDerived A M)) ≅
      principalTateModule f M)
  r_one_torsion : PrincipalRlimModuleData A
    (principalTateSystemData f M).system
  r_one_quotient : PrincipalRlimModuleData A
    (principalQuotientModuleSystemData f M).system
  h_zero : PrincipalHZeroSequenceData A f M
  h_one_zero : IsZero ((derivedCohomologyFunctor A 1).obj
    (principalDerivedCompletion f (moduleInDerived A M)))
  other_cohomology_zero : ∀ i : ℤ, i < -1 ∨ 1 < i →
    IsZero ((derivedCohomologyFunctor A i).obj
      (principalDerivedCompletion f (moduleInDerived A M)))
  cohomology_window : ∀ (K : D A) (p : ℤ),
    Nonempty (PrincipalCohomologyShortExactData A f K p)

theorem principal_spectral_sequence_statements {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (M : Mod A) :
    Nonempty (PrincipalSpectralSequenceData A f M) := by
  sorry

/-! ## 94.6. Comparison with ordinary completion and the ML remark -/

def principalKoszulCohomologySystem {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (p : ℤ) :
    ℕᵒᵖ ⥤ Mod A :=
  (derivedTensorInverseSystem K (principalKoszulSystemData f).system) ⋙
    derivedCohomologyFunctor A p

noncomputable def principalUsualCompletion {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : Mod A :=
  ModuleCat.of A (AdicCompletion (principalIdeal A f) (M : Type u))

structure PrincipalCompletionComparisonDiagram (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (p : ℤ) where
  r_one_torsion_data : PrincipalRlimModuleData A
    (principalTateSystemData f
      ((derivedCohomologyFunctor A p).obj K)).system
  r_one_koszul_data : PrincipalRlimModuleData A
    (principalKoszulCohomologySystem f K (p - 1))
  top_left :
    principalUsualCompletion f ((derivedCohomologyFunctor A p).obj K) ⟶
      limit (principalKoszulCohomologySystem f K p)
  top_right :
    limit (principalKoszulCohomologySystem f K p) ⟶
      principalTateModule f ((derivedCohomologyFunctor A (p + 1)).obj K)
  top_zero : top_left ≫ top_right = 0
  top_exact : (CategoryTheory.ShortComplex.mk top_left top_right top_zero).ShortExact
  middle_left :
    (derivedCohomologyFunctor A 0).obj
      (principalDerivedCompletion f
        (moduleInDerived A ((derivedCohomologyFunctor A p).obj K))) ⟶
      (derivedCohomologyFunctor A p).obj
        (principalDerivedCompletion f K)
  middle_right :
    (derivedCohomologyFunctor A p).obj
        (principalDerivedCompletion f K) ⟶
      principalTateModule f ((derivedCohomologyFunctor A (p + 1)).obj K)
  middle_zero : middle_left ≫ middle_right = 0
  middle_exact :
    (CategoryTheory.ShortComplex.mk middle_left middle_right middle_zero).ShortExact
  left_bottom :
    principalROneLimit _ r_one_torsion_data.hasProduct ⟶
      (derivedCohomologyFunctor A 0).obj
        (principalDerivedCompletion f
          (moduleInDerived A ((derivedCohomologyFunctor A p).obj K)))
  left_top :
    (derivedCohomologyFunctor A 0).obj
        (principalDerivedCompletion f
          (moduleInDerived A ((derivedCohomologyFunctor A p).obj K))) ⟶
      principalUsualCompletion f ((derivedCohomologyFunctor A p).obj K)
  left_zero : left_bottom ≫ left_top = 0
  left_exact : (CategoryTheory.ShortComplex.mk left_bottom left_top left_zero).ShortExact
  middle_bottom :
    principalROneLimit _ r_one_koszul_data.hasProduct ⟶
      (derivedCohomologyFunctor A p).obj
        (principalDerivedCompletion f K)
  middle_top :
    (derivedCohomologyFunctor A p).obj
        (principalDerivedCompletion f K) ⟶
      limit (principalKoszulCohomologySystem f K p)
  middle_column_zero : middle_bottom ≫ middle_top = 0
  middle_column_exact :
    (CategoryTheory.ShortComplex.mk middle_bottom middle_top
      middle_column_zero).ShortExact
  bottom_identification : Nonempty
    (principalROneLimit _ r_one_torsion_data.hasProduct ≅
      principalROneLimit _ r_one_koszul_data.hasProduct)
  right_vertical :
    principalTateModule f ((derivedCohomologyFunctor A (p + 1)).obj K) ⟶
      principalTateModule f ((derivedCohomologyFunctor A (p + 1)).obj K)
  right_vertical_is_identity : right_vertical = 𝟙 _
  left_square_commutes : left_top ≫ top_left = middle_left ≫ middle_top
  right_square_commutes : middle_right ≫ right_vertical = middle_top ≫ top_right

theorem principal_completion_comparison_diagram
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A) (K : D A) (p : ℤ) :
    Nonempty (PrincipalCompletionComparisonDiagram A f K p) := by
  sorry

def PrincipalModuleSystemHasML {A : Type u} [CommRing A]
    (S : ℕᵒᵖ ⥤ Mod A) : Prop :=
  (S ⋙ CategoryTheory.forget (ModuleCat A)).IsMittagLeffler

def PrincipalCompletionSystemHasML {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (p : ℤ) : Prop :=
  PrincipalModuleSystemHasML (principalKoszulCohomologySystem f K p)

def PrincipalTateSystemHasML {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : Prop :=
  PrincipalModuleSystemHasML (principalTateSystemData f M).system

theorem principal_completion_ML_iff_tate_ML
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A) (K : D A) (p : ℤ) :
    PrincipalCompletionSystemHasML f K p ↔
      PrincipalTateSystemHasML f
        ((derivedCohomologyFunctor A (p + 1)).obj K) := by
  sorry

/-! ## 94.7. Bounded torsion, kernels, henselianity, and reduced rings -/

def IsAnnihilatedByIdealPower {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) : Prop :=
  (I ^ n) • (⊤ : Submodule A (M : Type u)) = ⊥

theorem torsion_and_derived_complete_bounded
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) (M : Mod A)
    (hM : derivedCompleteModule I M)
    (hT : IsIPowerTorsion I (M : Type u)) :
    ∃ n : ℕ, IsAnnihilatedByIdealPower I n M := by
  sorry

def principalPowerIntersection (A : Type u) [CommRing A]
    (f : A) : Ideal A :=
  ⨅ n : ℕ, (principalIdeal A f) ^ n

noncomputable def ordinaryCompletionMap {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : M ⟶ principalUsualCompletion f M :=
  ModuleCat.ofHom (AdicCompletion.of (principalIdeal A f) (M : Type u))

noncomputable def ordinaryCompletionKernel {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : Mod A :=
  kernel (ordinaryCompletionMap f M)

theorem kernel_to_completion_annihilated
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A) (M : Mod A)
    (hM : derivedCompleteModule (principalIdeal A f) M) :
    (principalPowerIntersection A f) •
        (⊤ : Submodule A (ordinaryCompletionKernel f M : Type u)) = ⊥ := by
  sorry

theorem principal_intersection_square_zero
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A)
    (hA : derivedComplete (principalIdeal A f)
      (moduleInDerived A (ModuleCat.of A A))) :
    (principalPowerIntersection A f) ^ 2 = ⊥ := by
  sorry

theorem derived_complete_henselian_pair
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A)
    (hA : derivedComplete I (moduleInDerived A (ModuleCat.of A A))) :
    HenselianPair ({ ideal := I } : Pair A) := by
  sorry

def IdealPowerIntersection (A : Type u) [CommRing A] (I : Ideal A) : Ideal A :=
  ⨅ n : ℕ, I ^ n

theorem ideal_power_intersection_nilpotent
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A)
    (hA : derivedComplete I (moduleInDerived A (ModuleCat.of A A)))
    (r : ℕ) (hgen : ∃ f : Fin r → A,
      I = Ideal.span (Set.range f)) :
    (IdealPowerIntersection A I) ^ (2 ^ r) = ⊥ := by
  sorry

theorem reduced_derived_complete_is_adic_complete
    {A : Type u} [CommRing A] [IsReduced A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (hI : I.FG)
    (hA : derivedComplete I (moduleInDerived A (ModuleCat.of A A))) :
    IsAdicComplete I A := by
  sorry

end Formalization.Books.MoreAlgebra.Unit94
