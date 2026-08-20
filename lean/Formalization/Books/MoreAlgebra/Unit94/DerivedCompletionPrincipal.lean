import Formalization.Books.MoreAlgebra.Unit92
import Formalization.Books.MoreAlgebra.Unit87
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

/-- The map of copies of A given by multiplication by f^n. -/
noncomputable def principalMultiplicationMap (A : Type u) [CommRing A]
    (f : A) (n : ℕ) : Mod A ⟶ Mod A :=
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
    degree_zero.hom ≫ complex.d 0 1 ≫ degree_one.hom =
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
    principalKoszulObject f n ⟶ principalQuotientObject f n
  from_quotient : ∀ n : ℕ, 0 < n →
    principalQuotientObject f (n + c) ⟶ principalKoszulObject f n
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
  ∃ n : ℕ, 0 < n ∧ ∀ x : A, f ^ n • x = 0 → f ^ (n - 1) • x = 0

noncomputable def naivePrincipalCompletion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) : D A :=
  let S := principalQuotientSystemData f
  derivedLimitWithProduct
    ((fun n : ℕ => Unit74.derivedTensor K
      (principalQuotientObject f (n + 1))) : D A)
    (by
      letI := S.hasProduct
      exact inferInstance)

noncomputable abbrev principalDerivedCompletionFunctor
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A) : D A ⥤ D A :=
  derivedCompletion (principalIdeal A f) (principalIdeal_finitelyGenerated A f)

noncomputable abbrev principalDerivedCompletion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) : D A :=
  (principalDerivedCompletionFunctor f).obj K

structure PrincipalCompletionComparisonData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) where
  naive : D A ⥤ D A
  comparison : principalDerivedCompletionFunctor f ⟶ naive
  stage_identification : ∀ K : D A,
    Nonempty (naive.obj K ≅ naivePrincipalCompletion f K)

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
  K L : Mod A
  left : K ⟶ L
  right : L ⟶ M
  zero : left ≫ right = 0
  exact : CategoryTheory.ShortComplex.ShortExact
    { f := left, g := right, zero := zero }
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
    ((p : PadicInt p) * Polynomial.X)

noncomputable def padicPolynomialIdeal (p : ℕ) [Fact p.Prime] :
    Ideal (Polynomial (PadicInt p)) :=
  Ideal.span ({Polynomial.C (p : PadicInt p)} : Set (Polynomial (PadicInt p)))

/-- Data for the induced map on ordinary completions in the polynomial example.
The completion map is retained as a module morphism so its cokernel is the
source's module M. -/
structure PadicPolynomialCompletionData (p : ℕ) [Fact p.Prime] where
  completionMap :
    ModuleCat.of (PadicInt p)
        (AdicCompletion (padicPolynomialIdeal p) (Polynomial (PadicInt p))) ⟶
      ModuleCat.of (PadicInt p)
        (AdicCompletion (padicPolynomialIdeal p) (Polynomial (PadicInt p)))
  inducedBy : Prop

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

structure PrincipalTateSystemData (A : Type u) [CommRing A] (f : A)
    (M : Mod A) where
  system : ℕᵒᵖ ⥤ Mod A
  stage_iso : ∀ n : ℕ,
    Nonempty (system.obj (Opposite.op n) ≅
      ModuleCat.of A (idealPowerTorsionSubmodule
        (principalIdeal A f) (n + 1)))
  transition_is_multiplication : ∀ n : ℕ, Prop
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

def PrincipalRlimModuleData (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Mod A) where
  first : Mod A
  first_is_R_one_lim : Prop

structure PrincipalSpectralSequenceData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (M : Mod A) where
  h_minus_one :
    Nonempty ((derivedCohomologyFunctor (Mod A) (-1)).obj
      (principalDerivedCompletion f (moduleInDerived A M)) ≅
      principalTateModule f M)
  r_one_torsion : PrincipalRlimModuleData A
    (principalTateSystemData f M).system
  r_one_quotient : PrincipalRlimModuleData A
    (principalQuotientSystemData f).system
  h_zero : PrincipalDerivedCompletePresentation A f M
  h_one_zero : IsZero ((derivedCohomologyFunctor (Mod A) 1).obj
    (principalDerivedCompletion f (moduleInDerived A M)))
  other_cohomology_zero : ∀ i : ℤ, i < -1 ∨ 1 < i →
    IsZero ((derivedCohomologyFunctor (Mod A) i).obj
      (principalDerivedCompletion f (moduleInDerived A M)))
  cohomology_window : ∀ (K : D A) (p : ℤ),
    Nonempty (PrincipalDerivedCompletePresentation A f
      ((derivedCohomologyFunctor (Mod A) (p + 1)).obj K))

theorem principal_spectral_sequence_statements {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (M : Mod A) :
    Nonempty (PrincipalSpectralSequenceData A f M) := by
  sorry

/-! ## 94.6. Comparison with ordinary completion and the ML remark -/

noncomputable def principalUsualCompletion {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : Mod A :=
  ModuleCat.of A (AdicCompletion (principalIdeal A f) (M : Type u))

structure PrincipalCompletionComparisonDiagram (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (p : ℤ) where
  usual_completion : Mod A
  usual_completion_identification :
    Nonempty (usual_completion ≅
      principalUsualCompletion f ((derivedCohomologyFunctor (Mod A) p).obj K))
  lim_cohomology : Mod A
  lim_cohomology_identification : Prop
  tate_next : Mod A
  tate_next_identification :
    Nonempty (tate_next ≅ principalTateModule f
      ((derivedCohomologyFunctor (Mod A) (p + 1)).obj K))
  h0_completion : Mod A
  middle_cohomology : Mod A
  r_one_torsion : Mod A
  r_one_koszul : Mod A
  top_row : CategoryTheory.ShortComplex.ShortExact
    { f := (0 : usual_completion ⟶ lim_cohomology),
      g := (0 : lim_cohomology ⟶ tate_next), zero := by simp }
  middle_row : CategoryTheory.ShortComplex.ShortExact
    { f := (0 : h0_completion ⟶ middle_cohomology),
      g := (0 : middle_cohomology ⟶ tate_next), zero := by simp }
  left_column : CategoryTheory.ShortComplex.ShortExact
    { f := (0 : usual_completion ⟶ h0_completion),
      g := (0 : h0_completion ⟶ r_one_torsion), zero := by simp }
  middle_column : CategoryTheory.ShortComplex.ShortExact
    { f := (0 : lim_cohomology ⟶ middle_cohomology),
      g := (0 : middle_cohomology ⟶ r_one_koszul), zero := by simp }
  right_column_identification : Nonempty (tate_next ≅ tate_next)
  right_square_commutes : Prop

theorem principal_completion_comparison_diagram
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A) (K : D A) (p : ℤ) :
    Nonempty (PrincipalCompletionComparisonDiagram A f K p) := by
  sorry

def PrincipalCompletionSystemHasML {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (f : A) (K : D A) (p : ℤ) : Prop :=
  ∀ n : ℕ, Prop

def PrincipalTateSystemHasML {A : Type u} [CommRing A]
    (f : A) (M : Mod A) : Prop :=
  ∀ n : ℕ, Prop

theorem principal_completion_ML_iff_tate_ML
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (f : A) (K : D A) (p : ℤ) :
    PrincipalCompletionSystemHasML f K p ↔
      PrincipalTateSystemHasML f
        ((derivedCohomologyFunctor (Mod A) (p + 1)).obj K) := by
  sorry

/-! ## 94.7. Bounded torsion, kernels, henselianity, and reduced rings -/

def IsAnnihilatedByIdealPower {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) : Prop :=
  (I ^ n) • (⊤ : Submodule A (M : Type u)) = ⊥

theorem torsion_and_derived_complete_bounded
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (M : Mod A)
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
    (hA : derivedComplete I (moduleInDerived A (ModuleCat.of A A))) :
    IsAdicComplete I A := by
  sorry

end Formalization.Books.MoreAlgebra.Unit94
