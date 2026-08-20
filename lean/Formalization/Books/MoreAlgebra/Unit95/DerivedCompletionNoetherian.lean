import Formalization.Books.MoreAlgebra.Unit92
import Formalization.Books.MoreAlgebra.Unit87
import Formalization.Books.MoreAlgebra.Unit65
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.Algebra.Unit75.TorGroups
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# More on Algebra, Chapter 95: Derived completion for Noetherian rings

This file records the source's definitions and theorem interfaces.  Derived
completion, derived tensor products, Koszul situations, Tor modules, and
adic completion use the canonical objects already introduced in earlier
chapters or in Mathlib.  The inverse systems and the `R¹ lim` terms are
recorded as data because the project API does not expose a single canonical
module-level realization for all of these constructions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit87
open Formalization.Books.MoreAlgebra.Unit92
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit34
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit95

abbrev Mod (A : Type u) [CommRing A] := Unit92.Mod A

abbrev Comp (A : Type u) [CommRing A] := Unit92.Comp A

abbrev D (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] := Unit92.D A

/-! ## The naive completion and its quotient system -/

def idealQuotientModule (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) : Mod A :=
  ModuleCat.of A (A ⧸ I ^ (n + 1))

noncomputable abbrev idealQuotientObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (n : ℕ) : D A :=
  moduleInDerived A (idealQuotientModule A I n)

/- The index starts at `n + 1`, so it represents the source's positive powers
   `I^n` while retaining an index in `ℕ`. -/
structure DerivedIdealQuotientSystemData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) where
  system : DerivedInverseSystem (D A)
  stage_iso : ∀ n : ℕ,
    Nonempty (system.obj (Opposite.op n) ≅ idealQuotientObject I n)
  hasProduct : ∀ K : D A,
    HasProduct (fun n : ℕ =>
      (derivedTensorInverseSystem K system).obj (Opposite.op n))

theorem exists_derivedIdealQuotientSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    Nonempty (DerivedIdealQuotientSystemData A I) := by
  sorry

noncomputable def derivedIdealQuotientSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    DerivedIdealQuotientSystemData A I :=
  Classical.choice (exists_derivedIdealQuotientSystemData I)

noncomputable def naiveDerivedCompletion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A) : D A :=
  let S := derivedIdealQuotientSystemData I
  derivedLimitWithProduct (derivedTensorInverseSystem K S.system)
    (S.hasProduct K)

structure NaiveDerivedCompletionData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) where
  functor : D A ⥤ D A
  unit : 𝟭 (D A) ⟶ functor
  stage_formula : ∀ K : D A,
    Nonempty (functor.obj K ≅ naiveDerivedCompletion I K)
  complete : ∀ K : D A, derivedComplete I (functor.obj K)

theorem exists_naiveDerivedCompletionData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    Nonempty (NaiveDerivedCompletionData A I) := by
  sorry

noncomputable def naiveDerivedCompletionData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    NaiveDerivedCompletionData A I :=
  Classical.choice (exists_naiveDerivedCompletionData I)

noncomputable abbrev naiveDerivedCompletionFunctor {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    D A ⥤ D A :=
  (naiveDerivedCompletionData I).functor

noncomputable abbrev naiveDerivedCompletionUnit {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    𝟭 (D A) ⟶ naiveDerivedCompletionFunctor I :=
  (naiveDerivedCompletionData I).unit

noncomputable def naiveDerivedCompletionMap {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (K : D A) : K ⟶ naiveDerivedCompletion I K :=
  (naiveDerivedCompletionUnit I).app K ≫
    (Classical.choice ((naiveDerivedCompletionData I).stage_formula K)).hom

theorem naiveDerivedCompletion_is_complete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (K : D A) :
    derivedComplete I (naiveDerivedCompletion I K) := by
  sorry

/- The source's example uses the trivial square-zero extension of the
   `p`-adic integers by their fraction quotient.  The derived-category class
   is made explicit here because the project does not install a global
   instance for this particular ring. -/
noncomputable def padicRationalQuotientSubmodule (p : ℕ) [Fact p.Prime] :
    Submodule (PadicInt p) (Localization.Away (p : PadicInt p)) :=
  LinearMap.range (Algebra.linearMap (PadicInt p)
    (Localization.Away (p : PadicInt p)))

noncomputable def padicRationalQuotient (p : ℕ) [Fact p.Prime] :
    ModuleCat.{0} (PadicInt p) :=
  ModuleCat.of (PadicInt p)
    (Localization.Away (p : PadicInt p) ⧸ padicRationalQuotientSubmodule p)

noncomputable def padicOppositeRingHom (p : ℕ) [Fact p.Prime] :
    (PadicInt p)ᵐᵒᵖ →+* PadicInt p :=
  { toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by intro x y; simp [mul_comm]
    map_zero' := rfl
    map_add' := by intro x y; rfl }

noncomputable instance padicRationalQuotient_oppositeModule
    (p : ℕ) [Fact p.Prime] :
    Module (PadicInt p)ᵐᵒᵖ (padicRationalQuotient p : Type 0) :=
  Module.compHom (padicRationalQuotient p : Type 0) (padicOppositeRingHom p)

noncomputable instance padicRationalQuotient_isCentralScalar
    (p : ℕ) [Fact p.Prime] :
    IsCentralScalar (PadicInt p) (padicRationalQuotient p : Type 0) where
  op_smul_eq_smul := by intro r x; rfl

abbrev padicSquareZeroRing (p : ℕ) [Fact p.Prime] :=
  TrivSqZeroExt (PadicInt p) (padicRationalQuotient p : Type 0)

def padicSquareZeroPIdeal (p : ℕ) [Fact p.Prime] :
    Ideal (padicSquareZeroRing p) :=
  Ideal.span ({((p : PadicInt p), 0)} : Set (padicSquareZeroRing p))

noncomputable def padicBaseModule (p : ℕ) [Fact p.Prime] :
    ModuleCat.{0} (padicSquareZeroRing p) :=
  letI : Module (padicSquareZeroRing p) (PadicInt p) :=
    Module.compHom _
      (TrivSqZeroExt.fstHom (PadicInt p) (PadicInt p)
        (padicRationalQuotient p : Type 0)).toRingHom
  ModuleCat.of (padicSquareZeroRing p) (PadicInt p)

noncomputable abbrev padicBaseObject (p : ℕ) [Fact p.Prime]
    [HasDerivedCategory.{w} (Mod (padicSquareZeroRing p))] :
    D (padicSquareZeroRing p) :=
  moduleInDerived (padicSquareZeroRing p) (padicBaseModule p)

noncomputable abbrev padicAdjointModel (p : ℕ) [Fact p.Prime]
    [HasDerivedCategory.{w} (Mod (padicSquareZeroRing p))] :
    D (padicSquareZeroRing p) :=
  (shiftFunctor (D (padicSquareZeroRing p)) (1 : ℤ)).obj
      (padicBaseObject p) ⊞ padicBaseObject p

structure PadicNaiveCompletionMismatchData (p : ℕ) [Fact p.Prime]
    [HasDerivedCategory.{w} (Mod (padicSquareZeroRing p))] where
  naive : D (padicSquareZeroRing p)
  adjoint : D (padicSquareZeroRing p)
  naive_computation : Nonempty
    (naiveDerivedCompletion (padicSquareZeroPIdeal p) (padicBaseObject p) ≅ naive)
  adjoint_computation : Nonempty
    ((derivedCompletion (padicSquareZeroPIdeal p)
      (by exact Submodule.fg_span_singleton _)).obj
        (padicBaseObject p) ≅ adjoint)
  naive_identification : Nonempty (naive ≅ padicBaseObject p)
  adjoint_identification : Nonempty (adjoint ≅ padicAdjointModel p)
  not_isomorphic : ¬ Nonempty (naive ≅ adjoint)

theorem exists_padic_naive_completion_mismatch (p : ℕ) [Fact p.Prime]
    [HasDerivedCategory.{w} (Mod (padicSquareZeroRing p))] :
    Nonempty (PadicNaiveCompletionMismatchData p) := by
  sorry

/-! ## 95.1. Koszul systems and naive completion -/

def generatedQuotientModule (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (n : ℕ) : Mod A :=
  ModuleCat.of A (A ⧸ Ideal.span (Set.range (fun i => f i ^ (n + 1))))

noncomputable abbrev generatedQuotientObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (r : ℕ) (f : Fin r → A) (n : ℕ) : D A :=
  moduleInDerived A (generatedQuotientModule A r f n)

structure GeneratedQuotientSystemData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (r : ℕ) (f : Fin r → A) where
  system : DerivedInverseSystem (D A)
  stage_iso : ∀ n : ℕ,
    Nonempty (system.obj (Opposite.op n) ≅ generatedQuotientObject r f n)
  hasProduct : ∀ K : D A,
    HasProduct (fun n : ℕ =>
      (derivedTensorInverseSystem K system).obj (Opposite.op n))

theorem exists_generatedQuotientSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (r : ℕ) (f : Fin r → A) :
    Nonempty (GeneratedQuotientSystemData A r f) := by
  sorry

noncomputable def generatedQuotientSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (r : ℕ) (f : Fin r → A) :
    GeneratedQuotientSystemData A r f :=
  Classical.choice (exists_generatedQuotientSystemData r f)

structure NoetherianKoszulProComparisonData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (S : KoszulSituation A I r f) where
  quotient : GeneratedQuotientSystemData A r f
  pro_isomorphism :
    IsProIsomorphism S.system quotient.system

structure GeneratedAdicProComparisonData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f)) where
  generated : GeneratedQuotientSystemData A r f
  adic : DerivedIdealQuotientSystemData A I
  pro_isomorphism : IsProIsomorphism generated.system adic.system

theorem sequence_Koszul_complexes {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f))
    (S : KoszulSituation A I r f) :
    Nonempty (NoetherianKoszulProComparisonData A I r f S) := by
  sorry

theorem generated_quotients_pro_equal_adic_quotients
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hgen : I = Ideal.span (Set.range f)) :
    Nonempty (GeneratedAdicProComparisonData A I r f hgen) := by
  sorry

theorem proposition_noetherian_naive_completion_is_completion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    ∃ C : NaiveDerivedCompletionData A I,
      ∀ K E : D A, derivedComplete I E →
        Function.Bijective
          (fun g : C.functor.obj K ⟶ E => C.unit.app K ≫ g) := by
  sorry

/-! ## Derived completion and the `R¹ lim` calculation -/

def torStage {A : Type u} [CommRing A] (I : Ideal A)
    (M : Mod A) (i n : ℕ) : Mod A :=
  Formalization.Books.Algebra.Unit75.Tor M (idealQuotientModule A I n) i

structure TorInverseSystemData (A : Type u) [CommRing A]
    (I : Ideal A) (M : Mod A) (i : ℕ) where
  system : ℕᵒᵖ ⥤ Mod A
  stage_iso : ∀ n : ℕ,
    Nonempty (system.obj (Opposite.op n) ≅ torStage I M i n)
  hasLimit : HasLimit system
  limit : Mod A
  limit_identification : Nonempty
    (limit ≅ (letI := hasLimit; Limits.limit system))
  first_derived_limit : Mod A

structure NoetherianCalculateSequenceData (A : Type u) [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (M : Mod A) (i : ℕ)
    (T : TorInverseSystemData A I M i)
    (Tnext : TorInverseSystemData A I M (i + 1)) where
  left : Tnext.first_derived_limit ⟶
    (derivedCohomologyFunctor A (-(i : ℤ))).obj
      ((derivedCompletion I (IsNoetherian.noetherian I)).obj
        (moduleInDerived A M))
  middle : (derivedCohomologyFunctor A (-(i : ℤ))).obj
      ((derivedCompletion I (IsNoetherian.noetherian I)).obj
        (moduleInDerived A M)) ⟶
    T.limit
  zero : left ≫ middle = 0
  exact :
    (ShortComplex.mk left middle zero).ShortExact

structure NoetherianCalculateData (A : Type u) [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (M : Mod A) where
  tor_system : ∀ i : ℕ, TorInverseSystemData A I M i
  sequence : ∀ i : ℕ,
    NoetherianCalculateSequenceData A I M i (tor_system i) (tor_system (i + 1))

theorem lemma_noetherian_calculate {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (M : Mod A) :
    Nonempty (NoetherianCalculateData A I M) := by
  sorry

def IsDerivedBoundedAbove {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A) : Prop :=
  ∃ C : Comp A, IsBoundedAbove C ∧
    Nonempty ((DerivedCategory.Q : Comp A ⥤ D A).obj C ≅ K)

structure DerivedCohomologySystemData (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A) (i : ℕ) where
  system : ℕᵒᵖ ⥤ Mod A
  stage_iso : ∀ n : ℕ,
    Nonempty (system.obj (Opposite.op n) ≅
      (derivedCohomologyFunctor A (-(i : ℤ))).obj
        (derivedTensor K (idealQuotientObject I n)))
  hasLimit : HasLimit system
  limit : Mod A
  limit_identification : Nonempty
    (limit ≅ (letI := hasLimit; Limits.limit system))
  first_derived_limit : Mod A

structure DerivedBoundedAboveSequenceData (A : Type u) [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (K : D A) (i : ℕ)
    (T : DerivedCohomologySystemData A I K i)
    (Tnext : DerivedCohomologySystemData A I K (i + 1)) where
  left : Tnext.first_derived_limit ⟶
    (derivedCohomologyFunctor A (-(i : ℤ))).obj
      ((derivedCompletion I (IsNoetherian.noetherian I)).obj K)
  middle : (derivedCohomologyFunctor A (-(i : ℤ))).obj
      ((derivedCompletion I (IsNoetherian.noetherian I)).obj K) ⟶ T.limit
  zero : left ≫ middle = 0
  exact : (ShortComplex.mk left middle zero).ShortExact

structure DerivedBoundedAboveCalculateData (A : Type u) [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (K : D A) where
  cohomology_system : ∀ i : ℕ, DerivedCohomologySystemData A I K i
  sequence : ∀ i : ℕ,
    DerivedBoundedAboveSequenceData A I K i
      (cohomology_system i) (cohomology_system (i + 1))

theorem lemma_noetherian_calculate_bounded_above
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A)
    (hK : IsDerivedBoundedAbove K) :
    Nonempty (DerivedBoundedAboveCalculateData A I K) := by
  sorry

/-! ## Finite cohomology and finite derived-complete modules -/

noncomputable def adicCompletionModule {A : Type u} [CommRing A]
    (I : Ideal A) (M : Mod A) : Mod A :=
  ModuleCat.of A (AdicCompletion I (M : Type u))

theorem lemma_derived_completion_pseudo_coherent
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A)
    (hfinite : ∀ n : ℤ,
      Module.Finite A ((derivedCohomologyFunctor A n).obj K : Type u)) :
    ∀ n : ℤ, Nonempty
      ((derivedCohomologyFunctor A n).obj
          ((derivedCompletion I (IsNoetherian.noetherian I)).obj K) ≅
        adicCompletionModule I ((derivedCohomologyFunctor A n).obj K)) := by
  sorry

def FiniteOver {R M : Type u} [CommRing R] [AddCommGroup M] : Prop :=
  ∃ h : Module R M, @Module.Finite R M inferInstance inferInstance h

structure DerivedCompleteFiniteModuleData (A : Type u) [CommRing A]
    (I : Ideal A) (M : Mod A) where
  ordinary_completion_iso : Nonempty (M ≅ adicCompletionModule I M)
  finite_over_completion :
    FiniteOver (R := AdicCompletion I A) (M := (M : Type u))

theorem lemma_derived_complete_finite {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (M : Mod A) (hM : derivedCompleteModule I M)
    (hfinite : Module.Finite (A ⧸ I)
      ((M : Type u) ⧸ (I • (⊤ : Submodule A (M : Type u))))) :
    Nonempty (DerivedCompleteFiniteModuleData A I M) := by
  sorry

/-! ## When derived completion is ordinary completion -/

noncomputable def tensorModule {A : Type u} [CommRing A]
    (M N : Mod A) : Mod A :=
  ModuleCat.of A (TensorProduct A (M : Type u) (N : Type u))

noncomputable def localizedTensorModule {A : Type u} [CommRing A]
    (M : Mod A) (f : A) : Mod A :=
  tensorModule M (localizedModule A f)

noncomputable def ordinaryDerivedCompletion {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M : Mod A) : D A :=
  (derivedCompletion I (IsNoetherian.noetherian I)).obj
    (moduleInDerived A M)

theorem lemma_when_derived_completion_is_completion_tensor
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M N : Mod A)
    [Module.Finite A (M : Type u)] [Module.Flat A (N : Type u)] :
    Nonempty (ordinaryDerivedCompletion I (tensorModule M N) ≅
      moduleInDerived A (adicCompletionModule I (tensorModule M N))) := by
  sorry

theorem lemma_when_derived_completion_is_completion_localization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M : Mod A) (f : A)
    [Module.Finite A (M : Type u)] :
    Nonempty (ordinaryDerivedCompletion I (localizedTensorModule M f) ≅
      moduleInDerived A (adicCompletionModule I (localizedTensorModule M f))) := by
  sorry

/-! ## Derived completion commutes with tensoring by finite objects -/

def IsPseudoCoherentObject {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A) : Prop :=
  Formalization.Books.MoreAlgebra.Unit65.IsPseudoCoherent A K

theorem lemma_derived_completion_tensor_finite_module
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A)
    (hK : IsDerivedBoundedAbove K) (M : Mod A)
    [Module.Finite A (M : Type u)] :
    Nonempty
      ((derivedCompletion I (IsNoetherian.noetherian I)).obj
          (derivedTensor K (moduleInDerived A M)) ≅
        derivedTensor
      ((derivedCompletion I (IsNoetherian.noetherian I)).obj K)
          (moduleInDerived A M)) := by
  sorry

theorem lemma_derived_completion_tensor_pseudo_coherent
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K L : D A)
    (hK : IsDerivedBoundedAbove K) (hL : IsPseudoCoherentObject L) :
    Nonempty
      ((derivedCompletion I (IsNoetherian.noetherian I)).obj (derivedTensor K L) ≅
        derivedTensor ((derivedCompletion I (IsNoetherian.noetherian I)).obj K) L) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit95
