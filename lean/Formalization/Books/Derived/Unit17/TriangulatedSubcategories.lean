import Formalization.Books.Derived.Unit17.Core

/-!
# Derived Categories, Chapter 17: triangulated subcategories

This file records the source-facing theorem interfaces for the chapter.  The
constructions themselves are in `Core`; proofs of the chapter's mathematical
lemmas are intentionally deferred to the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit10
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u w' v' u'

namespace Formalization.Books.Derived.Unit17

/-! ## Strictly full saturated triangulated subcategories -/

theorem derivedCohomologyProperty_properties
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] :
    IsStrictlyFullSaturatedPretriangulated (derivedCohomologyProperty P) ∧
      IsStrictlyFullSaturatedPretriangulated (derivedCohomologyPlusProperty P) ∧
        IsStrictlyFullSaturatedPretriangulated (derivedCohomologyMinusProperty P) ∧
          IsStrictlyFullSaturatedPretriangulated
            (derivedCohomologyBoundedProperty P) := by
  sorry

theorem derivedCohomologyWithinProperty_properties
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] :
    IsStrictlyFullSaturatedPretriangulated
        (derivedCohomologyPlusWithinProperty P) ∧
      IsStrictlyFullSaturatedPretriangulated
        (derivedCohomologyMinusWithinProperty P) ∧
        IsStrictlyFullSaturatedPretriangulated
          (derivedCohomologyBoundedWithinProperty P) := by
  sorry

/-! ## The exact comparison functors -/

theorem derivedComparisonFunctor_is_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    Nonempty (ExactTriangulatedFunctorData (derivedComparisonFunctor P)) := by
  sorry

theorem derivedInclusionPlus_is_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    Nonempty (ExactTriangulatedFunctorData (derivedInclusionPlusFunctor P)) := by
  sorry

theorem derivedInclusionMinus_is_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    Nonempty (ExactTriangulatedFunctorData (derivedInclusionMinusFunctor P)) := by
  sorry

theorem derivedInclusionBounded_is_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    Nonempty (ExactTriangulatedFunctorData (derivedInclusionBoundedFunctor P)) := by
  sorry

theorem derivedComparisonFunctor_fac
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    derivedComparisonFunctor P ⋙ (derivedCohomologyProperty P).ι =
      derivedInclusionFunctor P := by
  sorry

theorem derivedComparisonPlus_fac
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    derivedComparisonPlus P ⋙ (derivedCohomologyPlusWithinProperty P).ι =
      derivedInclusionPlusFunctor P := by
  sorry

theorem derivedComparisonMinus_fac
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    derivedComparisonMinus P ⋙ (derivedCohomologyMinusWithinProperty P).ι =
      derivedInclusionMinusFunctor P := by
  sorry

theorem derivedComparisonBounded_fac
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    derivedComparisonBounded P ⋙
        (derivedCohomologyBoundedWithinProperty P).ι =
      derivedInclusionBoundedFunctor P := by
  sorry

/-! ## Serre quotients -/

theorem derivedSerreQuotient_kernel_obj_iff
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)]
    (X : DerivedCategory A) :
    IsZero ((derivedSerreQuotientFunctor P).obj X) ↔
      derivedCohomologyProperty P X := by
  sorry

theorem derivedSerreQuotientFactor_fac
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    quotientFunctor (derivedCohomologyProperty P) ⋙
        derivedSerreQuotientFactor P =
      derivedSerreQuotientFunctor P := by
  sorry

theorem derivedSerreQuotientPlusFactor_fac
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    quotientFunctor (derivedCohomologyPlusWithinProperty P) ⋙
        derivedSerreQuotientPlusFactor P =
      derivedSerreQuotientPlusFunctor P := by
  sorry

theorem derivedSerreQuotientMinusFactor_fac
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    quotientFunctor (derivedCohomologyMinusWithinProperty P) ⋙
        derivedSerreQuotientMinusFactor P =
      derivedSerreQuotientMinusFunctor P := by
  sorry

theorem derivedSerreQuotientBoundedFactor_fac
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    quotientFunctor (derivedCohomologyBoundedWithinProperty P) ⋙
        derivedSerreQuotientBoundedFactor P =
      derivedSerreQuotientBoundedFunctor P := by
  sorry

theorem derivedSerreQuotient_essentially_surjective
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    (derivedSerreQuotientFunctor P).EssSurj := by
  sorry

/-! ## The left-adjoint criterion -/

theorem derivedSerreQuotientFactor_is_equivalence
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)]
    (u : serreQuotient P ⥤ A)
    (adj : u ⊣ serreQuotientFunctor P)
    (hvu : u ⋙ serreQuotientFunctor P ≅ 𝟭 (serreQuotient P)) :
    Functor.IsEquivalence (derivedSerreQuotientFactor P) := by
  sorry

theorem derivedSerreQuotientPlusFactor_is_equivalence
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)]
    (u : serreQuotient P ⥤ A)
    (adj : u ⊣ serreQuotientFunctor P)
    (hvu : u ⋙ serreQuotientFunctor P ≅ 𝟭 (serreQuotient P)) :
    Functor.IsEquivalence (derivedSerreQuotientPlusFactor P) := by
  sorry

theorem derivedSerreQuotientMinusFactor_is_equivalence
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)]
    (u : serreQuotient P ⥤ A)
    (adj : u ⊣ serreQuotientFunctor P)
    (hvu : u ⋙ serreQuotientFunctor P ≅ 𝟭 (serreQuotient P)) :
    Functor.IsEquivalence (derivedSerreQuotientMinusFactor P) := by
  sorry

theorem derivedSerreQuotientBoundedFactor_is_equivalence
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)]
    (u : serreQuotient P ⥤ A)
    (adj : u ⊣ serreQuotientFunctor P)
    (hvu : u ⋙ serreQuotientFunctor P ≅ 𝟭 (serreQuotient P)) :
    Functor.IsEquivalence (derivedSerreQuotientBoundedFactor P) := by
  sorry

/-! ## The bounded-above lifting hypothesis and the replacement claim -/

theorem boundedAbove_subcomplex_replacement
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsSerreClass]
    (hP : SerreLiftingCondition P)
    (X : CochainComplex A ℤ)
    (hX : IsBoundedAbove X)
    (hcoh : ∀ i : ℤ, P (X.homology i))
    (B : ℤ → A) (b : ∀ i : ℤ, B i ⟶ X.X i)
    (hbmem : ∀ i : ℤ, P (B i))
    (hbmono : ∀ i : ℤ, Mono (b i)) :
    Nonempty (BoundedAboveSubcomplexReplacement P X B b) := by
  sorry

theorem derivedComparisonMinus_is_equivalence
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory]
    (hP : SerreLiftingCondition P) :
    Functor.IsEquivalence (derivedComparisonMinus P) := by
  sorry

end Formalization.Books.Derived.Unit17
