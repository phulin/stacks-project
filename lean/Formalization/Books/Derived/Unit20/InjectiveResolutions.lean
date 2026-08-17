import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit14.Core
import Formalization.Books.Derived.Unit14.DerivedFunctors
import Formalization.Books.Homology.Unit27.Injectives

/-!
# Derived Categories, Chapter 20: injective resolutions

This file records the bounded-below injective-complex computation of right
derived functors, the right-acyclicity of injectives, and the existence
interfaces supplied by enough injectives.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit27
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w w'

namespace Formalization.Books.Derived.Unit20

/-! ## Injective complexes -/

/-- Every term of a bounded-below complex is injective. -/
def IsTermwiseInjectiveComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : CompPlus A) : Prop :=
  ∀ n : ℤ, Injective (I.obj.X n)

/-- A bounded-below complex computes the right derived functor of a functor on
the homotopy category. -/
def ComputesRightDerivedComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : KPlus A ⥤ D) (I : CompPlus A) : Prop :=
  ComputesRightDerived (quasiIsoPlusProperty A)
    (boundedQuasiIsoProperty_properties A).1 F
    ((HomotopyCategory.Plus.quotient A).obj I)

/- The functor on `K⁺(A)` obtained by applying an additive functor termwise and
then passing to the bounded-below derived category of its target. -/
noncomputable def rightDerivedSourceFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] :
    KPlus A ⥤ DPlus B :=
  F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

/- An object is right acyclic for an additive functor when its stalk complex
computes the associated right derived functor. -/
noncomputable def RightAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (X : A) : Prop :=
  ComputesRightDerived (quasiIsoPlusProperty A)
    (boundedQuasiIsoProperty_properties A).1
    (rightDerivedSourceFunctor F)
    ((HomotopyCategory.Plus.singleFunctor A 0).obj X)

/-- A bounded-below termwise injective complex computes any exact right
derived functor. -/
theorem termwiseInjectiveComplex_computes
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : KPlus A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (I : CompPlus A) (hI : IsTermwiseInjectiveComplex I) :
    ComputesRightDerivedComplex F I := by
  sorry

/-- An injective object is right acyclic for every additive functor. -/
theorem injective_rightAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (I : A) [Injective I] :
    RightAcyclic F I := by
  sorry

/-! ## Enough injectives -/

/-- Enough injectives make an exact functor on `K⁺` right derivable. -/
theorem rightDerived_everywhere_defined_of_enoughInjectives
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : KPlus A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    RightDerivable (quasiIsoPlusProperty A)
      (boundedQuasiIsoProperty_properties A).1 F := by
  sorry

/-- For an additive functor between abelian categories, Mathlib's canonical
bounded-below right-derived functor is defined everywhere when the source has
enough injectives. -/
theorem additive_rightDerived_everywhere_defined_of_enoughInjectives
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    ∃ (RF : DPlus A ⥤ DPlus B)
      (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
        DerivedCategory.Plus.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α (quasiIsoPlusProperty A) := by
  exact ⟨F.rightDerivedFunctorPlus, F.rightDerivedFunctorPlusUnit, inferInstance⟩

end Formalization.Books.Derived.Unit20
