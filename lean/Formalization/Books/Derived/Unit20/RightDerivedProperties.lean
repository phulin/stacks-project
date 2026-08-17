import Formalization.Books.Derived.Unit20.InjectiveResolutions
import Formalization.Books.Derived.Unit12.CanonicalDeltaFunctor
import Formalization.Books.Derived.Unit03.Definitions

/-!
# Derived Categories, Chapter 20: properties of right derived functors

The canonical bounded-below right-derived functor is used throughout.  The
exactness and δ-functor assertions are retained as interfaces for the prove
stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w w'

namespace Formalization.Books.Derived.Unit20

/-! ## The induced functors -/

/-- The right derived functor on bounded-below complexes. -/
noncomputable abbrev rightDerivedComplexFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    CompPlus A ⥤ DPlus B :=
  DerivedCategory.Plus.Q (C := A) ⋙ F.rightDerivedFunctorPlus

/-- The right derived functor after passing from complexes to the homotopy
category. -/
noncomputable abbrev rightDerivedHomotopyFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    KPlus A ⥤ DPlus B :=
  DerivedCategory.Plus.Qh (C := A) ⋙ F.rightDerivedFunctorPlus

/-- The right derived functor restricted to stalk complexes in degree zero. -/
noncomputable abbrev rightDerivedObjectFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    A ⥤ DPlus B :=
  DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus

/-! ## Exactness and δ-functors -/

/-- The canonical right-derived functor is exact on the bounded-below derived
categories.  The shift-commutation datum is exposed explicitly because
Mathlib's right-derived construction does not yet install it as a global
instance. -/
theorem rightDerivedFunctorPlus_isExact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    ∃ hG : (F.rightDerivedFunctorPlus).CommShift ℤ,
      letI : (F.rightDerivedFunctorPlus).CommShift ℤ := hG
      (F.rightDerivedFunctorPlus).IsTriangulated := by
  sorry

/-- The right-derived functor induces an exact functor from `K⁺(A)` to
`D⁺(B)`. -/
theorem rightDerivedHomotopyFunctor_isExact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    ∃ hG : (rightDerivedHomotopyFunctor F).CommShift ℤ,
      letI : (rightDerivedHomotopyFunctor F).CommShift ℤ := hG
      (rightDerivedHomotopyFunctor F).IsTriangulated := by
  sorry

/-- The right-derived functor on bounded-below complexes carries the
canonical δ-functor structure. -/
theorem rightDerivedComplexFunctor_isDeltaFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    Nonempty (DeltaFunctor (rightDerivedComplexFunctor F)) := by
  sorry

/-- The right-derived functor on objects carries the induced δ-functor
structure. -/
theorem rightDerivedObjectFunctor_isDeltaFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    Nonempty (DeltaFunctor (rightDerivedObjectFunctor F)) := by
  sorry

end Formalization.Books.Derived.Unit20
