import Formalization.Books.Derived.Unit20.RightDerivedProperties
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Homology.Unit07.AdditiveFunctors
import Formalization.Books.Homology.Unit12.CohomologicalDeltaFunctors
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Derived Categories, Chapter 20: higher derived functors

The higher derived functors are defined by applying the canonical cohomology
functors to the bounded-below right-derived functor.  Long exact sequences are
represented by the finite exact windows supplied by Mathlib's homological
functor API.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit12
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w w'

namespace Formalization.Books.Derived.Unit20

/-! ## The higher derived functors -/

/-- The bounded-below right-derived functor attached to a left exact functor,
using the canonical additivity consequence for functors between abelian
categories. -/
noncomputable def leftExactRightDerivedComplexFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    CompPlus A ⥤ DPlus B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact rightDerivedComplexFunctor F

/-- The integer-indexed higher right-derived functor `R^i F`. -/
noncomputable def higherRightDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) (i : ℤ) : A ⥤ B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact
    DerivedCategory.Plus.singleFunctor A 0 ⋙
      F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B i

/-- The triangle in `D⁺(B)` whose cohomology sequence is the long sequence
attached to a short exact sequence of bounded-below complexes. -/
noncomputable def rightDerivedTriangle
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {S : ShortComplex (CompPlus A)}
    (δ : (leftExactRightDerivedComplexFunctor F hF).obj S.X₃ ⟶
      (shiftFunctor (DPlus B) (1 : ℤ)).obj
        ((leftExactRightDerivedComplexFunctor F hF).obj S.X₁)) :
    Triangle (DPlus B) :=
  Triangle.mk
    ((leftExactRightDerivedComplexFunctor F hF).map S.f)
    ((leftExactRightDerivedComplexFunctor F hF).map S.g)
    δ

/-- A finite exact window of the long cohomology sequence associated to a
right-derived triangle. -/
noncomputable def rightDerivedLongExactWindow
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {S : ShortComplex (CompPlus A)}
    (δ : (leftExactRightDerivedComplexFunctor F hF).obj S.X₃ ⟶
      (shiftFunctor (DPlus B) (1 : ℤ)).obj
        ((leftExactRightDerivedComplexFunctor F hF).obj S.X₁))
    (n : ℤ) : ComposableArrows B 5 :=
  (DerivedCategory.Plus.homologyFunctor B 0).homologySequenceComposableArrows₅
    (rightDerivedTriangle F hF δ) n (n + 1) rfl

/-- A short exact sequence of bounded-below complexes has the associated long
exact cohomology sequence after applying the right-derived functor. -/
theorem rightDerived_shortExact_longExact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    {S : ShortComplex (CompPlus A)} (hS : S.ShortExact) :
    ∃ δ : (leftExactRightDerivedComplexFunctor F hF).obj S.X₃ ⟶
      (shiftFunctor (DPlus B) (1 : ℤ)).obj
        ((leftExactRightDerivedComplexFunctor F hF).obj S.X₁),
      rightDerivedTriangle F hF δ ∈ distTriang (DPlus B) ∧
        ∀ n : ℤ, (rightDerivedLongExactWindow F hF δ n).Exact := by
  sorry

/-! ## Normalizations and universality -/

/-- Objectwise vanishing of a functor. -/
def FunctorObjectwiseIsZero
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] [HasZeroObject B]
    (G : A ⥤ B) : Prop :=
  ∀ X : A, IsZero (G.obj X)

/-- The family of higher right-derived functors, with its universal
cohomological δ-functor structure. -/
def IsUniversalHigherRightDerivedDeltaFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) : Prop :=
  ∃ G : CohomologicalDeltaFunctor A B,
    G.IsUniversal ∧
      ∀ n : ℕ, G.functor n = higherRightDerivedFunctor F hF (n : ℤ)

/-- Negative higher right-derived functors vanish. -/
theorem higherRightDerivedFunctor_isZero_of_negative
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) (i : ℤ) (hi : i < 0) :
    FunctorObjectwiseIsZero (higherRightDerivedFunctor F hF i) := by
  sorry

/-- The degree-zero higher right-derived functor is naturally isomorphic to
the original left exact functor. -/
theorem higherRightDerivedFunctor_zero_iso
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    Nonempty (higherRightDerivedFunctor F hF 0 ≅ F) := by
  sorry

/-- Positive higher right-derived functors vanish on injective objects. -/
theorem higherRightDerivedFunctor_obj_isZero_of_injective
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F)
    (i : ℤ) (hi : 0 < i) (I : A) [Injective I] :
    IsZero ((higherRightDerivedFunctor F hF i).obj I) := by
  sorry

/-- The higher right-derived functors form the universal cohomological
δ-functor extending `F`. -/
theorem higherRightDerivedFunctor_universal
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    IsUniversalHigherRightDerivedDeltaFunctor F hF := by
  sorry

end Formalization.Books.Derived.Unit20
