import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit14.DerivedFunctors

/-!
# Derived Categories, Chapter 15: derived functors on derived categories

The classical situation in the source is expressed using Mathlib's canonical
homotopy and derived categories.  Chapter 14 supplies the generic
essentially-constant derived-value constructions; this file specializes them
to the quasi-isomorphism systems on `K`, `K⁺`, and `K⁻`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Categories.Unit27
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u v' u'

namespace Formalization.Books.Derived.Unit15

/-! ## The quasi-isomorphism systems used in the classical cases -/

theorem classicalQuasiIsoSaturated
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (quasiIsoHomotopyProperty C) :=
  (quasiIsoHomotopyProperty_properties C).1

theorem classicalQuasiIsoPlusSaturated
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (quasiIsoPlusProperty C) :=
  (boundedQuasiIsoProperty_properties C).1

theorem classicalQuasiIsoMinusSaturated
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (quasiIsoMinusProperty C) :=
  (boundedQuasiIsoProperty_properties C).2.1

/-! ## The classical situation -/

section Situation

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : A ⥤ B) [F.Additive]

/-- The additive functor induced by `F` on the unbounded homotopy category. -/
noncomputable def classicalHomotopyFunctor :
    BookHomotopyCategory A ⥤ BookHomotopyCategory B :=
  additiveHomotopyFunctor F

/-- The additive functor induced by `F` on the bounded-below homotopy category. -/
noncomputable def classicalHomotopyPlusFunctor :
    KPlus A ⥤ KPlus B :=
  additiveHomotopyPlusFunctor F

/-- The additive functor induced by `F` on the bounded-above homotopy category. -/
noncomputable def classicalHomotopyMinusFunctor :
    KMinus A ⥤ KMinus B :=
  additiveHomotopyMinusFunctor F

/-- The three induced homotopy-category functors are exact in the
triangulated sense used by the source. -/
theorem classical_homotopy_functors_are_exact :
    Nonempty (ExactTriangulatedFunctorData (classicalHomotopyFunctor F)) ∧
      Nonempty (ExactTriangulatedFunctorData (classicalHomotopyPlusFunctor F)) ∧
        Nonempty (ExactTriangulatedFunctorData (classicalHomotopyMinusFunctor F)) := by
  have h := additive_homotopy_functors_are_exact F
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/- The source denotes the composites with the localization functors by the
same letter `F`.  These are the three distinct input functors occurring in
the four right/left derived cases. -/

/-- The input functor `K(A) ⥤ D(B)` in the unbounded cases. -/
noncomputable def classicalHomotopyToDerived
    [HasDerivedCategory.{w} B] :
    BookHomotopyCategory A ⥤ DerivedCategory B :=
  classicalHomotopyFunctor F ⋙ DerivedCategory.Qh

/-- The input functor `K⁺(A) ⥤ D⁺(B)` in the bounded-below case. -/
noncomputable def classicalHomotopyPlusToDerived
    [HasDerivedCategory.{w} B] :
    KPlus A ⥤ DPlus B :=
  classicalHomotopyPlusFunctor F ⋙ plusDerivedLocalizationFunctor B

/-- The input functor `K⁻(A) ⥤ D⁻(B)` in the bounded-above case. -/
noncomputable def classicalHomotopyMinusToDerived
    [HasDerivedCategory.{w} B] :
    KMinus A ⥤ DMinus B :=
  classicalHomotopyMinusFunctor F ⋙ minusDerivedLocalizationFunctor B

end Situation

/-! ## The four partial derived functors -/

section PartialDerivedFunctors

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

/-- The partial right derived functor attached to `K(A) ⥤ D(B)`. -/
noncomputable def classicalRightDerivedFunctor :
    rightDerivedSubcategory (quasiIsoHomotopyProperty A)
        (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F) ⥤
      DerivedCategory B :=
  rightDerivedFunctor (quasiIsoHomotopyProperty A)
    (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F)

/-- The partial right derived functor attached to `K⁺(A) ⥤ D⁺(B)`. -/
noncomputable def classicalRightDerivedPlusFunctor :
    rightDerivedSubcategory (quasiIsoPlusProperty A)
        (classicalQuasiIsoPlusSaturated A) (classicalHomotopyPlusToDerived F) ⥤
      DPlus B :=
  rightDerivedFunctor (quasiIsoPlusProperty A)
    (classicalQuasiIsoPlusSaturated A) (classicalHomotopyPlusToDerived F)

/-- The partial left derived functor attached to `K(A) ⥤ D(B)`. -/
noncomputable def classicalLeftDerivedFunctor :
    leftDerivedSubcategory (quasiIsoHomotopyProperty A)
        (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F) ⥤
      DerivedCategory B :=
  leftDerivedFunctor (quasiIsoHomotopyProperty A)
    (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F)

/-- The partial left derived functor attached to `K⁻(A) ⥤ D⁻(B)`. -/
noncomputable def classicalLeftDerivedMinusFunctor :
    leftDerivedSubcategory (quasiIsoMinusProperty A)
        (classicalQuasiIsoMinusSaturated A) (classicalHomotopyMinusToDerived F) ⥤
      DMinus B :=
  leftDerivedFunctor (quasiIsoMinusProperty A)
    (classicalQuasiIsoMinusSaturated A) (classicalHomotopyMinusToDerived F)

/-! ### Definedness and computing predicates -/

def classicalRightDerivedDefined (X : BookHomotopyCategory A) : Prop :=
  rightDerivedDefined (quasiIsoHomotopyProperty A)
    (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F) X

def classicalRightDerivedPlusDefined (X : KPlus A) : Prop :=
  rightDerivedDefined (quasiIsoPlusProperty A)
    (classicalQuasiIsoPlusSaturated A) (classicalHomotopyPlusToDerived F) X

def classicalLeftDerivedDefined (X : BookHomotopyCategory A) : Prop :=
  leftDerivedDefined (quasiIsoHomotopyProperty A)
    (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F) X

def classicalLeftDerivedMinusDefined (X : KMinus A) : Prop :=
  leftDerivedDefined (quasiIsoMinusProperty A)
    (classicalQuasiIsoMinusSaturated A) (classicalHomotopyMinusToDerived F) X

def classicalRightDerivedComputes (X : BookHomotopyCategory A) : Prop :=
  ComputesRightDerived (quasiIsoHomotopyProperty A)
    (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F) X

def classicalRightDerivedPlusComputes (X : KPlus A) : Prop :=
  ComputesRightDerived (quasiIsoPlusProperty A)
    (classicalQuasiIsoPlusSaturated A) (classicalHomotopyPlusToDerived F) X

def classicalLeftDerivedComputes (X : BookHomotopyCategory A) : Prop :=
  ComputesLeftDerived (quasiIsoHomotopyProperty A)
    (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F) X

def classicalLeftDerivedMinusComputes (X : KMinus A) : Prop :=
  ComputesLeftDerived (quasiIsoMinusProperty A)
    (classicalQuasiIsoMinusSaturated A) (classicalHomotopyMinusToDerived F) X

/-! ### Objects concentrated in degree zero -/

/-- The source's functor `A ⥤ K(A)` sending an object to the complex
concentrated in degree zero. -/
noncomputable abbrev degreeZeroHomotopyFunctor :
    A ⥤ BookHomotopyCategory A :=
  HomotopyCategory.singleFunctor A (0 : ℤ)

/-- An object of `A` is right acyclic when its degree-zero complex computes
the unbounded right derived functor. -/
def classicalRightAcyclic (X : A) : Prop :=
  classicalRightDerivedComputes F
    ((degreeZeroHomotopyFunctor (A := A)).obj X)

/-- An object of `A` is left acyclic when its degree-zero complex computes the
unbounded left derived functor. -/
def classicalLeftAcyclic (X : A) : Prop :=
  classicalLeftDerivedComputes F
    ((degreeZeroHomotopyFunctor (A := A)).obj X)

end PartialDerivedFunctors

/-! ## The bounded-versus-unbounded comparison -/

section Irrelevant

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

/-- On a bounded-below homotopy object, unbounded and bounded-below
right-derived definedness agree. -/
theorem classical_rightDerived_defined_iff_plus
    (X : KPlus A) :
    classicalRightDerivedDefined F ((HomotopyCategory.Plus.ι A).obj X) ↔
      classicalRightDerivedPlusDefined F X := by
  sorry

/-- The two right-derived values in the preceding equivalence are canonically
isomorphic after including `D⁺(B)` into `D(B)`. -/
theorem classical_rightDerived_value_iso_plus
    (X : KPlus A)
    (hX : classicalRightDerivedDefined F ((HomotopyCategory.Plus.ι A).obj X))
    (hX' : classicalRightDerivedPlusDefined F X) :
    Nonempty
      (rightDerivedValue (quasiIsoHomotopyProperty A)
          (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F)
          ((HomotopyCategory.Plus.ι A).obj X) hX ≅
        (DerivedCategory.Plus.ι (C := B)).obj
          (rightDerivedValue (quasiIsoPlusProperty A)
            (classicalQuasiIsoPlusSaturated A) (classicalHomotopyPlusToDerived F)
            X hX')) := by
  sorry

/-- A bounded-below homotopy object computes the unbounded right-derived
functor exactly when it computes the bounded-below one. -/
theorem classical_rightDerived_computes_iff_plus
    (X : KPlus A) :
    classicalRightDerivedComputes F ((HomotopyCategory.Plus.ι A).obj X) ↔
      classicalRightDerivedPlusComputes F X := by
  sorry

/-- On a bounded-above homotopy object, unbounded and bounded-above
left-derived definedness agree. -/
theorem classical_leftDerived_defined_iff_minus
    (X : KMinus A) :
    classicalLeftDerivedDefined F ((boundedAboveHomotopyProperty A).ι.obj X) ↔
      classicalLeftDerivedMinusDefined F X := by
  sorry

/-- The two left-derived values in the preceding equivalence are canonically
isomorphic after including `D⁻(B)` into `D(B)`. -/
theorem classical_leftDerived_value_iso_minus
    (X : KMinus A)
    (hX : classicalLeftDerivedDefined F
      ((boundedAboveHomotopyProperty A).ι.obj X))
    (hX' : classicalLeftDerivedMinusDefined F X) :
    Nonempty
      (leftDerivedValue (quasiIsoHomotopyProperty A)
          (classicalQuasiIsoSaturated A) (classicalHomotopyToDerived F)
          ((boundedAboveHomotopyProperty A).ι.obj X) hX ≅
        (DerivedCategory.Minus.ι (C := B)).obj
          (leftDerivedValue (quasiIsoMinusProperty A)
            (classicalQuasiIsoMinusSaturated A) (classicalHomotopyMinusToDerived F)
            X hX')) := by
  sorry

/-- A bounded-above homotopy object computes the unbounded left-derived
functor exactly when it computes the bounded-above one. -/
theorem classical_leftDerived_computes_iff_minus
    (X : KMinus A) :
    classicalLeftDerivedComputes F
        ((boundedAboveHomotopyProperty A).ι.obj X) ↔
      classicalLeftDerivedMinusComputes F X := by
  sorry

end Irrelevant

end Formalization.Books.Derived.Unit15
