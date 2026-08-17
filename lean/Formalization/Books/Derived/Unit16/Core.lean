import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit14.DerivedFunctors
import Formalization.Books.Homology.Unit12.CohomologicalDeltaFunctors

/-!
# Derived Categories, Chapter 16: higher derived functors

This file records the source-facing interfaces used in the chapter.  The
localization and cohomology functors are Mathlib's canonical ones; the
properties which require the comparison theorems are left as theorem
interfaces in the companion file.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Homology.Unit12
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u w' v' u'

namespace Formalization.Books.Derived.Unit16

/-! ## The bounded derived-functor interfaces -/

/-- The functor on `K⁺` obtained from an additive functor before deriving it. -/
noncomputable def rightDerivedInputFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    KPlus A ⥤ DPlus B :=
  additiveHomotopyPlusFunctor F ⋙ plusDerivedLocalizationFunctor B

/-- The functor on `K⁻` obtained from an additive functor before deriving it. -/
noncomputable def leftDerivedInputFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    KMinus A ⥤ DMinus B :=
  additiveHomotopyMinusFunctor F ⋙ minusDerivedLocalizationFunctor B

/-- The `i`-th higher right derived functor, `Hⁱ ∘ RF ∘ [0]`. -/
noncomputable def higherRightDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] (RF : DPlus A ⥤ DPlus B) (i : ℤ) :
    A ⥤ B :=
  HomotopyCategory.Plus.singleFunctor A 0 ⋙
    plusDerivedLocalizationFunctor A ⋙ RF ⋙
    DerivedCategory.Plus.homologyFunctor B i

/-- The degree-zero cohomology of the image of the concentrated complex
  before deriving.  This is canonically isomorphic to `F`. -/
noncomputable def rightDerivedSourceCohomology
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] : A ⥤ B :=
  HomotopyCategory.Plus.singleFunctor A 0 ⋙
    rightDerivedInputFunctor F ⋙
    DerivedCategory.Plus.homologyFunctor B 0

/-- A chosen everywhere-defined right derived functor on `D⁺`. -/
structure RightDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] where
  /-- The derived functor on the bounded-below derived category. -/
  functor : DPlus A ⥤ DPlus B
  /-- The universal comparison map from the functor on `K⁺`. -/
  unit : rightDerivedInputFunctor F ⟶
    plusDerivedLocalizationFunctor A ⋙ functor
  /-- The comparison is a right derived functor in the localization sense. -/
  isRightDerived :
    letI : (plusDerivedLocalizationFunctor A).IsLocalization
        (quasiIsoPlusProperty A) := plusDerivedLocalizationFunctor_is_localization A
    functor.IsRightDerivedFunctor unit (quasiIsoPlusProperty A)
  /-- The functor is exact as a triangulated functor. -/
  exact : Nonempty (ExactTriangulatedFunctorData functor)
  /-- The canonical degree-zero comparison is obtained from `unit` after
  applying degree-zero cohomology. -/
  zeroSourceIso : F ≅ rightDerivedSourceCohomology F

/-- The canonical comparison `F ⟶ R⁰F` attached to a right derived functor. -/
noncomputable def RightDerivedFunctorData.zeroComparison
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) :
    F ⟶ higherRightDerivedFunctor F R.functor 0 :=
  R.zeroSourceIso.hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor A 0) R.unit)
      (DerivedCategory.Plus.homologyFunctor B 0)

/-- Cohomology of a bounded-below derived object after applying `RF`. -/
noncomputable def rightDerivedCohomology
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (RF : DPlus A ⥤ DPlus B) (K : DPlus A) (i : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B i).obj (RF.obj K)

/-- The canonical `≤ a` truncation in `D⁺(𝒜)`. -/
noncomputable def derivedPlusTruncLE
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (K : DPlus A) (a : ℤ) : DPlus A :=
  (DerivedCategory.Plus.TStructure.t.truncLE a).obj K

/-! ## Acyclic objects and complexes -/

/-- An object is right `F`-acyclic when its canonical concentrated complex
  comparison is an isomorphism in `D⁺`. -/
def RightAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) (X : A) : Prop :=
  IsIso (R.unit.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X))

/-- The bounded-above homotopy object represented by a bounded-above complex. -/
theorem minusHomotopyQuotient_mem
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (K : CompMinus A) :
    boundedAboveHomotopyProperty A
      (((boundedAboveProperty A).ι ⋙
        HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) := by
  sorry

/-- The canonical functor `Comp⁻(𝒜) ⥤ K⁻(𝒜)`. -/
noncomputable def minusHomotopyQuotient
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    CompMinus A ⥤ KMinus A :=
  ObjectProperty.lift (boundedAboveHomotopyProperty A)
    ((boundedAboveProperty A).ι ⋙
      HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (minusHomotopyQuotient_mem)

/-- The concentrated bounded-above homotopy functor used for left derived
  functors. -/
theorem singleFunctor_mem_KMinus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (X : A) (n : ℤ) :
    boundedAboveHomotopyProperty A
      ((HomotopyCategory.singleFunctor A n).obj X) := by
  sorry

noncomputable def singleMinusFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (n : ℤ) : A ⥤ KMinus A :=
  ObjectProperty.lift (boundedAboveHomotopyProperty A)
    (HomotopyCategory.singleFunctor A n)
    (fun X => singleFunctor_mem_KMinus X n)

/-- A chosen everywhere-defined left derived functor on `D⁻`. -/
structure LeftDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] where
  functor : DMinus A ⥤ DMinus B
  /-- The universal comparison map `LF` receives from `F`. -/
  counit : minusDerivedLocalizationFunctor A ⋙ functor ⟶
    leftDerivedInputFunctor F
  isLeftDerived :
    letI : (minusDerivedLocalizationFunctor A).IsLocalization
        (quasiIsoMinusProperty A) := minusDerivedLocalizationFunctor_is_localization A
    functor.IsLeftDerivedFunctor counit (quasiIsoMinusProperty A)
  exact : Nonempty (ExactTriangulatedFunctorData functor)

/-- An object is left `F`-acyclic when its concentrated comparison is an
  isomorphism in `D⁻`. -/
def LeftAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (L : LeftDerivedFunctorData F) (X : A) : Prop :=
  IsIso (L.counit.app ((singleMinusFunctor (A := A) 0).obj X))

/-- A bounded-below complex computes the right derived functor when the
  canonical comparison from its localization is an isomorphism. -/
def ComputesRightDerivedComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (K : CompPlus A) : Prop :=
  IsIso (R.unit.app ((HomotopyCategory.Plus.quotient A).obj K))

/-- A bounded-above complex computes the left derived functor when its
  canonical comparison is an isomorphism. -/
def ComputesLeftDerivedComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (L : LeftDerivedFunctorData F)
    (K : CompMinus A) : Prop :=
  IsIso (L.counit.app ((minusHomotopyQuotient (A := A)).obj K))

def AllTermsRightAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (K : CompPlus A) : Prop :=
  ∀ n : ℤ, RightAcyclic R (K.1.X n)

def AllTermsLeftAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (L : LeftDerivedFunctorData F)
    (K : CompMinus A) : Prop :=
  ∀ n : ℤ, LeftAcyclic L (K.1.X n)

def InjectsIntoRightAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) : Prop :=
  ∀ X : A, ∃ (I : A) (u : X ⟶ I), Mono u ∧ RightAcyclic R I

def QuotientOfLeftAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (L : LeftDerivedFunctorData F) : Prop :=
  ∀ X : A, ∃ (P : A) (p : P ⟶ X), Epi p ∧ LeftAcyclic L P

/-! ## The delta-functor and the unbounded interface -/

/-- The bounded-below family of higher derived functors together with its
  canonical connecting morphisms.  The family is fixed to the actual
  `RⁿF`, so the existing delta-functor API can be reused without weakening
  the source's assertion to a merely degreewise-isomorphic family. -/
structure RightDerivedDeltaFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F) where
  additive : ∀ n : ℕ,
    (higherRightDerivedFunctor F R.functor (n : ℤ)).Additive
  delta : ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
    (higherRightDerivedFunctor F R.functor (n : ℤ)).obj S.X₃ ⟶
      (higherRightDerivedFunctor F R.functor (n + 1 : ℕ)).obj S.X₁
  exact : ∀ (S : ShortComplex A) (hS : S.ShortExact),
    LongExactness
      (fun n : ℕ => higherRightDerivedFunctor F R.functor (n : ℤ))
      delta S hS
  natural : ∀ {S₁ S₂ : ShortComplex A}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ),
    delta S₁ h₁ n ≫
        (higherRightDerivedFunctor F R.functor (n + 1 : ℕ)).map φ.τ₁ =
      (higherRightDerivedFunctor F R.functor (n : ℤ)).map φ.τ₃ ≫
        delta S₂ h₂ n

/-- The cohomological delta-functor represented by the canonical data. -/
noncomputable def rightDerivedDeltaFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive] (R : RightDerivedFunctorData F)
    (Δ : RightDerivedDeltaFunctorData R) : CohomologicalDeltaFunctor A B :=
  { functor := fun n : ℕ => higherRightDerivedFunctor F R.functor (n : ℤ)
    additive := Δ.additive
    delta := Δ.delta
    exact := Δ.exact
    natural := Δ.natural }

/-- A chosen everywhere-defined right derived functor on the unbounded
  derived category. -/
structure UnboundedRightDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory B
  unit :
    additiveHomotopyFunctor F ⋙ DerivedCategory.Qh (C := B) ⟶
      DerivedCategory.Qh (C := A) ⋙ functor
  isRightDerived : functor.IsRightDerivedFunctor unit (quasiIsoHomotopyProperty A)
  exact : Nonempty (ExactTriangulatedFunctorData functor)

noncomputable def unboundedHigherRightDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B) (i : ℤ) : A ⥤ B :=
  DerivedCategory.singleFunctor A 0 ⋙ RF ⋙
    DerivedCategory.homologyFunctor B i

def ComputesUnboundedRightDerivedComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    {F : A ⥤ B} [F.Additive]
    (R : UnboundedRightDerivedFunctorData F) (K : BookComplex A) : Prop :=
  IsIso (R.unit.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))

end Formalization.Books.Derived.Unit16
