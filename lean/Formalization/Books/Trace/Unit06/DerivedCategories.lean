import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Formalization.Books.Homology.Unit07.AdditiveFunctors

/-!
# The Trace Formula, Chapter 6: derived categories

The source introduces complexes, homotopy categories, derived categories,
bounded variants, and total derived functors.  The categorical constructions
are Mathlib's canonical ones; this file supplies the Trace-book names and the
source-facing theorem interfaces which are not already exposed by those APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit07
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u w' v' u'

namespace Formalization.Books.Trace.Unit06

/-! ## Complexes, homotopy categories, and derived categories -/

/- The source's `Comp(𝒜)` and `K(𝒜)` are the canonical cochain-complex and
   homotopy-category constructions. -/
abbrev Comp (A : Type u) [Category.{v} A] [Preadditive A] :=
  CochainComplex A ℤ

abbrev K (A : Type u) [Category.{v} A] [Preadditive A] :=
  HomotopyCategory A (ComplexShape.up ℤ)

abbrev D (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :=
  DerivedCategory A

/- The source deliberately suppresses the set-theoretic size qualifications;
   `HasDerivedCategory` records the corresponding localization interface. -/

/- Bounded complexes are represented by the standard support predicates and
   full-subcategory constructions. -/
abbrev IsBoundedBelow
    {A : Type u} [Category.{v} A] [AdditiveCategory A] (K : Comp A) : Prop :=
  CochainComplex.plus A K

def IsBoundedAbove
    {A : Type u} [Category.{v} A] [AdditiveCategory A] (K : Comp A) : Prop :=
  ∃ n : ℤ, K.IsStrictlyLE n

def IsBounded
    {A : Type u} [Category.{v} A] [AdditiveCategory A] (K : Comp A) : Prop :=
  ∃ p q : ℤ, K.IsStrictlyGE p ∧ K.IsStrictlyLE q

abbrev boundedBelowProperty
    (A : Type u) [Category.{v} A] [AdditiveCategory A] :
    ObjectProperty (Comp A) :=
  CochainComplex.plus A

def boundedAboveProperty
    (A : Type u) [Category.{v} A] [AdditiveCategory A] :
    ObjectProperty (Comp A) :=
  fun K => IsBoundedAbove K

def boundedProperty
    (A : Type u) [Category.{v} A] [AdditiveCategory A] :
    ObjectProperty (Comp A) :=
  fun K => IsBounded K

abbrev CompPlus (A : Type u) [Category.{v} A] [AdditiveCategory A] :=
  CochainComplex.Plus A

abbrev CompMinus (A : Type u) [Category.{v} A] [AdditiveCategory A] :=
  (boundedAboveProperty A).FullSubcategory

abbrev CompBounded (A : Type u) [Category.{v} A] [AdditiveCategory A] :=
  (boundedProperty A).FullSubcategory

abbrev KPlus (A : Type u) [Category.{v} A] [AdditiveCategory A] :=
  HomotopyCategory.Plus A

abbrev boundedBelowHomotopyProperty
    (A : Type u) [Category.{v} A] [AdditiveCategory A] :
    ObjectProperty (K A) :=
  HomotopyCategory.plus A

def boundedAboveHomotopyProperty
    (A : Type u) [Category.{v} A] [AdditiveCategory A] :
    ObjectProperty (K A) :=
  (boundedAboveProperty A).strictMap (HomotopyCategory.quotient A (.up ℤ))

def boundedHomotopyProperty
    (A : Type u) [Category.{v} A] [AdditiveCategory A] :
    ObjectProperty (K A) :=
  (boundedProperty A).strictMap (HomotopyCategory.quotient A (.up ℤ))

abbrev KMinus (A : Type u) [Category.{v} A] [AdditiveCategory A] :=
  (boundedAboveHomotopyProperty A).FullSubcategory

abbrev KBounded (A : Type u) [Category.{v} A] [AdditiveCategory A] :=
  (boundedHomotopyProperty A).FullSubcategory

abbrev DPlus (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :=
  DerivedCategory.Plus A

abbrev DMinus (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :=
  DerivedCategory.Minus A

abbrev DBounded (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :=
  DerivedCategory.Bounded A

/- The complex category is abelian when its coefficient category is abelian. -/
instance complexCategory_abelian
    (A : Type u) [Category.{v} A] [Abelian A] :
    Abelian (Comp A) := by infer_instance

noncomputable instance abelian_additiveCategory
    (A : Type u) [Category.{v} A] [Abelian A] :
    AdditiveCategory A :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

/- The source's warning that `K(𝒜)` is not abelian is a general warning, not
   a claim for every degenerate abelian category. -/
theorem homotopyCategory_not_abelian_in_general :
    ∃ (A : Type u) (_ : Category.{v} A) (_ : Abelian A),
      ¬ Nonempty (Abelian (K A)) := by
  sorry

/- The source's additive-category remark is already witnessed by the standard
   preadditive/additive instances on complexes and homotopy categories. -/
instance complexCategory_additive
    (A : Type u) [Category.{v} A] [Abelian A] :
    AdditiveCategory (Comp A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

instance homotopyCategory_additive
    (A : Type u) [Category.{v} A] [Abelian A] :
    AdditiveCategory (K A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

theorem homotopyCategory_triangulated
    (A : Type u) [Category.{v} A] [Abelian A] :
    IsTriangulated (K A) := by
  infer_instance

theorem derivedCategory_triangulated
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    IsTriangulated (D A) := by
  infer_instance

/-! ## Homology on the three levels -/

noncomputable abbrev complexHomologyFunctor
    (A : Type u) [Category.{v} A] [Abelian A] (i : ℤ) :
    Comp A ⥤ A :=
  HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i

noncomputable abbrev homotopyHomologyFunctor
    (A : Type u) [Category.{v} A] [Abelian A] (i : ℤ) :
    K A ⥤ A :=
  HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i

noncomputable abbrev derivedHomologyFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (i : ℤ) :
    D A ⥤ A :=
  DerivedCategory.homologyFunctor A i

noncomputable def homologyFunctorFactorsThroughHomotopy
    (A : Type u) [Category.{v} A] [Abelian A] (i : ℤ) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙
        homotopyHomologyFunctor A i ≅ complexHomologyFunctor A i :=
  HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i

noncomputable def homologyFunctorFactorsThroughDerived
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (i : ℤ) :
    (DerivedCategory.Qh (C := A)) ⋙ derivedHomologyFunctor A i ≅
      homotopyHomologyFunctor A i :=
  DerivedCategory.homologyFunctorFactorsh A i

/-! ## Boundedness detected by homology -/

def DerivedHomologyVanishesBelow
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : D A) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n → IsZero ((derivedHomologyFunctor A i).obj E)

def DerivedHomologyVanishesAbove
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : D A) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero ((derivedHomologyFunctor A i).obj E)

def DerivedHomologyVanishesBounded
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : D A) : Prop :=
  DerivedHomologyVanishesBelow A E ∧ DerivedHomologyVanishesAbove A E

abbrev DPlusProperty
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : ObjectProperty (D A) :=
  (DerivedCategory.TStructure.t (C := A)).plus

abbrev DMinusProperty
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : ObjectProperty (D A) :=
  (DerivedCategory.TStructure.t (C := A)).minus

abbrev DBoundedProperty
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : ObjectProperty (D A) :=
  (DerivedCategory.TStructure.t (C := A)).bounded

theorem mem_DPlus_iff_homology_vanishes_below
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : D A) :
    DPlusProperty A E ↔ DerivedHomologyVanishesBelow A E := by
  sorry

theorem mem_DMinus_iff_homology_vanishes_above
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : D A) :
    DMinusProperty A E ↔ DerivedHomologyVanishesAbove A E := by
  sorry

theorem mem_DBounded_iff_homology_vanishes_bounded
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : D A) :
    DBoundedProperty A E ↔ DerivedHomologyVanishesBounded A E := by
  sorry

/-! ## Morphisms in the derived category -/

theorem derivedHom_to_boundedBelowInjective_bijective
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (K : K A) (I : CompPlus A)
    (hI : ∀ n : ℤ, Injective (I.obj.X n)) :
    Function.Bijective
      ((DerivedCategory.Qh (C := A)).map :
        (K ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I.obj) →
          ((DerivedCategory.Qh (C := A)).obj K ⟶
            (DerivedCategory.Qh (C := A)).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I.obj))) := by
  sorry

theorem derivedHom_from_boundedAboveProjective_bijective
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : CompMinus A) (K : K A)
    (hP : ∀ n : ℤ, Projective (P.obj.X n)) :
    Function.Bijective
      ((DerivedCategory.Qh (C := A)).map :
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P.obj ⟶ K) →
          ((DerivedCategory.Qh (C := A)).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P.obj) ⟶
            (DerivedCategory.Qh (C := A)).obj K)) := by
  sorry

theorem derivedPlus_equiv_injectiveHomotopy
    (A : Type u) [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A] :
    Nonempty (DPlus A ≌ HomotopyCategory.Plus (InjectiveObject A)) := by
  sorry

theorem derivedMinus_equiv_projectiveHomotopy
    (A : Type u) [Category.{v} A] [Abelian A]
    [EnoughProjectives A] [HasDerivedCategory.{w} A]
    {P : Type u} [Category.{v} P] [AdditiveCategory P]
    (ι : P ⥤ A) [ι.Full] [ι.Faithful]
    (hP : ∀ X : P, Projective (ι.obj X)) :
    Nonempty (DMinus A ≌ KMinus P) := by
  sorry

/-! ## Total derived functors -/

noncomputable def totalRightDerivedInputFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A] (F : A ⥤ B) (hF : IsLeftExact F) :
    KPlus A ⥤ DPlus B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

noncomputable def totalRightDerivedFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A] (F : A ⥤ B) (hF : IsLeftExact F) :
    DPlus A ⥤ DPlus B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact F.rightDerivedFunctorPlus

noncomputable def totalRightDerivedUnit
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A] (F : A ⥤ B) (hF : IsLeftExact F) :
    totalRightDerivedInputFunctor A B F hF ⟶
      (DerivedCategory.Plus.Qh (C := A)) ⋙ totalRightDerivedFunctor A B F hF :=
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  F.rightDerivedFunctorPlusUnit

/- The left-derived construction is recorded by the commutative diagram in
   the source.  The right vertical functor is the canonical localization
   restricted to bounded-above objects; preservation of boundedness and the
   comparison isomorphism are the theorem interfaces below. -/
noncomputable def minusDerivedLocalizationFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    KMinus A ⥤ DMinus A :=
  ObjectProperty.lift (DMinusProperty A)
    (ObjectProperty.ι (boundedAboveHomotopyProperty A) ⋙
      (DerivedCategory.Qh (C := A)))
    (fun _ => by sorry)

noncomputable def mapKMinus
    {P : Type u} [Category.{v} P] [AdditiveCategory P]
    {B : Type u'} [Category.{v'} B] [AdditiveCategory B]
    (G : P ⥤ B) [G.Additive] :
    KMinus P ⥤ KMinus B :=
  ObjectProperty.lift (boundedAboveHomotopyProperty B)
    (ObjectProperty.ι (boundedAboveHomotopyProperty P) ⋙
      G.mapHomotopyCategory (ComplexShape.up ℤ))
    (fun _ => by sorry)

structure LeftDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (G : A ⥤ B) [G.Additive]
    {P : Type u} [Category.{v} P] [AdditiveCategory P]
    (ι : P ⥤ A) [ι.Full] [ι.Faithful] [ι.Additive]
    (e : DMinus A ≌ KMinus P) where
  functor : DMinus A ⥤ DMinus B
  comparison :
    mapKMinus (ι ⋙ G) ⋙ minusDerivedLocalizationFunctor B ≅
      e.inverse ⋙ functor

theorem totalLeftDerivedData_exists
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A] (G : A ⥤ B) [G.Additive] (hG : IsRightExact G)
    {P : Type u} [Category.{v} P] [AdditiveCategory P]
    (ι : P ⥤ A) [ι.Full] [ι.Faithful] [ι.Additive]
    (hP : ∀ X : P, Projective (ι.obj X))
    (e : DMinus A ≌ KMinus P) :
    Nonempty (LeftDerivedFunctorData G ι e) := by
  sorry

noncomputable def totalLeftDerivedFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughProjectives A] (G : A ⥤ B) (hG : IsRightExact G)
    {P : Type u} [Category.{v} P] [AdditiveCategory P]
    (ι : P ⥤ A) [ι.Full] [ι.Faithful] [ι.Additive]
    (hP : ∀ X : P, Projective (ι.obj X))
    (e : DMinus A ≌ KMinus P) :
    DMinus A ⥤ DMinus B := by
  letI : G.Additive := left_or_right_exact_additive G (Or.inr hG)
  exact (Classical.choice
    (totalLeftDerivedData_exists A B G hG ι hP e)).functor

/-! ## The cohomology compatibility of total derived functors -/

noncomputable abbrev rightDerivedDegree
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A] (F : A ⥤ B) (hF : IsLeftExact F) (i : ℤ) :
    DPlus A ⥤ B :=
  totalRightDerivedFunctor A B F hF ⋙ DerivedCategory.Plus.homologyFunctor B i

theorem rightDerivedDegree_is_cohomology_of_total_functor
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A] (F : A ⥤ B) (hF : IsLeftExact F) (i : ℤ) :
    rightDerivedDegree A B F hF i =
      totalRightDerivedFunctor A B F hF ⋙ DerivedCategory.Plus.homologyFunctor B i :=
  rfl

end Formalization.Books.Trace.Unit06
