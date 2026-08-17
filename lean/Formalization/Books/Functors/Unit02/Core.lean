import Formalization.Books.Algebra.Unit90.CoherentRings
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Categories.Unit26.CategoricallyCompact
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Functors on module categories: common interfaces

This file records the category-theoretic interfaces used by the statements in the
chapter.  In particular, finitely presented modules are represented by the full
subcategory cut out by `Module.FinitePresentation`, and the pair `(K, κ)` in the
module-category classification is represented by `ModuleActionObject`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit90
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit03

universe u v u' v' w

namespace Formalization.Books.Functors.Unit02

/-! ## Finitely presented modules -/

def finitelyPresentedModuleProperty (A : Type u) [Ring A] :
    ObjectProperty (ModuleCat.{v} A) :=
  fun M => Module.FinitePresentation A (M : Type v)

abbrev FinitelyPresentedModuleCat (A : Type u) [Ring A] :=
  (finitelyPresentedModuleProperty A).FullSubcategory

instance finitelyPresentedModuleCat_hasFiniteColimits
    (A : Type u) [Ring A] :
    HasFiniteColimits (FinitelyPresentedModuleCat A) := by
  sorry

theorem finitelyPresentedModuleCat_hasFiniteLimits_of_coherent
    (A : Type u) [CommRing A] (hA : IsCoherentRing A) :
    HasFiniteLimits (FinitelyPresentedModuleCat A) := by
  sorry

/-! ## Filtered colimits, direct sums, and finite limits/colimits -/

instance additiveCategory_hasCoproducts_of_hasFilteredColimits
    (B : Type u') [Category.{v'} B] [AdditiveCategory B]
    [HasFilteredColimitsOfSize.{w, w} B] :
    HasCoproducts.{w} B :=
  hasCoproducts_of_finite_and_filtered

def PreservesArbitraryDirectSums
    {C : Type u} [Category.{v} C]
    {B : Type u'} [Category.{v'} B]
    [HasCoproducts.{w} C] [HasCoproducts.{w} B]
    (F : C ⥤ B) : Prop :=
  ∀ (J : Type w) (X : J → C), IsIso (sigmaComparison F X)

theorem hasFiniteLimits_of_additive_of_hasKernels
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasKernels B] :
    HasFiniteLimits B := by
  let hEq : HasEqualizers B := Preadditive.hasEqualizers_of_hasKernels
  exact @hasFiniteLimits_of_hasEqualizers_and_finite_products B _ _ hEq

theorem hasFiniteColimits_of_additive_of_hasCokernels
    (B : Type u') [Category.{v'} B] [AdditiveCategory B] [HasCokernels B] :
    HasFiniteColimits B := by
  let hCoEq : HasCoequalizers B := Preadditive.hasCoequalizers_of_hasCokernels
  exact @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts B _ _ hCoEq

def filteredKernelComparison
    (B : Type u') [Category.{v'} B] [HasZeroMorphisms B] [HasKernels B]
    [HasFilteredColimitsOfSize.{w, w} B]
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Arrow B) :
    colimit (D ⋙ (ker (C := B))) ⟶ kernel (colimit D).hom := by
  let c : Cocone (D ⋙ (ker (C := B))) :=
    { pt := (colimit D).left
      ι :=
        { app := fun i =>
            kernel.ι ((D.obj i).hom) ≫ (colimit.ι D i).left
          naturality := by sorry } }
  exact kernel.lift _ (colimit.desc (D ⋙ (ker (C := B))) c) (by sorry)

def FilteredColimitsCommuteWithKernels
    (B : Type u') [Category.{v'} B]
    [HasFilteredColimitsOfSize.{w, w} B] [HasZeroMorphisms B] [HasKernels B] : Prop :=
  ∀ {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Arrow B),
    IsIso (filteredKernelComparison B D)

/-! ## The category of pairs `(K, κ)` -/

structure ModuleActionObject (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B] [Preadditive B] where
  carrier : B
  action : A →+* End carrier

namespace ModuleActionObject

structure Hom {A : Type u} [Ring A]
    {B : Type u'} [Category.{v'} B] [Preadditive B]
    (X Y : ModuleActionObject A B) where
  hom : X.carrier ⟶ Y.carrier
  comm : ∀ a : A, X.action a ≫ hom = hom ≫ Y.action a

@[ext]
theorem hom_ext {A : Type u} [Ring A]
    {B : Type u'} [Category.{v'} B] [Preadditive B]
    {X Y : ModuleActionObject A B} {f g : Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

end ModuleActionObject

abbrev ModuleActionCat (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B] [Preadditive B] :=
  ModuleActionObject A B

instance moduleActionCat_category (A : Type u) [Ring A]
    (B : Type u') [Category.{v'} B] [Preadditive B] :
    Category (ModuleActionCat A B) where
  Hom X Y := ModuleActionObject.Hom X Y
  id X :=
    { hom := 𝟙 X.carrier
      comm := by simp }
  comp := by
    intro X Y Z f g
    refine
      { hom := f.hom ≫ g.hom
        comm := ?_ }
    intro a
    calc
      X.action a ≫ (f.hom ≫ g.hom) =
          (X.action a ≫ f.hom) ≫ g.hom := by rw [Category.assoc]
      _ =
          (f.hom ≫ Y.action a) ≫ g.hom := by rw [f.comm]
      _ = f.hom ≫ (Y.action a ≫ g.hom) := by simp [Category.assoc]
      _ = f.hom ≫ (g.hom ≫ Z.action a) := by rw [g.comm]
      _ = (f.hom ≫ g.hom) ≫ Z.action a := by simp [Category.assoc]
  id_comp := by
    intro X Y f
    apply ModuleActionObject.hom_ext
    simp
  comp_id := by
    intro X Y f
    apply ModuleActionObject.hom_ext
    simp
  assoc := by
    intro W X Y Z f g h
    apply ModuleActionObject.hom_ext
    simp [Category.assoc]

/-! ## Full subcategories of exact functors -/

def rightExactFunctorProperty
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    {B : Type u'} [Category.{v'} B] :
    ObjectProperty (C ⥤ B) :=
  fun F => IsRightExact F

abbrev RightExactFunctorCat
    (C : Type u) [Category.{v} C] [HasFiniteColimits C]
    (B : Type u') [Category.{v'} B] :=
  (rightExactFunctorProperty (C := C) (B := B)).FullSubcategory

def rightExactAndDirectSumsFunctorProperty
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    {B : Type u'} [Category.{v'} B]
    [HasCoproducts.{w} C] [HasCoproducts.{w} B] :
    ObjectProperty (C ⥤ B) :=
  fun F => IsRightExact F ∧ PreservesArbitraryDirectSums F

abbrev RightExactDirectSumsFunctorCat
    (C : Type u) [Category.{v} C] [HasFiniteColimits C]
    (B : Type u') [Category.{v'} B]
    [HasCoproducts.{w} C] [HasCoproducts.{w} B] :=
  (rightExactAndDirectSumsFunctorProperty (C := C) (B := B)).FullSubcategory

end Formalization.Books.Functors.Unit02
