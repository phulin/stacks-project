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
  change HasFiniteColimits ((finitelyPresentedModuleProperty A).FullSubcategory)
  let P := finitelyPresentedModuleProperty.{u, u_1} A
  letI : P.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro X Y e hX
      letI : Module.FinitePresentation A (X : Type _) := hX
      change Module.FinitePresentation A (Y : Type _)
      exact Module.FinitePresentation.of_equiv e.toLinearEquiv
  }
  letI : P.ContainsZero := {
    exists_zero := by
      refine ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _, ?_⟩
      · change Module.FinitePresentation A PUnit
        exact inferInstance
  }
  letI : P.IsClosedUnderBinaryCoproducts := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    let X₁ := F.obj ⟨WalkingPair.left⟩
    let X₂ := F.obj ⟨WalkingPair.right⟩
    letI : Module.FinitePresentation A (X₁ : Type u_1) := hF _
    letI : Module.FinitePresentation A (X₂ : Type u_1) := hF _
    have hprod : P (ModuleCat.of A (X₁ × X₂)) := by
      change Module.FinitePresentation A (X₁ × X₂)
      exact inferInstance
    have eprod : ModuleCat.of A (X₁ × X₂) ≅ colimit F :=
      (ModuleCat.biprodIsoProd X₁ X₂).symm.trans
        (IsColimit.coconePointUniqueUpToIso
        (F := pair X₁ X₂)
        (s := (BinaryBiproduct.bicone X₁ X₂).toCocone)
        (t := ((Cocone.precompose (diagramIsoPair F).inv).obj (colimit.cocone F)))
        (BinaryBiproduct.isColimit X₁ X₂)
        ((IsColimit.precomposeHomEquiv (diagramIsoPair F).symm (colimit.cocone F)).2
          (colimit.isColimit F)))
    exact P.prop_of_iso eprod hprod
  letI : P.IsClosedUnderFiniteCoproducts :=
    ObjectProperty.IsClosedUnderFiniteCoproducts.mk'
  letI : P.IsClosedUnderCokernels := by
    refine { cokernels_le := ?_ }
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    letI : Module.FinitePresentation A _ := hX
    letI : Module.FinitePresentation A _ := hY
    have hrange : Module.Finite A (LinearMap.range f.hom) := inferInstance
    letI : Module.Finite A (LinearMap.range f.hom) := hrange
    have hquot :=
      Module.finitePresentation_of_surjective (LinearMap.range f.hom).mkQ
        (Submodule.mkQ_surjective _) (by
          simpa only [Submodule.ker_mkQ] using (Module.Finite.iff_fg.mp hrange))
    have e : ModuleCat.of A _ ≅ k.pt :=
      (ModuleCat.cokernelIsoRangeQuotient f).symm.trans
        (IsColimit.coconePointUniqueUpToIso
          (colimit.isColimit (parallelPair f 0)) hk)
    exact P.prop_of_iso e hquot
  let hCoEq : HasCoequalizers P.FullSubcategory :=
    Preadditive.hasCoequalizers_of_hasCokernels
  exact @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
    P.FullSubcategory _ _ hCoEq

theorem finitelyPresentedModuleCat_hasFiniteLimits_of_coherent
    (A : Type u) [CommRing A] (hA : IsCoherentRing A) :
    HasFiniteLimits (FinitelyPresentedModuleCat A) := by
  change HasFiniteLimits ((finitelyPresentedModuleProperty.{u, u_1} A).FullSubcategory)
  let P := finitelyPresentedModuleProperty.{u, u_1} A
  letI : P.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro X Y e hX
      letI : Module.FinitePresentation A (X : Type u_1) := hX
      change Module.FinitePresentation A (Y : Type u_1)
      exact Module.FinitePresentation.of_equiv e.toLinearEquiv
  }
  letI : P.ContainsZero := {
    exists_zero := by
      refine ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _, ?_⟩
      change Module.FinitePresentation A PUnit
      exact inferInstance
  }
  letI : P.IsClosedUnderBinaryProducts := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    let X₁ := F.obj ⟨WalkingPair.left⟩
    let X₂ := F.obj ⟨WalkingPair.right⟩
    letI : Module.FinitePresentation A (X₁ : Type u_1) := hF _
    letI : Module.FinitePresentation A (X₂ : Type u_1) := hF _
    have hprod : P (ModuleCat.of A (X₁ × X₂)) := by
      change Module.FinitePresentation A (X₁ × X₂)
      exact inferInstance
    have eprod : ModuleCat.of A (X₁ × X₂) ≅ limit F :=
      IsLimit.conePointUniqueUpToIso
        (F := pair X₁ X₂)
        (s := (ModuleCat.binaryProductLimitCone X₁ X₂).cone)
        (t := ((Cone.postcompose (diagramIsoPair F).hom).obj (limit.cone F)))
        (ModuleCat.binaryProductLimitCone X₁ X₂).isLimit
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair F) (limit.cone F)).2
          (limit.isLimit F))
    exact P.prop_of_iso eprod hprod
  letI : P.IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  letI : P.IsClosedUnderKernels := by
    refine { kernels_le := ?_ }
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    have hkercoh :=
      (coherent_kernel_cokernel_of_coherent f
        ((coherentModule_iff_finitePresentation hA _).mpr hX)
        ((coherentModule_iff_finitePresentation hA _).mpr hY)).1
    have hkerfp : Module.FinitePresentation A (LinearMap.ker f.hom) :=
      (coherentModule_iff_finitePresentation hA
        (ModuleCat.of A (LinearMap.ker f.hom))).mp hkercoh
    have hker : P (ModuleCat.of A (LinearMap.ker f.hom)) := by
      change Module.FinitePresentation A (LinearMap.ker f.hom)
      exact hkerfp
    have e : ModuleCat.of A (LinearMap.ker f.hom) ≅ k.pt :=
      (ModuleCat.kernelIsoKer f).symm.trans
        (IsLimit.conePointUniqueUpToIso
          (limit.isLimit (parallelPair f 0)) hk)
    exact P.prop_of_iso e hker
  let hEq : HasEqualizers P.FullSubcategory :=
    Preadditive.hasEqualizers_of_hasKernels
  exact @hasFiniteLimits_of_hasEqualizers_and_finite_products
    P.FullSubcategory _ _ hEq

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
          naturality := by
            intro i j f
            dsimp only [Functor.comp_map, ker, Functor.const]
            simp only [Category.comp_id]
            change
              (kernel.lift (D.obj j).hom
                (kernel.ι (D.obj i).hom ≫ (D.map f).left) _) ≫
                  kernel.ι (D.obj j).hom ≫ (colimit.ι D j).left =
                kernel.ι (D.obj i).hom ≫ (colimit.ι D i).left
            rw [← Category.assoc, kernel.lift_ι]
            rw [Category.assoc,
              ← congrArg (fun g => g.left) (colimit.w D f)]
            rw [Arrow.comp_left] } }
  exact kernel.lift _ (colimit.desc (D ⋙ (ker (C := B))) c) (by
    apply colimit.hom_ext
    intro i
    simp only [colimit.ι_desc_assoc, comp_zero]
    dsimp [c, ker, Functor.comp]
    change
      (kernel.ι (D.obj i).hom ≫ (colimit.ι D i).left) ≫ (colimit D).hom =
        (0 : kernel (D.obj i).hom ⟶ (colimit D).right)
    rw [Category.assoc, Arrow.Hom.w (colimit.ι D i)]
    simp [Category.assoc])

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
