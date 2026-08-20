import Formalization.Books.Cohomology.Unit20.CupProduct

/-!
# Cohomology of Sheaves, Chapter 20, Section 6: Some properties of K-injective complexes
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Derived.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v

namespace Formalization.Books.Cohomology.Unit20

/-! Open restrictions and extension by zero. -/

structure OpenImmersionData (X : RingedSpace.{v})
    (U : Opens X.carrier) where
  openSpace : RingedSpace.{v}
  immersion : RingedSpaceHom openSpace X
  carrier_identification : Prop
  restriction : Mod X.structureSheaf ⥤ Mod openSpace.structureSheaf
  extensionByZero : Mod openSpace.structureSheaf ⥤ Mod X.structureSheaf
  restriction_additive : restriction.Additive
  extension_additive : extensionByZero.Additive
  restriction_exact : IsExact restriction
  extension_exact : IsExact extensionByZero
  adjunction : extensionByZero ⊣ restriction

theorem exists_openImmersionData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (OpenImmersionData X U) := by
  sorry

noncomputable def openImmersionData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    OpenImmersionData X U :=
  Classical.choice (exists_openImmersionData X U)

noncomputable def restrictionComplexFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleComplex X ⥤ ModuleComplex (openImmersionData X U).openSpace := by
  let D := openImmersionData X U
  letI : D.restriction.Additive := D.restriction_additive
  exact D.restriction.mapHomologicalComplex (ComplexShape.up ℤ)

noncomputable def extensionByZeroComplexFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleComplex (openImmersionData X U).openSpace ⥤ ModuleComplex X := by
  let D := openImmersionData X U
  letI : D.extensionByZero.Additive := D.extension_additive
  exact D.extensionByZero.mapHomologicalComplex (ComplexShape.up ℤ)

theorem restrict_KInjective
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (I : ModuleComplex X) (hI : I.IsKInjective) :
    ((restrictionComplexFunctor X U).obj I).IsKInjective := by
  sorry

structure OpenCohomologyRestrictionData
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : ModuleDerived X) (q : ℤ) where
  left : Type v
  right : Type v
  comparison : left ≃ right

theorem cohomology_of_open_restriction
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : ModuleDerived X) (q : ℤ) :
    Nonempty (OpenCohomologyRestrictionData X U K q) := by
  sorry

structure SheafifiedCohomologyData
    (X : RingedSpace.{v}) (K : ModuleDerived X) (q : ℤ) where
  presheaf : Opens X.carrier ⥤ Type v
  cohomologySheaf : Type v
  sheafification_comparison : presheaf.obj (⊤ : Opens X.carrier) ≃ cohomologySheaf

theorem sheafification_of_cohomology
    (X : RingedSpace.{v}) (K : ModuleDerived X) (q : ℤ) :
    Nonempty (SheafifiedCohomologyData X K q) := by
  sorry

/-! Direct image, Leray, and higher direct images on opens. -/

structure RestrictDirectImageOpenData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (K : ModuleDerived X) where
  U : Opens X.carrier
  inverse_image_identification : U = (Opens.map f.continuous).obj V
  left : Type v
  right : Type v
  comparison : left ≃ right

theorem restrict_directImage_to_open
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (K : ModuleDerived X) :
    Nonempty (RestrictDirectImageOpenData f V K) := by
  sorry

structure LerayUnboundedData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  left : Type v
  right : Type v
  comparison : left ≃ right
  open_comparison : ∀ (V : Opens Y.carrier), Type v

theorem leray_unbounded
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (LerayUnboundedData f) := by
  sorry

structure HigherDirectImageDescription
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : ModuleDerived X) (i : ℤ) where
  higherDirectImage : Type v
  presheafValue : ∀ V : Opens Y.carrier, Type v
  comparison : ∀ V : Opens Y.carrier, presheafValue V ≃ higherDirectImage

theorem describe_higher_direct_images
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : ModuleDerived X) (i : ℤ) :
    Nonempty (HigherDirectImageDescription f K i) := by
  sorry

/-! Forgetting scalars to abelian sheaves. -/

structure ModulesAbelianComparisonData
    (X : RingedSpace.{v}) (K : ModuleDerived X) where
  on_open : ∀ U : Opens X.carrier, Type v
  comparison_on_open : ∀ U : Opens X.carrier, Type v
  open_isomorphism : ∀ U : Opens X.carrier,
    on_open U ≃ comparison_on_open U
  direct_image_comparison : Type v

theorem modules_abelian_unbounded
    (X : RingedSpace.{v}) (K : ModuleDerived X) :
    Nonempty (ModulesAbelianComparisonData X K) := by
  sorry

/-! The derived adjunction for an open immersion. -/

structure ExtensionByZeroRestrictionDerivedData
    (X : RingedSpace.{v}) (U : Opens X.carrier) where
  left : ModuleDerived (openImmersionData X U).openSpace ⥤ ModuleDerived X
  right : ModuleDerived X ⥤ ModuleDerived (openImmersionData X U).openSpace
  adjunction : left ⊣ right

theorem extension_by_zero_is_left_adjoint_to_restriction
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (ExtensionByZeroRestrictionDerivedData X U) := by
  sorry

/-! Flat pushforward preserves K-injectives. -/

theorem pushforwardComplex_additive
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    (Formalization.Books.Sheaves.Unit26.ringedSpaceModulePushforward f).Additive := by
  sorry

noncomputable def pushforwardComplexFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ModuleComplex X ⥤ ModuleComplex Y := by
  letI : (Formalization.Books.Sheaves.Unit26.ringedSpaceModulePushforward f).Additive :=
    pushforwardComplex_additive f
  exact (Formalization.Books.Sheaves.Unit26.ringedSpaceModulePushforward f).mapHomologicalComplex
    (ComplexShape.up ℤ)

theorem pushforward_flat_preserves_KInjective
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hf : FlatRingedSpaceHomData f)
    (I : ModuleComplex X) (hI : I.IsKInjective) :
    ((pushforwardComplexFunctor f).obj I).IsKInjective := by
  sorry

end Formalization.Books.Cohomology.Unit20
