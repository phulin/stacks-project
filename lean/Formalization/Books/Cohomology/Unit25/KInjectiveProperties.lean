import Formalization.Books.Cohomology.Unit07.LocalityOfCohomology
import Formalization.Books.Cohomology.Unit21.UnboundedComplexes
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Cohomology of Sheaves, Chapter 25: Some properties of K-injective complexes

This file follows `books/cohomology.tex`, Section
`section-properties-K-injective`.  The derived-category comparisons are
recorded as categorical isomorphisms; the source's displayed equalities are
canonical identifications rather than definitional equalities.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Cohomology.Unit07
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Cohomology.Unit21
open Formalization.Books.Homology.Unit07
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v

namespace Formalization.Books.Cohomology.Unit25

/-! ## The open-immersion functors and their complexes -/

abbrev ModuleComplex (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleComplex X

abbrev ModuleDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleDerived X

abbrev openSpace (X : RingedSpace.{v}) (U : Opens X.carrier) : RingedSpace.{v} :=
  Formalization.Books.Sheaves.Unit22.ringedOpenSubspace X U

abbrev openInclusion (X : RingedSpace.{v}) (U : Opens X.carrier) :
    RingedSpaceHom (openSpace X U) X :=
  Formalization.Books.Sheaves.Unit22.ringedOpenInclusion X U

noncomputable abbrev openRestrictionModuleFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod X.structureSheaf ⥤ Mod (openSpace X U).structureSheaf :=
  Formalization.Books.Sheaves.Unit22.openModuleRestrictionFunctor X U

noncomputable abbrev openExtensionByZeroModuleFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod (openSpace X U).structureSheaf ⥤ Mod X.structureSheaf :=
  Formalization.Books.Sheaves.Unit22.openModuleExtensionFunctor X U

theorem openRestrictionModuleFunctor_additive
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    (openRestrictionModuleFunctor X U).Additive := by
  sorry

theorem openExtensionByZeroModuleFunctor_additive
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    (openExtensionByZeroModuleFunctor X U).Additive := by
  sorry

theorem openRestrictionModuleFunctor_isExact
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    IsExact (openRestrictionModuleFunctor X U) := by
  sorry

theorem openExtensionByZeroModuleFunctor_isExact
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    IsExact (openExtensionByZeroModuleFunctor X U) := by
  sorry

noncomputable def openRestrictionComplexFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleComplex X ⥤ ModuleComplex (openSpace X U) := by
  letI : (openRestrictionModuleFunctor X U).Additive :=
    openRestrictionModuleFunctor_additive X U
  exact (openRestrictionModuleFunctor X U).mapHomologicalComplex
    (ComplexShape.up ℤ)

noncomputable def openExtensionByZeroComplexFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleComplex (openSpace X U) ⥤ ModuleComplex X := by
  letI : (openExtensionByZeroModuleFunctor X U).Additive :=
    openExtensionByZeroModuleFunctor_additive X U
  exact (openExtensionByZeroModuleFunctor X U).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-! The exact functors induce the derived functors used by the source. -/

structure OpenRestrictionDerivedData
    (X : RingedSpace.{v}) (U : Opens X.carrier) where
  functor : ModuleDerived X ⥤ ModuleDerived (openSpace X U)
  computed_on_complex : ∀ K : ModuleComplex X,
    Nonempty (functor.obj
        (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex X K) ≅
      (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex
        (openSpace X U) ((openRestrictionComplexFunctor X U).obj K)))

theorem exists_openRestrictionDerivedData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (OpenRestrictionDerivedData X U) := by
  sorry

noncomputable def openRestrictionDerivedFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleDerived X ⥤ ModuleDerived (openSpace X U) :=
  (Classical.choice (exists_openRestrictionDerivedData X U)).functor

structure OpenExtensionByZeroDerivedData
    (X : RingedSpace.{v}) (U : Opens X.carrier) where
  functor : ModuleDerived (openSpace X U) ⥤ ModuleDerived X
  computed_on_complex : ∀ K : ModuleComplex (openSpace X U),
    Nonempty (functor.obj
        (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex
          (openSpace X U) K) ≅
      (Formalization.Books.Cohomology.Unit20.derivedObjectOfComplex X
        ((openExtensionByZeroComplexFunctor X U).obj K)))

theorem exists_openExtensionByZeroDerivedData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (OpenExtensionByZeroDerivedData X U) := by
  sorry

noncomputable def openExtensionByZeroDerivedFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleDerived (openSpace X U) ⥤ ModuleDerived X :=
  (Classical.choice (exists_openExtensionByZeroDerivedData X U)).functor

/-! ## Restriction of K-injectives and cohomology on an open -/

theorem restrict_KInjective_to_open
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (I : ModuleComplex X) (hI : I.IsKInjective) :
    ((openRestrictionComplexFunctor X U).obj I).IsKInjective := by
  letI : (openRestrictionModuleFunctor X U).Additive :=
    openRestrictionModuleFunctor_additive X U
  letI : (openExtensionByZeroModuleFunctor X U).Additive :=
    openExtensionByZeroModuleFunctor_additive X U
  exact Formalization.Books.Derived.Unit31.additive_right_adjoint_preserves_isKInjective
    (openRestrictionModuleFunctor X U)
    (openExtensionByZeroModuleFunctor X U)
    (Formalization.Books.Sheaves.Unit22.openModuleExtensionAdjunction X U)
    (openExtensionByZeroModuleFunctor_isExact X U) hI

abbrev openCohomologyGroup
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : ModuleDerived X) (q : ℤ) : AddCommGrpCat.{v} :=
  (forget₂ (ModuleCat (X.structureSheaf.obj.obj (op U))) AddCommGrpCat).obj
    ((Formalization.Books.Cohomology.Unit21.derivedSectionsCohomology
      X U q).obj K)

abbrev restrictedOpenCohomologyGroup
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : ModuleDerived X) (q : ℤ) : AddCommGrpCat.{v} :=
  (forget₂ (ModuleCat
      ((openSpace X U).structureSheaf.obj.obj
        (op (⊤ : Opens (openSpace X U).carrier)))) AddCommGrpCat).obj
    ((Formalization.Books.Cohomology.Unit21.derivedSectionsCohomology
      (openSpace X U) (⊤ : Opens (openSpace X U).carrier) q).obj
      ((openRestrictionDerivedFunctor X U).obj K))

structure OpenCohomologyRestrictionData
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : ModuleDerived X) (q : ℤ) where
  comparison : openCohomologyGroup X U K q ≅
    restrictedOpenCohomologyGroup X U K q

theorem unbounded_cohomology_of_open
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : ModuleDerived X) (q : ℤ) :
    Nonempty (OpenCohomologyRestrictionData X U K q) := by
  sorry

/-! ## Sheafification of the presheaf of cohomology -/

structure SheafificationCohomologyData
    (X : RingedSpace.{v}) (K : ModuleDerived X) (q : ℤ) where
  presheaf : PMod X.structureSheaf.obj
  value_comparison : ∀ U : Opens X.carrier, Nonempty
    (presheaf.obj (op U) ≅
      ((Formalization.Books.Cohomology.Unit21.derivedSectionsCohomology
        X U q).obj K))
  sheafification_comparison : Nonempty
    ((PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)).obj presheaf ≅
      (DerivedCategory.homologyFunctor (Mod X.structureSheaf) q).obj K)

theorem sheafification_of_unbounded_cohomology
    (X : RingedSpace.{v}) (K : ModuleDerived X) (q : ℤ) :
    Nonempty (SheafificationCohomologyData X K q) := by
  sorry

/-! ## Restriction of direct images and the unbounded Leray comparison -/

abbrev inverseImageOpen
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) : Opens X.carrier :=
  (Opens.map f.continuous).obj V

noncomputable abbrev openRestrictionOfMorphism
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    RingedSpaceHom (openSpace X (inverseImageOpen f V))
      (openSpace Y V) :=
  Formalization.Books.Cohomology.Unit07.ringedSpaceOpenRestriction f V

structure RestrictDirectImageOpenData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (K : ModuleDerived X) where
  comparison :
    (openRestrictionDerivedFunctor Y V).obj
        ((Formalization.Books.Cohomology.Unit21.derivedPushforward f).obj K) ≅
      (Formalization.Books.Cohomology.Unit21.derivedPushforward
          (openRestrictionOfMorphism f V)).obj
        ((openRestrictionDerivedFunctor X (inverseImageOpen f V)).obj K)

theorem restrict_directImage_to_open
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (K : ModuleDerived X) :
    Nonempty (RestrictDirectImageOpenData f V K) := by
  sorry

noncomputable def globalScalarMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    RingCat.of (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier))) ⟶
      RingCat.of (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))) := by
  have h := Formalization.Books.Cohomology.Unit07.higherDirectImageScalarMap
    f (⊤ : Opens Y.carrier)
  rw [Opens.map_top] at h
  exact h

theorem globalScalarMap_restrictScalars_isExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    IsExact (ModuleCat.restrictScalars (globalScalarMap f).hom) := by
  sorry

noncomputable def derivedSectionsViewedOverTarget
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ModuleDerived X ⥤
      DerivedCategory (ModuleCat
        (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier)))) := by
  letI : PreservesFiniteLimits
      (ModuleCat.restrictScalars (globalScalarMap f).hom) :=
    globalScalarMap_restrictScalars_isExact f |>.1
  letI : PreservesFiniteColimits
      (ModuleCat.restrictScalars (globalScalarMap f).hom) :=
    globalScalarMap_restrictScalars_isExact f |>.2
  exact Formalization.Books.Cohomology.Unit21.derivedGlobalSections X ⋙
    (ModuleCat.restrictScalars (globalScalarMap f).hom).mapDerivedCategory

noncomputable abbrev openGlobalSections
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleDerived (openSpace X U) ⥤
      DerivedCategory AddCommGrpCat := by
  letI : PreservesFiniteLimits
      (forget₂ (ModuleCat
        ((openSpace X U).structureSheaf.obj.obj
          (op (⊤ : Opens (openSpace X U).carrier)))) AddCommGrpCat) := by
    infer_instance
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat
        ((openSpace X U).structureSheaf.obj.obj
          (op (⊤ : Opens (openSpace X U).carrier)))) AddCommGrpCat) := by
    infer_instance
  exact Formalization.Books.Cohomology.Unit21.derivedSections
      (openSpace X U) (⊤ : Opens (openSpace X U).carrier) ⋙
    (forget₂ (ModuleCat
      ((openSpace X U).structureSheaf.obj.obj
        (op (⊤ : Opens (openSpace X U).carrier)))) AddCommGrpCat).mapDerivedCategory

structure LerayUnboundedData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  global_comparison :
    Formalization.Books.Cohomology.Unit21.derivedPushforward f ⋙
        Formalization.Books.Cohomology.Unit21.derivedGlobalSections Y ≅
      derivedSectionsViewedOverTarget f
  open_comparison : ∀ V : Opens Y.carrier, Nonempty
    (Formalization.Books.Cohomology.Unit21.derivedPushforward
          (openRestrictionOfMorphism f V) ⋙
        Formalization.Books.Cohomology.Unit21.derivedGlobalSections
          (openSpace Y V) ≅
      derivedSectionsViewedOverTarget (openRestrictionOfMorphism f V))

theorem leray_unbounded
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (LerayUnboundedData f) := by
  sorry

/-! ## Higher direct images -/

noncomputable abbrev higherDirectImageOpenValue
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : ModuleDerived X) (i : ℤ) (V : Opens Y.carrier) :
    ModuleCat (Y.structureSheaf.obj.obj (op V)) :=
  (ModuleCat.restrictScalars
      (Formalization.Books.Cohomology.Unit07.higherDirectImageScalarMap f V).hom).obj
    ((Formalization.Books.Cohomology.Unit21.derivedSectionsCohomology
      X (inverseImageOpen f V) i).obj K)

structure HigherDirectImageDescription
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : ModuleDerived X) (i : ℤ) where
  presheaf : PMod Y.structureSheaf.obj
  value_comparison : ∀ V : Opens Y.carrier, Nonempty
    (presheaf.obj (op V) ≅ higherDirectImageOpenValue f K i V)
  sheafification_comparison : Nonempty
    ((PresheafOfModules.sheafification (𝟙 Y.structureSheaf.obj)).obj presheaf ≅
      (Formalization.Books.Cohomology.Unit21.derivedPushforwardCohomology
        f i).obj K)

theorem describe_higher_direct_images
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : ModuleDerived X) (i : ℤ) :
    Nonempty (HigherDirectImageDescription f K i) := by
  sorry

/-! ## Forgetting the module structure -/

abbrev AbelianSheafCategory (X : RingedSpace.{v}) :=
  TopCat.Sheaf AddCommGrpCat.{v} X.carrier

noncomputable instance abelianSheafCategory_hasDerivedCategory
    (X : RingedSpace.{v}) : HasDerivedCategory (AbelianSheafCategory X) :=
  HasDerivedCategory.standard _

structure ModuleToAbelianDerivedData (X : RingedSpace.{v}) where
  functor : ModuleDerived X ⥤ DerivedCategory (AbelianSheafCategory X)
  underlying_is_exact :
    IsExact (SheafOfModules.toSheaf X.structureSheaf)

theorem exists_moduleToAbelianDerivedData
    (X : RingedSpace.{v}) : Nonempty (ModuleToAbelianDerivedData X) := by
  sorry

noncomputable def moduleToAbelianDerived
    (X : RingedSpace.{v}) :
    ModuleDerived X ⥤ DerivedCategory (AbelianSheafCategory X) :=
  (Classical.choice (exists_moduleToAbelianDerivedData X)).functor

structure AbelianDerivedSectionsData
    (X : RingedSpace.{v}) (U : Opens X.carrier) where
  functor : DerivedCategory (AbelianSheafCategory X) ⥤
    DerivedCategory AddCommGrpCat

theorem exists_abelianDerivedSectionsData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (AbelianDerivedSectionsData X U) := by
  sorry

noncomputable def abelianDerivedSections
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    DerivedCategory (AbelianSheafCategory X) ⥤
      DerivedCategory AddCommGrpCat :=
  (Classical.choice (exists_abelianDerivedSectionsData X U)).functor

structure AbelianDerivedDirectImageData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  functor : DerivedCategory (AbelianSheafCategory X) ⥤
    DerivedCategory (AbelianSheafCategory Y)

theorem exists_abelianDerivedDirectImageData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (AbelianDerivedDirectImageData f) := by
  sorry

noncomputable def abelianDerivedDirectImage
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    DerivedCategory (AbelianSheafCategory X) ⥤
      DerivedCategory (AbelianSheafCategory Y) :=
  (Classical.choice (exists_abelianDerivedDirectImageData f)).functor

structure ModulesAbelianComparisonData
    (X : RingedSpace.{v}) (K : ModuleDerived X) where
  K_ab : DerivedCategory (AbelianSheafCategory X)
  K_ab_is_image : Nonempty (K_ab ≅ (moduleToAbelianDerived X).obj K)
  sections_comparison : ∀ U : Opens X.carrier, Nonempty
    ((openGlobalSections X U).obj
        ((openRestrictionDerivedFunctor X U).obj K) ≅
      (abelianDerivedSections X U).obj K_ab)
  direct_image_comparison : ∀ {Y : RingedSpace.{v}} (f : RingedSpaceHom X Y),
    Nonempty
      ((moduleToAbelianDerived Y).obj
          ((Formalization.Books.Cohomology.Unit21.derivedPushforward f).obj K) ≅
        (abelianDerivedDirectImage f).obj K_ab)

theorem modules_abelian_unbounded
    (X : RingedSpace.{v}) (K : ModuleDerived X) :
    Nonempty (ModulesAbelianComparisonData X K) := by
  sorry

/-! ## The derived extension-by-zero adjunction -/

structure ExtensionByZeroRestrictionDerivedData
    (X : RingedSpace.{v}) (U : Opens X.carrier) where
  adjunction : openExtensionByZeroDerivedFunctor X U ⊣
    openRestrictionDerivedFunctor X U

theorem extension_by_zero_is_left_adjoint_to_restriction
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (ExtensionByZeroRestrictionDerivedData X U) := by
  sorry

/-! ## Flat pushforward preserves K-injectives -/

theorem pushforwardComplex_additive
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    (sheafModuleRingedSpacePushforward f).Additive := by
  exact left_or_right_exact_additive
    (sheafModuleRingedSpacePushforward f)
    (Or.inl (sheafModuleRingedSpacePushforward_isLeftExact f))

noncomputable def pushforwardComplexFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ModuleComplex X ⥤ ModuleComplex Y := by
  letI : (sheafModuleRingedSpacePushforward f).Additive :=
    pushforwardComplex_additive f
  exact (sheafModuleRingedSpacePushforward f).mapHomologicalComplex
    (ComplexShape.up ℤ)

theorem pushforward_flat_preserves_KInjective
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hf : FlatRingedSpaceHomData f)
    (I : ModuleComplex X) (hI : I.IsKInjective) :
    ((pushforwardComplexFunctor f).obj I).IsKInjective := by
  letI : (sheafModuleRingedSpacePushforward f).Additive :=
    pushforwardComplex_additive f
  letI : hf.pullback.Additive :=
    left_or_right_exact_additive hf.pullback (Or.inl hf.pullback_isExact.1)
  exact Formalization.Books.Derived.Unit31.additive_right_adjoint_preserves_isKInjective
    (sheafModuleRingedSpacePushforward f) hf.pullback hf.adjunction
    hf.pullback_isExact hI

end Formalization.Books.Cohomology.Unit25
