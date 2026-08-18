import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Sheaves.Unit22.OpenImmersions
import Formalization.Books.Topology.Unit02.BasicNotions
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian

/-!
# Cohomology of Sheaves, Chapter 7: locality of cohomology

This file formalizes the precise statements in the source section
`Locality of cohomology` (the open-cohomology lemma, the restriction presheaf,
local vanishing, higher direct images and their localization, the
bounded-below complex variants, and the derived-functor remark).  Cohomology
over an open is represented by the derived sections functor from Chapter 3.
Restriction maps are represented by the presheaf structure of the higher
derived functor of the inclusion of sheaves of modules into presheaves of
modules.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Set
open TopologicalSpace
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit12
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Topology.Unit02

universe v u

namespace Formalization.Books.Cohomology.Unit07

/-! ## Lemma `cohomology-of-open`: cohomology on an open -/

noncomputable instance presheafModule_hasDerivedCategory
    (X : RingedSpace.{v}) :
    HasDerivedCategory (PMod X.structureSheaf.obj) :=
  HasDerivedCategory.standard _

/- The canonical Chapter 3 representation of `Hⁱ(U, F)`. -/
noncomputable abbrev cohomologyOnOpenModule
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  ringedSpaceModuleSectionsCohomologyObject X U F i

/- The restriction of a sheaf of modules to the open subspace. -/
noncomputable abbrev restrictedSheaf
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) :
    Mod (ringedOpenSubspace X U).structureSheaf :=
  (openModuleRestrictionFunctor X U).obj F

/- The cohomology over `U` computed on the restricted ringed space. -/
noncomputable abbrev cohomologyOfRestrictedSheaf
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    ModuleCat.{v}
      ((ringedOpenSubspace X U).structureSheaf.obj.obj
        (op (⊤ : Opens (ringedOpenSubspace X U).carrier))) :=
  ringedSpaceModuleSectionsCohomologyObject
    (ringedOpenSubspace X U) (⊤ : Opens (ringedOpenSubspace X U).carrier)
    (restrictedSheaf X U F) i

noncomputable abbrev cohomologyOnOpenAdditive
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) : AddCommGrpCat.{v} :=
  (forget₂ (ModuleCat (X.structureSheaf.obj.obj (op U)))
    AddCommGrpCat).obj (cohomologyOnOpenModule X U F i)

noncomputable abbrev cohomologyOfRestrictedSheafAdditive
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) : AddCommGrpCat.{v} :=
  (forget₂
      (ModuleCat ((ringedOpenSubspace X U).structureSheaf.obj.obj
        (op (⊤ : Opens (ringedOpenSubspace X U).carrier))))
      AddCommGrpCat).obj (cohomologyOfRestrictedSheaf X U F i)

/- The two formulations of cohomology in Lemma `cohomology-of-open`. -/
theorem injective_restrict_to_open
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (I : Mod X.structureSheaf) [Injective I] :
    Injective ((openModuleRestrictionFunctor X U).obj I) := by
  sorry

theorem cohomology_of_open
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (p : ℕ) :
    Nonempty (cohomologyOnOpenAdditive X U F (p : ℤ) ≅
      cohomologyOfRestrictedSheafAdditive X U F (p : ℤ)) := by
  sorry

/-! ## Equation `restriction-mapping` and the restriction presheaf `underline Hⁱ(F)` -/

/- The inclusion `i_X : Mod(O_X) ⥤ PMod(O_X)`. -/
noncomputable def sheafModuleUnderlyingPresheafFunctor (X : RingedSpace.{v}) :
    Mod X.structureSheaf ⥤ PMod X.structureSheaf.obj :=
  SheafOfModules.forget X.structureSheaf

theorem sheafModuleUnderlyingPresheafFunctor_isLeftExact
    (X : RingedSpace.{v}) :
    IsLeftExact (sheafModuleUnderlyingPresheafFunctor X) := by
  sorry

/- The source's `underline Hⁱ` as the canonical higher derived functor. -/
noncomputable def localCohomologyPresheafFunctor
    (X : RingedSpace.{v}) (i : ℤ) :
    Mod X.structureSheaf ⥤ PMod X.structureSheaf.obj :=
  higherRightDerivedFunctor
    (sheafModuleUnderlyingPresheafFunctor X)
    (sheafModuleUnderlyingPresheafFunctor_isLeftExact X) i

noncomputable abbrev localCohomologyPresheaf
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℤ) :
    PMod X.structureSheaf.obj :=
  (localCohomologyPresheafFunctor X i).obj F

noncomputable abbrev localCohomologyPresheafObject
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  (localCohomologyPresheaf X F i).obj (op U)

/- The objectwise description `U ↦ Hⁱ(U,F)`. -/
theorem localCohomologyPresheafObject_iso
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    Nonempty (localCohomologyPresheafObject X U F i ≅
      cohomologyOnOpenModule X U F i) := by
  sorry

noncomputable def localCohomologyPresheafObjectIso
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    localCohomologyPresheafObject X U F i ≅
      cohomologyOnOpenModule X U F i :=
  Classical.choice (localCohomologyPresheafObject_iso X U F i)

/- The canonical restriction map of the cohomology presheaf. -/
noncomputable abbrev localCohomologyPresheafRestriction
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℤ)
    {U V : Opens X.carrier} (h : U ≤ V) :
    localCohomologyPresheafObject X V F i ⟶
      (ModuleCat.restrictScalars
        (X.structureSheaf.1.map (homOfLE h).op).hom).obj
        (localCohomologyPresheafObject X U F i) :=
  moduleRestriction (localCohomologyPresheaf X F i) h

noncomputable def cohomologyRestrictionMap
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℤ)
    {U V : Opens X.carrier} (h : U ≤ V) :
    cohomologyOnOpenModule X V F i ⟶
      (ModuleCat.restrictScalars
        (X.structureSheaf.1.map (homOfLE h).op).hom).obj
        (cohomologyOnOpenModule X U F i) :=
  (localCohomologyPresheafObjectIso X V F i).inv ≫
    localCohomologyPresheafRestriction X F i h ≫
      (ModuleCat.restrictScalars
        (X.structureSheaf.1.map (homOfLE h).op).hom).map
        (localCohomologyPresheafObjectIso X U F i).hom

abbrev cohomologyRestrictionMapValue
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℤ)
    {U V : Opens X.carrier} (h : U ≤ V)
    (ξ : cohomologyOnOpenModule X V F i) :
    (ModuleCat.restrictScalars
      (X.structureSheaf.1.map (homOfLE h).op).hom).obj
      (cohomologyOnOpenModule X U F i) :=
  (cohomologyRestrictionMap X F i h).hom ξ

theorem cohomologyRestrictionMap_natural
    (X : RingedSpace.{v}) (i : ℤ)
    {F G : Mod X.structureSheaf} (φ : F ⟶ G)
    {U V : Opens X.carrier} (h : U ≤ V) :
    cohomologyRestrictionMap X F i h ≫
        (ModuleCat.restrictScalars
          (X.structureSheaf.1.map (homOfLE h).op).hom).map
          ((ringedSpaceModuleSectionsCohomology X U i).map φ) =
      (ringedSpaceModuleSectionsCohomology X V i).map φ ≫
        cohomologyRestrictionMap X G i h := by
  sorry

/-! ## Lemma `kill-cohomology-class-on-covering` -/

theorem cohomology_class_killed_on_open_cover
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (U : Opens X.carrier) (n : ℕ) (_hn : 0 < n)
    (ξ : cohomologyOnOpenModule X U F (n : ℤ)) :
    ∃ (ι : Type u) (U_i : ι → Opens X.carrier)
      (hU : ∀ i, U_i i ≤ U),
      IsOpenCoverOf (U : Set X.carrier)
        (fun i => (U_i i : Set X.carrier)) ∧
        ∀ i, cohomologyRestrictionMapValue X F (n : ℤ) (hU i) ξ = 0 := by
  sorry

/-! ## Lemma `describe-higher-direct-images` -/

noncomputable abbrev higherDirectImageScalarMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    Y.structureSheaf.obj.obj (op V) ⟶
      X.structureSheaf.obj.obj
        (op ((Opens.map f.continuous).obj V)) :=
  ringedSpaceBasisScalarMap f (U := (Opens.map f.continuous).obj V)
    (V := V) le_rfl

/- The presheaf-valued form of `Rⁱ(i_Y ∘ f_*)`. -/
theorem presheafHigherDirectImageFunctor_isLeftExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    IsLeftExact
      (sheafModuleRingedSpacePushforward f ⋙
        sheafModuleUnderlyingPresheafFunctor Y) := by
  sorry

noncomputable def presheafHigherDirectImageFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (i : ℤ) :
    Mod X.structureSheaf ⥤ PMod Y.structureSheaf.obj :=
  higherRightDerivedFunctor
    (sheafModuleRingedSpacePushforward f ⋙
      sheafModuleUnderlyingPresheafFunctor Y)
    (presheafHigherDirectImageFunctor_isLeftExact f) i

noncomputable abbrev presheafHigherDirectImageObject
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ) : PMod Y.structureSheaf.obj :=
  (presheafHigherDirectImageFunctor f i).obj F

noncomputable abbrev higherDirectImageRestriction
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ)
    {V W : Opens Y.carrier} (h : V ≤ W) :
    (presheafHigherDirectImageObject f F i).obj (op W) ⟶
      (ModuleCat.restrictScalars
        (Y.structureSheaf.1.map (homOfLE h).op).hom).obj
        ((presheafHigherDirectImageObject f F i).obj (op V)) :=
  moduleRestriction (presheafHigherDirectImageObject f F i) h

theorem presheafHigherDirectImageObject_obj_iso
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ) (V : Opens Y.carrier) :
    Nonempty (
      (presheafHigherDirectImageObject f F i).obj (op V) ≅
        (ModuleCat.restrictScalars
          (higherDirectImageScalarMap f V).hom).obj
          (cohomologyOnOpenModule X
            ((Opens.map f.continuous).obj V) F i)) := by
  sorry

theorem higherDirectImage_is_sheafification
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ) :
    Nonempty (
      (PresheafOfModules.sheafification
        (𝟙 Y.structureSheaf.obj)).obj
        (presheafHigherDirectImageObject f F i) ≅
      (ringedSpaceModuleHigherDirectImage f i).obj F) := by
  sorry

/-! ## The bounded-below-complex variant of `describe-higher-direct-images` -/

noncomputable def sectionsComplexCohomology
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : CompPlus (Mod X.structureSheaf)) (i : ℤ) :
    ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  (DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) i).obj
    ((ringedSpaceModuleTotalDerivedSections X U).obj
      ((DerivedCategory.Plus.Q (C := Mod X.structureSheaf)).obj K))

noncomputable def presheafHigherDirectImageComplexFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (i : ℤ) :
    CompPlus (Mod X.structureSheaf) ⥤ PMod Y.structureSheaf.obj :=
  rightDerivedFunctorOfLeftExactOnComplexes
      (sheafModuleRingedSpacePushforward f ⋙
        sheafModuleUnderlyingPresheafFunctor Y)
      (presheafHigherDirectImageFunctor_isLeftExact f) ⋙
    DerivedCategory.Plus.homologyFunctor (PMod Y.structureSheaf.obj) i

noncomputable abbrev presheafHigherDirectImageComplexObject
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf)) (i : ℤ) :
    PMod Y.structureSheaf.obj :=
  (presheafHigherDirectImageComplexFunctor f i).obj K

theorem presheafHigherDirectImageComplexObject_obj_iso
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf)) (i : ℤ) (V : Opens Y.carrier) :
    Nonempty (
      (presheafHigherDirectImageComplexObject f K i).obj (op V) ≅
        (ModuleCat.restrictScalars
          (higherDirectImageScalarMap f V).hom).obj
          (sectionsComplexCohomology X
            ((Opens.map f.continuous).obj V) K i))) := by
  sorry

theorem higherDirectImageComplex_is_sheafification
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf)) (i : ℤ) :
    Nonempty (
      (PresheafOfModules.sheafification
        (𝟙 Y.structureSheaf.obj)).obj
        (presheafHigherDirectImageComplexObject f K i) ≅
      (ringedSpaceModuleDerivedPushforwardCohomology f i).obj
        ((DerivedCategory.Plus.Q (C := Mod X.structureSheaf)).obj K)) := by
  sorry

/-! ## Lemma `localize-higher-direct-images` -/

noncomputable def ringedSpaceOpenRestrictionContinuous
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    openSubspace ((Opens.map f.continuous).obj V) ⟶ openSubspace V :=
  TopCat.ofHom
    { toFun := fun x => ⟨f.continuous.hom x.1, x.2⟩
      continuous_toFun :=
        Continuous.subtype_mk
          (f.continuous.hom.continuous.comp continuous_subtype_val)
          (fun x => by simpa using (Opens.mem_map.mp x.2)) }

structure RingedSpaceOpenRestrictionData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) where
  morphism : RingedSpaceHom
    (ringedOpenSubspace X ((Opens.map f.continuous).obj V))
    (ringedOpenSubspace Y V)
  continuous_eq : morphism.continuous = ringedSpaceOpenRestrictionContinuous f V

theorem exists_ringedSpaceOpenRestrictionData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    Nonempty (RingedSpaceOpenRestrictionData f V) := by
  sorry

noncomputable def ringedSpaceOpenRestriction
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    RingedSpaceHom
      (ringedOpenSubspace X ((Opens.map f.continuous).obj V))
      (ringedOpenSubspace Y V) :=
  (Classical.choice (exists_ringedSpaceOpenRestrictionData f V)).morphism

theorem ringedSpaceOpenRestriction_continuous
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    (ringedSpaceOpenRestriction f V).continuous =
      ringedSpaceOpenRestrictionContinuous f V :=
  (Classical.choice (exists_ringedSpaceOpenRestrictionData f V)).continuous_eq

noncomputable abbrev localizedHigherDirectImageObject
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (F : Mod X.structureSheaf) (i : ℤ) :
    Mod (ringedOpenSubspace Y V).structureSheaf :=
  (ringedSpaceModuleHigherDirectImage (ringedSpaceOpenRestriction f V) i).obj
    ((openModuleRestrictionFunctor X ((Opens.map f.continuous).obj V)).obj F)

theorem localize_higher_direct_image
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (F : Mod X.structureSheaf) (i : ℤ) :
    Nonempty (localizedHigherDirectImageObject f V F i ≅
      (openModuleRestrictionFunctor Y V).obj
        ((ringedSpaceModuleHigherDirectImage f i).obj F)) := by
  sorry

noncomputable def openRestrictionOnComplexes
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    CompPlus (Mod X.structureSheaf) ⥤
      CompPlus (Mod (ringedOpenSubspace X U).structureSheaf) :=
  (openModuleRestrictionFunctor X U).mapCochainComplexPlus

theorem localize_higher_direct_image_complex
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (K : CompPlus (Mod X.structureSheaf))
    (i : ℤ) :
    Nonempty (
      (ringedSpaceModuleDerivedPushforwardCohomology
          (ringedSpaceOpenRestriction f V) i).obj
        ((DerivedCategory.Plus.Q
          (C := Mod (ringedOpenSubspace X
            ((Opens.map f.continuous).obj V)).structureSheaf)).obj
          ((openRestrictionOnComplexes X
            ((Opens.map f.continuous).obj V)).obj K)) ≅
      (openModuleRestrictionFunctor Y V).obj
        ((ringedSpaceModuleDerivedPushforwardCohomology f i).obj
          ((DerivedCategory.Plus.Q
            (C := Mod X.structureSheaf)).obj K))) := by
  sorry

/-! ## Remark `daniel`: derived-functor reformulation -/

noncomputable def modulePresheafSheafification (X : RingedSpace.{v}) :
    PMod X.structureSheaf.obj ⥤ Mod X.structureSheaf :=
  PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)

theorem modulePresheafSheafification_isExact (X : RingedSpace.{v}) :
    IsExact (modulePresheafSheafification X) := by
  sorry

theorem sheafModuleUnderlyingPresheafFunctor_comp_sheafification_iso
    (X : RingedSpace.{v}) :
    Nonempty (
      sheafModuleUnderlyingPresheafFunctor X ⋙
          modulePresheafSheafification X ≅
        𝟭 (Mod X.structureSheaf)) := by
  sorry

theorem localCohomologyPresheafFunctor_is_rightDerived
    (X : RingedSpace.{v}) (i : ℤ) :
    localCohomologyPresheafFunctor X i =
      higherRightDerivedFunctor
        (sheafModuleUnderlyingPresheafFunctor X)
        (sheafModuleUnderlyingPresheafFunctor_isLeftExact X) i :=
  rfl

theorem localCohomologyPresheafFunctor_zero_iso
    (X : RingedSpace.{v}) :
    Nonempty (localCohomologyPresheafFunctor X 0 ≅
      sheafModuleUnderlyingPresheafFunctor X) := by
  exact higherRightDerivedFunctor_zero_iso
    (sheafModuleUnderlyingPresheafFunctor X)
    (sheafModuleUnderlyingPresheafFunctor_isLeftExact X)

theorem localCohomologyPresheafFunctor_is_universal
    (X : RingedSpace.{v}) :
    IsUniversalHigherRightDerivedDeltaFunctor
      (sheafModuleUnderlyingPresheafFunctor X)
      (sheafModuleUnderlyingPresheafFunctor_isLeftExact X) := by
  exact higherRightDerivedFunctor_universal
    (sheafModuleUnderlyingPresheafFunctor X)
    (sheafModuleUnderlyingPresheafFunctor_isLeftExact X)

theorem localCohomologySheafification_isZero
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (p : ℕ) (_hp : 0 < p) :
    IsZero ((modulePresheafSheafification X).obj
      ((localCohomologyPresheafFunctor X (p : ℤ)).obj F)) := by
  sorry

theorem presheafHigherDirectImageFunctor_is_the_derived_composite
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (i : ℤ) :
    presheafHigherDirectImageFunctor f i =
      higherRightDerivedFunctor
        (sheafModuleRingedSpacePushforward f ⋙
          sheafModuleUnderlyingPresheafFunctor Y)
        (presheafHigherDirectImageFunctor_isLeftExact f) i :=
  rfl

theorem presheafHigherDirectImageFunctor_is_universal
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    IsUniversalHigherRightDerivedDeltaFunctor
      (sheafModuleRingedSpacePushforward f ⋙
        sheafModuleUnderlyingPresheafFunctor Y)
      (presheafHigherDirectImageFunctor_isLeftExact f) := by
  exact higherRightDerivedFunctor_universal
    (sheafModuleRingedSpacePushforward f ⋙
      sheafModuleUnderlyingPresheafFunctor Y)
    (presheafHigherDirectImageFunctor_isLeftExact f)

end Formalization.Books.Cohomology.Unit07
