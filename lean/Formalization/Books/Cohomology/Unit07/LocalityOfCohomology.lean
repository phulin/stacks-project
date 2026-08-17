import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Sheaves.Unit22.OpenImmersions
import Formalization.Books.Topology.Unit02.BasicNotions
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian

/-!
# Cohomology of Sheaves, Chapter 7: locality of cohomology

This file formalizes the precise statements in the source section
`Locality of cohomology`.  Cohomology over an open is represented by the
derived sections functor from Chapter 3.  The presheaf
`U ↦ Hⁱ(U, F)` is represented by the higher right-derived functor of the
inclusion of sheaves of modules into presheaves of modules; its objectwise
identification with derived sections is recorded explicitly below.
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

/-! ## Cohomology on an open and its restriction maps -/

/- The presheaf-of-modules category is abelian by Mathlib.  Choosing the
  standard derived category is the same infrastructure already used for
  sheaves and modules in Chapter 2. -/
noncomputable instance presheafModule_hasDerivedCategory
    (X : RingedSpace.{v}) :
    HasDerivedCategory (PMod X.structureSheaf.obj) :=
  HasDerivedCategory.standard _

/- The source's `Hⁱ(U,F)` is the derived sections object from Chapter 3. -/
noncomputable abbrev cohomologyOnOpenModule
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  ringedSpaceModuleSectionsCohomologyObject X U F i

/-! ## Injective restriction and cohomology of an open -/

/-- Restriction of an injective sheaf of modules to an open subspace is
 injective. -/
theorem injective_restrict_to_open
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (I : Mod X.structureSheaf) [Injective I] :
    Injective ((openModuleRestrictionFunctor X U).obj I) := by
  sorry

/- The restriction in the right-hand side of the source's cohomology-of-open
 lemma is the canonical module restriction from the open-immersion API. -/
noncomputable abbrev restrictedSheaf
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) :
    Mod (ringedOpenSubspace X U).structureSheaf :=
  (openModuleRestrictionFunctor X U).obj F

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

/-- Cohomology over an open agrees with cohomology of the restricted sheaf.
 Since the two module objects use section rings presented at different open
 objects, the source equality is represented by the canonical additive-group
 isomorphism between the underlying cohomology groups. -/
theorem cohomology_of_open
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (p : ℕ) :
    Nonempty (cohomologyOnOpenAdditive X U F (p : ℤ) ≅
      cohomologyOfRestrictedSheafAdditive X U F (p : ℤ)) := by
  sorry

/-! The inclusion `i_X : Mod(O_X) ⥤ PMod(O_X)`. -/

/- The source calls this functor left exact.  The interface is kept explicit
  because it is used both for the interpretation of `underline H` and in the
  Daniel remark at the end of the section. -/
noncomputable def sheafModuleUnderlyingPresheafFunctor (X : RingedSpace.{v}) :
    Mod X.structureSheaf ⥤ PMod X.structureSheaf.obj :=
  SheafOfModules.forget X.structureSheaf

theorem sheafModuleUnderlyingPresheafFunctor_isLeftExact
    (X : RingedSpace.{v}) :
    IsLeftExact (sheafModuleUnderlyingPresheafFunctor X) := by
  sorry

/-! The sheaf `Hⁱ(U,F)` of the source, with its restriction maps. -/

/- Defining this by the canonical higher right-derived functor makes the
  presheaf structure and functoriality in `F` part of the type, rather than
  introducing a parallel family of maps. -/
noncomputable def localCohomologyPresheafFunctor
    (X : RingedSpace.{v}) (i : ℤ) :
    Mod X.structureSheaf ⥤ PMod X.structureSheaf.obj :=
  higherRightDerivedFunctor
    (sheafModuleUnderlyingPresheafFunctor X)
    (sheafModuleUnderlyingPresheafFunctor_isLeftExact X) i

/- The presheaf customarily denoted `underline Hⁱ(F)` in the source.  Its
  identity and composition laws are supplied by the `PMod` object itself. -/
noncomputable abbrev localCohomologyPresheaf
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℤ) :
    PMod X.structureSheaf.obj :=
  (localCohomologyPresheafFunctor X i).obj F

/- The object of the canonical cohomology presheaf at `U`. -/
noncomputable abbrev localCohomologyPresheafObject
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  (localCohomologyPresheaf X F i).obj (op U)

/-- The objectwise interpretation of `U ↦ Hⁱ(U,F)` by derived sections. -/
theorem localCohomologyPresheafObject_iso
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    Nonempty (localCohomologyPresheafObject X U F i ≅
      cohomologyOnOpenModule X U F i) := by
  sorry

/- A chosen comparison is useful for source-facing class and restriction
  declarations.  Its existence is the preceding source-faithful theorem. -/
noncomputable def localCohomologyPresheafObjectIso
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    localCohomologyPresheafObject X U F i ≅
      cohomologyOnOpenModule X U F i :=
  Classical.choice (localCohomologyPresheafObject_iso X U F i)

/- The restriction morphism in the presheaf itself.  Its source and target
  are the module-valued form of Equation (restriction-mapping). -/
noncomputable abbrev localCohomologyPresheafRestriction
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℤ)
    {U V : Opens X.carrier} (h : U ≤ V) :
    localCohomologyPresheafObject X V F i ⟶
      (ModuleCat.restrictScalars
        (X.structureSheaf.1.map (homOfLE h).op).hom).obj
        (localCohomologyPresheafObject X U F i) :=
  (localCohomologyPresheaf X F i).map (homOfLE h).op

/- The same restriction map transported to the Chapter 3 derived-sections
 objects. -/
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

/- The restriction map of Equation (restriction-mapping), on sections
 cohomology objects. -/
abbrev cohomologyRestrictionMapValue
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℤ)
    {U V : Opens X.carrier} (h : U ≤ V)
    (ξ : cohomologyOnOpenModule X V F i) :
    (ModuleCat.restrictScalars
      (X.structureSheaf.1.map (homOfLE h).op).hom).obj
      (cohomologyOnOpenModule X U F i) :=
  (cohomologyRestrictionMap X F i h).hom ξ

/- The presheaf laws give identity and composition of restriction maps, and
 the functoriality in `F` is the functoriality of
 `localCohomologyPresheafFunctor`.  The following theorem records the latter
 after transport to the source-facing derived-sections objects. -/
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

/-! ## Local vanishing of a positive-degree class -/

/-- A positive-degree cohomology class becomes zero on every member of an
 open cover. -/
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

/-! ## Higher direct images as associated presheaves -/

/- The direct-image scalar map on sections. -/
noncomputable abbrev higherDirectImageScalarMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    Y.structureSheaf.obj.obj (op V) ⟶
      X.structureSheaf.obj.obj
        (op ((Opens.map f.continuous).obj V)) :=
  ringedSpaceBasisScalarMap f (U := (Opens.map f.continuous).obj V)
    (V := V) le_rfl

theorem presheafHigherDirectImageFunctor_isLeftExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    IsLeftExact
      (sheafModuleRingedSpacePushforward f ⋙
        sheafModuleUnderlyingPresheafFunctor Y) := by
  sorry

/-- The presheaf-valued `Rⁱ(i_Y ∘ f_*)`. -/
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

/- The restriction maps of the presheaf in Lemma
`describe-higher-direct-images`.  Keeping this as the canonical presheaf map
also records the compatibility of the local cohomology description with
restriction in the target open. -/
noncomputable abbrev higherDirectImageRestriction
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ)
    {V W : Opens Y.carrier} (h : V ≤ W) :
    (presheafHigherDirectImageObject f F i).obj (op W) ⟶
      (ModuleCat.restrictScalars
        (Y.structureSheaf.1.map (homOfLE h).op).hom).obj
        ((presheafHigherDirectImageObject f F i).obj (op V)) :=
  (presheafHigherDirectImageObject f F i).map (homOfLE h).op

noncomputable abbrev higherDirectImageObject
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ) : Mod Y.structureSheaf :=
  (ringedSpaceModuleHigherDirectImage f i).obj F

/-- The sections of the presheaf-valued higher direct image are the cohomology
 of the inverse image open. -/
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

/-- The higher direct image is the sheaf associated to the presheaf of local
 cohomology groups. -/
theorem higherDirectImage_is_sheafification
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ) :
    Nonempty (
      (PresheafOfModules.sheafification
        (𝟙 Y.structureSheaf.obj)).obj
        (presheafHigherDirectImageObject f F i) ≅
      higherDirectImageObject f F i) := by
  sorry

/-! ## Restriction of a ringed-space morphism to an open -/

/- The continuous map on the underlying open subspaces is explicit. -/
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

/-- The restriction `f⁻¹(V) → V` of a morphism of ringed spaces. -/
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

/-! ## Locality of higher direct images -/

/-- The higher direct image after restricting both source and target opens. -/
noncomputable abbrev localizedHigherDirectImageObject
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (F : Mod X.structureSheaf) (i : ℤ) :
    Mod (ringedOpenSubspace Y V).structureSheaf :=
  (ringedSpaceModuleHigherDirectImage (ringedSpaceOpenRestriction f V) i).obj
    ((openModuleRestrictionFunctor X ((Opens.map f.continuous).obj V)).obj F)

noncomputable instance openModuleRestrictionFunctor_preservesZeroMorphisms
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    (openModuleRestrictionFunctor X U).PreservesZeroMorphisms := by
  sorry

/- The derived pushforward of a bounded-below complex is treated in the same
way as the object case, using the Chapter 3 derived-category model. -/
noncomputable def openRestrictionOnComplexes
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    CompPlus (Mod X.structureSheaf) ⥤
      CompPlus (Mod (ringedOpenSubspace X U).structureSheaf) :=
  (openModuleRestrictionFunctor X U).mapCochainComplexPlus

noncomputable def sectionsComplexCohomology
    (Z : RingedSpace.{v}) (U : Opens Z.carrier)
    (K : CompPlus (Mod Z.structureSheaf)) (i : ℤ) :
    ModuleCat.{v} (Z.structureSheaf.obj.obj (op U)) :=
  (DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{v} (Z.structureSheaf.obj.obj (op U))) i).obj
    ((ringedSpaceModuleTotalDerivedSections Z U).obj
      ((DerivedCategory.Plus.Q (C := Mod Z.structureSheaf)).obj K))

noncomputable abbrev higherDirectImageComplexObject
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf)) (i : ℤ) :
    Mod Y.structureSheaf :=
  (ringedSpaceModuleDerivedPushforwardCohomology f i).obj
    ((DerivedCategory.Plus.Q (C := Mod X.structureSheaf)).obj K)

/-- The presheaf-valued higher direct image on bounded-below complexes. -/
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

/-- The complex version of higher direct image is the associated sheaf of the
 presheaf of cohomology of inverse-image opens. -/
theorem higherDirectImageComplex_is_sheafification
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf)) (i : ℤ) :
    Nonempty (
      (PresheafOfModules.sheafification
        (𝟙 Y.structureSheaf.obj)).obj
        (presheafHigherDirectImageComplexObject f K i) ≅
      higherDirectImageComplexObject f K i) := by
  sorry

/-- Higher direct images commute with restriction to an open of the target. -/
theorem localize_higher_direct_image
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) (F : Mod X.structureSheaf) (i : ℤ) :
    Nonempty (localizedHigherDirectImageObject f V F i ≅
      (openModuleRestrictionFunctor Y V).obj
        (higherDirectImageObject f F i)) := by
  sorry

/-- The complex version of locality of higher direct images. -/
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
        (higherDirectImageComplexObject f K i)) := by
  sorry

/-! ## The derived-functor reformulation -/

/- The source's `#` is the canonical module sheafification for the identity
 ring-presheaf map on a sheaf of rings. -/
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

/-- The definition of `underline Hⁱ(F)` is the right-derived functor of the
 inclusion of sheaves into presheaves. -/
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

/- The universal delta-functor property used in the first part of the
  derived-functor remark is inherited from the canonical construction. -/
theorem localCohomologyPresheafFunctor_is_universal
    (X : RingedSpace.{v}) :
    IsUniversalHigherRightDerivedDeltaFunctor
      (sheafModuleUnderlyingPresheafFunctor X)
      (sheafModuleUnderlyingPresheafFunctor_isLeftExact X) := by
  exact higherRightDerivedFunctor_universal
    (sheafModuleUnderlyingPresheafFunctor X)
    (sheafModuleUnderlyingPresheafFunctor_isLeftExact X)

/-- Positive-degree `underline Hⁱ(F)` sheafifies to zero. -/
theorem localCohomologySheafification_isZero
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (p : ℕ) (_hp : 0 < p) :
    IsZero ((modulePresheafSheafification X).obj
      ((localCohomologyPresheafFunctor X (p : ℤ)).obj F)) := by
  sorry

/-- The presheaf-valued higher direct image is `Rⁱ(i_Y ∘ f_*)`. -/
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
