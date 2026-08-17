import Formalization.Books.Sheaves.Unit22.OpenImmersions

/-!
# Sheaves on Spaces, Chapter 31: Open immersions and (pre)sheaves

The source section is `books/sheaves.tex:4439-4924`.  The preceding sheaf
chapters already provide the canonical open-subspace, pullback, pushforward,
sheafification, module, stalk, and essential-image constructions.  This
section re-exports those interfaces under the chapter's source-order API.
The extension-by-initial presheaf has the genuine sectionwise body in the
earlier canonical implementation; all proposition-valued results below are
the corresponding source statements, with proofs deferred to the prove
stage where the earlier interface itself uses `sorry`.
-/

namespace Formalization.Books.Sheaves.Unit31

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.Topology
open scoped ZeroObject

open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe u v

noncomputable section

/-! ## Restriction and direct image -/

abbrev openSubspace {X : TopCat.{v}} (U : Opens X) : TopCat.{v} :=
  Formalization.Books.Sheaves.Unit22.openSubspace U

abbrev openInclusion {X : TopCat.{v}} (U : Opens X) : openSubspace U ⟶ X :=
  Formalization.Books.Sheaves.Unit22.openInclusion U

noncomputable abbrev openPresheafRestriction (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C (openSubspace U) :=
  Formalization.Books.Sheaves.Unit22.openPresheafRestriction C U

abbrev openPresheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X :=
  Formalization.Books.Sheaves.Unit22.openPresheafDirectImage C U

abbrev openSheafRestriction (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubspace U) :=
  Formalization.Books.Sheaves.Unit22.openSheafRestriction C U

abbrev openSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X :=
  Formalization.Books.Sheaves.Unit22.openSheafDirectImage C U

/- The source writes restriction sectionwise.  For an arbitrary open of the
   open subspace, its image under the open embedding is open in `X`, and
   Mathlib's pointwise left-Kan-extension API gives exactly that section. -/
noncomputable def openPresheafRestriction_obj_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C X) (V : Opens (openSubspace U)) :
    ((openPresheafRestriction C U).obj F).obj (op V) ≅
      F.obj (op ⟨(openInclusion U) '' V,
        (U.isOpenEmbedding.isOpenMap V V.2)⟩) := by
  exact TopCat.Presheaf.pullbackObjObjOfImageOpen
    (openInclusion U) F V (U.isOpenEmbedding.isOpenMap V V.2)

theorem openPresheafRestriction_formula (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C X) :
    Nonempty ((openPresheafRestriction C U).obj F ≅
      (TopCat.Presheaf.pullback C (openInclusion U)).obj F) :=
  Formalization.Books.Sheaves.Unit22.openPresheafRestriction_formula C U F

theorem openSheafRestriction_formula (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X) :
    Nonempty (((openSheafRestriction C U).obj F).presheaf ≅
      (openPresheafRestriction C U).obj F.presheaf) :=
  Formalization.Books.Sheaves.Unit22.openSheafRestriction_formula C U F

theorem openSheafRestriction_obj_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Sheaf C X) (V : Opens (openSubspace U)) :
    Nonempty ((((openSheafRestriction C U).obj F).presheaf).obj (op V) ≅
      F.presheaf.obj (op ⟨(openInclusion U) '' V,
        (U.isOpenEmbedding.isOpenMap V V.2)⟩)) := by
  rcases openSheafRestriction_formula C U F with ⟨e⟩
  exact ⟨e.app (op V) ≪≫ openPresheafRestriction_obj_iso C U F.presheaf V⟩

theorem openSheafRestriction_stalk_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X)
    (u : openSubspace U) :
    Nonempty (((openSheafRestriction C U).obj F).presheaf.stalk u ≅
      F.presheaf.stalk ((openInclusion U) u)) :=
  Formalization.Books.Sheaves.Unit22.openSheafRestriction_stalk_iso C U F u

@[simp] theorem openPresheafDirectImage_obj (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) :
    ((openPresheafDirectImage C U).obj F).obj (op V) =
      F.obj (op ((Opens.map (openInclusion U)).obj V)) :=
  Formalization.Books.Sheaves.Unit22.openPresheafDirectImage_obj C U F V

theorem openPresheafRestriction_directImage_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) :
    Nonempty ((openPresheafRestriction C U).obj
      ((openPresheafDirectImage C U).obj F) ≅ F) :=
  Formalization.Books.Sheaves.Unit22.openPresheafRestriction_directImage_iso C U F

theorem openSheafRestriction_directImage_iso {C : Type u} [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C (openSubspace U)) :
    Nonempty ((openSheafRestriction C U).obj
      ((openSheafDirectImage C U).obj F) ≅ F) :=
  Formalization.Books.Sheaves.Unit22.openSheafRestriction_directImage_iso U F

theorem openSheafDirectImage_fullFaithful (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    Nonempty (openSheafDirectImage C U).FullyFaithful :=
  Formalization.Books.Sheaves.Unit22.openSheafDirectImage_fullFaithful C U

/-! ## Extension by the empty set and by an initial object -/

noncomputable def openPresheafExtensionByInitial (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X :=
  Formalization.Books.Sheaves.Unit22.openPresheafExtensionByInitial C U

@[simp] theorem openPresheafExtensionByInitial_obj_of_le (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) (hV : V ≤ U) :
    ((openPresheafExtensionByInitial C U).obj F).obj (op V) =
      F.obj (op ((Opens.map (openInclusion U)).obj V)) := by
  simp [openPresheafExtensionByInitial,
    Formalization.Books.Sheaves.Unit22.openPresheafExtensionByInitial, hV]

@[simp] theorem openPresheafExtensionByInitial_obj_of_not_le (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) (hV : ¬ V ≤ U) :
    ((openPresheafExtensionByInitial C U).obj F).obj (op V) = (⊥_ C) := by
  simp [openPresheafExtensionByInitial,
    Formalization.Books.Sheaves.Unit22.openPresheafExtensionByInitial, hV]

noncomputable abbrev openPresheafExtensionByEmpty {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf (Type v) (openSubspace U) ⥤ TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit22.openPresheafExtensionByEmpty U

noncomputable abbrev openAbelianPresheafExtensionByZero {X : TopCat.{v}}
    (U : Opens X) :
    AbelianPresheaf (openSubspace U) ⥤ AbelianPresheaf X :=
  Formalization.Books.Sheaves.Unit22.openAbelianPresheafExtensionByZero U

noncomputable abbrev openAlgebraicPresheafExtensionByInitial
    (C : Type u) [Category.{v} C] [HasInitial C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X :=
  Formalization.Books.Sheaves.Unit22.openAlgebraicPresheafExtensionByInitial C U

noncomputable def openSheafExtensionByInitial (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X :=
  Formalization.Books.Sheaves.Unit22.openSheafExtensionByInitial C U

noncomputable abbrev openSetSheafExtensionByEmpty {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    TopCat.Sheaf (Type v) (openSubspace U) ⥤ TopCat.Sheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit22.openSetSheafExtensionByEmpty U

noncomputable abbrev openAbelianSheafExtensionByZero {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    Ab (openSubspace U) ⥤ Ab X :=
  Formalization.Books.Sheaves.Unit22.openAbelianSheafExtensionByZero U

theorem exists_openPresheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    Nonempty (openPresheafExtensionByInitial C U ⊣ openPresheafRestriction C U) :=
  Formalization.Books.Sheaves.Unit22.exists_openPresheafExtensionAdjunction C U

noncomputable def openPresheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    openPresheafExtensionByInitial C U ⊣ openPresheafRestriction C U :=
  Formalization.Books.Sheaves.Unit22.openPresheafExtensionAdjunction C U

noncomputable abbrev openAbelianPresheafExtensionAdjunction
    {X : TopCat.{v}} (U : Opens X) :
    openAbelianPresheafExtensionByZero U ⊣ openPresheafRestriction AddCommGrpCat U :=
  Formalization.Books.Sheaves.Unit22.openAbelianPresheafExtensionAdjunction U

theorem exists_openSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    Nonempty (openSheafExtensionByInitial C U ⊣ openSheafRestriction C U) :=
  Formalization.Books.Sheaves.Unit22.exists_openSheafExtensionAdjunction C U

noncomputable def openSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    openSheafExtensionByInitial C U ⊣ openSheafRestriction C U :=
  Formalization.Books.Sheaves.Unit22.openSheafExtensionAdjunction C U

theorem openPresheafExtension_restrict_iso (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) :
    Nonempty ((openPresheafRestriction C U).obj
      ((openPresheafExtensionByInitial C U).obj F) ≅ F) :=
  Formalization.Books.Sheaves.Unit22.openPresheafExtension_restrict_iso C U F

theorem openAlgebraicSheafExtension_restrict_iso (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) :
    Nonempty ((openSheafRestriction C U).obj
      ((openSheafExtensionByInitial C U).obj F) ≅ F) :=
  Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtension_restrict_iso C U F

noncomputable abbrev openSetSheafExtensionHomEquiv {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (G : TopCat.Sheaf (Type v) X) :
    ((openSetSheafExtensionByEmpty U).obj F ⟶ G) ≃
      (F ⟶ (openSheafRestriction (Type v) U).obj G) :=
  Formalization.Books.Sheaves.Unit22.openSetSheafExtensionHomEquiv U F G

theorem openSetSheafExtension_stalk_empty {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (x : X) (hx : x ∉ U) :
    IsEmpty (((openSetSheafExtensionByEmpty U).obj F).presheaf.stalk x) :=
  Formalization.Books.Sheaves.Unit22.openSetSheafExtension_stalk_empty U F x hx

theorem openSetSheafExtension_stalk_iso {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (x : X) (hx : x ∈ U) :
    Nonempty (((openSetSheafExtensionByEmpty U).obj F).presheaf.stalk x ≃
      F.presheaf.stalk ⟨x, hx⟩) :=
  Formalization.Books.Sheaves.Unit22.openSetSheafExtension_stalk_iso U F x hx

theorem openSetSheafExtension_restrict_iso {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) :
    Nonempty ((openSheafRestriction (Type v) U).obj
      ((openSetSheafExtensionByEmpty U).obj F) ≅ F) :=
  Formalization.Books.Sheaves.Unit22.openSetSheafExtension_restrict_iso U F

/-! ## Algebraic structures and modules -/

noncomputable def openAlgebraicSheafExtensionFunctor (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X :=
  Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtensionFunctor C U

noncomputable def openAlgebraicSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    openAlgebraicSheafExtensionFunctor C U ⊣ openSheafRestriction C U :=
  Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtensionAdjunction C U

theorem openAlgebraicSheafExtension_stalk_initial (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) (x : X) (hx : x ∉ U) :
    Nonempty (((openAlgebraicSheafExtensionFunctor C U).obj F).presheaf.stalk x ≅
      (⊥_ C)) :=
  Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtension_stalk_initial C U F x hx

theorem openAlgebraicSheafExtension_stalk_iso (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) (x : X) (hx : x ∈ U) :
    Nonempty (((openAlgebraicSheafExtensionFunctor C U).obj F).presheaf.stalk x ≅
      F.presheaf.stalk ⟨x, hx⟩) :=
  Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtension_stalk_iso C U F x hx

noncomputable abbrev openAbelianSheafExtensionFunctor {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :=
  Formalization.Books.Sheaves.Unit22.openAbelianSheafExtensionFunctor U

noncomputable abbrev openAbelianSheafExtensionAdjunction
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    openAbelianSheafExtensionFunctor U ⊣
      openSheafRestriction AddCommGrpCat U :=
  Formalization.Books.Sheaves.Unit22.openAbelianSheafExtensionAdjunction U

abbrev ringedOpenSubspace (X : RingedSpace.{v}) (U : Opens X.carrier) :
    RingedSpace.{v} :=
  Formalization.Books.Sheaves.Unit22.ringedOpenSubspace X U

noncomputable abbrev ringedOpenInclusion (X : RingedSpace.{v}) (U : Opens X.carrier) :
    RingedSpaceHom (ringedOpenSubspace X U) X :=
  Formalization.Books.Sheaves.Unit22.ringedOpenInclusion X U

abbrev OpenModulePresheafExtensionData (X : RingedSpace.{v})
    (U : Opens X.carrier) :=
  Formalization.Books.Sheaves.Unit22.OpenModulePresheafExtensionData X U

theorem exists_openModulePresheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (OpenModulePresheafExtensionData X U) :=
  Formalization.Books.Sheaves.Unit22.exists_openModulePresheafExtensionByZero X U

noncomputable abbrev openModulePresheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    PMod (ringedOpenSubspace X U).structureSheaf.obj ⥤
      PMod X.structureSheaf.obj :=
  Formalization.Books.Sheaves.Unit22.openModulePresheafExtensionByZero X U

theorem openModulePresheafExtension_underlying_iso (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty
      (openModulePresheafExtensionByZero X U ⋙
          PresheafOfModules.toPresheaf X.structureSheaf.obj ≅
        PresheafOfModules.toPresheaf
            (ringedOpenSubspace X U).structureSheaf.obj ⋙
          openPresheafExtensionByInitial AddCommGrpCat U) := by
  exact (Classical.choice
    (exists_openModulePresheafExtensionByZero X U)).underlying_functor_iso

structure OpenModulePresheafAdjunctionData (X : RingedSpace.{v})
    (U : Opens X.carrier) where
  restriction : PMod X.structureSheaf.obj ⥤
    PMod (ringedOpenSubspace X U).structureSheaf.obj
  adjunction : openModulePresheafExtensionByZero X U ⊣ restriction

theorem exists_openModulePresheafAdjunctionData (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (OpenModulePresheafAdjunctionData X U) := by
  sorry

noncomputable def openModulePresheafAdjunctionData (X : RingedSpace.{v})
    (U : Opens X.carrier) : OpenModulePresheafAdjunctionData X U :=
  Classical.choice (exists_openModulePresheafAdjunctionData X U)

noncomputable abbrev openModulePresheafRestrictionFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    PMod X.structureSheaf.obj ⥤ PMod (ringedOpenSubspace X U).structureSheaf.obj :=
  (openModulePresheafAdjunctionData X U).restriction

noncomputable abbrev openModulePresheafExtensionAdjunction (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    openModulePresheafExtensionByZero X U ⊣
      openModulePresheafRestrictionFunctor X U :=
  (openModulePresheafAdjunctionData X U).adjunction

noncomputable abbrev openModuleExtensionFunctor (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf :=
  Formalization.Books.Sheaves.Unit22.openModuleExtensionFunctor X U

theorem exists_openModuleExtensionFunctor (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf) :=
  Formalization.Books.Sheaves.Unit22.exists_openModuleExtensionFunctor X U

noncomputable abbrev openModuleSheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf :=
  Formalization.Books.Sheaves.Unit22.openModuleSheafExtensionByZero X U

noncomputable abbrev openModuleRestrictionFunctor (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod X.structureSheaf ⥤ Mod (ringedOpenSubspace X U).structureSheaf :=
  Formalization.Books.Sheaves.Unit22.openModuleRestrictionFunctor X U

theorem exists_openModuleExtensionAdjunction (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (openModuleExtensionFunctor X U ⊣ openModuleRestrictionFunctor X U) :=
  Formalization.Books.Sheaves.Unit22.exists_openModuleExtensionAdjunction X U

noncomputable def openModuleExtensionAdjunction (X : RingedSpace.{v}) (U : Opens X.carrier) :
    openModuleExtensionFunctor X U ⊣ openModuleRestrictionFunctor X U :=
  Formalization.Books.Sheaves.Unit22.openModuleExtensionAdjunction X U

theorem openModuleExtension_stalk_zero (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) (x : X.carrier) (hx : x ∉ U) :
    Nonempty ((moduleStalkFunctor X.structureSheaf x).obj
      ((openModuleExtensionFunctor X U).obj F) ≅ 0) :=
  Formalization.Books.Sheaves.Unit22.openModuleExtension_stalk_zero X U F x hx

theorem openModuleExtension_stalk_iso (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) (x : X.carrier) (hx : x ∈ U) :
    Nonempty ((moduleStalkFunctor X.structureSheaf x).obj
      ((openModuleExtensionFunctor X U).obj F) ≅
      (ModuleCat.restrictScalars
        (moduleSheafFMapStalkScalarMap
          (ringedOpenInclusion X U).sharp ⟨x, hx⟩).hom).obj
        ((moduleStalkFunctor (ringedOpenSubspace X U).structureSheaf
          ⟨x, hx⟩).obj F)) :=
  Formalization.Books.Sheaves.Unit22.openModuleExtension_stalk_iso X U F x hx

theorem openModuleExtension_restrict_iso (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) :
    Nonempty ((openModuleRestrictionFunctor X U).obj
      ((openModuleExtensionFunctor X U).obj F) ≅ F) :=
  Formalization.Books.Sheaves.Unit22.openModuleExtension_restrict_iso X U F

/-! ## Essential images and the exactness warning -/

abbrev OpenEmptyStalkCondition {X : TopCat.{v}} (U : Opens X)
    (G : TopCat.Sheaf (Type v) X) : Prop :=
  Formalization.Books.Sheaves.Unit22.OpenEmptyStalkCondition U G

theorem openSetSheafExtension_fullFaithful {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    Nonempty (openSetSheafExtensionByEmpty U).FullyFaithful :=
  Formalization.Books.Sheaves.Unit22.openSetSheafExtension_fullFaithful U

theorem openSetSheafExtension_essentialImage {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (G : TopCat.Sheaf (Type v) X) :
    (∃ F, Nonempty ((openSetSheafExtensionByEmpty U).obj F ≅ G)) ↔
      OpenEmptyStalkCondition U G :=
  Formalization.Books.Sheaves.Unit22.openSetSheafExtension_essentialImage U G

theorem openAbelianSheafExtension_fullFaithful {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    Nonempty (openAbelianSheafExtensionFunctor U).FullyFaithful :=
  Formalization.Books.Sheaves.Unit22.openAbelianSheafExtension_fullFaithful U

abbrev OpenAbelianZeroStalkCondition {X : TopCat.{v}} (U : Opens X)
    (G : Ab X) : Prop :=
  Formalization.Books.Sheaves.Unit22.OpenAbelianZeroStalkCondition U G

theorem openAbelianSheafExtension_essentialImage {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    (G : Ab X) :
    (∃ F, Nonempty ((openAbelianSheafExtensionFunctor U).obj F ≅ G)) ↔
      OpenAbelianZeroStalkCondition U G :=
  Formalization.Books.Sheaves.Unit22.openAbelianSheafExtension_essentialImage U G

abbrev OpenInitialStalkCondition (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X) [HasColimits C]
    (G : TopCat.Sheaf C X) : Prop :=
  Formalization.Books.Sheaves.Unit22.OpenInitialStalkCondition C U G

theorem openAlgebraicSheafExtension_fullFaithful (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    Nonempty (openAlgebraicSheafExtensionFunctor C U).FullyFaithful :=
  Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtension_fullFaithful C U

theorem openAlgebraicSheafExtension_essentialImage (C : Type u)
    [Category.{v} C] [HasInitial C] [HasColimits C]
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (G : TopCat.Sheaf C X) :
    (∃ F, Nonempty ((openAlgebraicSheafExtensionFunctor C U).obj F ≅ G)) ↔
      OpenInitialStalkCondition C U G :=
  Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtension_essentialImage C U G

theorem openModuleExtension_fullFaithful (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (openModuleExtensionFunctor X U).FullyFaithful :=
  Formalization.Books.Sheaves.Unit22.openModuleExtension_fullFaithful X U

abbrev OpenModuleZeroStalkCondition (X : RingedSpace.{v})
    (U : Opens X.carrier) (G : Mod X.structureSheaf) : Prop :=
  Formalization.Books.Sheaves.Unit22.OpenModuleZeroStalkCondition X U G

theorem openModuleExtension_essentialImage (X : RingedSpace.{v})
    (U : Opens X.carrier) (G : Mod X.structureSheaf) :
    (∃ F, Nonempty ((openModuleExtensionFunctor X U).obj F ≅ G)) ↔
      OpenModuleZeroStalkCondition X U G :=
  Formalization.Books.Sheaves.Unit22.openModuleExtension_essentialImage X U G

theorem openSetSheafExtension_not_left_exact {X : TopCat.{v}} (U : Opens X)
    (hU : ∃ x : X, x ∉ U)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    ¬ PreservesFiniteLimits (openSetSheafExtensionByEmpty U) :=
  Formalization.Books.Sheaves.Unit22.openSetSheafExtension_not_left_exact U hU

/-!
The source's warning that algebraic `j_!` depends on the value category is
represented by the parameterized initial-object construction above: the same
underlying open and source sheaf can be extended using different initial
objects, so no underlying-set commutation is asserted here.
-/

end

end Formalization.Books.Sheaves.Unit31
