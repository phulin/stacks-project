import Formalization.Books.Cohomology.Unit21.UnboundedComplexes
import Formalization.Books.Cohomology.Unit24.CupProduct
import Formalization.Books.Modules.Unit13.ClosedImmersions
import Formalization.Books.Sheaves.Unit31.OpenImmersions
import Formalization.Books.Derived.Unit06.Quotients

/-!
# Cohomology of Sheaves, Chapter 27: cohomology with support in a closed subset, II

This file records the unbounded derived-category statements in the source
section.  The sectionwise supported-module construction and the closed-space
module adjunction are reused from Modules 13; the unbounded derived and cup
product interfaces are kept in the chapter-owned namespace below.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Opposite
open Set
open TopologicalSpace
open Formalization.Books.Cohomology.Unit21
open Formalization.Books.Cohomology.Unit24
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit07
open Formalization.Books.Categories.Unit23
open Formalization.Books.Modules.Unit05
open Formalization.Books.Modules.Unit13
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit25

universe v u

namespace Formalization.Books.Cohomology.Unit27

/-! ## The source categories and supported sections -/

abbrev ModuleComplex (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleComplex X

abbrev ModuleHomotopy (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleHomotopy X

abbrev ModuleDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleDerived X

abbrev GlobalModuleCategory (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.GlobalModuleCategory X

abbrev GlobalDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.GlobalDerived X

/-- The open complement of a closed subset. -/
def supportComplementOpen {X : RingedSpace.{v}} (Z : Set X)
    (hZ : IsClosed Z) : Opens X.carrier :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The ringed space and inclusion associated to the open complement. -/
abbrev supportComplementSpace {X : RingedSpace.{v}} (Z : Set X)
  (hZ : IsClosed Z) : RingedSpace :=
  Formalization.Books.Sheaves.Unit22.ringedOpenSubspace X
    (supportComplementOpen Z hZ)

abbrev supportComplementInclusion {X : RingedSpace.{v}} (Z : Set X)
    (hZ : IsClosed Z) : RingedSpaceHom (supportComplementSpace Z hZ) X :=
  Formalization.Books.Sheaves.Unit22.ringedOpenInclusion X
    (supportComplementOpen Z hZ)

/-- The sheaf of modules of sections supported in `Z`, viewed on the closed
subspace.  This is the canonical right adjoint from Modules 13. -/
abbrev supportedSectionsFunctor {X : RingedSpace.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    Mod X.structureSheaf ⥤
      Mod (ringedClosedSubspace X Z).structureSheaf :=
  moduleSectionsWithSupportFunctor X Z hZ

/-- The sectionwise module used for `Γ_Z(X, -)`. -/
noncomputable def supportedGlobalSectionsObject
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) : GlobalModuleCategory X :=
  ModuleCat.of (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)))
    (moduleSectionsWithSupportInClosedSubmodule (F := F) Z
      (⊤ : Opens X.carrier) : Type v)

/-! The module-valued global-sections functor is not duplicated: its object
assignment is fixed by the canonical section submodule, and the functorial
extension is recorded by this small interface. -/

structure SupportedGlobalSectionsData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) where
  functor : Mod X.structureSheaf ⥤ GlobalModuleCategory X
  object_iso : ∀ F : Mod X.structureSheaf,
    Nonempty (functor.obj F ≅ supportedGlobalSectionsObject Z hZ F)

theorem exists_supportedGlobalSectionsData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (SupportedGlobalSectionsData X Z hZ) := by
  sorry

noncomputable def supportedGlobalSectionsData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    SupportedGlobalSectionsData X Z hZ :=
  Classical.choice (exists_supportedGlobalSectionsData X Z hZ)

noncomputable abbrev supportedGlobalSectionsFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Mod X.structureSheaf ⥤ GlobalModuleCategory X :=
  (supportedGlobalSectionsData X Z hZ).functor

theorem supportedGlobalSectionsFunctor_isLeftExact
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    IsLeftExact (supportedGlobalSectionsFunctor X Z hZ) := by
  sorry

/- The source's warning that this left-exact functor need not be exact is
   already represented by `not_allModuleSupportedSectionsFunctorsExact` in
   Modules 13, for the canonical functor used by this abbreviation. -/

/-- The derived object whose cohomology is `H^q_Z(X, K)`. -/
structure SupportDerivedData
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) where
  data : UnboundedRightDerivedData
    (A := Mod X.structureSheaf)
    (D := ModuleDerived (ringedClosedSubspace X Z))
    (by
      letI : (supportedSectionsFunctor Z hZ).Additive :=
        left_or_right_exact_additive (supportedSectionsFunctor Z hZ)
          (Or.inl (moduleSectionsWithSupportFunctor_isLeftExact X Z hZ))
      exact additiveHomotopyFunctor (supportedSectionsFunctor Z hZ) ⋙
        DerivedCategory.Qh)

theorem exists_supportDerivedData
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (SupportDerivedData Z hZ) := by
  sorry

noncomputable def supportDerivedFunctor
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) :
    ModuleDerived X ⥤ ModuleDerived (ringedClosedSubspace X Z) :=
  (Classical.choice (exists_supportDerivedData Z hZ)).data.functor

noncomputable abbrev supportSheafCohomologyFunctor
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) (q : ℤ) :
  Mod X.structureSheaf ⥤
      Mod (ringedClosedSubspace X Z).structureSheaf :=
  higherRightDerivedFunctor
    (supportedSectionsFunctor Z hZ)
    (moduleSectionsWithSupportFunctor_isLeftExact X Z hZ) q

abbrev supportSheafCohomologyObject
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) (q : ℤ) :
    Mod (ringedClosedSubspace X Z).structureSheaf :=
  (supportSheafCohomologyFunctor Z hZ q).obj F

theorem supportSheafCohomologyFunctor_zero
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (supportSheafCohomologyFunctor Z hZ 0 ≅
      supportedSectionsFunctor Z hZ) := by
  sorry

/-! ## `RΓ_Z`, `D_Z`, and the adjunction -/

structure SupportGlobalDerivedData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) where
  data : UnboundedRightDerivedData
    (A := Mod X.structureSheaf) (D := GlobalDerived X)
    (by
      letI : (supportedGlobalSectionsFunctor X Z hZ).Additive :=
        left_or_right_exact_additive (supportedGlobalSectionsFunctor X Z hZ)
          (Or.inl (supportedGlobalSectionsFunctor_isLeftExact X Z hZ))
      exact additiveHomotopyFunctor (supportedGlobalSectionsFunctor X Z hZ) ⋙
        DerivedCategory.Qh)

theorem exists_supportGlobalDerivedData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (SupportGlobalDerivedData X Z hZ) := by
  sorry

noncomputable def supportGlobalDerivedFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    ModuleDerived X ⥤ GlobalDerived X :=
  (Classical.choice (exists_supportGlobalDerivedData X Z hZ)).data.functor

noncomputable abbrev supportGlobalCohomologyFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) (q : ℤ) :
    ModuleDerived X ⥤ GlobalModuleCategory X :=
  supportGlobalDerivedFunctor X Z hZ ⋙
    DerivedCategory.homologyFunctor (GlobalModuleCategory X) q

abbrev supportGlobalCohomologyObject
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K : ModuleDerived X) (q : ℤ) : GlobalModuleCategory X :=
  (supportGlobalCohomologyFunctor X Z hZ q).obj K

abbrev supportGlobalCohomologyElement
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K : ModuleDerived X) (q : ℤ) : Type v :=
  (supportGlobalCohomologyObject X Z hZ K q : Type v)

abbrev ordinaryGlobalCohomologyElement
    (X : RingedSpace.{v}) (K : ModuleDerived X) (q : ℤ) :=
  Formalization.Books.Cohomology.Unit24.globalCohomologyElement X K q

/-- The strictly full subcategory `D_Z(O_X)`. -/
def derivedSupportProperty (X : RingedSpace.{v}) (Z : Set X)
    (_hZ : IsClosed Z) : ObjectProperty (ModuleDerived X) :=
  fun K => ∀ q : ℤ,
    moduleSupport ((DerivedCategory.homologyFunctor
      (Mod X.structureSheaf) q).obj K) ⊆ Z

abbrev derivedSupportSubcategory (X : RingedSpace.{v}) (Z : Set X)
    (hZ : IsClosed Z) :=
  (derivedSupportProperty X Z hZ).FullSubcategory

theorem derivedSupportSubcategory_is_strictly_full_saturated_triangulated
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    IsStrictlyFullSaturatedPretriangulated (derivedSupportProperty X Z hZ) := by
  sorry

theorem supportDerivedFunctor_right_adjoint
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (derivedPushforward (ringedClosedInclusion X Z) ⊣
      supportDerivedFunctor Z hZ) := by
  sorry

noncomputable def supportDerivedAdjunction
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) :
    derivedPushforward (ringedClosedInclusion X Z) ⊣
      supportDerivedFunctor Z hZ :=
  Classical.choice (supportDerivedFunctor_right_adjoint Z hZ)

theorem supportDerivedFunctor_on_pushforward
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (K : ModuleDerived (ringedClosedSubspace X Z)) :
  Nonempty ((supportDerivedFunctor Z hZ).obj
      ((derivedPushforward (ringedClosedInclusion X Z)).obj K) ≅ K) := by
  sorry

/-- The closed-immersion pushforward identifies the derived category on `Z`
with the strictly full subcategory of complexes whose cohomology is supported
on `Z`.  The preceding adjunction and counit isomorphism record that this is
the equivalence induced by `i_*`, while this declaration records the source's
quasi-inverse statement as an actual categorical equivalence. -/
theorem supportDerived_pushforward_equivalence
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (ModuleDerived (ringedClosedSubspace X Z) ≌
      derivedSupportSubcategory X Z hZ) := by
  sorry

noncomputable def supportDerivedPushforwardEquivalence
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) :
    ModuleDerived (ringedClosedSubspace X Z) ≌
      derivedSupportSubcategory X Z hZ :=
  Classical.choice (supportDerived_pushforward_equivalence Z hZ)

structure SupportSubcategoryProjectionData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) where
  projection : ModuleDerived X ⥤ derivedSupportSubcategory X Z hZ
  adjunction : (derivedSupportProperty X Z hZ).ι ⊣ projection
  projection_obj_iso : ∀ K : ModuleDerived X,
    Nonempty ((derivedSupportProperty X Z hZ).ι.obj (projection.obj K) ≅
      (derivedPushforward (ringedClosedInclusion X Z)).obj
        ((supportDerivedFunctor Z hZ).obj K))

theorem supportSubcategory_projection_right_adjoint
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (SupportSubcategoryProjectionData X Z hZ) := by
  sorry

noncomputable def supportSubcategoryProjection
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    ModuleDerived X ⥤ derivedSupportSubcategory X Z hZ :=
  (Classical.choice (supportSubcategory_projection_right_adjoint X Z hZ)).projection

theorem supportSheafCohomology_pushforward_isZero
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (G : Mod (ringedClosedSubspace X Z).structureSheaf) (p : ℤ)
    (hp : 0 < p) :
    IsZero ((supportSheafCohomologyFunctor Z hZ p).obj
      ((Formalization.Books.Sheaves.Unit26.ringedSpaceModulePushforward
        (ringedClosedInclusion X Z)).obj G)) := by
  sorry

/-! ## Resolution and localization interfaces -/

noncomputable def supportComplexFunctor
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z) :
    ModuleComplex X ⥤ ModuleComplex (ringedClosedSubspace X Z) := by
  letI : (supportedSectionsFunctor Z hZ).Additive :=
    left_or_right_exact_additive (supportedSectionsFunctor Z hZ)
      (Or.inl (moduleSectionsWithSupportFunctor_isLeftExact X Z hZ))
  exact (supportedSectionsFunctor Z hZ).mapHomologicalComplex (ComplexShape.up ℤ)

theorem supportComplexFunctor_preserves_KInjective
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (I : ModuleComplex X) (hI : I.IsKInjective) :
    ((supportComplexFunctor Z hZ).obj I).IsKInjective := by
  sorry

/- The scalar comparison between sections on the closed subspace and the
   ambient global-section category is a separate interface.  The local-to-
   global theorem identifies this functor with `RΓ_Z`. -/
structure ClosedGlobalDerivedData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) where
  functor : ModuleDerived X ⥤ GlobalDerived X

theorem exists_closedGlobalDerivedData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (ClosedGlobalDerivedData X Z hZ) := by
  sorry

noncomputable def closedGlobalDerivedFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    ModuleDerived X ⥤ GlobalDerived X :=
  (Classical.choice (exists_closedGlobalDerivedData X Z hZ)).functor

noncomputable def complementGlobalDerivedFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    ModuleDerived X ⥤ GlobalDerived X :=
  derivedPullback (supportComplementInclusion Z hZ) ⋙
    derivedPushforward (supportComplementInclusion Z hZ) ⋙
      derivedGlobalSections X

theorem supportGlobalDerived_local_to_global
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (supportGlobalDerivedFunctor X Z hZ ≅
      closedGlobalDerivedFunctor X Z hZ) := by
  sorry

noncomputable def supportGlobalDerivedLocalToGlobal
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    supportGlobalDerivedFunctor X Z hZ ≅ closedGlobalDerivedFunctor X Z hZ :=
  Classical.choice (supportGlobalDerived_local_to_global X Z hZ)

structure SupportGlobalLocalizationTriangle
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K : ModuleDerived X) where
  triangle : Triangle (GlobalDerived X)
  obj₁ : triangle.obj₁ = (supportGlobalDerivedFunctor X Z hZ).obj K
  obj₂ : triangle.obj₂ = (derivedGlobalSections X).obj K
  obj₃ : triangle.obj₃ =
    (complementGlobalDerivedFunctor X Z hZ).obj K
  distinguished : triangle ∈ distTriang (GlobalDerived X)

theorem supportGlobal_localization_triangle
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K : ModuleDerived X) :
    Nonempty (SupportGlobalLocalizationTriangle X Z hZ K) := by
  sorry

structure SupportSheafLocalizationTriangle
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K : ModuleDerived X) where
  triangle : Triangle (ModuleDerived X)
  obj₁ : triangle.obj₁ =
    (derivedPushforward (ringedClosedInclusion X Z)).obj
      ((supportDerivedFunctor Z hZ).obj K)
  obj₂ : triangle.obj₂ = K
  obj₃ : triangle.obj₃ =
    (derivedPushforward (supportComplementInclusion Z hZ)).obj
      ((derivedPullback (supportComplementInclusion Z hZ)).obj K)
  distinguished : triangle ∈ distTriang (ModuleDerived X)

theorem supportSheaf_localization_triangle
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K : ModuleDerived X) :
    Nonempty (SupportSheafLocalizationTriangle X Z hZ K) := by
  sorry

theorem supportDerivedFunctor_vanishes_on_disjoint_open
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (U : Opens X.carrier) (hUZ : Disjoint (U : Set X) Z)
    (K : ModuleDerived
      (Formalization.Books.Sheaves.Unit22.ringedOpenSubspace X U)) :
    IsZero ((supportDerivedFunctor Z hZ).obj
      ((derivedPushforward
        (Formalization.Books.Sheaves.Unit22.ringedOpenInclusion X U)).obj K)) := by
  sorry

/-! ## Forgetting the module structure and the two cup-product statements -/

abbrev AbelianSheafDerived (X : RingedSpace.{v}) :=
  DerivedCategory (Ab X.carrier)

abbrev AbelianGlobalDerived := DerivedCategory AddCommGrpCat.{v}

/- The forgetful functors from derived module categories and the comparison
 maps into the derived categories of abelian sheaves/groups are kept as an
 interface here because the unbounded derived forgetful construction is not
 supplied by the earlier chapters.  The target categories and the maps are
 nevertheless the source's abelianization comparison, rather than endomaps of
 the module-valued derived functors. -/
structure AbelianSupportComparisonData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) where
  globalForget : GlobalDerived X ⥤ AbelianGlobalDerived
  sheafForget : ModuleDerived (ringedClosedSubspace X Z) ⥤
    AbelianSheafDerived (ringedClosedSubspace X Z)
  abelianGlobal : ModuleDerived X ⥤ AbelianGlobalDerived
  abelianSheaf : ModuleDerived X ⥤
    AbelianSheafDerived (ringedClosedSubspace X Z)
  globalComparison :
    supportGlobalDerivedFunctor X Z hZ ⋙ globalForget ⟶ abelianGlobal
  sheafComparison :
    supportDerivedFunctor Z hZ ⋙ sheafForget ⟶ abelianSheaf
  globalComparison_isIso : IsIso globalComparison
  sheafComparison_isIso : IsIso sheafComparison

theorem abelian_support_comparison
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (AbelianSupportComparisonData X Z hZ) := by
  sorry

noncomputable def abelianSupportComparison
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    AbelianSupportComparisonData X Z hZ :=
  Classical.choice (abelian_support_comparison X Z hZ)

structure SupportCupProductData
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (K M : ModuleDerived X) where
  map :
    (derivedTensor (ringedClosedSubspace X Z)
      ((derivedPullback (ringedClosedInclusion X Z)).obj K)
      ((supportDerivedFunctor Z hZ).obj M)) ⟶
      (supportDerivedFunctor Z hZ).obj (derivedTensor X K M)

theorem exists_supportCupProductData
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (K M : ModuleDerived X) :
    Nonempty (SupportCupProductData Z hZ K M) := by
  sorry

noncomputable def supportCupProduct
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (K M : ModuleDerived X) :
    (derivedTensor (ringedClosedSubspace X Z)
      ((derivedPullback (ringedClosedInclusion X Z)).obj K)
      ((supportDerivedFunctor Z hZ).obj M)) ⟶
      (supportDerivedFunctor Z hZ).obj (derivedTensor X K M) :=
  (Classical.choice (exists_supportCupProductData Z hZ K M)).map

structure SupportGlobalCupProductData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K M : ModuleDerived X) (a b : ℤ) where
  pairing :
    ordinaryGlobalCohomologyElement X K a →
      supportGlobalCohomologyElement X Z hZ M b →
        supportGlobalCohomologyElement X Z hZ (derivedTensor X K M) (a + b)

theorem exists_supportGlobalCupProductData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K M : ModuleDerived X) (a b : ℤ) :
    Nonempty (SupportGlobalCupProductData X Z hZ K M a b) := by
  sorry

noncomputable def supportGlobalCupProduct
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K M : ModuleDerived X) (a b : ℤ) :
    ordinaryGlobalCohomologyElement X K a →
      supportGlobalCohomologyElement X Z hZ M b →
        supportGlobalCohomologyElement X Z hZ (derivedTensor X K M) (a + b) :=
  (Classical.choice (exists_supportGlobalCupProductData X Z hZ K M a b)).pairing

structure SupportCupProductCompatibilityData
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K M : ModuleDerived X) (a b : ℤ) where
  supportToOrdinary :
    supportGlobalCohomologyElement X Z hZ M b →
      ordinaryGlobalCohomologyElement X M b
  supportTensorToOrdinary :
    supportGlobalCohomologyElement X Z hZ (derivedTensor X K M) (a + b) →
      ordinaryGlobalCohomologyElement X (derivedTensor X K M) (a + b)
  commutes : ∀ x y,
    supportTensorToOrdinary
        (supportGlobalCupProduct X Z hZ K M a b x y) =
      Formalization.Books.Cohomology.Unit24.cupPairing X K M a b x
        (supportToOrdinary y)

theorem support_cup_product_compatibility
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (K M : ModuleDerived X) (a b : ℤ) :
    Nonempty (SupportCupProductCompatibilityData X Z hZ K M a b) := by
  sorry

/-! ## Functoriality in the ambient ringed space -/

structure SupportMorphism where
  X' : RingedSpace.{v}
  Xbase : RingedSpace.{v}
  f : RingedSpaceHom X' Xbase
  Z : Set Xbase
  hZ : IsClosed Z
  Z' : Set X'
  hZ' : IsClosed Z'
  preimage : Z' = f.continuous ⁻¹' Z
  restriction : RingedSpaceHom (ringedClosedSubspace X' Z')
    (ringedClosedSubspace Xbase Z)
  restriction_commutes :
    RingedSpaceHom.comp restriction (ringedClosedInclusion Xbase Z) =
      RingedSpaceHom.comp (ringedClosedInclusion X' Z') f

structure SupportFunctorialMapData
    (S : SupportMorphism) (K : ModuleDerived S.Xbase) where
  map :
    (derivedPullback S.restriction).obj
        ((supportDerivedFunctor S.Z S.hZ).obj K) ⟶
      (supportDerivedFunctor S.Z' S.hZ').obj
        ((derivedPullback S.f).obj K)

theorem exists_supportFunctorialMap
    (S : SupportMorphism) (K : ModuleDerived S.Xbase) :
    Nonempty (SupportFunctorialMapData S K) := by
  sorry

noncomputable def supportFunctorialMap
    (S : SupportMorphism) (K : ModuleDerived S.Xbase) :
    (derivedPullback S.restriction).obj
        ((supportDerivedFunctor S.Z S.hZ).obj K) ⟶
      (supportDerivedFunctor S.Z' S.hZ').obj
        ((derivedPullback S.f).obj K) :=
  (Classical.choice (exists_supportFunctorialMap S K)).map

structure SupportFunctorialCohomologyData
    (S : SupportMorphism) (K : ModuleDerived S.Xbase) (p : ℤ) where
  supportMap :
    supportGlobalCohomologyElement S.Xbase S.Z S.hZ K p →
      supportGlobalCohomologyElement S.X' S.Z' S.hZ'
        ((derivedPullback S.f).obj K) p
  ordinaryMap :
    ordinaryGlobalCohomologyElement S.Xbase K p →
      ordinaryGlobalCohomologyElement S.X' ((derivedPullback S.f).obj K) p
  forget :
    supportGlobalCohomologyElement S.Xbase S.Z S.hZ K p →
      ordinaryGlobalCohomologyElement S.Xbase K p
  forget' :
    supportGlobalCohomologyElement S.X' S.Z' S.hZ'
      ((derivedPullback S.f).obj K) p →
      ordinaryGlobalCohomologyElement S.X' ((derivedPullback S.f).obj K) p
  commutes : ∀ x, forget' (supportMap x) = ordinaryMap (forget x)

theorem support_functorial_cohomology_commutes
    (S : SupportMorphism) (K : ModuleDerived S.Xbase) (p : ℤ) :
    Nonempty (SupportFunctorialCohomologyData S K p) := by
  sorry

end Formalization.Books.Cohomology.Unit27
