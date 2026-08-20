import Formalization.Books.Cohomology.Unit20.DerivedPullback
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
# Cohomology of Sheaves, Chapter 20, Section 2: Cohomology of unbounded complexes
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v

namespace Formalization.Books.Cohomology.Unit20

/-! The Grothendieck and functorial K-injective input. -/

theorem ringedSpaceModule_isGrothendieck
    (X : RingedSpace.{v}) :
    Nonempty (IsGrothendieckAbelian (Mod X.structureSheaf)) := by
  sorry

structure FunctorialKInjectiveResolutionData (X : RingedSpace.{v}) where
  resolution : ModuleComplex X ⥤ ModuleComplex X
  augmentation : 𝟭 (ModuleComplex X) ⟶ resolution
  augmentation_quasiIso : ∀ K : ModuleComplex X,
    QuasiIso (augmentation.app K)
  resolution_isKInjective : ∀ K : ModuleComplex X,
    ((resolution.obj K).IsKInjective)
  resolution_terms_injective : ∀ (K : ModuleComplex X) (n : ℤ),
    Injective ((resolution.obj K).X n)

theorem exists_functorialKInjectiveResolutionData
    (X : RingedSpace.{v}) :
    Nonempty (FunctorialKInjectiveResolutionData X) := by
  sorry

/-! Full derived pushforward and the three examples of unbounded derived
    functors in the source. -/

structure DerivedPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  functor : ModuleDerived X ⥤ ModuleDerived Y
  exact : ∃ h : functor.CommShift ℤ,
    letI : functor.CommShift ℤ := h
    functor.IsTriangulated
  adjoint_to_pullback : Nonempty (derivedPullback f ⊣ functor)

theorem exists_derivedPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (DerivedPushforwardData f) := by
  sorry

noncomputable def derivedPushforward
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  (Classical.choice (exists_derivedPushforwardData f)).functor

theorem derivedPushforward_isExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ∃ h : (derivedPushforward f).CommShift ℤ,
      letI : (derivedPushforward f).CommShift ℤ := h
      (derivedPushforward f).IsTriangulated := by
  sorry

structure DerivedPushforwardCohomologyData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  cohomology : ℤ → ModuleDerived X ⥤ Mod Y.structureSheaf
  cohomology_is_derived : ∀ n : ℤ,
    cohomology n = derivedPushforward f ⋙
      DerivedCategory.homologyFunctor (Mod Y.structureSheaf) n

theorem exists_derivedPushforwardCohomologyData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (DerivedPushforwardCohomologyData f) := by
  sorry

noncomputable def derivedPushforwardCohomology
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (n : ℤ) :
    ModuleDerived X ⥤ Mod Y.structureSheaf :=
  (Classical.choice (exists_derivedPushforwardCohomologyData f)).cohomology n

abbrev GlobalModuleCategory (X : RingedSpace.{v}) :=
  ModuleCat.{v} (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)))

abbrev GlobalDerived (X : RingedSpace.{v}) :=
  DerivedCategory (GlobalModuleCategory X)

structure DerivedSectionsData
    (X : RingedSpace.{v}) (U : Opens X.carrier) where
  functor : ModuleDerived X ⥤
    DerivedCategory (ModuleCat.{v} (X.structureSheaf.obj.obj (op U)))
  computes_on_KInjectives : Prop

theorem exists_derivedSectionsData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (DerivedSectionsData X U) := by
  sorry

noncomputable def derivedSections
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleDerived X ⥤
      DerivedCategory (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) :=
  (Classical.choice (exists_derivedSectionsData X U)).functor

noncomputable abbrev derivedGlobalSections (X : RingedSpace.{v}) :
    ModuleDerived X ⥤ GlobalDerived X :=
  derivedSections X (⊤ : Opens X.carrier)

structure DerivedSectionsCohomologyData
    (X : RingedSpace.{v}) (U : Opens X.carrier) where
  cohomology : ℤ → ModuleDerived X ⥤
    ModuleCat.{v} (X.structureSheaf.obj.obj (op U))
  cohomology_is_derived : ∀ n : ℤ,
    cohomology n = derivedSections X U ⋙
      DerivedCategory.homologyFunctor
        (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) n

theorem exists_derivedSectionsCohomologyData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (DerivedSectionsCohomologyData X U) := by
  sorry

noncomputable def derivedSectionsCohomology
    (X : RingedSpace.{v}) (U : Opens X.carrier) (n : ℤ) :
    ModuleDerived X ⥤
      ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  (Classical.choice (exists_derivedSectionsCohomologyData X U)).cohomology n

noncomputable abbrev globalCohomologyObject
    (X : RingedSpace.{v}) (n : ℤ) : ModuleDerived X ⥤ GlobalModuleCategory X :=
  derivedSectionsCohomology X (⊤ : Opens X.carrier) n

theorem derivedSections_isExact
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ∃ h : (derivedSections X U).CommShift ℤ,
      letI : (derivedSections X U).CommShift ℤ := h
      (derivedSections X U).IsTriangulated := by
  sorry

theorem derivedPullback_derivedPushforward_adjunction
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (derivedPullback f ⊣ derivedPushforward f) := by
  exact (Classical.choice (exists_derivedPushforwardData f)).adjoint_to_pullback

theorem derivedPushforward_comp
    {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z) :
    (derivedPushforward f ⋙ derivedPushforward g) =
      derivedPushforward (RingedSpaceHom.comp f g) := by
  sorry

/-! Base change maps and their two composition laws. -/

structure DerivedBaseChangeSquare where
  X' : RingedSpace.{v}
  X : RingedSpace.{v}
  S' : RingedSpace.{v}
  S : RingedSpace.{v}
  g' : RingedSpaceHom X' X
  f' : RingedSpaceHom X' S'
  g : RingedSpaceHom S' S
  f : RingedSpaceHom X S
  comm : RingedSpaceHom.comp g' f = RingedSpaceHom.comp f' g

theorem exists_baseChangeMap
    (B : DerivedBaseChangeSquare) (K : ModuleDerived B.X) :
    Nonempty ((derivedPullback B.g).obj ((derivedPushforward B.f).obj K) ⟶
      (derivedPushforward B.f').obj ((derivedPullback B.g').obj K)) := by
  sorry

noncomputable def baseChangeMap
    (B : DerivedBaseChangeSquare) (K : ModuleDerived B.X) :
    (derivedPullback B.g).obj ((derivedPushforward B.f).obj K) ⟶
      (derivedPushforward B.f').obj ((derivedPullback B.g').obj K) :=
  Classical.choice (exists_baseChangeMap B K)

structure BaseChangeCompositionData
    (B₁ B₂ : DerivedBaseChangeSquare) where
  outer_map : Prop
  composite_map : Prop
  commutes : outer_map = composite_map

theorem baseChange_composes_vertically
    (B₁ B₂ : DerivedBaseChangeSquare) :
    Nonempty (BaseChangeCompositionData B₁ B₂) := by
  sorry

theorem baseChange_composes_horizontally
    (B₁ B₂ : DerivedBaseChangeSquare) :
    Nonempty (BaseChangeCompositionData B₁ B₂) := by
  sorry

/-! Compatibility of the ordinary and derived push-pull maps. -/

structure PushPullCompatibilityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : ModuleDerived X) where
  derived_counit :
    (derivedPullback f).obj ((derivedPushforward f).obj K) ⟶ K
  complex_comparison :
    (derivedPullback f).obj ((derivedPushforward f).obj K) ⟶ K
  commutes : derived_counit = complex_comparison

theorem adjoints_push_pull_compatibility
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : ModuleDerived X) :
    Nonempty (PushPullCompatibilityData f K) := by
  sorry

/-! Relative and global cup products. -/

theorem exists_relativeCupProduct
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : ModuleDerived X) :
    Nonempty (derivedTensor Y ((derivedPushforward f).obj K)
        ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj (derivedTensor X K L)) := by
  sorry

noncomputable def relativeCupProduct
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : ModuleDerived X) :
    derivedTensor Y ((derivedPushforward f).obj K)
        ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj (derivedTensor X K L) :=
  Classical.choice (exists_relativeCupProduct f K L)

end Formalization.Books.Cohomology.Unit20
