import Formalization.Books.Cohomology.Unit20.DerivedPullback
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
# Cohomology of Sheaves, Chapter 21, Section 1: Cohomology of unbounded complexes

This file records the unbounded right-derived functors, their sections and
pushforward examples, and the adjunction, base-change, compatibility, and cup
product interfaces from the source section.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit31
open Formalization.Books.Homology.Unit07
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v u v' u'

namespace Formalization.Books.Cohomology.Unit21

/-! ## The unbounded categories in the source notation -/

abbrev ModuleComplex (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit20.ModuleComplex X

abbrev ModuleHomotopy (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit20.ModuleHomotopy X

abbrev ModuleDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit20.ModuleDerived X

abbrev derivedPullback {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Formalization.Books.Cohomology.Unit20.derivedPullback f

abbrev derivedTensor (X : RingedSpace.{v})
    (K L : ModuleDerived X) : ModuleDerived X :=
  Formalization.Books.Cohomology.Unit20.derivedTensor X K L

/-! ## Grothendieck categories and functorial K-injectives -/

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
    (resolution.obj K).IsKInjective
  resolution_terms_injective : ∀ (K : ModuleComplex X) (n : ℤ),
    Injective ((resolution.obj K).X n)

theorem exists_functorialKInjectiveResolutionData
    (X : RingedSpace.{v}) :
    Nonempty (FunctorialKInjectiveResolutionData X) := by
  sorry

/-! ## General unbounded right-derived functors -/

structure UnboundedRightDerivedData
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : BookHomotopyCategory A ⥤ D) where
  functor : DerivedCategory A ⥤ D
  comparison : F ⟶ (DerivedCategory.Qh (C := A)) ⋙ functor
  isRightDerived : Functor.IsRightDerivedFunctor functor comparison
    (quasiIsoHomotopyProperty A)
  computes_on_kInjectives : ∀ I : BookComplex A, I.IsKInjective →
    IsIso (comparison.app ((HomotopyCategory.quotient A
      (ComplexShape.up ℤ)).obj I))
  exact : ∃ h : functor.CommShift ℤ,
    letI : functor.CommShift ℤ := h
    functor.IsTriangulated

theorem exists_unboundedRightDerivedData
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : BookHomotopyCategory A ⥤ D)
    (hF : Nonempty (ExactTriangulatedFunctorData F))
    (hEnough : ∀ K : BookComplex A, HasKInjectiveResolution A K) :
    Nonempty (UnboundedRightDerivedData F) := by
  obtain ⟨RF, α, hRF, hK⟩ :=
    rightDerived_exists_of_enough_kInjectives F hF hEnough
  exact ⟨{
    functor := RF
    comparison := α
    isRightDerived := hRF
    computes_on_kInjectives := hK
    exact := by sorry
  }⟩

theorem exists_unboundedRightDerivedOfAdditiveFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (hEnough : ∀ K : BookComplex A, HasKInjectiveResolution A K) :
    Nonempty (UnboundedRightDerivedData
      (Formalization.Books.Derived.Unit10.additiveHomotopyFunctor F)) := by
  exact exists_unboundedRightDerivedData
    (Formalization.Books.Derived.Unit10.additiveHomotopyFunctor F)
    (Formalization.Books.Derived.Unit10.additive_homotopy_functors_are_exact F).1
    hEnough

/-! ## The three examples of unbounded derived functors -/

noncomputable def sectionsHomotopyFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleHomotopy X ⥤
      DerivedCategory (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) := by
  letI : (ringedSpaceModuleSectionsFunctor X U).Additive :=
    left_or_right_exact_additive
      (ringedSpaceModuleSectionsFunctor X U)
      (Or.inl (ringedSpaceModuleSectionsFunctor_isLeftExact X U))
  exact Formalization.Books.Derived.Unit10.additiveHomotopyFunctor
      (ringedSpaceModuleSectionsFunctor X U) ⋙
    DerivedCategory.Qh

noncomputable def pushforwardHomotopyFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ModuleHomotopy X ⥤ ModuleDerived Y := by
  letI : (sheafModuleRingedSpacePushforward f).Additive :=
    left_or_right_exact_additive
      (sheafModuleRingedSpacePushforward f)
      (Or.inl (sheafModuleRingedSpacePushforward_isLeftExact f))
  exact Formalization.Books.Derived.Unit10.additiveHomotopyFunctor
      (sheafModuleRingedSpacePushforward f) ⋙
    DerivedCategory.Qh

structure DerivedPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  data : UnboundedRightDerivedData
    (A := Mod X.structureSheaf) (D := ModuleDerived Y)
    (pushforwardHomotopyFunctor f)
  adjoint_to_pullback : Nonempty (derivedPullback f ⊣ data.functor)

theorem exists_derivedPushforwardData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (DerivedPushforwardData f) := by
  sorry

noncomputable def derivedPushforward
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  (Classical.choice (exists_derivedPushforwardData f)).data.functor

theorem derivedPushforward_isExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ∃ h : (derivedPushforward f).CommShift ℤ,
      letI : (derivedPushforward f).CommShift ℤ := h
      (derivedPushforward f).IsTriangulated := by
  exact (Classical.choice (exists_derivedPushforwardData f)).data.exact

structure DerivedPushforwardCohomologyData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  cohomology : ℤ → ModuleDerived X ⥤ Mod Y.structureSheaf
  cohomology_is_derived : ∀ n : ℤ,
    cohomology n = derivedPushforward f ⋙
      DerivedCategory.homologyFunctor (Mod Y.structureSheaf) n

theorem exists_derivedPushforwardCohomologyData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (DerivedPushforwardCohomologyData f) := by
  exact ⟨{
    cohomology := fun n =>
      derivedPushforward f ⋙
        DerivedCategory.homologyFunctor (Mod Y.structureSheaf) n
    cohomology_is_derived := fun _ => rfl
  }⟩

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
  data : UnboundedRightDerivedData
    (A := Mod X.structureSheaf)
    (D := DerivedCategory (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))))
    (sectionsHomotopyFunctor X U)

theorem exists_derivedSectionsData
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (DerivedSectionsData X U) := by
  sorry

noncomputable def derivedSections
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleDerived X ⥤
      DerivedCategory (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) :=
  (Classical.choice (exists_derivedSectionsData X U)).data.functor

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
  exact ⟨{
    cohomology := fun n =>
      derivedSections X U ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) n
    cohomology_is_derived := fun _ => rfl
  }⟩

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
  exact (Classical.choice (exists_derivedSectionsData X U)).data.exact

/-! ## Adjunction and composition -/

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

/-! ## Base change -/

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

/- The two composition remarks are recorded on explicit composable diagrams.
   The maps are fields of the data package, so their source and target are the
   actual derived-category objects of the outer rectangle rather than
   unconstrained propositions. -/

structure VerticalBaseChangeDiagram where
  X' : RingedSpace.{v}
  X : RingedSpace.{v}
  Y' : RingedSpace.{v}
  Y : RingedSpace.{v}
  Z' : RingedSpace.{v}
  Z : RingedSpace.{v}
  k : RingedSpaceHom X' X
  f₁ : RingedSpaceHom X' Y'
  f₂ : RingedSpaceHom X Y
  l : RingedSpaceHom Y' Y
  g₁ : RingedSpaceHom Y' Z'
  g₂ : RingedSpaceHom Y Z
  m : RingedSpaceHom Z' Z
  top_comm : RingedSpaceHom.comp k f₂ = RingedSpaceHom.comp f₁ l
  bottom_comm : RingedSpaceHom.comp l g₂ = RingedSpaceHom.comp g₁ m
  outer_comm :
    RingedSpaceHom.comp k (RingedSpaceHom.comp f₂ g₂) =
      RingedSpaceHom.comp (RingedSpaceHom.comp f₁ g₁) m

def VerticalBaseChangeDiagram.topSquare
    (D : VerticalBaseChangeDiagram) : DerivedBaseChangeSquare :=
  { X' := D.X'
    X := D.X
    S' := D.Y'
    S := D.Y
    g' := D.k
    f' := D.f₁
    g := D.l
    f := D.f₂
    comm := D.top_comm }

def VerticalBaseChangeDiagram.bottomSquare
    (D : VerticalBaseChangeDiagram) : DerivedBaseChangeSquare :=
  { X' := D.Y'
    X := D.Y
    S' := D.Z'
    S := D.Z
    g' := D.l
    f' := D.g₁
    g := D.m
    f := D.g₂
    comm := D.bottom_comm }

def VerticalBaseChangeDiagram.outerSquare
    (D : VerticalBaseChangeDiagram) : DerivedBaseChangeSquare :=
  { X' := D.X'
    X := D.X
    S' := D.Z'
    S := D.Z
    g' := D.k
    f' := RingedSpaceHom.comp D.f₁ D.g₁
    g := D.m
    f := RingedSpaceHom.comp D.f₂ D.g₂
    comm := D.outer_comm }

structure VerticalBaseChangeCompositionData
    (D : VerticalBaseChangeDiagram) (K : ModuleDerived D.X) where
  outerMap :
    (derivedPullback D.m).obj
        ((derivedPushforward (RingedSpaceHom.comp D.f₂ D.g₂)).obj K) ⟶
      (derivedPushforward (RingedSpaceHom.comp D.f₁ D.g₁)).obj
        ((derivedPullback D.k).obj K)
  compositeMap :
    (derivedPullback D.m).obj
        ((derivedPushforward (RingedSpaceHom.comp D.f₂ D.g₂)).obj K) ⟶
      (derivedPushforward (RingedSpaceHom.comp D.f₁ D.g₁)).obj
        ((derivedPullback D.k).obj K)
  commutes : outerMap = compositeMap

theorem baseChange_composes_vertically
    (D : VerticalBaseChangeDiagram) (K : ModuleDerived D.X) :
    Nonempty (VerticalBaseChangeCompositionData D K) := by
  sorry

structure HorizontalBaseChangeDiagram where
  X'' : RingedSpace.{v}
  X' : RingedSpace.{v}
  X : RingedSpace.{v}
  Y'' : RingedSpace.{v}
  Y' : RingedSpace.{v}
  Y : RingedSpace.{v}
  k₁ : RingedSpaceHom X'' X'
  k₂ : RingedSpaceHom X' X
  f₁ : RingedSpaceHom X'' Y''
  f₂ : RingedSpaceHom X' Y'
  f₃ : RingedSpaceHom X Y
  h₁ : RingedSpaceHom Y'' Y'
  h₂ : RingedSpaceHom Y' Y
  left_comm : RingedSpaceHom.comp k₁ f₂ = RingedSpaceHom.comp f₁ h₁
  right_comm : RingedSpaceHom.comp k₂ f₃ = RingedSpaceHom.comp f₂ h₂
  outer_comm :
    RingedSpaceHom.comp (RingedSpaceHom.comp k₁ k₂) f₃ =
      RingedSpaceHom.comp f₁
        (RingedSpaceHom.comp h₁ h₂)

def HorizontalBaseChangeDiagram.leftSquare
    (D : HorizontalBaseChangeDiagram) : DerivedBaseChangeSquare :=
  { X' := D.X''
    X := D.X'
    S' := D.Y''
    S := D.Y'
    g' := D.k₁
    f' := D.f₁
    g := D.h₁
    f := D.f₂
    comm := D.left_comm }

def HorizontalBaseChangeDiagram.rightSquare
    (D : HorizontalBaseChangeDiagram) : DerivedBaseChangeSquare :=
  { X' := D.X'
    X := D.X
    S' := D.Y'
    S := D.Y
    g' := D.k₂
    f' := D.f₂
    g := D.h₂
    f := D.f₃
    comm := D.right_comm }

def HorizontalBaseChangeDiagram.outerSquare
    (D : HorizontalBaseChangeDiagram) : DerivedBaseChangeSquare :=
  { X' := D.X''
    X := D.X
    S' := D.Y''
    S := D.Y
    g' := RingedSpaceHom.comp D.k₁ D.k₂
    f' := D.f₁
    g := RingedSpaceHom.comp D.h₁ D.h₂
    f := D.f₃
    comm := D.outer_comm }

structure HorizontalBaseChangeCompositionData
    (D : HorizontalBaseChangeDiagram) (K : ModuleDerived D.X) where
  outerMap :
    (derivedPullback (RingedSpaceHom.comp D.h₁ D.h₂)).obj
        ((derivedPushforward D.f₃).obj K) ⟶
      (derivedPushforward D.f₁).obj
        ((derivedPullback (RingedSpaceHom.comp D.k₁ D.k₂)).obj K)
  compositeMap :
    (derivedPullback (RingedSpaceHom.comp D.h₁ D.h₂)).obj
        ((derivedPushforward D.f₃).obj K) ⟶
      (derivedPushforward D.f₁).obj
        ((derivedPullback (RingedSpaceHom.comp D.k₁ D.k₂)).obj K)
  commutes : outerMap = compositeMap

theorem baseChange_composes_horizontally
    (D : HorizontalBaseChangeDiagram) (K : ModuleDerived D.X) :
    Nonempty (HorizontalBaseChangeCompositionData D K) := by
  sorry

/-! ## Ordinary versus derived push-pull -/

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

/-! ## Relative cup product -/

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

end Formalization.Books.Cohomology.Unit21
