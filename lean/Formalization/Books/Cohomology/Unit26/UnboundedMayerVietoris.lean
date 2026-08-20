import Formalization.Books.Cohomology.Unit24.CupProduct
import Formalization.Books.Cohomology.Unit25.KInjectiveProperties
import Formalization.Books.Derived.Unit27.ExtGroups

/-!
# Cohomology of Sheaves, Chapter 26: Unbounded Mayer--Vietoris

This file records the unbounded Mayer--Vietoris triangles, the induced derived
Hom and cohomology sequences, the relative pushforward version, the supported
restriction comparison, and the cup-product map of triangles.  The earlier
chapters provide the derived open restriction, extension-by-zero, pushforward,
global-sections, support, and cup-product interfaces used here.
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
open Formalization.Books.Cohomology.Unit25
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit27
open Formalization.Books.Homology.Unit07
open Formalization.Books.Modules.Unit05
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v

namespace Formalization.Books.Cohomology.Unit26

/-! ## Common derived-category notation -/

abbrev ModuleDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleDerived X

abbrev GlobalModuleCategory (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.GlobalModuleCategory X

abbrev GlobalDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.GlobalDerived X

abbrev openIntersection (X : RingedSpace.{v})
    (U V : Opens X.carrier) : Opens X.carrier := U ⊓ V

abbrev openIntersectionSpace (X : RingedSpace.{v})
    (U V : Opens X.carrier) : RingedSpace.{v} :=
  openSpace X (U ⊓ V)

abbrev openIntersectionInclusion (X : RingedSpace.{v})
    (U V : Opens X.carrier) :
    RingedSpaceHom (openIntersectionSpace X U V) X :=
  openInclusion X (U ⊓ V)

/- The restriction of a morphism to an arbitrary open of its source.  The
   target-open restriction from Chapter 25 is a different construction, so
   this small abbreviation is needed for the relative statement below. -/
abbrev openRestrictionMorphism
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (U : Opens X.carrier) : RingedSpaceHom (openSpace X U) Y :=
  RingedSpaceHom.comp (openInclusion X U) f

abbrev openGlobalDerivedSectionsOverTarget
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleDerived (openSpace X U) ⥤ GlobalDerived X :=
  derivedSectionsViewedOverTarget (openInclusion X U)

abbrev openGlobalDerivedSections
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ModuleDerived X ⥤ GlobalDerived X :=
  openRestrictionDerivedFunctor X U ⋙
    openGlobalDerivedSectionsOverTarget X U

/-! ## The lower-shriek and direct-image triangles -/

structure LowerShriekTriangleData
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (_hcover : U ⊔ V = ⊤) (E : ModuleDerived X) where
  triangle : Triangle (ModuleDerived X)
  obj₁ : triangle.obj₁ =
    (openExtensionByZeroDerivedFunctor X (U ⊓ V)).obj
      ((openRestrictionDerivedFunctor X (U ⊓ V)).obj E)
  obj₂ : triangle.obj₂ =
    ((openExtensionByZeroDerivedFunctor X U).obj
        ((openRestrictionDerivedFunctor X U).obj E) ⊞
      (openExtensionByZeroDerivedFunctor X V).obj
        ((openRestrictionDerivedFunctor X V).obj E))
  obj₃ : triangle.obj₃ = E
  distinguished : triangle ∈ distTriang (ModuleDerived X)

theorem exists_lowerShriekTriangle
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (E : ModuleDerived X) :
    Nonempty (LowerShriekTriangleData X U V hcover E) := by
  sorry

noncomputable def lowerShriekTriangle
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (E : ModuleDerived X) :
    Triangle (ModuleDerived X) :=
  (Classical.choice (exists_lowerShriekTriangle X U V hcover E)).triangle

structure DirectImageTriangleData
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (_hcover : U ⊔ V = ⊤) (E : ModuleDerived X) where
  triangle : Triangle (ModuleDerived X)
  obj₁ : triangle.obj₁ = E
  obj₂ : triangle.obj₂ =
    ((derivedPushforward (openInclusion X U)).obj
        ((openRestrictionDerivedFunctor X U).obj E) ⊞
      (derivedPushforward (openInclusion X V)).obj
        ((openRestrictionDerivedFunctor X V).obj E))
  obj₃ : triangle.obj₃ =
    (derivedPushforward (openIntersectionInclusion X U V)).obj
      ((openRestrictionDerivedFunctor X (U ⊓ V)).obj E)
  distinguished : triangle ∈ distTriang (ModuleDerived X)

theorem exists_directImageTriangle
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (E : ModuleDerived X) :
    Nonempty (DirectImageTriangleData X U V hcover E) := by
  sorry

noncomputable def directImageTriangle
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (E : ModuleDerived X) :
    Triangle (ModuleDerived X) :=
  (Classical.choice (exists_directImageTriangle X U V hcover E)).triangle

/-! ## The derived Hom Mayer--Vietoris sequence -/

abbrev derivedHomGroup {X : RingedSpace.{v}}
    (E F : ModuleDerived X) : AddCommGrpCat :=
  AddCommGrpCat.of (E ⟶ F)

abbrev derivedExtGroup {X : RingedSpace.{v}}
    (E F : ModuleDerived X) (n : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (DerivedExt E F n)

structure MayerVietorisHomSequenceData
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (_hcover : U ⊔ V = ⊤) (E F : ModuleDerived X) where
  extToHom :
    derivedExtGroup
        ((openRestrictionDerivedFunctor X (U ⊓ V)).obj E)
        ((openRestrictionDerivedFunctor X (U ⊓ V)).obj F) (-1) ⟶
      derivedHomGroup E F
  homToPair :
    derivedHomGroup E F ⟶
      derivedHomGroup
          ((openRestrictionDerivedFunctor X U).obj E)
          ((openRestrictionDerivedFunctor X U).obj F) ⊞
      derivedHomGroup
          ((openRestrictionDerivedFunctor X V).obj E)
          ((openRestrictionDerivedFunctor X V).obj F)
  pairToIntersection :
    (derivedHomGroup
          ((openRestrictionDerivedFunctor X U).obj E)
          ((openRestrictionDerivedFunctor X U).obj F) ⊞
      derivedHomGroup
          ((openRestrictionDerivedFunctor X V).obj E)
          ((openRestrictionDerivedFunctor X V).obj F)) ⟶
      derivedHomGroup
          ((openRestrictionDerivedFunctor X (U ⊓ V)).obj E)
          ((openRestrictionDerivedFunctor X (U ⊓ V)).obj F)
  exact :
    (ComposableArrows.mk₃ extToHom homToPair pairToIntersection).Exact

theorem exists_mayerVietorisHomSequence
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (E F : ModuleDerived X) :
    Nonempty (MayerVietorisHomSequenceData X U V hcover E F) := by
  sorry

noncomputable def mayerVietorisHomSequence
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (E F : ModuleDerived X) :
    ComposableArrows AddCommGrpCat 3 :=
  let D := Classical.choice (exists_mayerVietorisHomSequence X U V hcover E F)
  ComposableArrows.mk₃ D.extToHom D.homToPair D.pairToIntersection

/-! ## Absolute unbounded cohomology -/

abbrev unboundedCohomologyGroup
    (X : RingedSpace.{v}) (E : ModuleDerived X) (n : ℤ) : AddCommGrpCat :=
  (forget₂ (GlobalModuleCategory X) AddCommGrpCat).obj
    ((DerivedCategory.homologyFunctor (GlobalModuleCategory X) n).obj
      ((derivedGlobalSections X).obj E))

abbrev openUnboundedCohomologyGroup
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (E : ModuleDerived X) (n : ℤ) : AddCommGrpCat :=
  (forget₂ (GlobalModuleCategory X) AddCommGrpCat).obj
    ((DerivedCategory.homologyFunctor (GlobalModuleCategory X) n).obj
      ((openGlobalDerivedSections X U).obj E))

structure UnboundedMayerVietorisCohomologyWindowData
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (_hcover : U ⊔ V = ⊤) (E : ModuleDerived X) (n : ℤ) where
  previous :
    openUnboundedCohomologyGroup X (U ⊓ V) E (n - 1) ⟶
      unboundedCohomologyGroup X E n
  restriction :
    unboundedCohomologyGroup X E n ⟶
      openUnboundedCohomologyGroup X U E n ⊞
      openUnboundedCohomologyGroup X V E n
  difference :
    (openUnboundedCohomologyGroup X U E n ⊞
      openUnboundedCohomologyGroup X V E n) ⟶
      openUnboundedCohomologyGroup X (U ⊓ V) E n
  connecting :
    openUnboundedCohomologyGroup X (U ⊓ V) E n ⟶
      unboundedCohomologyGroup X E (n + 1)
  exact :
    (ComposableArrows.mk₄ previous restriction difference connecting).Exact

structure UnboundedMayerVietorisData
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) where
  triangleFunctor : ModuleDerived X ⥤ Triangle (GlobalDerived X)
  obj₁ : ∀ E : ModuleDerived X,
    (triangleFunctor.obj E).obj₁ = (derivedGlobalSections X).obj E
  obj₂ : ∀ E : ModuleDerived X,
    (triangleFunctor.obj E).obj₂ =
      ((openGlobalDerivedSections X U).obj E ⊞
        (openGlobalDerivedSections X V).obj E)
  obj₃ : ∀ E : ModuleDerived X,
    (triangleFunctor.obj E).obj₃ =
      (openGlobalDerivedSections X (U ⊓ V)).obj E
  distinguished : ∀ E : ModuleDerived X,
    triangleFunctor.obj E ∈ distTriang (GlobalDerived X)
  cohomologyWindow : ∀ (E : ModuleDerived X) (n : ℤ),
    UnboundedMayerVietorisCohomologyWindowData X U V hcover E n

theorem exists_unboundedMayerVietoris
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) :
    Nonempty (UnboundedMayerVietorisData X U V hcover) := by
  sorry

noncomputable def unboundedMayerVietorisData
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) :
    UnboundedMayerVietorisData X U V hcover :=
  Classical.choice (exists_unboundedMayerVietoris X U V hcover)

noncomputable def unboundedMayerVietorisTriangle
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (E : ModuleDerived X) :
    Triangle (GlobalDerived X) :=
  (unboundedMayerVietorisData X U V hcover).triangleFunctor.obj E

/-! ## The relative unbounded triangle -/

structure RelativeMayerVietorisData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (U V : Opens X.carrier) (hcover : U ⊔ V = ⊤) where
  triangleFunctor : ModuleDerived X ⥤ Triangle (ModuleDerived Y)
  obj₁ : ∀ E : ModuleDerived X,
    (triangleFunctor.obj E).obj₁ = (derivedPushforward f).obj E
  obj₂ : ∀ E : ModuleDerived X,
    (triangleFunctor.obj E).obj₂ =
      ((derivedPushforward (openRestrictionMorphism f U)).obj
          ((openRestrictionDerivedFunctor X U).obj E) ⊞
        (derivedPushforward (openRestrictionMorphism f V)).obj
          ((openRestrictionDerivedFunctor X V).obj E))
  obj₃ : ∀ E : ModuleDerived X,
    (triangleFunctor.obj E).obj₃ =
      (derivedPushforward
        (openRestrictionMorphism f (U ⊓ V))).obj
        ((openRestrictionDerivedFunctor X (U ⊓ V)).obj E)
  distinguished : ∀ E : ModuleDerived X,
    triangleFunctor.obj E ∈ distTriang (ModuleDerived Y)

theorem exists_relativeMayerVietoris
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (U V : Opens X.carrier) (hcover : U ⊔ V = ⊤) :
    Nonempty (RelativeMayerVietorisData f U V hcover) := by
  sorry

noncomputable def relativeMayerVietorisData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (U V : Opens X.carrier) (hcover : U ⊔ V = ⊤) :
    RelativeMayerVietorisData f U V hcover :=
  Classical.choice (exists_relativeMayerVietoris f U V hcover)

/-! ## Restriction and pushforward for supported complexes -/

def derivedSupportContainedIn
    (X : RingedSpace.{v}) (T : Set X.carrier) (E : ModuleDerived X) : Prop :=
  ∀ n : ℤ,
    moduleSupport
        ((DerivedCategory.homologyFunctor (Mod X.structureSheaf) n).obj E) ⊆ T

def derivedSupportContainedInOpen
    (X : RingedSpace.{v}) (U : Opens X.carrier) (T : Set X.carrier)
    (F : ModuleDerived (openSpace X U)) : Prop :=
  ∀ n : ℤ,
    moduleSupport
        ((DerivedCategory.homologyFunctor
          (Mod (openSpace X U).structureSheaf) n).obj F) ⊆
      (fun x : (openSpace X U).carrier => x.1) ⁻¹' T

structure AmbientPushforwardRestrictionData
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (T : Set X.carrier) (hT : IsClosed T) (hTU : T ⊆ U)
    (E : ModuleDerived X) where
  comparison : E ≅
    (derivedPushforward (openInclusion X U)).obj
      ((openRestrictionDerivedFunctor X U).obj E)

theorem exists_ambientPushforwardRestriction
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (T : Set X.carrier) (hT : IsClosed T) (hTU : T ⊆ U)
    (E : ModuleDerived X) (hE : derivedSupportContainedIn X T E) :
    Nonempty (AmbientPushforwardRestrictionData X U T hT hTU E) := by
  sorry

noncomputable def ambientPushforwardRestrictionIso
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (T : Set X.carrier) (hT : IsClosed T) (hTU : T ⊆ U)
    (E : ModuleDerived X) (hE : derivedSupportContainedIn X T E) :
    E ≅
      (derivedPushforward (openInclusion X U)).obj
        ((openRestrictionDerivedFunctor X U).obj E) :=
  (Classical.choice
    (exists_ambientPushforwardRestriction X U T hT hTU E hE)).comparison

structure OpenPushforwardRestrictionData
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (T : Set X.carrier) (hT : IsClosed T) (hTU : T ⊆ U)
    (F : ModuleDerived (openSpace X U)) where
  comparison :
    (openExtensionByZeroDerivedFunctor X U).obj F ≅
      (derivedPushforward (openInclusion X U)).obj F

theorem exists_openPushforwardRestriction
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (T : Set X.carrier) (hT : IsClosed T) (hTU : T ⊆ U)
    (F : ModuleDerived (openSpace X U))
    (hF : derivedSupportContainedInOpen X U T F) :
    Nonempty (OpenPushforwardRestrictionData X U T hT hTU F) := by
  sorry

noncomputable def openPushforwardRestrictionIso
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (T : Set X.carrier) (hT : IsClosed T) (hTU : T ⊆ U)
    (F : ModuleDerived (openSpace X U))
    (hF : derivedSupportContainedInOpen X U T F) :
    (openExtensionByZeroDerivedFunctor X U).obj F ≅
      (derivedPushforward (openInclusion X U)).obj F :=
  (Classical.choice
    (exists_openPushforwardRestriction X U T hT hTU F hF)).comparison

/-! ## The cup-product map of Mayer--Vietoris triangles -/

structure MayerVietorisCupMapData
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (_hcover : U ⊔ V = ⊤)
    (K M : ModuleDerived X) where
  leftTriangle : Triangle (GlobalDerived X)
  rightTriangle : Triangle (GlobalDerived X)
  left_obj₁ : leftTriangle.obj₁ =
    ((globalCupProductData X K M).tensor.obj
      ((derivedGlobalSections X).obj K)).obj
      ((derivedGlobalSections X).obj M)
  left_obj₂ : leftTriangle.obj₂ =
    ((globalCupProductData X K M).tensor.obj
      ((derivedGlobalSections X).obj K)).obj
      ((openGlobalDerivedSections X U).obj M ⊞
        (openGlobalDerivedSections X V).obj M)
  left_obj₃ : leftTriangle.obj₃ =
    ((globalCupProductData X K M).tensor.obj
      ((derivedGlobalSections X).obj K)).obj
      ((openGlobalDerivedSections X (U ⊓ V)).obj M)
  right_obj₁ : rightTriangle.obj₁ =
    (derivedGlobalSections X).obj (derivedTensor X K M)
  right_obj₂ : rightTriangle.obj₂ =
    ((openGlobalDerivedSections X U).obj (derivedTensor X K M) ⊞
      (openGlobalDerivedSections X V).obj (derivedTensor X K M))
  right_obj₃ : rightTriangle.obj₃ =
    (openGlobalDerivedSections X (U ⊓ V)).obj (derivedTensor X K M)
  left_distinguished : leftTriangle ∈ distTriang (GlobalDerived X)
  right_distinguished : rightTriangle ∈ distTriang (GlobalDerived X)
  tensor_exact : Nonempty
    (ExactTriangulatedFunctorData
      ((globalCupProductData X K M).tensor.obj
        ((derivedGlobalSections X).obj K)))
  triangleMap : leftTriangle ⟶ rightTriangle

theorem exists_mayerVietorisCupMap
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (K M : ModuleDerived X) :
    Nonempty (MayerVietorisCupMapData X U V hcover K M) := by
  sorry

noncomputable def mayerVietorisCupMap
    (X : RingedSpace.{v}) (U V : Opens X.carrier)
    (hcover : U ⊔ V = ⊤) (K M : ModuleDerived X) :
    MayerVietorisCupMapData X U V hcover K M :=
  Classical.choice (exists_mayerVietorisCupMap X U V hcover K M)

end Formalization.Books.Cohomology.Unit26
