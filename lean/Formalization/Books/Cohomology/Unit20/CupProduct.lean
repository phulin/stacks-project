import Formalization.Books.Cohomology.Unit20.Godement
import Formalization.Books.Cohomology.Unit02

/-!
# Cohomology of Sheaves, Chapter 20, Section 5: Cup product
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Sheaves.Unit25

universe v u

namespace Formalization.Books.Cohomology.Unit20

/-! Global cup product and its elementwise description. -/

structure GlobalCupProductData
    (X : RingedSpace.{v}) (K L : ModuleDerived X) where
  tensor : GlobalDerived X ⥤ GlobalDerived X ⥤ GlobalDerived X
  map : (tensor.obj ((derivedGlobalSections X).obj K)).obj
      ((derivedGlobalSections X).obj L) ⟶
    (derivedGlobalSections X).obj (derivedTensor X K L)

theorem exists_globalCupProductData
    (X : RingedSpace.{v}) (K L : ModuleDerived X) :
    Nonempty (GlobalCupProductData X K L) := by
  sorry

noncomputable def globalCupProduct
    (X : RingedSpace.{v}) (K L : ModuleDerived X) :
    GlobalCupProductData X K L :=
  Classical.choice (exists_globalCupProductData X K L)

theorem exists_cupPairing
    (X : RingedSpace.{v}) (K L : ModuleDerived X) (i j : ℤ) :
    Nonempty ((globalCohomologyObject X i).obj K →
      (globalCohomologyObject X j).obj L →
      (globalCohomologyObject X (i + j)).obj (derivedTensor X K L)) := by
  sorry

noncomputable def cupPairing
    (X : RingedSpace.{v}) (K L : ModuleDerived X) (i j : ℤ) :
    (globalCohomologyObject X i).obj K →
      (globalCohomologyObject X j).obj L →
      (globalCohomologyObject X (i + j)).obj (derivedTensor X K L) :=
  Classical.choice (exists_cupPairing X K L i j)

structure CupProductDescriptionData
    (X : RingedSpace.{v}) (K L : ModuleDerived X) (i j : ℤ) where
  cup : (globalCohomologyObject X i).obj K →
    (globalCohomologyObject X j).obj L →
    (globalCohomologyObject X (i + j)).obj (derivedTensor X K L)
  tensor_description :
    cup = cupPairing X K L i j

theorem cup_product_agrees_with_tensor_description
    (X : RingedSpace.{v}) (K L : ModuleDerived X) (i j : ℤ) :
    Nonempty (CupProductDescriptionData X K L i j) := by
  sorry

structure CupByElementData
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i : ℤ)
    (ξ : (globalCohomologyObject X i).obj K) where
  map : (shiftFunctor (GlobalDerived X) (-i)).obj
      ((derivedGlobalSections X).obj M) ⟶
    (derivedGlobalSections X).obj (derivedTensor X K M)

theorem exists_cup_by_element_map
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i : ℤ)
    (ξ : (globalCohomologyObject X i).obj K) :
    Nonempty (CupByElementData X K M i ξ) := by
  sorry

noncomputable def cupByElementMap
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i : ℤ)
    (ξ : (globalCohomologyObject X i).obj K) :
    CupByElementData X K M i ξ :=
  Classical.choice (exists_cup_by_element_map X K M i ξ)

/-! Compatibility with the naive complex-level product. -/

theorem globalSections_additive (X : RingedSpace.{v}) :
    (ringedSpaceModuleGlobalSections X).Additive := by
  sorry

noncomputable def globalSectionsComplexFunctor (X : RingedSpace.{v}) :
    ModuleComplex X ⥤ BookComplex (GlobalModuleCategory X) := by
  letI : (ringedSpaceModuleGlobalSections X).Additive :=
    globalSections_additive X
  exact (ringedSpaceModuleGlobalSections X).mapHomologicalComplex
    (ComplexShape.up ℤ)

structure NaiveCupProductData
    (X : RingedSpace.{v}) (K M : ModuleComplex X) where
  tensor : BookComplex (GlobalModuleCategory X) ⥤
    BookComplex (GlobalModuleCategory X) ⥤
      BookComplex (GlobalModuleCategory X)
  map : (tensor.obj ((globalSectionsComplexFunctor X).obj K)).obj
      ((globalSectionsComplexFunctor X).obj M) ⟶
    (globalSectionsComplexFunctor X).obj
      (((tensorComplexData X).tensor.obj K).obj M)

theorem exists_naiveCupProductData
    (X : RingedSpace.{v}) (K M : ModuleComplex X) :
    Nonempty (NaiveCupProductData X K M) := by
  sorry

noncomputable def naiveCupProduct
    (X : RingedSpace.{v}) (K M : ModuleComplex X) :
    NaiveCupProductData X K M :=
  Classical.choice (exists_naiveCupProductData X K M)

structure RelativeCupNaiveCompatibilityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleDerived X) where
  derived_route :
    derivedTensor Y ((derivedPushforward f).obj K)
      ((derivedPushforward f).obj M) ⟶
      (derivedPushforward f).obj (derivedTensor X K M)
  naive_route :
    derivedTensor Y ((derivedPushforward f).obj K)
      ((derivedPushforward f).obj M) ⟶
      (derivedPushforward f).obj (derivedTensor X K M)
  commutes : derived_route = naive_route

theorem cup_compatible_with_naive
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleDerived X) :
    Nonempty (RelativeCupNaiveCompatibilityData f K M) := by
  sorry

structure CechCupCompatibilityData
    {X : RingedSpace.{v}} (𝒰 : CechOpenCover X)
    (K M : ModuleComplex X) where
  derived_route : Prop
  naive_route : Prop
  commutes : derived_route = naive_route

theorem cech_cup_compatibility
    {X : RingedSpace.{v}} (𝒰 : CechOpenCover X)
    (K M : ModuleComplex X)
    (hK : IsBoundedBelow K) (hM : IsBoundedBelow M) :
    Nonempty (CechCupCompatibilityData 𝒰 K M) := by
  sorry

/-! Associativity, commutativity, composition, and base change. -/

structure CupAssociativityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L M : ModuleDerived X) where
  left : derivedTensor Y
      (derivedTensor Y ((derivedPushforward f).obj K)
        ((derivedPushforward f).obj L))
      ((derivedPushforward f).obj M) ⟶
    (derivedPushforward f).obj (derivedTensor X (derivedTensor X K L) M)
  right : derivedTensor Y
      (derivedTensor Y ((derivedPushforward f).obj K)
        ((derivedPushforward f).obj L))
      ((derivedPushforward f).obj M) ⟶
    (derivedPushforward f).obj (derivedTensor X (derivedTensor X K L) M)
  commutes : left = right

theorem cup_product_associative
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L M : ModuleDerived X) :
    Nonempty (CupAssociativityData f K L M) := by
  sorry

structure CupCommutativityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : ModuleDerived X) where
  left : derivedTensor Y ((derivedPushforward f).obj K)
      ((derivedPushforward f).obj L) ⟶
    (derivedPushforward f).obj (derivedTensor X K L)
  right : derivedTensor Y ((derivedPushforward f).obj L)
      ((derivedPushforward f).obj K) ⟶
    (derivedPushforward f).obj (derivedTensor X L K)
  source_swap : derivedTensor Y ((derivedPushforward f).obj K)
      ((derivedPushforward f).obj L) ≅
    derivedTensor Y ((derivedPushforward f).obj L)
      ((derivedPushforward f).obj K)
  target_swap : derivedTensor X K L ≅ derivedTensor X L K
  commutes : left ≫ (derivedPushforward f).map target_swap.hom =
    source_swap.hom ≫ right

theorem cup_product_commutative
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : ModuleDerived X) :
    Nonempty (CupCommutativityData f K L) := by
  sorry

structure CupCompositionData
    {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z)
    (K L : ModuleDerived X) where
  left : derivedTensor Z
      ((derivedPushforward (RingedSpaceHom.comp f g)).obj K)
      ((derivedPushforward (RingedSpaceHom.comp f g)).obj L) ⟶
    (derivedPushforward (RingedSpaceHom.comp f g)).obj (derivedTensor X K L)
  right : derivedTensor Z
      ((derivedPushforward (RingedSpaceHom.comp f g)).obj K)
      ((derivedPushforward (RingedSpaceHom.comp f g)).obj L) ⟶
    (derivedPushforward (RingedSpaceHom.comp f g)).obj (derivedTensor X K L)
  commutes : left = right

theorem cup_product_compatible_with_composition
    {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z)
    (K L : ModuleDerived X) :
    Nonempty (CupCompositionData f g K L) := by
  sorry

structure CupBaseChangeData
    (B : DerivedBaseChangeSquare)
    (K L : ModuleDerived B.X) where
  left : (derivedPullback B.g).obj
      (derivedTensor B.S ((derivedPushforward B.f).obj K)
        ((derivedPushforward B.f).obj L)) ⟶
    (derivedPushforward B.f').obj
      (derivedTensor B.X' ((derivedPullback B.g').obj K)
        ((derivedPullback B.g').obj L))
  right : (derivedPullback B.g).obj
      (derivedTensor B.S ((derivedPushforward B.f).obj K)
        ((derivedPushforward B.f).obj L)) ⟶
    (derivedPushforward B.f').obj
      (derivedTensor B.X' ((derivedPullback B.g').obj K)
        ((derivedPullback B.g').obj L))
  commutes : left = right

theorem cup_product_compatible_with_base_change
    (B : DerivedBaseChangeSquare) (K L : ModuleDerived B.X) :
    Nonempty (CupBaseChangeData B K L) := by
  sorry

end Formalization.Books.Cohomology.Unit20
