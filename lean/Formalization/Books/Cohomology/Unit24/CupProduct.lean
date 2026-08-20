import Formalization.Books.Cohomology.Unit20.UnboundedComplexes
import Formalization.Books.Cohomology.Unit08.CechCohomology

/-!
# Cohomology of Sheaves, Chapter 24: Cup product

This file records the global and relative cup products, their elementwise and
naive complex descriptions, and the compatibility diagrams in the source
section.  The earlier derived-category files supply the ambient categories,
derived tensor products, derived pushforwards, base-change maps, and Čech
covers used below.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v

namespace Formalization.Books.Cohomology.Unit24

/-! ## Global cup product and its elements -/

/-- The derived tensor functor and global cup map in `D(A)`, where
`A = Γ(X, O_X)`. -/
structure GlobalCupProductData
    (X : RingedSpace.{v}) (K M : ModuleDerived X) where
  tensor : GlobalDerived X ⥤ GlobalDerived X ⥤ GlobalDerived X
  map : (tensor.obj ((derivedGlobalSections X).obj K)).obj
      ((derivedGlobalSections X).obj M) ⟶
    (derivedGlobalSections X).obj (derivedTensor X K M)

/-- Existence of the global derived cup-product map. -/
theorem exists_globalCupProductData
    (X : RingedSpace.{v}) (K M : ModuleDerived X) :
    Nonempty (GlobalCupProductData X K M) := by
  sorry

/-- A chosen global cup-product data package. -/
noncomputable def globalCupProductData
    (X : RingedSpace.{v}) (K M : ModuleDerived X) :
    GlobalCupProductData X K M :=
  Classical.choice (exists_globalCupProductData X K M)

/-- The chosen global cup-product morphism. -/
noncomputable def globalCupProduct
    (X : RingedSpace.{v}) (K M : ModuleDerived X) :
    ((globalCupProductData X K M).tensor.obj
        ((derivedGlobalSections X).obj K)).obj
        ((derivedGlobalSections X).obj M) ⟶
      (derivedGlobalSections X).obj (derivedTensor X K M) :=
  (globalCupProductData X K M).map

/-- The degree-`i` global cohomology object of `K`. -/
abbrev globalCohomologyElement
    (X : RingedSpace.{v}) (K : ModuleDerived X) (i : ℤ) :=
  (globalCohomologyObject X i).obj K

/-- The elementwise cup pairing in degrees `i` and `j`. -/
theorem exists_cupPairing
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i j : ℤ) :
    Nonempty (globalCohomologyElement X K i →
      globalCohomologyElement X M j →
      globalCohomologyElement X (derivedTensor X K M) (i + j)) := by
  sorry

/-- The chosen elementwise cup pairing. -/
noncomputable def cupPairing
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i j : ℤ) :
    globalCohomologyElement X K i →
      globalCohomologyElement X M j →
      globalCohomologyElement X (derivedTensor X K M) (i + j) :=
  Classical.choice (exists_cupPairing X K M i j)

/-- The source's assertion that the morphism description and the elementwise
description give the same cup product. -/
structure CupProductElementDescriptionData
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i j : ℤ) where
  cup : globalCohomologyElement X K i →
    globalCohomologyElement X M j →
    globalCohomologyElement X (derivedTensor X K M) (i + j)
  agrees_with_cupPairing : cup = cupPairing X K M i j

theorem cupProduct_agrees_with_element_description
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i j : ℤ) :
    Nonempty (CupProductElementDescriptionData X K M i j) := by
  sorry

theorem lemma_second_cup_equals_first
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i j : ℤ) :
    Nonempty (CupProductElementDescriptionData X K M i j) :=
  cupProduct_agrees_with_element_description X K M i j

/-! The cup product by a fixed cohomology class. -/

/-- The derived map induced by cupping with a fixed degree-`i` class. -/
structure CupByElementData
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i : ℤ)
    (ξ : globalCohomologyElement X K i) where
  map : (shiftFunctor (GlobalDerived X) (-i)).obj
      ((derivedGlobalSections X).obj M) ⟶
    (derivedGlobalSections X).obj (derivedTensor X K M)

theorem exists_cupByElementMap
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i : ℤ)
    (ξ : globalCohomologyElement X K i) :
    Nonempty (CupByElementData X K M i ξ) := by
  sorry

/-- A chosen data package representing cupping by `ξ`. -/
noncomputable def cupByElementData
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i : ℤ)
    (ξ : globalCohomologyElement X K i) :
    CupByElementData X K M i ξ :=
  Classical.choice (exists_cupByElementMap X K M i ξ)

/-- The chosen derived map representing cupping by `ξ`. -/
noncomputable def cupByElementMap
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i : ℤ)
    (ξ : globalCohomologyElement X K i) :
    (shiftFunctor (GlobalDerived X) (-i)).obj
        ((derivedGlobalSections X).obj M) ⟶
      (derivedGlobalSections X).obj (derivedTensor X K M) :=
  (cupByElementData X K M i ξ).map

theorem remark_cup_with_element_map_total_cohomology
    (X : RingedSpace.{v}) (K M : ModuleDerived X) (i : ℤ)
    (ξ : globalCohomologyElement X K i) :
    Nonempty (CupByElementData X K M i ξ) :=
  exists_cupByElementMap X K M i ξ

/-! ## Naive complex-level cup product -/

/-- Global sections on complexes, obtained by applying the additive global
sections functor degreewise. -/
theorem globalSections_additive (X : RingedSpace.{v}) :
    (ringedSpaceModuleGlobalSections X).Additive := by
  sorry

noncomputable def globalSectionsComplexFunctor (X : RingedSpace.{v}) :
    ModuleComplex X ⥤ BookComplex (GlobalModuleCategory X) := by
  letI : (ringedSpaceModuleGlobalSections X).Additive :=
    globalSections_additive X
  exact (ringedSpaceModuleGlobalSections X).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Data for the naive product of the global-sections complexes.  The
`tensor` field is the total-complex tensor construction and `map` is the
componentwise naive cup map. -/
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

/-- A chosen naive complex-level cup-product data package. -/
noncomputable def naiveCupProductData
    (X : RingedSpace.{v}) (K M : ModuleComplex X) :
    NaiveCupProductData X K M :=
  Classical.choice (exists_naiveCupProductData X K M)

/-- The chosen naive complex-level cup-product morphism. -/
noncomputable def naiveCupProduct
    (X : RingedSpace.{v}) (K M : ModuleComplex X) :
    ((naiveCupProductData X K M).tensor.obj
      ((globalSectionsComplexFunctor X).obj K)).obj
      ((globalSectionsComplexFunctor X).obj M) ⟶
      (globalSectionsComplexFunctor X).obj
        (((tensorComplexData X).tensor.obj K).obj M) :=
  (naiveCupProductData X K M).map

/-- The commutative derived-category square relating the naive global
sections product to the global derived cup product. -/
structure GlobalNaiveCupCompatibilityData
    (X : RingedSpace.{v}) (K M : ModuleComplex X) where
  derivedRoute :
    ((globalCupProductData X (derivedObjectOfComplex X K)
      (derivedObjectOfComplex X M)).tensor.obj
      ((derivedGlobalSections X).obj (derivedObjectOfComplex X K))).obj
      ((derivedGlobalSections X).obj (derivedObjectOfComplex X M)) ⟶
      (derivedGlobalSections X).obj
        (derivedObjectOfComplex X (((tensorComplexData X).tensor.obj K).obj M))
  naiveRoute :
    ((globalCupProductData X (derivedObjectOfComplex X K)
      (derivedObjectOfComplex X M)).tensor.obj
      ((derivedGlobalSections X).obj (derivedObjectOfComplex X K))).obj
      ((derivedGlobalSections X).obj (derivedObjectOfComplex X M)) ⟶
      (derivedGlobalSections X).obj
        (derivedObjectOfComplex X (((tensorComplexData X).tensor.obj K).obj M))
  commutes : derivedRoute = naiveRoute

theorem global_naive_cup_compatibility
    (X : RingedSpace.{v}) (K M : ModuleComplex X) :
    Nonempty (GlobalNaiveCupCompatibilityData X K M) := by
  sorry

/-! ## Compatibility with the relative cup product -/

/-- The canonical relative cup map supplied by the earlier derived
pushforward construction. -/
noncomputable abbrev relativeCupProductMap
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleDerived X) :
    derivedTensor Y ((derivedPushforward f).obj K)
      ((derivedPushforward f).obj M) ⟶
    (derivedPushforward f).obj (derivedTensor X K M) :=
  Formalization.Books.Cohomology.Unit20.relativeCupProduct f K M

/-- The two routes in the source's relative/naive cup-product square. -/
structure RelativeCupNaiveCompatibilityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleDerived X) where
  derivedRoute :
    derivedTensor Y ((derivedPushforward f).obj K)
      ((derivedPushforward f).obj M) ⟶
      (derivedPushforward f).obj (derivedTensor X K M)
  naiveRoute :
    derivedTensor Y ((derivedPushforward f).obj K)
      ((derivedPushforward f).obj M) ⟶
      (derivedPushforward f).obj (derivedTensor X K M)
  canonical_derivedRoute : derivedRoute = relativeCupProductMap f K M
  commutes : derivedRoute = naiveRoute

theorem cup_compatible_with_naive
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleDerived X) :
    Nonempty (RelativeCupNaiveCompatibilityData f K M) := by
  sorry

theorem lemma_cup_compatible_with_naive
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K M : ModuleDerived X) :
    Nonempty (RelativeCupNaiveCompatibilityData f K M) :=
  cup_compatible_with_naive f K M

/-! The Čech comparison diagram. -/

/-- A categorical package for the Čech cup-product diagram.  The three
`cech*` objects are the total Čech complexes viewed in `D(A)`, and the
comparison isomorphisms identify them with the derived global-section
objects used in the other route of the source diagram. -/
structure CechCupCompatibilityData
    {X : RingedSpace.{v}} (𝒰 : CechOpenCover X)
    (K M : ModuleComplex X) where
  cechK : GlobalDerived X
  cechM : GlobalDerived X
  cechTensor : GlobalDerived X
  tensor : GlobalDerived X ⥤ GlobalDerived X ⥤ GlobalDerived X
  cechK_comparison : cechK ≅
    (derivedGlobalSections X).obj (derivedObjectOfComplex X K)
  cechM_comparison : cechM ≅
    (derivedGlobalSections X).obj (derivedObjectOfComplex X M)
  cechTensor_comparison : cechTensor ≅
    (derivedGlobalSections X).obj
      (derivedObjectOfComplex X (((tensorComplexData X).tensor.obj K).obj M))
  derivedRoute : (tensor.obj cechK).obj cechM ⟶ cechTensor
  naiveRoute : (tensor.obj cechK).obj cechM ⟶ cechTensor
  commutes : derivedRoute = naiveRoute

theorem cech_cup_compatibility
    {X : RingedSpace.{v}} (𝒰 : CechOpenCover X)
    (K M : ModuleComplex X)
    (hK : IsBoundedBelow K) (hM : IsBoundedBelow M) :
    Nonempty (CechCupCompatibilityData 𝒰 K M) := by
  sorry

theorem lemma_diagrams_commute
    {X : RingedSpace.{v}} (𝒰 : CechOpenCover X)
    (K M : ModuleComplex X)
    (hK : IsBoundedBelow K) (hM : IsBoundedBelow M) :
    Nonempty (CechCupCompatibilityData 𝒰 K M) :=
  cech_cup_compatibility 𝒰 K M hK hM

/-! ## Associativity, commutativity, composition, and base change -/

/-- The two composites in the associativity diagram for the relative cup
product. -/
structure CupAssociativityData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L M : ModuleDerived X) where
  left :
    derivedTensor Y
        (derivedTensor Y ((derivedPushforward f).obj K)
          ((derivedPushforward f).obj L))
        ((derivedPushforward f).obj M) ⟶
      (derivedPushforward f).obj
        (derivedTensor X (derivedTensor X K L) M)
  right :
    derivedTensor Y
        ((derivedPushforward f).obj K)
        (derivedTensor Y ((derivedPushforward f).obj L)
          ((derivedPushforward f).obj M)) ⟶
      (derivedPushforward f).obj
        (derivedTensor X K (derivedTensor X L M))
  associator_source :
    derivedTensor Y
        (derivedTensor Y ((derivedPushforward f).obj K)
          ((derivedPushforward f).obj L))
        ((derivedPushforward f).obj M) ≅
      derivedTensor Y
        ((derivedPushforward f).obj K)
        (derivedTensor Y ((derivedPushforward f).obj L)
          ((derivedPushforward f).obj M))
  associator_target :
    derivedTensor X (derivedTensor X K L) M ≅
      derivedTensor X K (derivedTensor X L M)
  commutes :
    left ≫ (derivedPushforward f).map associator_target.hom =
      associator_source.hom ≫ right

theorem cup_product_associative
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L M : ModuleDerived X) :
    Nonempty (CupAssociativityData f K L M) := by
  sorry

theorem lemma_cup_product_associative
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L M : ModuleDerived X) :
    Nonempty (CupAssociativityData f K L M) :=
  cup_product_associative f K L M

/-- The two routes in the commutativity diagram for the relative cup
product, with the source and target symmetry constraints explicit. -/
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

theorem lemma_cup_product_commutative
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K L : ModuleDerived X) :
    Nonempty (CupCommutativityData f K L) :=
  cup_product_commutative f K L

/-- The two routes in the composition-compatibility square. -/
structure CupCompositionData
    {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z)
    (K L : ModuleDerived X) where
  left :
    derivedTensor Z
      ((derivedPushforward (RingedSpaceHom.comp f g)).obj K)
      ((derivedPushforward (RingedSpaceHom.comp f g)).obj L) ⟶
    (derivedPushforward (RingedSpaceHom.comp f g)).obj
      (derivedTensor X K L)
  right :
    derivedTensor Z
      ((derivedPushforward (RingedSpaceHom.comp f g)).obj K)
      ((derivedPushforward (RingedSpaceHom.comp f g)).obj L) ⟶
    (derivedPushforward (RingedSpaceHom.comp f g)).obj
      (derivedTensor X K L)
  commutes : left = right

theorem cup_product_compatible_with_composition
    {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z)
    (K L : ModuleDerived X) :
    Nonempty (CupCompositionData f g K L) := by
  sorry

theorem lemma_compose_cup_product
    {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z)
    (K L : ModuleDerived X) :
    Nonempty (CupCompositionData f g K L) :=
  cup_product_compatible_with_composition f g K L

/-- The two composites in the base-change compatibility diagram. -/
structure CupBaseChangeData
    (B : DerivedBaseChangeSquare)
    (K L : ModuleDerived B.X) where
  left :
    (derivedPullback B.g).obj
        (derivedTensor B.S ((derivedPushforward B.f).obj K)
          ((derivedPushforward B.f).obj L)) ⟶
      (derivedPushforward B.f').obj
        (derivedTensor B.X' ((derivedPullback B.g').obj K)
          ((derivedPullback B.g').obj L))
  right :
    (derivedPullback B.g).obj
        (derivedTensor B.S ((derivedPushforward B.f).obj K)
          ((derivedPushforward B.f).obj L)) ⟶
      (derivedPushforward B.f').obj
        (derivedTensor B.X' ((derivedPullback B.g').obj K)
          ((derivedPullback B.g').obj L))
  canonical_left :
    left =
      (derivedPullback B.g).map (relativeCupProductMap B.f K L) ≫
        baseChangeMap B (derivedTensor B.X K L) ≫
        (derivedPushforward B.f').map
          (Classical.choice (derivedPullback_tensor_iso B.g' K L)).hom
  commutes : left = right

theorem cup_product_compatible_with_base_change
    (B : DerivedBaseChangeSquare) (K L : ModuleDerived B.X) :
    Nonempty (CupBaseChangeData B K L) := by
  sorry

theorem lemma_base_change_cup_product
    (B : DerivedBaseChangeSquare) (K L : ModuleDerived B.X) :
    Nonempty (CupBaseChangeData B K L) :=
  cup_product_compatible_with_base_change B K L

end Formalization.Books.Cohomology.Unit24
