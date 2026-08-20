import Formalization.Books.Modules.Unit21.SymmetricExterior
import Formalization.Books.Modules.Unit22.InternalHom
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.PicardGroup

/-!
# Sheaves of Modules, Chapter 25: Invertible modules

This file records the definitions and interfaces in `books/modules.tex`,
Section `Invertible modules`.  Tensor products, duals, local freeness, and
pullbacks use the canonical constructions established in Chapters 14, 16,
18, and 22.  The sectionwise graded constructions are exposed through
degreewise direct-sum carriers and explicit data interfaces because the
project's sheafification API does not yet provide a canonical map on sections
for every displayed tensor-product expression.
-/

namespace Formalization.Books.Modules.Unit25

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit14
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit18
open Formalization.Books.Modules.Unit21
open Formalization.Books.Modules.Unit22
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Sheaves.Unit24
open scoped DirectSum

universe v

noncomputable section

/-! ## Invertibility and triviality -/

/- The source's tensoring functor is the left tensor functor in the
   symmetric monoidal category supplied by Chapter 18. -/
def IsInvertibleModule {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : Prop :=
  letI := sheafModuleMonoidalCategory O
  Formalization.Books.Categories.Unit43.IsInvertible L

/-- An invertible sheaf is trivial when it is isomorphic to the unit module. -/
def IsTrivialInvertibleModule {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : Prop :=
  Nonempty (L ≅ sheafModuleUnit O)

/-! The one-sided tensor-inverse formulation used throughout the section. -/

def HasTensorInverse {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : Prop :=
  ∃ N : CommRingSheafModule O,
    Nonempty (tensorProductSheaf O L N ≅ sheafModuleUnit O)

theorem isInvertibleModule_iff_tensorLeftFunctor {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    IsInvertibleModule O L ↔
      (tensorLeftFunctor O L).IsEquivalence := by
  sorry

/-! ## Characterization, duals, and local finite presentation -/

theorem isInvertibleModule_iff_hasTensorInverse {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    IsInvertibleModule O L ↔ HasTensorInverse O L := by
  sorry

theorem hasTensorInverse_equiv_dual {X : TopCat.{v}}
    (O : CommRingSheaf X) (L N : CommRingSheafModule O)
    (hL : IsInvertibleModule O L)
    (e : Nonempty (tensorProductSheaf O L N ≅ sheafModuleUnit O)) :
    Nonempty (N ≅ internalHom O L (sheafModuleUnit O)) := by
  sorry

theorem invertible_isLocallyDirectSummandOfFiniteFree
    {X : TopCat.{v}} {O : CommRingSheaf X} {L : CommRingSheafModule O}
    (hL : IsInvertibleModule O L) :
    IsLocallyDirectSummand L := by
  sorry

theorem invertible_isFinitePresentation
    {X : TopCat.{v}} {O : CommRingSheaf X} {L : CommRingSheafModule O}
    (hL : IsInvertibleModule O L) :
    IsFinitePresentation L := by
  sorry

/- The evaluation morphism supplied by the internal-Hom interface is the
   source's `L ⊗ Hom(L, O) → O`. -/
noncomputable abbrev invertibleDual {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    CommRingSheafModule O :=
  internalHom O L (sheafModuleUnit O)

noncomputable abbrev invertibleDualEvaluation {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    tensorProductSheaf O L (invertibleDual O L) ⟶ sheafModuleUnit O :=
  internalHomEvaluation O L (sheafModuleUnit O)

theorem invertibleDual_isInvertible {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O)
    (hL : IsInvertibleModule O L) :
    IsInvertibleModule O (invertibleDual O L) := by
  sorry

theorem invertibleDual_evaluation_iso {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O)
    (hL : IsInvertibleModule O L) :
    Nonempty (tensorProductSheaf O L (invertibleDual O L) ≅
      sheafModuleUnit O) := by
  sorry

theorem invertibleDual_evaluation_isIso {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O)
    (hL : IsInvertibleModule O L) :
    IsIso (invertibleDualEvaluation O L) := by
  sorry

theorem tensorProduct_isInvertible {X : TopCat.{v}}
    (O : CommRingSheaf X) (L N : CommRingSheafModule O)
    (hL : IsInvertibleModule O L) (hN : IsInvertibleModule O N) :
    IsInvertibleModule O (tensorProductSheaf O L N) := by
  sorry

/-! ## Pullback -/

theorem pullback_isInvertibleModule
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (Formalization.Books.Sheaves.Unit24.sheafRingPushforward f).obj
        (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    {L : CommRingSheafModule OY} (hL : IsInvertibleModule OY L) :
    IsInvertibleModule OX ((pullbackModule f α).obj L) := by
  sorry

/-! ## Locally free modules of rank one -/

abbrev IsLocallyFreeRankOne {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : Prop :=
  Formalization.Books.Modules.Unit14.IsFiniteLocallyFreeOfRank
    (X := underlyingRingedSpace O) L 1

theorem locallyFreeRankOne_isInvertible {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O)
    (hL : IsLocallyFreeRankOne O L) :
    IsInvertibleModule O L := by
  sorry

theorem invertible_isLocallyFreeRankOne_of_localStalks
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (hO : StructureSheafHasLocalStalks (underlyingRingedSpace O))
    (L : CommRingSheafModule O) (hL : IsInvertibleModule O L) :
    IsLocallyFreeRankOne O L := by
  sorry

/- The source's warning is witnessed by the corresponding ring statement on
   a one-point ringed space (Chapter 10 supplies `onePointRingedSpace`). -/
def HasNontrivialPicardRing : Prop :=
  ∃ (R : Type v) (_ : CommRing R), ¬ Subsingleton (CommRing.Pic R)

theorem exists_nonfree_invertible_module_of_nontrivialPicard
    (R : Type v) [CommRing R] (hR : ¬ Subsingleton (CommRing.Pic R)) :
    ∃ M : ModuleCat R,
      Module.Invertible R (M : Type v) ∧
        ¬ Nonempty ((M : Type v) ≃ₗ[R] R) := by
  sorry

/-! ## Tensor powers -/

noncomputable def tensorPower {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : ℤ → CommRingSheafModule O
  | Int.ofNat n => tensorPowerSheaf O L n
  | Int.negSucc n => tensorPowerSheaf O (invertibleDual O L) (n + 1)

@[simp] theorem tensorPower_zero {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    tensorPower O L 0 = sheafModuleUnit O := rfl

@[simp] theorem tensorPower_negOne {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    tensorPower O L (-1) = invertibleDual O L := rfl

theorem tensorPower_ofNat {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) (n : ℕ) :
    tensorPower O L (Int.ofNat n) = tensorPowerSheaf O L n := rfl

theorem tensorPower_negSucc {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) (n : ℕ) :
    tensorPower O L (Int.negSucc n) =
      tensorPowerSheaf O (invertibleDual O L) (n + 1) := rfl

theorem tensorPower_add_iso_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    Nonempty (∀ n m : ℤ,
      tensorProductSheaf O (tensorPower O L n) (tensorPower O L m) ≅
        tensorPower O L (n + m)) := by
  sorry

noncomputable def tensorPowerAddIso {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) (n m : ℤ) :
    tensorProductSheaf O (tensorPower O L n) (tensorPower O L m) ≅
      tensorPower O L (n + m) :=
  Classical.choice (tensorPower_add_iso_exists O L) n m

structure TensorPowerCoherenceData {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) where
  addIso : ∀ n m : ℤ,
    tensorProductSheaf O (tensorPower O L n) (tensorPower O L m) ≅
      tensorPower O L (n + m)
  commutativity : Prop
  commutativity_proof : commutativity
  associativity : Prop
  associativity_proof : associativity

theorem tensorPowerCoherenceData_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    Nonempty (TensorPowerCoherenceData O L) := by
  sorry

noncomputable def tensorPowerCoherenceData {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    TensorPowerCoherenceData O L :=
  Classical.choice (tensorPowerCoherenceData_exists O L)

/-! ## Associated graded ring and module -/

abbrev sectionType {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (U : Opens X) : Type v :=
  ↑((SheafOfModules.evaluation (commRingSheafToRingSheaf O) (op U)).obj F)

abbrev globalModuleSections {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : Type v :=
  sectionType O F (⊤ : Opens X)

instance sectionType_addCommGroup {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (U : Opens X) :
    AddCommGroup (sectionType O F U) := by
  change AddCommGroup
    (↑((SheafOfModules.evaluation (commRingSheafToRingSheaf O) (op U)).obj F))
  infer_instance

def gammaStarCarrier {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : Type v :=
  ⨁ n : ℕ, sectionType O (tensorPower O L (Int.ofNat n)) (⊤ : Opens X)

abbrev gammaStarModuleCarrier {X : TopCat.{v}} (O : CommRingSheaf X)
    (L F : CommRingSheafModule O) : Type v :=
  ⨁ n : ℤ, sectionType O
    (tensorProductSheaf O F (tensorPower O L n)) (⊤ : Opens X)

def signedGammaStarCarrier {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : Type v :=
  ⨁ n : ℤ, sectionType O (tensorPower O L n) (⊤ : Opens X)

def HasNoNegativeDegrees {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : Prop :=
  ∀ n : ℤ, n < 0 → ∀ s : sectionType O (tensorPower O L n) (⊤ : Opens X),
    s = 0

structure SignedGammaStarData {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) where
  ring : Ring (signedGammaStarCarrier O L)
  multiplication_is_tensor_product : Prop
  multiplication_is_tensor_product_proof : multiplication_is_tensor_product

theorem signedGammaStarData_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    Nonempty (SignedGammaStarData O L) := by
  sorry

abbrev associatedGradedRing {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) : Type v := gammaStarCarrier O L

structure AssociatedGradedRingData {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) where
  ring : Ring (gammaStarCarrier O L)
  homogeneousMultiplication : Prop
  homogeneousMultiplication_proof : homogeneousMultiplication

theorem associatedGradedRingData_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    Nonempty (AssociatedGradedRingData O L) := by
  sorry

noncomputable def associatedGradedRingData {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    AssociatedGradedRingData O L :=
  Classical.choice (associatedGradedRingData_exists O L)

noncomputable instance gammaStarRingInstance {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) :
    Ring (gammaStarCarrier O L) :=
  (associatedGradedRingData O L).ring

structure AssociatedGradedModuleData {X : TopCat.{v}}
    (O : CommRingSheaf X) (L F : CommRingSheafModule O) where
  module : Module (gammaStarCarrier O L) (gammaStarModuleCarrier O L F)
  gradedModuleLaws : Prop
  gradedModuleLaws_proof : gradedModuleLaws

theorem associatedGradedModuleData_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (L F : CommRingSheafModule O) :
    Nonempty (AssociatedGradedModuleData O L F) := by
  sorry

noncomputable def associatedGradedModuleData {X : TopCat.{v}}
    (O : CommRingSheaf X) (L F : CommRingSheafModule O) :
    AssociatedGradedModuleData O L F :=
  Classical.choice (associatedGradedModuleData_exists O L F)

noncomputable instance gammaStarModuleInstance {X : TopCat.{v}}
    (O : CommRingSheaf X) (L F : CommRingSheafModule O) :
    Module (gammaStarCarrier O L) (gammaStarModuleCarrier O L F) :=
  (associatedGradedModuleData O L F).module

theorem gammaStar_ringHom_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (L N : CommRingSheafModule O)
    (hL : IsInvertibleModule O L) (hN : IsInvertibleModule O N)
    (α : L ⟶ N) :
    Nonempty (gammaStarCarrier O L →+* gammaStarCarrier O N) := by
  sorry

noncomputable def gammaStarRingHom {X : TopCat.{v}}
    (O : CommRingSheaf X) (L N : CommRingSheafModule O)
    (hL : IsInvertibleModule O L) (hN : IsInvertibleModule O N)
    (α : L ⟶ N) : gammaStarCarrier O L →+* gammaStarCarrier O N :=
  Classical.choice (gammaStar_ringHom_exists O L N hL hN α)

theorem gammaStar_moduleHom_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (L F G : CommRingSheafModule O)
    (hL : IsInvertibleModule O L) (γ : F ⟶ G) :
    Nonempty (gammaStarModuleCarrier O L F →ₗ[gammaStarCarrier O L]
      gammaStarModuleCarrier O L G) := by
  sorry

noncomputable def gammaStarModuleHom {X : TopCat.{v}}
    (O : CommRingSheaf X) (L F G : CommRingSheafModule O)
    (hL : IsInvertibleModule O L) (γ : F ⟶ G) :
    gammaStarModuleCarrier O L F →ₗ[gammaStarCarrier O L]
      gammaStarModuleCarrier O L G :=
  Classical.choice (gammaStar_moduleHom_exists O L F G hL γ)

/-! ## A set of representatives and the Picard group -/

def InvertibleModuleObject {X : TopCat.{v}} (O : CommRingSheaf X) :=
  {L : CommRingSheafModule O // IsInvertibleModule O L}

noncomputable def invertibleModuleSetoid {X : TopCat.{v}}
    (O : CommRingSheaf X) : Setoid (InvertibleModuleObject O) where
  r L N := Nonempty (L.1 ≅ N.1)
  iseqv := {
    refl := fun L => ⟨Iso.refl L.1⟩
    symm := fun {L N} h => ⟨h.some.symm⟩
    trans := fun {L N P} h₁ h₂ => ⟨h₁.some ≪≫ h₂.some⟩
  }

def PicardRepresentativeSet {X : TopCat.{v}} (O : CommRingSheaf X) :=
  Set (CommRingSheafModule O)

theorem exists_picard_representative_set {X : TopCat.{v}}
    (O : CommRingSheaf X) :
    ∃ S : PicardRepresentativeSet O,
      ∀ L : CommRingSheafModule O, IsInvertibleModule O L →
        ∃! N : CommRingSheafModule O,
          S N ∧ Nonempty (L ≅ N) := by
  sorry

def PicardCarrier {X : TopCat.{v}} (O : CommRingSheaf X) : Type (v + 1) :=
  _root_.Quotient (invertibleModuleSetoid O)

theorem picardGroup_exists {X : TopCat.{v}} (O : CommRingSheaf X) :
    Nonempty (AddCommGroup (PicardCarrier O)) := by
  sorry

noncomputable instance picardGroupInstance {X : TopCat.{v}}
    (O : CommRingSheaf X) : AddCommGroup (PicardCarrier O) :=
  Classical.choice (picardGroup_exists O)

noncomputable def tensorInvertibleObject {X : TopCat.{v}}
    (O : CommRingSheaf X) (L N : InvertibleModuleObject O) :
    InvertibleModuleObject O :=
  ⟨tensorProductSheaf O L.1 N.1,
    tensorProduct_isInvertible O L.1 N.1 L.2 N.2⟩

theorem unit_isInvertible {X : TopCat.{v}} (O : CommRingSheaf X) :
    IsInvertibleModule O (sheafModuleUnit O) := by
  sorry

noncomputable def unitInvertibleObject {X : TopCat.{v}}
    (O : CommRingSheaf X) : InvertibleModuleObject O :=
  ⟨sheafModuleUnit O, unit_isInvertible O⟩

noncomputable def dualInvertibleObject {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : InvertibleModuleObject O) :
    InvertibleModuleObject O :=
  ⟨invertibleDual O L.1,
    (by sorry : IsInvertibleModule O (invertibleDual O L.1))⟩

noncomputable def picardClass {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : InvertibleModuleObject O) : PicardCarrier O :=
  _root_.Quotient.mk (invertibleModuleSetoid O) L

theorem picardClass_tensor {X : TopCat.{v}} (O : CommRingSheaf X)
    (L N : InvertibleModuleObject O) :
    picardClass O (tensorInvertibleObject O L N) =
      picardClass O L + picardClass O N := by
  sorry

theorem picardClass_dual {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : InvertibleModuleObject O) :
    picardClass O (dualInvertibleObject O L) =
      -(picardClass O L) := by
  sorry

theorem picardClass_unit {X : TopCat.{v}} (O : CommRingSheaf X) :
    picardClass O (unitInvertibleObject O) = 0 := by
  sorry

/-! ## Nonvanishing sections -/

abbrev stalkRing {X : TopCat.{v}} (O : CommRingSheaf X) (x : X) : Type v :=
  ↑(TopCat.Presheaf.stalk (C := CommRingCat.{v}) O.obj x)

def CommRingSheafHasLocalStalks {X : TopCat.{v}}
    (O : CommRingSheaf X) : Prop :=
  ∀ x : X,
    IsLocalRing (stalkRing O x)

def stalkMaximalSubmodule {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) (x : X)
    (hx : IsLocalRing (stalkRing O x)) :
    Submodule (stalkRing O x) (↑(commRingSheafModuleStalk L x)) := by
  letI := hx
  letI : Module (stalkRing O x)
      (↑(TopCat.Presheaf.stalk L.val.presheaf x)) :=
    Formalization.Books.Sheaves.Unit14.stalkModule O.obj L.val x
  exact IsLocalRing.maximalIdeal (stalkRing O x) •
    (⊤ : Submodule (stalkRing O x) (↑(commRingSheafModuleStalk L x)))

noncomputable def sectionGerm {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) (x : X) (s : globalModuleSections O L) :
    ↑(commRingSheafModuleStalk L x) :=
  TopCat.Presheaf.germ L.val.presheaf (⊤ : Opens X) x (by trivial) s

def nonvanishingLocus {X : TopCat.{v}} (O : CommRingSheaf X)
    (hO : CommRingSheafHasLocalStalks O) (L : CommRingSheafModule O)
    (s : globalModuleSections O L) : Set X :=
  {x | sectionGerm O L x s ∉ stalkMaximalSubmodule O L x (hO x)}

theorem nonvanishingLocus_isOpen {X : TopCat.{v}}
    (O : CommRingSheaf X) (hO : CommRingSheafHasLocalStalks O)
    (L : CommRingSheafModule O) (s : globalModuleSections O L) :
    IsOpen (nonvanishingLocus O hO L s) := by
  sorry

noncomputable def nonvanishingOpen {X : TopCat.{v}}
    (O : CommRingSheaf X) (hO : CommRingSheafHasLocalStalks O)
    (L : CommRingSheafModule O) (s : globalModuleSections O L) : Opens X :=
  ⟨nonvanishingLocus O hO L s, nonvanishingLocus_isOpen O hO L s⟩

abbrev localRestriction {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) (U : Opens X) :
    Mod (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf :=
  (openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj L

abbrev localUnit {X : TopCat.{v}} (O : CommRingSheaf X) (U : Opens X) :
    Mod (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf :=
  SheafOfModules.unit (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf

structure SectionInducedMapData {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) (U : Opens X)
    (s : globalModuleSections O L) where
  map : localUnit O U ⟶ localRestriction O L U
  isInducedBySection : Prop
  isInducedBySection_proof : isInducedBySection

theorem sectionInducedMap_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) (U : Opens X) (s : globalModuleSections O L) :
    Nonempty (SectionInducedMapData O L U s) := by
  sorry

noncomputable def sectionInducedMap {X : TopCat.{v}} (O : CommRingSheaf X)
    (L : CommRingSheafModule O) (U : Opens X) (s : globalModuleSections O L) :
    localUnit O U ⟶ localRestriction O L U :=
  (Classical.choice (sectionInducedMap_exists O L U s)).map

theorem sectionInducedMap_isInducedBySection {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) (U : Opens X)
    (s : globalModuleSections O L) :
    (Classical.choice (sectionInducedMap_exists O L U s)).isInducedBySection := by
  exact (Classical.choice (sectionInducedMap_exists O L U s)).isInducedBySection_proof

theorem nonvanishing_section_map_isIso {X : TopCat.{v}}
    (O : CommRingSheaf X) (hO : CommRingSheafHasLocalStalks O)
    (L : CommRingSheafModule O) (s : globalModuleSections O L) :
    IsIso (sectionInducedMap O L (nonvanishingOpen O hO L s) s) := by
  sorry

noncomputable def restrictGlobalSection {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O)
  (s : globalModuleSections O L) (U : Opens X) : sectionType O L U :=
  L.val.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s

structure SectionTensorProductData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) (U : Opens X)
    (s : sectionType O F U) (t : sectionType O G U) where
  value : sectionType O (tensorProductSheaf O F G) U
  representsTensorProduct : Prop
  representsTensorProduct_proof : representsTensorProduct

theorem sectionTensorProduct_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) (U : Opens X)
    (s : sectionType O F U) (t : sectionType O G U) :
    Nonempty (SectionTensorProductData O F G U s t) := by
  sorry

noncomputable def sectionTensorProduct {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) (U : Opens X)
    (s : sectionType O F U) (t : sectionType O G U) :
    sectionType O (tensorProductSheaf O F G) U :=
  (Classical.choice (sectionTensorProduct_exists O F G U s t)).value

noncomputable def sectionEvaluation {X : TopCat.{v}}
    (O : CommRingSheaf X) (L : CommRingSheafModule O) (U : Opens X)
    (s : sectionType O L U)
    (t : sectionType O (invertibleDual O L) U) :
    sectionType O (sheafModuleUnit O) U :=
  sheafModuleSectionsMap (commRingSheafToRingSheaf O)
    (invertibleDualEvaluation O L) U
    (sectionTensorProduct O L (invertibleDual O L) U s t)

noncomputable def unitSection {X : TopCat.{v}} (O : CommRingSheaf X)
    (U : Opens X) : sectionType O (sheafModuleUnit O) U := by
  change (O.obj.obj (op U) : Type v)
  exact 1

theorem exists_local_inverse_section {X : TopCat.{v}}
    (O : CommRingSheaf X) (hO : CommRingSheafHasLocalStalks O)
    (L : CommRingSheafModule O) (s : globalModuleSections O L) :
    ∃ t : sectionType O (invertibleDual O L)
        (nonvanishingOpen O hO L s),
      sectionEvaluation O L (nonvanishingOpen O hO L s)
          (restrictGlobalSection O L s (nonvanishingOpen O hO L s)) t =
        unitSection O (nonvanishingOpen O hO L s) := by
  sorry

/-! The pullback remark is stated in the same commutative-sheaf model as the
    tensor product and invertibility declarations above. -/

structure PullbackGlobalSectionData
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (Formalization.Books.Sheaves.Unit24.sheafRingPushforward f).obj
        (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    {L : CommRingSheafModule OY} (s : globalModuleSections OY L) where
  value : globalModuleSections OX ((pullbackModule f α).obj L)
  isPullbackOfSection : Prop
  isPullbackOfSection_proof : isPullbackOfSection

theorem pullback_global_section_exists
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (Formalization.Books.Sheaves.Unit24.sheafRingPushforward f).obj
        (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    {L : CommRingSheafModule OY} (s : globalModuleSections OY L) :
    Nonempty (PullbackGlobalSectionData f α s) := by
  sorry

noncomputable def pullbackGlobalSection
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (Formalization.Books.Sheaves.Unit24.sheafRingPushforward f).obj
        (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    {L : CommRingSheafModule OY} (s : globalModuleSections OY L) :
    globalModuleSections OX ((pullbackModule f α).obj L) :=
  (Classical.choice (pullback_global_section_exists f α s)).value

theorem pullback_nonvanishingLocus_eq
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (Formalization.Books.Sheaves.Unit24.sheafRingPushforward f).obj
        (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    (hOX : CommRingSheafHasLocalStalks OX)
    (hOY : CommRingSheafHasLocalStalks OY)
    {L : CommRingSheafModule OY} (s : globalModuleSections OY L) :
    f ⁻¹' nonvanishingLocus OY hOY L s =
      nonvanishingLocus OX hOX ((pullbackModule f α).obj L)
        (pullbackGlobalSection f α s) := by
  sorry

end

end Formalization.Books.Modules.Unit25
