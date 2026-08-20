import Formalization.Books.Sheaves.Unit17.Modules
import Formalization.Books.Sheaves.Unit25.RingedSpaces
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Module

/-!
# Sheaves of Modules, Chapter 28: Modules of differentials

The canonical presheaf-level construction is Mathlib's
`PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`.  This
file records the sheaf-level source interfaces using the established sheaf,
module, ringed-space, and sheafification APIs.
-/

namespace Formalization.Books.Modules.Unit28

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v

noncomputable section

/-! ## Relative derivations -/

/-- A relative derivation of sheaves of commutative rings with values in a
sheaf of modules.  This is Mathlib's canonical presheaf derivation structure,
with the target restricted to a sheaf of modules. -/
abbrev RelativeSheafDerivation {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) : Type _ :=
  PresheafOfModules.Derivation' F.val φ.hom

/-- Postcomposition of a relative derivation by a morphism of modules. -/
def postcomposeRelativeSheafDerivation {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} {F G : CommRingSheafModule O₂}
    (φ : O₁ ⟶ O₂) (D : RelativeSheafDerivation φ F) (α : F ⟶ G) :
    RelativeSheafDerivation φ G :=
  D.postcomp α.val

/-- The induced map on derivations for a module morphism. -/
def relativeSheafDerivationsMap {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} {F G : CommRingSheafModule O₂}
    (φ : O₁ ⟶ O₂) (α : F ⟶ G) :
    RelativeSheafDerivation φ F → RelativeSheafDerivation φ G :=
  fun D => postcomposeRelativeSheafDerivation φ D α

/-- On the top open, a sheaf derivation gives the corresponding derivation of
the rings of global sections. -/
def globalSectionsDerivation {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} {F : CommRingSheafModule O₂}
    (φ : O₁ ⟶ O₂) (D : RelativeSheafDerivation φ F) :
    ModuleCat.Derivation (F.val.obj (op (⊤ : Opens X)))
      (φ.hom.app (op (⊤ : Opens X))) :=
  D.app (op (⊤ : Opens X))

/-! ## The sheaf of differentials -/

/-- The presheaf whose sections over an open are the ordinary module of
Kähler differentials of the corresponding section rings. -/
noncomputable def sectionwiseModuleOfDifferentials {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom

/-- The sheafification of the sectionwise module of differentials. -/
noncomputable def moduleOfDifferentials {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :
    CommRingSheafModule O₂ := by
  exact (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf O₂).obj)).obj
    (sectionwiseModuleOfDifferentials φ)

/-- The source's universal derivation, obtained by composing the canonical
presheaf derivation with the module-sheafification unit. -/
noncomputable def universalRelativeSheafDerivation {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :
    RelativeSheafDerivation φ (moduleOfDifferentials φ) := by
  sorry

/-- The universal property of the sheaf of differentials, expressed among
sheaf targets as in the textbook. -/
structure IsUniversalRelativeSheafDerivation {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} {F : CommRingSheafModule O₂}
    (φ : O₁ ⟶ O₂) (D : RelativeSheafDerivation φ F) where
  desc : ∀ {G : CommRingSheafModule O₂}, RelativeSheafDerivation φ G →
    SheafOfModules.Hom F G
  fac : ∀ {G : CommRingSheafModule O₂} (D' : RelativeSheafDerivation φ G),
    postcomposeRelativeSheafDerivation φ D (desc D') = D'
  postcompose_injective : ∀ {G : CommRingSheafModule O₂}
    (α β : SheafOfModules.Hom F G),
    postcomposeRelativeSheafDerivation φ D α =
      postcomposeRelativeSheafDerivation φ D β → α = β

/-- The sheafification construction has the universal property of the module
of differentials. -/
theorem moduleOfDifferentials_isUniversal {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :
    IsUniversalRelativeSheafDerivation φ
      (universalRelativeSheafDerivation φ) := by
  sorry

/-- The module of differentials is the sheaf associated to the presheaf of
sectionwise Kähler differentials. -/
theorem moduleOfDifferentials_isSheafification {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :
    moduleOfDifferentials φ =
      (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf O₂).obj)).obj
        (sectionwiseModuleOfDifferentials φ) := by
  rfl

/-! ## Restriction, inverse image, stalks, and functoriality -/

/-- Restriction of a commutative-ring sheaf to an open subspace. -/
noncomputable abbrev restrictCommRingSheaf {X : TopCat.{v}} (U : Opens X)
    (O : CommRingSheaf X) :
    CommRingSheaf ((Opens.toTopCat X).obj U) :=
  (Opens.sheafRestrict (C := CommRingCat) U).obj O

/-- The canonical restriction comparison for relative differentials. -/
theorem restrict_moduleOfDifferentials {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) (U : Opens X) :
    Nonempty
      (((Opens.sheafRestrict (C := AddCommGrpCat) U).obj
          ((SheafOfModules.toSheaf (commRingSheafToRingSheaf O₂)).obj
            (moduleOfDifferentials φ))) ≅
        (SheafOfModules.toSheaf
          (commRingSheafToRingSheaf (restrictCommRingSheaf U O₂))).obj
          (moduleOfDifferentials
            ((Opens.sheafRestrict (C := CommRingCat) U).map φ))) := by
  sorry

/-- Pullback of a commutative-ring sheaf along a continuous map. -/
noncomputable abbrev pullbackCommRingSheaf {X Y : TopCat.{v}} (f : X ⟶ Y)
    (O : CommRingSheaf Y) : CommRingSheaf X :=
  (TopCat.Sheaf.pullback CommRingCat f).obj O

/-- Pullback comparison for modules of differentials. -/
theorem pullback_moduleOfDifferentials {X Y : TopCat.{v}}
    (f : X ⟶ Y) {O₁ O₂ : CommRingSheaf Y} (φ : O₁ ⟶ O₂) :
    Nonempty
      ((TopCat.Sheaf.pullback AddCommGrpCat f).obj
          ((SheafOfModules.toSheaf (commRingSheafToRingSheaf O₂)).obj
            (moduleOfDifferentials φ)) ≅
        (SheafOfModules.toSheaf
          (commRingSheafToRingSheaf (pullbackCommRingSheaf f O₂))).obj
          (moduleOfDifferentials
            ((TopCat.Sheaf.pullback CommRingCat f).map φ))) := by
  sorry

/-- The stalk of the sheaf of differentials is the module of differentials of
the stalk rings. -/
noncomputable def stalkModuleOfDifferentials {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat (TopCat.Presheaf.stalk (C := CommRingCat) O₂.obj x) := by
  letI : Module (TopCat.Presheaf.stalk (C := CommRingCat) O₂.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
        (moduleOfDifferentials φ).val.presheaf x)) :=
    Formalization.Books.Sheaves.Unit14.stalkModule O₂.obj
      (moduleOfDifferentials φ).val x
  exact ModuleCat.of _
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (moduleOfDifferentials φ).val.presheaf x))

theorem stalk_moduleOfDifferentials {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) (x : X) :
    Nonempty
      (stalkModuleOfDifferentials φ x ≅
        CommRingCat.KaehlerDifferential
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map φ.hom)) := by
  sorry

/-- A commutative square of sheaves of rings induces a map of modules of
differentials. -/
theorem map_moduleOfDifferentials {X : TopCat.{v}}
    {O₁ O₂ O₁' O₂' : CommRingSheaf X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (a : O₁ ⟶ O₁') (b : O₂ ⟶ O₂')
    (comm : a ≫ φ' = φ ≫ b) :
    Nonempty ((sheafChangeOfRings (commRingSheafMorphismToRingSheaf b)).obj
      (moduleOfDifferentials φ) ⟶ moduleOfDifferentials φ') := by
  sorry

/-! ## Exact conormal sequence -/

/-- Exactness of a morphism of sheaves of modules, checked on every open. -/
def SheafModuleExact {X : TopCat.{v}} {O : RingSheaf X}
    {F G H : SheafOfModules O} (α : F ⟶ G) (β : G ⟶ H) : Prop :=
  ∀ U, Function.Exact ((α.val.app U).hom) ((β.val.app U).hom)

/-- The sheaf-level data in the conormal--differential sequence. -/
structure ConormalDifferentialSequence {X : TopCat.{v}}
    {O₁ O₂ O₃ : CommRingSheaf X} (base : O₁ ⟶ O₂) (quotient : O₂ ⟶ O₃) where
  conormal : CommRingSheafModule O₃
  leftMap : conormal ⟶
    (sheafChangeOfRings (commRingSheafMorphismToRingSheaf quotient)).obj
      (moduleOfDifferentials base)
  rightMap :
    (sheafChangeOfRings (commRingSheafMorphismToRingSheaf quotient)).obj
      (moduleOfDifferentials base) ⟶
    moduleOfDifferentials (base ≫ quotient)
  exact : SheafModuleExact leftMap rightMap

/-- The conormal--differential exact sequence for a surjective map of sheaves
of commutative rings.  The left map is characterized on local sections by
`f ↦ d f ⊗ 1`. -/
theorem conormal_differential_exact
    {X : TopCat.{v}} {O₁ O₂ : CommRingSheaf X}
    {O₃ : CommRingSheaf X} (base : O₁ ⟶ O₂) (quotient : O₂ ⟶ O₃)
    (hquotient : ∀ U, Function.Surjective (quotient.hom.app U)) :
    Nonempty (ConormalDifferentialSequence base quotient) := by
  sorry

/-! ## Ringed-space terminology and deformation lemma -/

/-- A commutative ringed space, used because relative differentials are
defined for commutative structure sheaves. -/
structure CommutativeRingedSpace where
  carrier : TopCat.{v}
  structureSheaf : CommRingSheaf carrier

/-- A morphism of commutative ringed spaces, with the inverse-image map on
structure sheaves. -/
structure CommutativeRingedSpaceHom (X Y : CommutativeRingedSpace) where
  continuous : X.carrier ⟶ Y.carrier
  sharp : (TopCat.Sheaf.pullback CommRingCat continuous).obj Y.structureSheaf ⟶
    X.structureSheaf

/-- An `S`-derivation into a sheaf of `O_X`-modules. -/
abbrev RingedSpaceDerivation {X S : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X S)
    (F : CommRingSheafModule X.structureSheaf) : Type _ :=
  RelativeSheafDerivation f.sharp F

/-- The sheaf of relative differentials of a commutative ringed space. -/
noncomputable abbrev ringedSpaceModuleOfDifferentials {X S : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X S) :
    CommRingSheafModule X.structureSheaf :=
  moduleOfDifferentials f.sharp

/-- A section of a square of commutative ringed-space morphisms supplies the
comparison map on relative differentials. -/
structure RingedSpaceDifferentialSquare
    (X X' S S' : CommutativeRingedSpace) where
  f : CommutativeRingedSpaceHom X S
  f' : CommutativeRingedSpaceHom X' S'
  mapBase : CommutativeRingedSpaceHom S S'
  mapTotal : CommutativeRingedSpaceHom X X'
  comparison : Prop

/-- The module and map supplied by the ringed-space functoriality statement.
The `pullback` field is the module denoted `f^* Ω` in the source. -/
structure RingedSpaceDifferentialComparison
    {X X' S S' : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X X' S S') where
  pullback : CommRingSheafModule X'.structureSheaf
  map : pullback ⟶ ringedSpaceModuleOfDifferentials square.f'

theorem ringedSpace_differentials_map
    {X X' S S' : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X X' S S') :
    Nonempty (RingedSpaceDifferentialComparison square) := by
  sorry

end

end Formalization.Books.Modules.Unit28
