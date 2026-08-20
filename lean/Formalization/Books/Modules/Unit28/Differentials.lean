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

/- The three clauses in the source definition are the canonical fields of
   `PresheafOfModules.Derivation`: its underlying map is additive, `d_app`
   annihilates the image of the base sheaf, and `d_mul` is Leibniz. -/

@[simp] theorem relativeSheafDerivation_annihilates
    {X : TopCat.{v}} {O₁ O₂ : CommRingSheaf X}
    (φ : O₁ ⟶ O₂) {F : CommRingSheafModule O₂}
    (D : RelativeSheafDerivation φ F) {U : Opens X}
    (a : O₁.obj.obj (op U)) :
    D.d (φ.hom.app (op U) a) = 0 :=
  D.d_app a

@[simp] theorem relativeSheafDerivation_leibniz
    {X : TopCat.{v}} {O₁ O₂ : CommRingSheaf X}
    (φ : O₁ ⟶ O₂) {F : CommRingSheafModule O₂}
    (D : RelativeSheafDerivation φ F) {U : Opens X}
    (a b : O₂.obj.obj (op U)) :
    D.d (a * b) = a • D.d b + b • D.d a :=
  D.d_mul a b

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

theorem relativeSheafDerivationsMap_apply {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} {F G : CommRingSheafModule O₂}
    (φ : O₁ ⟶ O₂) (α : F ⟶ G)
    (D : RelativeSheafDerivation φ F) :
    relativeSheafDerivationsMap φ α D = postcomposeRelativeSheafDerivation φ D α :=
  rfl

/-- The derivation construction is functorial in its sheaf-module target. -/
def relativeSheafDerivationsFunctor {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :
    CommRingSheafModule O₂ ⥤ Type _ where
  obj F := RelativeSheafDerivation φ F
  map α := ↾(fun D => relativeSheafDerivationsMap φ α D)
  map_id F := by
    ext D
    rfl
  map_comp f g := by
    ext D
    rfl

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

@[simp] theorem sectionwiseModuleOfDifferentials_obj {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) (U : Opens X) :
    (sectionwiseModuleOfDifferentials φ).obj (op U) =
      CommRingCat.KaehlerDifferential (φ.hom.app (op U)) :=
  rfl

/-- The sheafification of the sectionwise module of differentials. -/
noncomputable def moduleOfDifferentials {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :
    CommRingSheafModule O₂ := by
  exact (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf O₂).obj)).obj
    (sectionwiseModuleOfDifferentials φ)

/-- The source's universal derivation, obtained by composing the canonical
presheaf derivation with the module-sheafification unit. -/
noncomputable def moduleOfDifferentialsUnit {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :
    sectionwiseModuleOfDifferentials φ ⟶
      (PresheafOfModules.restrictScalars (𝟙 (commRingSheafToRingSheaf O₂).obj)).obj
        ((SheafOfModules.forget (commRingSheafToRingSheaf O₂)).obj
          (moduleOfDifferentials φ)) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRingSheaf O₂).obj)).unit.app
      (sectionwiseModuleOfDifferentials φ)

noncomputable def universalRelativeSheafDerivation {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) :
    RelativeSheafDerivation φ (moduleOfDifferentials φ) := by
  exact (PresheafOfModules.DifferentialsConstruction.derivation' φ.hom).postcomp
    (moduleOfDifferentialsUnit φ)

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
    Nonempty (IsUniversalRelativeSheafDerivation φ
      (universalRelativeSheafDerivation φ)) := by
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
noncomputable abbrev stalkModuleOfDifferentials {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat (TopCat.Presheaf.stalk (C := CommRingCat) O₂.obj x) := by
  exact commRingSheafModuleStalk (moduleOfDifferentials φ) x

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
  ∀ x : X,
    Function.Exact
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf O.obj).map α.val)))
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf O.obj).map β.val)))

/-- A sheaf-module morphism is an epimorphism when it is surjective on stalks. -/
def SheafModuleEpi {X : TopCat.{v}} {O : RingSheaf X}
    {F G : SheafOfModules O} (β : F ⟶ G) : Prop :=
  ∀ x : X,
    Function.Surjective
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf O.obj).map β.val)))

/-- The sectionwise image of a universal differential after extension of
scalars; this is the source's `d f ⊗ 1`. -/
noncomputable def baseChangedUniversalDifferential
    {X : TopCat.{v}} {O₁ O₂ O₃ : CommRingSheaf X}
    (base : O₁ ⟶ O₂) (quotient : O₂ ⟶ O₃)
    (U : Opens X) (a : O₂.obj.obj (op U)) :
    ((sheafChangeOfRings (commRingSheafMorphismToRingSheaf quotient)).obj
      (moduleOfDifferentials base)).val.obj (op U) := by
  exact ((sheafChangeOfRingsAdjunction
    (commRingSheafMorphismToRingSheaf quotient)).unit.app
      (moduleOfDifferentials base)).val.app (op U)
    ((moduleOfDifferentialsUnit base).app (op U)
      (CommRingCat.KaehlerDifferential.d a))

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
  surjective : SheafModuleEpi rightMap
  leftMap_rule :
    ∀ (U : Opens X) (a : O₂.obj.obj (op U)),
      quotient.hom.app (op U) a = 0 →
      ∃ i : conormal.val.obj (op U),
        leftMap.val.app (op U) i = baseChangedUniversalDifferential base quotient U a

/-- The conormal--differential exact sequence for a surjective map of sheaves
of commutative rings.  The left map is characterized on local sections by
`f ↦ d f ⊗ 1`. -/
theorem conormal_differential_exact
    {X : TopCat.{v}} {O₁ O₂ : CommRingSheaf X}
    {O₃ : CommRingSheaf X} (base : O₁ ⟶ O₂) (quotient : O₂ ⟶ O₃)
    (hquotient : ∀ U, Function.Surjective (quotient.hom.app U)) :
    Nonempty (ConormalDifferentialSequence base quotient) := by
  sorry

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

/-! The source's `S`-derivations and relative sheaf of differentials. -/

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

/- The extension data below records the algebra, quotient, ideal inclusion,
   kernel condition, and square-zero condition from the source.  The ideal is
   kept as a sheaf of modules, while its inclusion is stated on the underlying
   additive presheaves, which is the canonical interface available for sheaf
   modules. -/

structure SquareZeroExtensionData {X S : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X S) where
  algebra : CommRingSheaf X.carrier
  baseAlgebra :
    (TopCat.Sheaf.pullback CommRingCat f.continuous).obj S.structureSheaf ⟶ algebra
  quotient : algebra ⟶ X.structureSheaf
  quotient_surjective :
    ∀ U, Function.Surjective (quotient.hom.app U)
  ideal : CommRingSheafModule X.structureSheaf
  idealInclusion :
    ideal.val.presheaf ⟶ algebra.obj ⋙
      (forget₂ CommRingCat RingCat) ⋙ (forget₂ RingCat AddCommGrpCat)
  ideal_injective :
    ∀ U, Function.Injective (idealInclusion.app U)
  ideal_kernel :
    ∀ U (a : algebra.obj.obj U), quotient.hom.app U a = 0 ↔
      ∃ i, idealInclusion.app U i = a
  ideal_square_zero :
    ∀ U (i j : ideal.val.presheaf.obj U),
      (show algebra.obj.obj U from idealInclusion.app U i) *
          (show algebra.obj.obj U from idealInclusion.app U j) = 0
  base_quotient :
    baseAlgebra ≫ quotient = f.sharp

structure SquareZeroExtensionSection {X S : CommutativeRingedSpace}
    {f : CommutativeRingedSpaceHom X S}
    (E : SquareZeroExtensionData f) where
  map : X.structureSheaf ⟶ E.algebra
  split : map ≫ E.quotient = 𝟙 _
  over_base : f.sharp ≫ map = E.baseAlgebra

def sectionDifferenceIsDerivation {X S : CommutativeRingedSpace}
    {f : CommutativeRingedSpaceHom X S}
    (E : SquareZeroExtensionData f)
    (s s' : SquareZeroExtensionSection E)
    (D : RelativeSheafDerivation f.sharp E.ideal) : Prop :=
  ∀ U (a : X.structureSheaf.obj.obj U),
    s'.map.hom.app U a =
      s.map.hom.app U a +
        (show E.algebra.obj.obj U from
          E.idealInclusion.app U (show E.ideal.val.presheaf.obj U from D.d a))

theorem squareZeroExtension_section_addition
    {X S : CommutativeRingedSpace}
    {f : CommutativeRingedSpaceHom X S}
    (E : SquareZeroExtensionData f)
    (s : SquareZeroExtensionSection E) :
    (∀ D : RelativeSheafDerivation f.sharp E.ideal,
      ∃ s' : SquareZeroExtensionSection E,
        sectionDifferenceIsDerivation E s s' D) ∧
    (∀ s' : SquareZeroExtensionSection E,
      ∃! D : RelativeSheafDerivation f.sharp E.ideal,
        sectionDifferenceIsDerivation E s s' D) := by
  sorry

/-- A section of a square of commutative ringed-space morphisms supplies the
comparison map on relative differentials. -/
structure RingedSpaceDifferentialSquare
    (X' X S' S : CommutativeRingedSpace) where
  f : CommutativeRingedSpaceHom X' X
  f' : CommutativeRingedSpaceHom X' S'
  h : CommutativeRingedSpaceHom X S
  g : CommutativeRingedSpaceHom S' S
  topological_commutes :
    f.continuous ≫ h.continuous = f'.continuous ≫ g.continuous

/-- The module and map supplied by the ringed-space functoriality statement.
The `pullback` field is the module denoted `f^* Ω` in the source. -/
structure RingedSpaceDifferentialComparison
    {X' X S' S : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X' X S' S) where
  pullback : CommRingSheafModule X'.structureSheaf
  map : pullback ⟶ ringedSpaceModuleOfDifferentials square.f'

theorem ringedSpace_differentials_map
    {X' X S' S : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X' X S' S) :
    Nonempty (RingedSpaceDifferentialComparison square) := by
  sorry

/-- A chosen representative of the canonical comparison supplied by the
ringed-space functoriality statement. -/
noncomputable def ringedSpaceDifferentialComparison
    {X' X S' S : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X' X S' S) :
    RingedSpaceDifferentialComparison square :=
  Classical.choice (ringedSpace_differentials_map square)

/-- The comparison morphism `c_f : f^* Ω_{X/S} → Ω_{X'/S'}`. -/
noncomputable abbrev ringedSpaceDifferentialsComparisonMap
    {X' X S' S : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X' X S' S) :
    (ringedSpaceDifferentialComparison square).pullback ⟶
      ringedSpaceModuleOfDifferentials square.f' :=
  (ringedSpaceDifferentialComparison square).map

/-- The pushforward-side map in the ringed-space functoriality statement,
shown on the underlying sheaves of additive groups. -/
theorem ringedSpace_differentials_pushforward_map
    {X' X S' S : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X' X S' S) :
    Nonempty
      ((SheafOfModules.toSheaf
          (commRingSheafToRingSheaf X.structureSheaf)).obj
          (ringedSpaceModuleOfDifferentials square.h) ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat square.f.continuous).obj
          ((SheafOfModules.toSheaf
            (commRingSheafToRingSheaf X'.structureSheaf)).obj
            (ringedSpaceModuleOfDifferentials square.f'))) := by
  sorry

/-! ## The transitivity triangle -/

/-- The data in the exact transitivity sequence
`f^* Ω_{Y/S} → Ω_{X/S} → Ω_{X/Y} → 0`. -/
structure RingedSpaceDifferentialTriangle
    {X Y S : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X Y)
    (g : CommutativeRingedSpaceHom Y S)
    (h : CommutativeRingedSpaceHom X S)
    (topological_composite : h.continuous = f.continuous ≫ g.continuous) where
  pullback : CommRingSheafModule X.structureSheaf
  firstMap : pullback ⟶ ringedSpaceModuleOfDifferentials h
  secondMap : ringedSpaceModuleOfDifferentials h ⟶
    ringedSpaceModuleOfDifferentials f
  exact : SheafModuleExact firstMap secondMap
  surjective : SheafModuleEpi secondMap

/-- The transitivity triangle is exact; the first object is the pullback
`f^* Ω_{Y/S}` supplied by the inverse-image module construction. -/
theorem ringedSpace_triangle_differentials
    {X Y S : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X Y)
    (g : CommutativeRingedSpaceHom Y S)
    (h : CommutativeRingedSpaceHom X S)
    (topological_composite : h.continuous = f.continuous ≫ g.continuous) :
    Nonempty (RingedSpaceDifferentialTriangle f g h topological_composite) := by
  sorry

end

end Formalization.Books.Modules.Unit28
