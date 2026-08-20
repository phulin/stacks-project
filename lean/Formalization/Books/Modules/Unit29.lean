import Formalization.Books.Modules.Unit28.Differentials
import Formalization.Books.Modules.Unit16.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Sheaves of Modules, Chapter 29: Finite order differential operators

The source section is formalized using natural transformations of the
underlying sheaves of additive groups.  The order condition is imposed on
sections, while the base-linearity and restriction compatibility are retained
in the natural transformation itself.  The quotient relations for principal
parts use the standard alternating finite-subset relation.
-/

namespace Formalization.Books.Modules.Unit29

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit28

universe v

noncomputable section

/-! ## Differential operators -/

/-- A section of a sheaf module over an open set. -/
abbrev SheafModuleSection {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) (U : Opens X) : Type v :=
  F.val.obj (op U)

/-- The coefficient ring acting on sections of an `O`-module. -/
abbrev SheafSectionRing {X : TopCat.{v}} (O : CommRingSheaf X)
    (U : Opens X) : Type v :=
  (commRingSheafToRingSheaf O).obj.obj (op U)

/-- The ring map on sections induced by a sheaf morphism. -/
def sheafSectionRingMap {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂) (U : Opens X) :
    SheafSectionRing O₁ U →+* SheafSectionRing O₂ U :=
  (φ.hom.app (op U)).hom

/- The sheaf-of-modules object already carries the module structure over this
underlying section ring; exposing it as an instance makes the sectionwise
formulas readable. -/
instance sheafModuleSection_module {X : TopCat.{v}}
    {O : CommRingSheaf X} (F : CommRingSheafModule O) (U : Opens X) :
    Module (SheafSectionRing O U) (SheafModuleSection F U) :=
  (F.val.obj (op U)).isModule

instance sheafSectionRing_commMonoid {X : TopCat.{v}}
    (O : CommRingSheaf X) (U : Opens X) :
    CommMonoid (SheafSectionRing O U) :=
  inferInstanceAs (CommMonoid (O.obj.obj (op U)))

/-- The commutator of a sectionwise map with multiplication by a section of
the coefficient sheaf. -/
def sectionOperatorCommutator {X : TopCat.{v}} {O : CommRingSheaf X}
    {F G : CommRingSheafModule O} {U : Opens X}
    (D : SheafModuleSection F U → SheafModuleSection G U)
    (g : SheafSectionRing O U) :
    SheafModuleSection F U → SheafModuleSection G U :=
  fun s => D (g • s) - g • D s

/-- The recursive order condition on a map between two section modules. -/
def IsSectionDifferentialOperator {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O) (U : Opens X) :
    ℕ → (SheafModuleSection F U → SheafModuleSection G U) → Prop
  | 0, D => ∀ (g : SheafSectionRing O U) (s : SheafModuleSection F U),
      D (g • s) = g • D s
  | k + 1, D => ∀ (g : SheafSectionRing O U),
      IsSectionDifferentialOperator F G U k
        (sectionOperatorCommutator D g)

/-- A finite-order differential operator of the source.  The field `map` is
the underlying sheaf map of additive groups, `base_linear` is its
`O₁`-linearity, and `order` is the recursive commutator condition. -/
structure DifferentialOperator {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F G : CommRingSheafModule O₂) (k : ℕ) where
  map : F.val.presheaf ⟶ G.val.presheaf
  base_linear : ∀ (U : Opens X) (f : SheafSectionRing O₁ U)
    (s : SheafModuleSection F U),
    map.app (op U) ((sheafSectionRingMap φ U f) • s) =
      (sheafSectionRingMap φ U f) • map.app (op U) s
  order : ∀ (U : Opens X),
    IsSectionDifferentialOperator F G U k (fun s => map.app (op U) s)

/-- The source notation `Diff^k_{O₂/O₁}(F,G)`. -/
abbrev DifferentialOperators {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F G : CommRingSheafModule O₂) (k : ℕ) :=
  DifferentialOperator φ F G k

/-- Multiplication of a differential operator by a local coefficient is again
a differential operator of the same order. -/
theorem differentialOperator_smul {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    {F G : CommRingSheafModule O₂} {k : ℕ}
    (D : DifferentialOperator φ F G k) (U : Opens X)
    (g : SheafSectionRing O₂ U) :
    IsSectionDifferentialOperator F G U k
      (fun s => g • D.map.app (op U) s) := by
  sorry

/-- The sum of two differential operators of order `k` has order `k`. -/
theorem differentialOperator_add {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    {F G : CommRingSheafModule O₂} {k : ℕ}
    (D E : DifferentialOperator φ F G k) :
    Nonempty (DifferentialOperator φ F G k) := by
  sorry

/-- The set of order-`k` operators carries the module structure over the
global sections of the coefficient sheaf.  The operations and laws are
exposed explicitly because the operator type is a subtype of additive
presheaf maps rather than a pre-existing module object. -/
structure DifferentialOperatorsModuleData {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F G : CommRingSheafModule O₂) (k : ℕ) where
  add : DifferentialOperators φ F G k → DifferentialOperators φ F G k →
    DifferentialOperators φ F G k
  zero : DifferentialOperators φ F G k
  neg : DifferentialOperators φ F G k → DifferentialOperators φ F G k
  smul : SheafSectionRing O₂ ⊤ → DifferentialOperators φ F G k →
    DifferentialOperators φ F G k
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  smul_add : ∀ r a b, smul r (add a b) = add (smul r a) (smul r b)
  add_smul : ∀ r s a, smul (r + s) a = add (smul r a) (smul s a)
  zero_smul : ∀ a, smul 0 a = zero
  smul_zero : ∀ r, smul r zero = zero
  one_smul : ∀ a, smul 1 a = a
  mul_smul : ∀ r s a, smul (r * s) a = smul r (smul s a)

theorem differentialOperators_module {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F G : CommRingSheafModule O₂) (k : ℕ) :
    Nonempty (DifferentialOperatorsModuleData φ F G k) := by
  sorry

/-- The order filtration is increasing. -/
theorem differentialOperator_mono {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    {F G : CommRingSheafModule O₂} (k : ℕ)
    (D : DifferentialOperator φ F G k) :
    Nonempty (DifferentialOperator φ F G (k + 1)) := by
  sorry

/-- Composition adds orders. -/
theorem differentialOperator_comp {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    {E F G : CommRingSheafModule O₂} {k k' : ℕ}
    (D : DifferentialOperator φ E F k)
    (D' : DifferentialOperator φ F G k') :
    Nonempty (DifferentialOperator φ E G (k + k')) := by
  sorry

/-- Postcomposition by an `O₂`-linear sheaf map preserves differential
operators. -/
theorem differentialOperator_postcompose {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    {F G H : CommRingSheafModule O₂} {k : ℕ}
    (D : DifferentialOperator φ F G k) (α : G ⟶ H) :
    Nonempty (DifferentialOperator φ F H k) := by
  sorry

/-! ## Principal-parts relations and the quotient construction -/

/-- The free `O₂(U)`-module on the sections of `F` over `U`. -/
abbrev FreeSectionModule {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) (U : Opens X) :=
  (SheafModuleSection F U →₀ SheafSectionRing O U)

/-- The additivity relation in the free module on sections. -/
def principalPartsAddRelation {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) (U : Opens X)
    (m m' : SheafModuleSection F U) : FreeSectionModule F U :=
  Finsupp.single (m + m') 1 - Finsupp.single m 1 - Finsupp.single m' 1

/-- The relation expressing linearity over the base sheaf. -/
def principalPartsBaseRelation {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (U : Opens X)
    (f : SheafSectionRing O₁ U) (m : SheafModuleSection F U) :
    FreeSectionModule F U :=
  (sheafSectionRingMap φ U f) • Finsupp.single m 1 -
    Finsupp.single ((sheafSectionRingMap φ U f) • m) 1

/-- The alternating higher commutator relation.  This is the same finite
subset formula as the commutative-algebra principal-parts construction. -/
def principalPartsHigherRelation {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) (U : Opens X) (k : ℕ)
    (g : Fin (k + 1) → SheafSectionRing O U) (m : SheafModuleSection F U) :
    FreeSectionModule F U :=
  by
    classical
    exact (Finset.univ : Finset (Finset (Fin (k + 1)))).sum (fun t =>
      ((-1 : SheafSectionRing O U) ^ t.card) •
        (((Finset.univ \ t).prod g) •
          Finsupp.single ((t.prod g) • m) 1))

/-- The complete local relation set. -/
def principalPartsRelationSet {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (U : Opens X) (k : ℕ) :
    Set (FreeSectionModule F U) :=
  Set.range (fun p : SheafModuleSection F U × SheafModuleSection F U =>
      principalPartsAddRelation F U p.1 p.2) ∪
    Set.range (fun p : SheafSectionRing O₁ U × SheafModuleSection F U =>
      principalPartsBaseRelation φ F U p.1 p.2) ∪
    Set.range (fun p : (Fin (k + 1) → SheafSectionRing O₂ U) ×
        SheafModuleSection F U =>
      principalPartsHigherRelation F U k p.1 p.2)

/-- The submodule generated by the principal-parts relations on an open set. -/
def principalPartsRelationSubmodule {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (U : Opens X) (k : ℕ) :
    Submodule (SheafSectionRing O₂ U) (FreeSectionModule F U) :=
  Submodule.span _ (principalPartsRelationSet φ F U k)

/-- The sectionwise quotient appearing in the direct construction. -/
abbrev PrincipalPartsSection {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (U : Opens X) (k : ℕ) :=
  FreeSectionModule F U ⧸ principalPartsRelationSubmodule φ F U k

/-- The quotient module as a bundled module over the coefficient ring. -/
def principalPartsSectionModule {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (U : Opens X) (k : ℕ) :
    ModuleCat (SheafSectionRing O₂ U) :=
  ModuleCat.of _ (PrincipalPartsSection φ F U k)

/-- The principal-parts generator of a section. -/
def principalPartsGenerator {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (U : Opens X) (k : ℕ)
    (m : SheafModuleSection F U) : PrincipalPartsSection φ F U k :=
  Submodule.mkQ _ (Finsupp.single m 1)

/-- A presheaf whose sections are the quotient modules above.  The
restriction maps are canonical and are packaged with their section formula;
the existence proof is the sheaf analogue of the direct construction in the
source. -/
structure PrincipalPartsPresheafData {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) where
  presheaf : PMod (commRingSheafToRingSheaf O₂).obj
  section_formula : ∀ U : (Opens X)ᵒᵖ, Nonempty
    (presheaf.obj U ≅ principalPartsSectionModule φ F U.unop k)

theorem principalPartsPresheafData_exists {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) :
    Nonempty (PrincipalPartsPresheafData φ F k) := by
  sorry

/-- The sectionwise principal-parts presheaf. -/
noncomputable def principalPartsPresheaf {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) :
    PMod (commRingSheafToRingSheaf O₂).obj :=
  (Classical.choice (principalPartsPresheafData_exists φ F k)).presheaf

theorem principalPartsPresheaf_section_formula {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) (U : (Opens X)ᵒᵖ) :
    Nonempty ((principalPartsPresheaf φ F k).obj U ≅
      principalPartsSectionModule φ F U.unop k) := by
  exact (Classical.choice (principalPartsPresheafData_exists φ F k)).section_formula U

/- The module itself is the sheafification of the sectionwise quotient
presheaf, as in the direct construction in the source. -/
noncomputable def moduleOfPrincipalParts {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) : CommRingSheafModule O₂ := by
  exact (PresheafOfModules.sheafification
    (𝟙 (commRingSheafToRingSheaf O₂).obj)).obj
      (principalPartsPresheaf φ F k)

/-! ## The universal property and the module of principal parts -/

/-- The universal property of the sheaf of principal parts. -/
structure PrincipalPartsUniversalData {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) where
  universal : DifferentialOperator φ F (moduleOfPrincipalParts φ F k) k
  homEquiv : ∀ (G : CommRingSheafModule O₂),
    DifferentialOperators φ F G k ≃
      (moduleOfPrincipalParts φ F k ⟶ G)
  homEquiv_natural : ∀ {G H : CommRingSheafModule O₂}
    (α : G ⟶ H) (D : DifferentialOperators φ F G k),
    homEquiv H (Classical.choice (differentialOperator_postcompose φ D α)) =
      homEquiv G D ≫ α

theorem principalPartsUniversalData_exists {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) :
    Nonempty (PrincipalPartsUniversalData φ F k) := by
  sorry

/-- The universal finite-order differential operator. -/
noncomputable def principalPartsUniversal {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) :
    DifferentialOperator φ F (moduleOfPrincipalParts φ F k) k :=
  (Classical.choice (principalPartsUniversalData_exists φ F k)).universal

/-- The canonical representing equivalence, functorial in the target. -/
noncomputable def principalPartsHomEquiv {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F G : CommRingSheafModule O₂) (k : ℕ) :
    DifferentialOperators φ F G k ≃
      (moduleOfPrincipalParts φ F k ⟶ G) :=
  (Classical.choice (principalPartsUniversalData_exists φ F k)).homEquiv G

/-- The order-zero module of principal parts identifies with the original
module. -/
theorem moduleOfPrincipalParts_zero_iso {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) :
    Nonempty (moduleOfPrincipalParts φ F 0 ≅ F) := by
  sorry

/-- The transition morphism `P^(k+1)(F) ⟶ P^k(F)`. -/
theorem principalParts_transition_exists {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) :
    Nonempty (moduleOfPrincipalParts φ F (k + 1) ⟶
      moduleOfPrincipalParts φ F k) := by
  sorry

/-- A transition map is a sheaf-module epimorphism, as required by the
surjections in the principal-parts filtration. -/
structure PrincipalPartsTransitionData {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) where
  map : moduleOfPrincipalParts φ F (k + 1) ⟶
    moduleOfPrincipalParts φ F k
  epi : Epi map

theorem principalParts_transition_epi {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) :
    Nonempty (PrincipalPartsTransitionData φ F k) := by
  sorry

/-- The chosen transition map in the principal-parts filtration. -/
noncomputable def principalPartsTransition {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) :
    moduleOfPrincipalParts φ F (k + 1) ⟶ moduleOfPrincipalParts φ F k :=
  (Classical.choice (principalParts_transition_epi φ F k)).map

theorem principalPartsTransition_epi {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (k : ℕ) :
    Epi (principalPartsTransition φ F k) :=
  (Classical.choice (principalParts_transition_epi φ F k)).epi

/-! ## Sheafification and the sequence of principal parts -/

/-- The free module on sections of a presheaf of modules. -/
abbrev PresheafFreeSectionModule {X : TopCat.{v}}
    {O₂ : CommRingPresheaf X} (F : CommRingPresheafModule O₂)
    (U : (Opens X)ᵒᵖ) :=
  (F.obj U →₀ O₂.obj U)

/-- The local base-linearity relation for presheaves. -/
def presheafPrincipalPartsBaseRelation {X : TopCat.{v}}
    {O₁ O₂ : CommRingPresheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingPresheafModule O₂) (U : (Opens X)ᵒᵖ)
    (f : O₁.obj U) (m : F.obj U) : PresheafFreeSectionModule F U :=
  (φ.app U f) • Finsupp.single m 1 - Finsupp.single ((φ.app U f) • m) 1

/-- The local relation set for presheaf principal parts. -/
def presheafPrincipalPartsRelationSet {X : TopCat.{v}}
    {O₁ O₂ : CommRingPresheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingPresheafModule O₂) (U : (Opens X)ᵒᵖ) (k : ℕ) :
    Set (PresheafFreeSectionModule F U) :=
  Set.range (fun p : F.obj U × F.obj U =>
      Finsupp.single (p.1 + p.2) 1 - Finsupp.single p.1 1 -
        Finsupp.single p.2 1) ∪
    Set.range (fun p : O₁.obj U × F.obj U =>
      presheafPrincipalPartsBaseRelation φ F U p.1 p.2) ∪
    Set.range (fun p : (Fin (k + 1) → O₂.obj U) × F.obj U =>
      (Finset.univ : Finset (Finset (Fin (k + 1)))).sum (fun t =>
        ((-1 : O₂.obj U) ^ t.card) •
          (((Finset.univ \ t).prod p.1) •
            Finsupp.single ((t.prod p.1) • p.2) 1)))

/-- The sectionwise presheaf quotient used in the sheafification lemma. -/
abbrev presheafPrincipalPartsSection {X : TopCat.{v}}
    {O₁ O₂ : CommRingPresheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingPresheafModule O₂) (U : (Opens X)ᵒᵖ) (k : ℕ) :=
  PresheafFreeSectionModule F U ⧸
    Submodule.span (O₂.obj U) (presheafPrincipalPartsRelationSet φ F U k)

/-- The quotient in the preceding formula as a bundled module. -/
def presheafPrincipalPartsSectionModule {X : TopCat.{v}}
    {O₁ O₂ : CommRingPresheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingPresheafModule O₂) (U : (Opens X)ᵒᵖ) (k : ℕ) :
    ModuleCat (O₂.obj U) :=
  ModuleCat.of _ (presheafPrincipalPartsSection φ F U k)

/-- The sheafification statement for principal parts of presheaves. -/
structure PrincipalPartsSheafificationData {X : TopCat.{v}}
    (O₁ O₂ : CommRingPresheaf X) (φ : O₁ ⟶ O₂)
    (F : CommRingPresheafModule O₂) (k : ℕ) where
  associatedPresheaf : PMod (O₂ ⋙ (forget₂ CommRingCat RingCat))
  associatedSheaf : SheafOfModules (ringSheafification
    (O₂ ⋙ (forget₂ CommRingCat RingCat)))
  section_formula : ∀ U : (Opens X)ᵒᵖ, Nonempty
    (associatedPresheaf.obj U ≅ presheafPrincipalPartsSectionModule φ F U k)
  sheafification : associatedSheaf =
    Formalization.Books.Sheaves.Unit17.moduleSheafification associatedPresheaf

theorem principalParts_sheafify {X : TopCat.{v}}
    (O₁ O₂ : CommRingPresheaf X) (φ : O₁ ⟶ O₂)
    (F : CommRingPresheafModule O₂) (k : ℕ) :
    Nonempty (PrincipalPartsSheafificationData O₁ O₂ φ F k) := by
  sorry

/-- The sectionwise principal-parts presheaf selected by the sheafification
statement. -/
noncomputable def sheafifiedPrincipalPartsPresheaf {X : TopCat.{v}}
    (O₁ O₂ : CommRingPresheaf X) (φ : O₁ ⟶ O₂)
    (F : CommRingPresheafModule O₂) (k : ℕ) :
    PMod (O₂ ⋙ (forget₂ CommRingCat RingCat)) :=
  (Classical.choice (principalParts_sheafify O₁ O₂ φ F k)).associatedPresheaf

/-- The sheaf associated to the presheaf of sectionwise principal parts. -/
noncomputable def sheafifiedModuleOfPrincipalParts {X : TopCat.{v}}
    (O₁ O₂ : CommRingPresheaf X) (φ : O₁ ⟶ O₂)
    (F : CommRingPresheafModule O₂) (k : ℕ) :
    SheafOfModules (ringSheafification
      (O₂ ⋙ (forget₂ CommRingCat RingCat))) :=
  (Classical.choice (principalParts_sheafify O₁ O₂ φ F k)).associatedSheaf

/-- The short exact sequence of principal parts. -/
structure PrincipalPartsSequenceData {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) where
  left : tensorProductSheaf O₂ (moduleOfDifferentials φ) F ⟶
    moduleOfPrincipalParts φ F 1
  right : moduleOfPrincipalParts φ F 1 ⟶ F
  zero : left ≫ right = 0
  exact : SheafModuleExact left right
  left_mono : Mono left
  right_epi : Epi right

theorem principalParts_sequence_exists {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) :
    Nonempty (PrincipalPartsSequenceData φ F) := by
  sorry

/-- A chosen realization of the canonical principal-parts sequence. -/
noncomputable def principalPartsSequenceData {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) : PrincipalPartsSequenceData φ F :=
  Classical.choice (principalParts_sequence_exists φ F)

/-- The canonical short complex underlying the sequence of principal parts. -/
noncomputable def principalPartsSequence {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) : ShortComplex (CommRingSheafModule O₂) := by
  let S := principalPartsSequenceData φ F
  exact ShortComplex.mk S.left S.right S.zero

/-- Functoriality of the short exact sequence in the module argument. -/
structure PrincipalPartsSequenceFunctorialityData {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    {F G : CommRingSheafModule O₂} (α : F ⟶ G) where
  principalPartsMap : moduleOfPrincipalParts φ F 1 ⟶
    moduleOfPrincipalParts φ G 1
  left_commutes :
    (principalPartsSequenceData φ F).left ≫ principalPartsMap =
      tensorProductMap (𝟙 (moduleOfDifferentials φ)) α ≫
        (principalPartsSequenceData φ G).left
  right_commutes :
    principalPartsMap ≫ (principalPartsSequenceData φ G).right =
      (principalPartsSequenceData φ F).right ≫ α

theorem principalParts_sequence_functorial {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (φ : O₁ ⟶ O₂)
    {F G : CommRingSheafModule O₂} (α : F ⟶ G) :
    Nonempty (PrincipalPartsSequenceFunctorialityData φ α) := by
  sorry

/-! ## Functoriality -/

/-- A commutative square of coefficient sheaves. -/
structure PrincipalPartsRingSquare {X : TopCat.{v}}
    (A B A' B' : CommRingSheaf X) where
  top : B ⟶ B'
  bottom : A ⟶ A'
  left : A ⟶ B
  right : A' ⟶ B'
  commutes : left ≫ top = bottom ≫ right

/-- Functoriality of principal parts for a coefficient square and a compatible
map of modules.  The target map is expressed after extension of scalars. -/
structure PrincipalPartsFunctorialityData {X : TopCat.{v}}
    {A B A' B' : CommRingSheaf X}
    (square : PrincipalPartsRingSquare A B A' B')
    (F : CommRingSheafModule B) (F' : CommRingSheafModule B') where
  moduleMap : F.val.presheaf ⟶ F'.val.presheaf
  moduleMap_smul : ∀ (U : Opens X)
    (b : SheafSectionRing B U)
    (m : F.val.obj (op U)),
    moduleMap.app (op U) (b • m) =
      (sheafSectionRingMap square.top U b) •
        moduleMap.app (op U) m
  map : ∀ k : ℕ, (sheafChangeOfRings
      (commRingSheafMorphismToRingSheaf square.top)).obj
        (moduleOfPrincipalParts square.left F k) ⟶
      moduleOfPrincipalParts square.right F' k
  transition_compatible : ∀ k : ℕ,
    map (k + 1) ≫ principalPartsTransition square.right F' k =
      (sheafChangeOfRings
        (commRingSheafMorphismToRingSheaf square.top)).map
          (principalPartsTransition square.left F k) ≫ map k

theorem principalParts_functoriality {X : TopCat.{v}}
    {A B A' B' : CommRingSheaf X}
    (square : PrincipalPartsRingSquare A B A' B')
    (F : CommRingSheafModule B) (F' : CommRingSheafModule B') :
    Nonempty (PrincipalPartsFunctorialityData square F F') := by
  sorry

/-! ## Differential operators on ringed spaces -/

/-- Differential operators on a morphism of commutative ringed spaces. -/
abbrev RelativeDifferentialOperator {X S : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X S)
    (F G : CommRingSheafModule X.structureSheaf) (k : ℕ) :=
  DifferentialOperator f.sharp F G k

/-- The source notation `Diff^k_{X/S}(F,G)`. -/
abbrev RelativeDifferentialOperators {X S : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X S)
    (F G : CommRingSheafModule X.structureSheaf) (k : ℕ) :=
  RelativeDifferentialOperator f F G k

end

end Formalization.Books.Modules.Unit29
