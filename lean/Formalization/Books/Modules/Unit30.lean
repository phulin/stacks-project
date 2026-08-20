import Formalization.Books.Modules.Unit29
import Formalization.Books.Modules.Unit21.SymmetricExterior
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Sheaves of Modules, Chapter 30: The de Rham complex

The terms of the de Rham complex use the sheafified exterior-power
construction from Chapter 21.  A differential is recorded together with the
sectionwise rule that characterizes it; the existence and uniqueness theorem
is left for the proof stage, as in the source's sheafification argument.
-/

namespace Formalization.Books.Modules.Unit30

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Modules.Unit21
open Formalization.Books.Modules.Unit28
open Formalization.Books.Modules.Unit29

universe v

noncomputable section

instance sectionModule {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) (U : Opens X) :
    Module (↑(O.obj.obj (op U))) (↑(F.val.obj (op U))) :=
  (F.val.obj (op U)).isModule

/-! ## Terms and generators -/

/-- The structure sheaf of `B`, regarded as an `A`-module along `φ`. -/
noncomputable abbrev deRhamDegreeZero
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    CommRingSheafModule A :=
  (sheafRestrictionOfScalars (commRingSheafMorphismToRingSheaf φ)).obj
    (SheafOfModules.unit (commRingSheafToRingSheaf B))

/-- The `p`th term of the relative de Rham complex. -/
noncomputable def deRhamTerm
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    ℕ → CommRingSheafModule A
  | 0 => deRhamDegreeZero φ
  | p + 1 =>
      (sheafRestrictionOfScalars (commRingSheafMorphismToRingSheaf φ)).obj
        (exteriorPowerSheaf B (moduleOfDifferentials φ) (p + 1))

@[simp] theorem deRhamTerm_zero
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    deRhamTerm φ 0 = deRhamDegreeZero φ :=
  rfl

@[simp] theorem deRhamTerm_succ
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) :
    deRhamTerm φ (p + 1) =
      (sheafRestrictionOfScalars (commRingSheafMorphismToRingSheaf φ)).obj
        (exteriorPowerSheaf B (moduleOfDifferentials φ) (p + 1)) :=
  rfl

/-- A section of the sheafified `(p+1)`st exterior power obtained from a
sectionwise pure wedge.  The chosen isomorphism is the one supplied by the
canonical Chapter 21 presheaf construction. -/
noncomputable def deRhamExteriorElement
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B)
    (p : ℕ) {U : Opens X}
    (x : Fin (p + 1) → (moduleOfDifferentials φ).val.obj (op U)) :
    (exteriorPowerSheaf B (moduleOfDifferentials φ) (p + 1)).val.obj
      (op U) := by
  letI := sectionwiseModule B (moduleOfDifferentials φ) (op U)
  let e := Classical.choice
    (exteriorPowerPresheaf_obj_formula B (moduleOfDifferentials φ) (p + 1)
      (op U))
  exact (moduleSheafificationUnit
    (exteriorPowerPresheaf B (moduleOfDifferentials φ) (p + 1))).app (op U)
      (e.inv.hom (exteriorPower.ιMulti (B.obj.obj (op U)) (p + 1) x))

/-- The section `b₀ db₁ ∧ ... ∧ dbₚ`. -/
noncomputable def deRhamGenerator
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B)
    (p : ℕ) {U : Opens X} (b₀ : B.obj.obj (op U))
    (b : Fin p → B.obj.obj (op U)) :
    (deRhamTerm φ p).val.obj (op U) := by
  cases p with
  | zero =>
      exact b₀
  | succ p =>
      change (exteriorPowerSheaf B (moduleOfDifferentials φ) (p + 1)).val.obj
        (op U)
      letI : Module (↑(B.obj.obj (op U)))
          (↑((exteriorPowerSheaf B (moduleOfDifferentials φ) (p + 1)).val.obj
            (op U))) :=
        ((exteriorPowerSheaf B (moduleOfDifferentials φ) (p + 1)).val.obj
          (op U)).isModule
      exact b₀ • deRhamExteriorElement φ p (fun i =>
          (universalRelativeSheafDerivation φ).d (b i))

/-- The pure wedge on the right side of the de Rham differential rule. -/
noncomputable def deRhamDifferentialGenerator
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B)
    (p : ℕ) {U : Opens X} (b₀ : B.obj.obj (op U))
    (b : Fin p → B.obj.obj (op U)) :
    (deRhamTerm φ (p + 1)).val.obj (op U) :=
  deRhamExteriorElement φ p (Fin.cons
    ((universalRelativeSheafDerivation φ).d b₀)
    (fun i => (universalRelativeSheafDerivation φ).d (b i)))

/-- A differential system for the relative de Rham terms. -/
structure DeRhamDifferentialData
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) where
  differential : ∀ p, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1)
  degree_zero : ∀ (U : Opens X) (b : B.obj.obj (op U)),
    (differential 0).val.app (op U) b =
      deRhamDifferentialGenerator φ 0 b (fun i => Fin.elim0 i)
  generator_rule : ∀ (p : ℕ) (U : Opens X)
    (b₀ : B.obj.obj (op U)) (b : Fin p → B.obj.obj (op U)),
    (differential p).val.app (op U) (deRhamGenerator φ p b₀ b) =
      deRhamDifferentialGenerator φ p b₀ b
  square_zero : ∀ p,
    differential p ≫ differential (p + 1) = 0

/-- The existence of the sheafified de Rham differential system. -/
theorem deRhamDifferentialData_exists
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty (DeRhamDifferentialData φ) := by
  sorry

/-- The differential system is unique, because the displayed generators span
each exterior-power term. -/
theorem deRhamDifferentialData_subsingleton
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Subsingleton (DeRhamDifferentialData φ) := by
  sorry

/-- The canonical differential system. -/
noncomputable def deRhamDifferentialData
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    DeRhamDifferentialData φ :=
  Classical.choice (deRhamDifferentialData_exists φ)

/-- The de Rham differential in degree `p`. -/
noncomputable abbrev deRhamDifferential
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) :
    deRhamTerm φ p ⟶ deRhamTerm φ (p + 1) :=
  (deRhamDifferentialData φ).differential p

@[simp] theorem deRhamDifferential_degree_zero
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B)
    (U : Opens X) (b : B.obj.obj (op U)) :
    (deRhamDifferential φ 0).val.app (op U) b =
      deRhamDifferentialGenerator φ 0 b (fun i => Fin.elim0 i) :=
  (deRhamDifferentialData φ).degree_zero U b

theorem deRhamDifferential_generator_rule
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B)
    (p : ℕ) (U : Opens X) (b₀ : B.obj.obj (op U))
    (b : Fin p → B.obj.obj (op U)) :
    (deRhamDifferential φ p).val.app (op U) (deRhamGenerator φ p b₀ b) =
      deRhamDifferentialGenerator φ p b₀ b :=
  (deRhamDifferentialData φ).generator_rule p U b₀ b

theorem deRhamDifferential_comp_zero
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) :
    deRhamDifferential φ p ≫ deRhamDifferential φ (p + 1) = 0 :=
  (deRhamDifferentialData φ).square_zero p

/-! ## The complex -/

/-- Nonnegative cochain complexes of sheaf `A`-modules. -/
abbrev DeRhamComplex
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :=
  HomologicalComplex (CommRingSheafModule A) (ComplexShape.up ℕ)

/-- The de Rham complex of `B` over `A`. -/
noncomputable def deRhamComplex
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    DeRhamComplex φ where
  X p := deRhamTerm φ p
  d i j := if h : i + 1 = j then
    h ▸ deRhamDifferential φ i
  else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    have hjk' : j + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hjk
    subst j
    subst k
    simp
    exact deRhamDifferential_comp_zero φ i

@[simp] theorem deRhamComplex_X
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) :
    (deRhamComplex φ).X p = deRhamTerm φ p :=
  rfl

theorem deRhamComplex_differential_comp_zero
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) :
    (deRhamComplex φ).d p (p + 1) ≫
        (deRhamComplex φ).d (p + 1) (p + 2) = 0 := by
  exact (deRhamComplex φ).d_comp_d p (p + 1) (p + 2)

/-- The positive terms are precisely the sheafifications of the sectionwise
exterior-power presheaves, after restriction of scalars to `A`. -/
theorem deRhamTerm_succ_sheafification
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) :
    deRhamTerm φ (p + 1) =
      (sheafRestrictionOfScalars (commRingSheafMorphismToRingSheaf φ)).obj
        (exteriorPowerSheaf B (moduleOfDifferentials φ) (p + 1)) := by
  rfl

/-- The degree-one term is the sheaf of differentials itself, after the same
restriction of scalars used for all de Rham terms. -/
theorem deRhamTerm_one_iso
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty
      (deRhamTerm φ 1 ≅
        (sheafRestrictionOfScalars
          (commRingSheafMorphismToRingSheaf φ)).obj
          (moduleOfDifferentials φ)) := by
  sorry

/-! ## Pullback -/

noncomputable abbrev pullbackDeRhamRingMap
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    {A B : CommRingSheaf Y} (φ : A ⟶ B) :
    ((TopCat.Sheaf.pullback CommRingCat f).obj A ⟶
      (TopCat.Sheaf.pullback CommRingCat f).obj B) :=
  (TopCat.Sheaf.pullback CommRingCat f).map φ

/-- A degreewise additive-sheaf identification of the pulled-back de Rham
complex, including compatibility with the differentials. -/
structure PullbackDeRhamComplexData
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    {A B : CommRingSheaf Y} (φ : A ⟶ B) where
  component : ∀ p, (TopCat.Sheaf.pullback AddCommGrpCat f).obj
      ((SheafOfModules.toSheaf (commRingSheafToRingSheaf A)).obj
        (deRhamTerm φ p)) ≅
      (SheafOfModules.toSheaf
        (commRingSheafToRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat f).obj A))).obj
        (deRhamTerm (pullbackDeRhamRingMap (A := A) (B := B) f φ) p)
  differential_commutes : ∀ p,
    (TopCat.Sheaf.pullback AddCommGrpCat f).map
          ((SheafOfModules.toSheaf (commRingSheafToRingSheaf A)).map
            (deRhamDifferential φ p)) ≫ (component (p + 1)).hom =
      (component p).hom ≫
        (SheafOfModules.toSheaf
          (commRingSheafToRingSheaf
            ((TopCat.Sheaf.pullback CommRingCat f).obj A))).map
          (deRhamDifferential
            (pullbackDeRhamRingMap (A := A) (B := B) f φ) p)

/-- Pullback identifies the de Rham complex with the de Rham complex of the
pulled-back sheaves of rings. -/
theorem pullback_deRhamComplex
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    {A B : CommRingSheaf Y} (φ : A ⟶ B) :
    Nonempty (PullbackDeRhamComplexData f φ) := by
  sorry

/-- The exterior-power terms as `B`-modules, before restriction to the base
sheaf `A`. -/
noncomputable def deRhamBTerm
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) :
    ℕ → CommRingSheafModule B
  | 0 => SheafOfModules.unit (commRingSheafToRingSheaf B)
  | p + 1 => exteriorPowerSheaf B (moduleOfDifferentials φ) (p + 1)

/-- The underlying section types of the `A`-module terms and their original
`B`-module presentations are canonically the same; this equivalence makes the
scalar restriction explicit when applying the differential. -/
noncomputable def deRhamTermSectionEquiv
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B)
    (p : ℕ) (U : Opens X) :
    SheafModuleSection (deRhamBTerm φ p) U ≃
      (deRhamTerm φ p).val.obj (op U) := by
  cases p <;> rfl

/-- The assertion that the actual de Rham differential has order one.  The
section operator predicate is reused from Chapter 29, while the map in its
last argument is the underlying map of the actual de Rham differential. -/
noncomputable def deRhamDifferentialOnBSection
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ)
    (U : Opens X) :
    SheafModuleSection (deRhamBTerm φ p) U →
      SheafModuleSection (deRhamBTerm φ (p + 1)) U :=
  fun m =>
    (deRhamTermSectionEquiv φ (p + 1) U).symm
      ((deRhamDifferential φ p).val.app (op U)
        (deRhamTermSectionEquiv φ p U m))

def IsDeRhamDifferentialOrderOne
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) : Prop :=
  ∀ (U : Opens X),
    IsSectionDifferentialOperator (deRhamBTerm φ p)
      (deRhamBTerm φ (p + 1)) U 1
      (deRhamDifferentialOnBSection φ p U)

/-- The full relative differential-operator assertion: the actual map is
`A`-linear and has order one. -/
def IsDeRhamDifferentialOperator
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) : Prop :=
  (∀ (U : Opens X) (a : A.obj.obj (op U))
    (m : SheafModuleSection (deRhamBTerm φ p) U),
    deRhamDifferentialOnBSection φ p U
        ((φ.hom.app (op U) a) • m) =
      (φ.hom.app (op U) a) • deRhamDifferentialOnBSection φ p U m) ∧
  IsDeRhamDifferentialOrderOne φ p

/-- Each de Rham differential is a relative differential operator of order
one. -/
theorem deRhamDifferential_order_one
    {X : TopCat.{v}} {A B : CommRingSheaf X} (φ : A ⟶ B) (p : ℕ) :
    IsDeRhamDifferentialOperator φ p := by
  sorry

/-! ## Functoriality for a square of sheaves of rings -/

/-- The commutative square of sheaves of rings used by the functoriality map.
This reuses the four-map square interface introduced for principal parts. -/
abbrev DeRhamRingSquare {X : TopCat.{v}}
    (A B A' B' : CommRingSheaf X) :=
  PrincipalPartsRingSquare A B A' B'

/-- The induced map of de Rham terms, with the target restricted along the
bottom map of the ring square. -/
structure DeRhamRingSquareMapData
    {X : TopCat.{v}} {A B A' B' : CommRingSheaf X}
    (square : DeRhamRingSquare A B A' B') where
  map : ∀ p, deRhamTerm square.left p ⟶
    (sheafRestrictionOfScalars
      (commRingSheafMorphismToRingSheaf square.bottom)).obj
      (deRhamTerm square.right p)
  degree_zero : ∀ (U : Opens X) (b : B.obj.obj (op U)),
    (map 0).val.app (op U) b = square.top.hom.app (op U) b
  degree_one : ∀ (U : Opens X) (b : B.obj.obj (op U)),
    (map 1).val.app (op U)
        (deRhamDifferentialGenerator square.left 0 b (fun i => Fin.elim0 i)) =
      deRhamDifferentialGenerator square.right 0
        (square.top.hom.app (op U) b) (fun i => Fin.elim0 i)
  generator_rule : ∀ (p : ℕ) (U : Opens X)
    (b₀ : B.obj.obj (op U)) (b : Fin p → B.obj.obj (op U)),
    (map p).val.app (op U) (deRhamGenerator square.left p b₀ b) =
      deRhamGenerator square.right p (square.top.hom.app (op U) b₀)
        (fun i => square.top.hom.app (op U) (b i))
  differential_commutes : ∀ p,
    map p ≫
        (sheafRestrictionOfScalars
          (commRingSheafMorphismToRingSheaf square.bottom)).map
          (deRhamDifferential square.right p) =
      deRhamDifferential square.left p ≫ map (p + 1)

/-- The natural map of de Rham complexes associated to a commutative square
of sheaves of rings. -/
theorem deRhamRingSquare_map
    {X : TopCat.{v}} {A B A' B' : CommRingSheaf X}
    (square : DeRhamRingSquare A B A' B') :
    Nonempty (DeRhamRingSquareMapData square) := by
  sorry

/-! ## Relative de Rham complexes of ringed spaces -/

/-- The de Rham complex of a morphism of commutative ringed spaces. -/
noncomputable abbrev ringedSpaceDeRhamComplex
    {X Y : CommutativeRingedSpace} (f : CommutativeRingedSpaceHom X Y) :=
  deRhamComplex f.sharp

/-- The de Rham terms of a ringed-space morphism. -/
noncomputable abbrev ringedSpaceDeRhamTerm
    {X Y : CommutativeRingedSpace} (f : CommutativeRingedSpaceHom X Y)
    (p : ℕ) :=
  deRhamTerm f.sharp p

/-- A map of relative de Rham complexes into the pushforward complex in a
commutative square of ringed spaces. -/
structure RingedSpaceDeRhamMapData
    {X' X S' S : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X' X S' S) where
  map : ∀ p,
    (SheafOfModules.toSheaf
      (commRingSheafToRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat square.h.continuous).obj
          S.structureSheaf))).obj
        (ringedSpaceDeRhamTerm square.h p) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat square.f.continuous).obj
        ((SheafOfModules.toSheaf
          (commRingSheafToRingSheaf
            ((TopCat.Sheaf.pullback CommRingCat square.f'.continuous).obj
              S'.structureSheaf))).obj
            (ringedSpaceDeRhamTerm square.f' p))
  differential_commutes : ∀ p,
    map p ≫ (TopCat.Sheaf.pushforward AddCommGrpCat square.f.continuous).map
        ((SheafOfModules.toSheaf
          (commRingSheafToRingSheaf
            ((TopCat.Sheaf.pullback CommRingCat square.f'.continuous).obj
              S'.structureSheaf))).map
            (deRhamDifferential square.f'.sharp p)) =
      (SheafOfModules.toSheaf
        (commRingSheafToRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat square.h.continuous).obj
            S.structureSheaf))).map
          (deRhamDifferential square.h.sharp p) ≫ map (p + 1)

/-- The canonical map of relative de Rham complexes attached to a square of
ringed spaces. -/
theorem ringedSpace_deRhamComplex_map
    {X' X S' S : CommutativeRingedSpace}
    (square : RingedSpaceDifferentialSquare X' X S' S) :
    Nonempty (RingedSpaceDeRhamMapData square) := by
  sorry

/-- The relative de Rham differentials are differential operators of order
one on the corresponding morphism of ringed spaces. -/
theorem ringedSpaceDeRhamDifferential_order_one
    {X Y : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X Y) (p : ℕ) :
    IsDeRhamDifferentialOperator f.sharp p := by
  exact deRhamDifferential_order_one f.sharp p

end
end Formalization.Books.Modules.Unit30
