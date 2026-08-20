import Formalization.Books.StacksMorphisms.Unit07.QuasiCompactMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# More on Morphisms of Stacks, Chapter 9: blowing up and flatness

The source applies the space-theoretic flattening-by-blowing-up theorem to a
smooth presentation of an algebraic stack.  Mathlib does not currently expose
algebraic stacks, open subspaces in an abstract stack category, or blowups.
This file therefore keeps the existing generic algebraic-stack category and
adds only the missing source-facing interfaces.  Pullbacks and the standard
morphism properties remain the canonical declarations from the earlier
formalization.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.StacksMorphisms.Unit07

universe u v

namespace Formalization.Books.StacksMoreMorphisms.Unit09

/-! ## Missing properties and constructions -/

/-
The preceding algebraic-stack interface already supplies flatness, local
finite presentation, quasi-compactness, quasi-separatedness, and closed
immersions.  Finite type and blowup are not supplied by that interface or by
Mathlib, so they are the additional geometric predicates needed by this
chapter.  Finite presentation is the standard combination of
quasi-compactness and local finite presentation already supplied above.
-/
class BlowingUpFlatnessGeometry (C : Type u) [Category.{v} C]
    [AlgebraicStackCategory C] where
  finiteType : ∀ {X Y : C}, (X ⟶ Y) → Prop
  finiteType_quasiCompact_of_quasiCompact_target :
    ∀ {X Y : C} (f : X ⟶ Y), finiteType f →
      IsQuasiCompactStack Y → IsQuasiCompactStack X
  isBlowup : ∀ {X Y : C}, (X ⟶ Y) → Prop

def FiniteType {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [BlowingUpFlatnessGeometry C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  BlowingUpFlatnessGeometry.finiteType f

lemma finiteType_quasiCompact_of_quasiCompact_target
    {C : Type u} [Category.{v} C] [AlgebraicStackCategory C]
    [BlowingUpFlatnessGeometry C] {X Y : C} (f : X ⟶ Y)
    (hf : FiniteType f) (hYqc : IsQuasiCompactStack Y) :
    IsQuasiCompactStack X :=
  BlowingUpFlatnessGeometry.finiteType_quasiCompact_of_quasiCompact_target
    f hf hYqc

def FinitePresentation {C : Type u} [Category.{v} C]
    [HasPullbacks C] [AlgebraicStackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  QuasiCompact f ∧ LocallyOfFinitePresentation f

def IsBlowup {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [BlowingUpFlatnessGeometry C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  BlowingUpFlatnessGeometry.isBlowup f

/-! The preceding algebraic-stack interface has no open-immersion predicate.
    Keep that missing geometric property separate from the blowup-specific
    interface, so an open subspace cannot be represented by an unrelated
    proposition. -/
class OpenSubspaceGeometry (C : Type u) [Category.{v} C]
    [AlgebraicStackCategory C] where
  isOpenImmersion : ∀ {X Y : C}, (X ⟶ Y) → Prop

def IsOpenImmersion {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [OpenSubspaceGeometry C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  OpenSubspaceGeometry.isOpenImmersion f

/-! ## Open subspaces and admissible blowups -/

/-- An open algebraic subspace of an object in the ambient stack category. -/
structure OpenSubspace {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [OpenSubspaceGeometry C] (Y : C) where
  carrier : C
  inclusion : carrier ⟶ Y
  algebraicSpace : IsAlgebraicSpace carrier
  openImmersion : IsOpenImmersion inclusion

/-- The stack-theoretic restriction of a morphism to an open subspace. -/
abbrev stackRestriction {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C] [OpenSubspaceGeometry C]
    {X Y : C} (f : X ⟶ Y) (V : OpenSubspace Y) : C :=
  pullback f V.inclusion

/-- A blowup whose center is disjoint from `V`, expressed by its base change
    to `V` being an isomorphism. -/
structure VAdmissibleBlowup {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C] [OpenSubspaceGeometry C]
    [BlowingUpFlatnessGeometry C]
    {Y : C} (V : OpenSubspace Y) where
  carrier : C
  map : carrier ⟶ Y
  algebraicSpace : IsAlgebraicSpace carrier
  blowup : IsBlowup map
  overV : IsIso (pullback.snd map V.inclusion)

/-
The inverse of the base-changed blowup map gives the morphism from `V` to the
blowup.  This is the categorical form of the fact that a `V`-admissible
blowup is unchanged over `V`.
-/
def VAdmissibleBlowup.liftToCarrier {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C] [OpenSubspaceGeometry C]
    [BlowingUpFlatnessGeometry C]
    {Y : C} {V : OpenSubspace Y} (B : VAdmissibleBlowup V) :
    V.carrier ⟶ B.carrier := by
  letI : IsIso (pullback.snd B.map V.inclusion) := B.overV
  exact inv (pullback.snd B.map V.inclusion) ≫ pullback.fst B.map V.inclusion

/-! ## Closed substacks after base change -/

/-- A closed substack is represented by a closed immersion in the ambient
    algebraic-stack category. -/
structure ClosedSubstack {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C]
    {X : C} where
  source : C
  inclusion : source ⟶ X
  closedImmersion : ClosedImmersion inclusion

/-- The base change of `X` to the carrier of an admissible blowup. -/
abbrev stackBaseChange {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C]
    [BlowingUpFlatnessGeometry C]
    [OpenSubspaceGeometry C]
    {X Y : C} (f : X ⟶ Y) {V : OpenSubspace Y}
    (B : VAdmissibleBlowup V) : C :=
  pullback f B.map

/-
The following definitions express the source's equality
`X'_V = X_V` by the canonical categorical replacement: an isomorphism of the
two pullback objects compatible with their maps to `X` and `V`.  The displayed
object on the left is the restriction of a closed substack along the inverse
of the admissible blowup over `V`.
-/
def restrictedClosedSubstack {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C]
    [BlowingUpFlatnessGeometry C] [OpenSubspaceGeometry C]
    {X Y : C} (f : X ⟶ Y) (V : OpenSubspace Y)
    (B : VAdmissibleBlowup V)
    (X' : ClosedSubstack (X := stackBaseChange f B)) : C :=
  pullback
    (X'.inclusion ≫ pullback.snd f B.map)
    B.liftToCarrier

/-
The two canonical maps record the ambient maps that are part of the
statement that the restricted closed substack agrees with `X_V`.
-/
def restrictedClosedSubstack.toX {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C]
    [BlowingUpFlatnessGeometry C] [OpenSubspaceGeometry C]
    {X Y : C} (f : X ⟶ Y) (V : OpenSubspace Y)
    (B : VAdmissibleBlowup V)
    (X' : ClosedSubstack (X := stackBaseChange f B)) :
    restrictedClosedSubstack f V B X' ⟶ X :=
  pullback.fst (X'.inclusion ≫ pullback.snd f B.map) B.liftToCarrier ≫
    X'.inclusion ≫ pullback.fst f B.map

def restrictedClosedSubstack.toV {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C]
    [BlowingUpFlatnessGeometry C] [OpenSubspaceGeometry C]
    {X Y : C} (f : X ⟶ Y) (V : OpenSubspace Y)
    (B : VAdmissibleBlowup V)
    (X' : ClosedSubstack (X := stackBaseChange f B)) :
    restrictedClosedSubstack f V B X' ⟶ V.carrier :=
  pullback.snd (X'.inclusion ≫ pullback.snd f B.map) B.liftToCarrier

def AgreesOnOpen {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C]
    [BlowingUpFlatnessGeometry C] [OpenSubspaceGeometry C]
    {X Y : C} (f : X ⟶ Y) (V : OpenSubspace Y)
    (B : VAdmissibleBlowup V)
    (X' : ClosedSubstack (X := stackBaseChange f B)) : Prop :=
  ∃ e : restrictedClosedSubstack f V B X' ≅ stackRestriction f V,
    e.hom ≫ pullback.fst f V.inclusion =
        restrictedClosedSubstack.toX f V B X' ∧
      e.hom ≫ pullback.snd f V.inclusion =
        restrictedClosedSubstack.toV f V B X'

/-! ## Flattening after a `V`-admissible blowup -/

/-- Algebraic-stack form of the source's flattening lemma. -/
theorem flatten_stack {C : Type u} [Category.{v} C]
    [AlgebraicStackCategory C] [HasPullbacks C]
    [BlowingUpFlatnessGeometry C] [OpenSubspaceGeometry C]
    {X Y : C} (f : X ⟶ Y) (hYspace : IsAlgebraicSpace Y)
    (V : OpenSubspace Y)
    (hYqc : IsQuasiCompactStack Y)
    (hYqs : IsQuasiSeparatedStack Y)
    (hf_type : FiniteType f)
    (hf_qs : QuasiSeparated f)
    (hVqc : IsQuasiCompactStack V.carrier)
    (hXV_flat : Flat (pullback.snd f V.inclusion))
    (hXV_lfp : LocallyOfFinitePresentation (pullback.snd f V.inclusion)) :
    ∃ (B : VAdmissibleBlowup V)
      (X' : ClosedSubstack (X := stackBaseChange f B)),
      AgreesOnOpen f V B X' ∧
        Flat (X'.inclusion ≫ pullback.snd f B.map) ∧
          FinitePresentation (X'.inclusion ≫ pullback.snd f B.map) := by
  sorry

end Formalization.Books.StacksMoreMorphisms.Unit09
