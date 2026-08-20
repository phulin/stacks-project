import Formalization.Books.Modules.Unit17.FlatModules
import Formalization.Books.Modules.Unit14.LocallyFree
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Properties of Schemes, Chapter 21: Locally free modules

The source section is `books/properties.tex:2626--2713`.  The affine
comparison and the two finite-local-freeness characterizations are recorded
using the canonical scheme-module predicates and the algebraic interfaces
from Commutative Algebra, Chapter 78.
-/

namespace Formalization.Books.Properties.Unit21

open CategoryTheory
open AlgebraicGeometry
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit10
open Formalization.Books.Modules.Unit11
open Formalization.Books.Modules.Unit14
open Formalization.Books.Modules.Unit17
open scoped TensorProduct

universe u

noncomputable section


/-! ## Common scheme-module predicates -/

/-- A module of finite presentation on a scheme, using Mathlib's canonical
finite-presentation class. -/
abbrev IsFinitePresentation {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsFinitePresentation F

/-- A finite-type module on a scheme, using Mathlib's canonical local
generator class. -/
abbrev IsFiniteType {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsFiniteType F

/-- A locally free module on a scheme, using Mathlib's canonical local
generator class. -/
abbrev IsLocallyFree {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsLocallyFree F

/-- A finite locally free scheme module.  This is the finite local-generator
form used by the preceding Modules chapter, specialized to `X.Modules`. -/
def IsFiniteLocallyFree {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{u} F,
    q.IsLocallyFreeData ∧ ∀ i, Finite (q.generators i).I

/-- The structure-sheaf stalk at a point of a scheme. -/
abbrev schemeStalkRing (X : Scheme.{u}) (x : X) : Type u :=
  X.presheaf.stalk x

/-- The stalk module of a scheme module. -/
abbrev schemeModuleStalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    ModuleCat (CommRingCat.of (schemeStalkRing X x)) :=
  Formalization.Books.Modules.Unit17.moduleStalk F x

/-- Freeness of a scheme module at one stalk. -/
def IsFreeAtStalk {X : Scheme.{u}} (F : X.Modules) (x : X) : Prop :=
  Module.Free (schemeStalkRing X x) (schemeModuleStalk F x : Type u)

/-- The fiber-dimension function appearing in the source, with values in
`ℤ` as in the textbook. -/
noncomputable def rankFunction {X : Scheme.{u}} (F : X.Modules) : X → ℤ :=
  fun x =>
    (Module.finrank (IsLocalRing.ResidueField (schemeStalkRing X x))
      (IsLocalRing.ResidueField (schemeStalkRing X x) ⊗[schemeStalkRing X x]
        (schemeModuleStalk F x : Type u)) : ℤ)

/-- Flatness of a scheme module, using the earlier sheaf-theoretic definition.
-/
abbrev IsFlat {X : Scheme.{u}} (F : X.Modules) : Prop :=
  Formalization.Books.Modules.Unit17.IsFlat X.sheaf F

/-! ## Lemma `lemma-locally-free-module` -/

/-- On an affine scheme, local freeness and finite local freeness of a tilde
module are exactly the corresponding algebraic properties of the module. -/
theorem lemma_locally_free_module (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    (IsLocallyFree (AlgebraicGeometry.tilde M) ↔
      Formalization.Books.Algebra.Unit78.LocallyFree
        (R : Type u) (M : Type u)) ∧
    (IsFiniteLocallyFree (AlgebraicGeometry.tilde M) ↔
      Formalization.Books.Algebra.Unit78.FiniteLocallyFree
        (R : Type u) (M : Type u)) := by
  sorry

/-! ## Lemma `lemma-finite-locally-free` -/

/-- The five source conditions for a quasi-coherent scheme module to be
finite locally free, in source order. -/
def finiteLocallyFreeConditions {X : Scheme.{u}} (F : X.Modules) : List Prop :=
  [ IsFlat F ∧ IsFinitePresentation F,
    IsFinitePresentation F ∧ ∀ x : X, IsFreeAtStalk F x,
    IsLocallyFree F ∧ IsFiniteType F,
    IsFiniteLocallyFree F,
    IsFiniteType F ∧
      (∀ x : X, IsFreeAtStalk F x) ∧
        IsLocallyConstant (rankFunction F) ]

/-- The five conditions in `finiteLocallyFreeConditions` are equivalent for a
quasi-coherent scheme module. -/
theorem lemma_finite_locally_free {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    List.TFAE (finiteLocallyFreeConditions F) := by
  sorry

/-! ## Lemma `lemma-finite-locally-free-reduced` -/

/-- The sixth, reduced-scheme condition from the source. -/
def finiteLocallyFreeReducedCondition {X : Scheme.{u}} (F : X.Modules) : Prop :=
  IsFiniteType F ∧ IsLocallyConstant (rankFunction F)

/-- The sixth rank criterion is equivalent to the five finite-local-free
criteria on a reduced scheme. -/
theorem lemma_finite_locally_free_reduced {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    List.TFAE (finiteLocallyFreeConditions F ++
      [finiteLocallyFreeReducedCondition F]) := by
  sorry

end

end Formalization.Books.Properties.Unit21
