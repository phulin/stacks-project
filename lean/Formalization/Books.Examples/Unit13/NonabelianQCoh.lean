import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Formalization.«Books.Examples».Unit10.CompleteModules
import Formalization.«Books.Stacks».Unit01.Setoids
import Formalization.«Books.SpacesGroupoids».Unit20.QuotientStacks

/-!
# Examples, Chapter 13: Nonabelian category of quasi-coherent modules

The finite affine level diagram and its fppf sheaf-valued form are recorded
explicitly below.  The formal-spectrum object is packaged by an explicit
colimit-cocone interface because the current algebraic-space API does not
provide a generic small-universe `HasColimit` instance for this large-site
diagram.  The associated stack uses the existing algebraic-space-to-stack
interface, while the module calculation uses Mathlib's adic-completion and
module-category APIs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

universe u

namespace Formalization.«Books.Examples».Unit13

/-! ## The formal spectrum `Spf(ℤ_[p])` -/

/-- The `p`-adic integers, using Mathlib's canonical `PadicInt` construction. -/
abbrev pAdicIntegers (p : ℕ) [Fact p.Prime] := ℤ_[p]

/-- Mathlib's p-adic integers are complete for their canonical topology. -/
theorem pAdicIntegers_completeSpace (p : ℕ) [Fact p.Prime] :
    CompleteSpace (pAdicIntegers p) := by
  infer_instance

abbrev BaseScheme := Spec (CommRingCat.of ℤ)

abbrev SchemesOverIntegers := Over BaseScheme

abbrev FppfTopologyOverIntegers : GrothendieckTopology SchemesOverIntegers :=
  AlgebraicGeometry.Scheme.fppfTopology.over BaseScheme

/-! ## The finite level schemes -/

/- The source numbers its levels by positive integers.  The Lean index `n`
denotes the source level `n + 1`. -/
def pAdicLevelExponent (n : ℕ) : ℕ :=
  n + 1

theorem pAdicLevelExponent_succ (n : ℕ) :
    pAdicLevelExponent (n + 1) = pAdicLevelExponent n + 1 := by
  simp [pAdicLevelExponent]

/-! ## Compatible systems of modules -/

/-- The ideal defining the `p`-adic filtration on abelian groups. -/
def pAdicIdeal (p : ℕ) : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)

/-- The ring of functions on the source's `n`-th finite level. -/
def pAdicLevelRing (p n : ℕ) : CommRingCat :=
  CommRingCat.of (ℤ ⧸ pAdicIdeal p ^ pAdicLevelExponent n)

/-- The affine scheme `Spec (ℤ / p^(n+1)ℤ)`. -/
abbrev pAdicLevelScheme (p n : ℕ) : Scheme :=
  Spec (pAdicLevelRing p n)

/-- The `n`-th finite level, regarded as a scheme over `Spec ℤ`. -/
def pAdicLevelSchemeOverIntegers (p n : ℕ) : SchemesOverIntegers :=
  Over.mk <|
    Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (pAdicIdeal p ^ pAdicLevelExponent n)))

/-- The closed immersion from one finite level to the next. -/
def pAdicLevelSchemeTransition (p n : ℕ) :
    pAdicLevelSchemeOverIntegers p n ⟶
      pAdicLevelSchemeOverIntegers p (n + 1) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factorPow (pAdicIdeal p)
        (show pAdicLevelExponent n ≤ pAdicLevelExponent (n + 1) by
          rw [pAdicLevelExponent_succ]
          exact Nat.le_succ _))))
    (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl)

/-- The directed system of finite schemes in the source's colimit description. -/
def pAdicLevelSchemeDiagram (p : ℕ) : ℕ ⥤ SchemesOverIntegers :=
  Functor.ofSequence (X := fun n => pAdicLevelSchemeOverIntegers p n)
    (fun n => pAdicLevelSchemeTransition p n)

/-- The same finite levels viewed as fppf sheaves of points. -/
def pAdicLevelSheafDiagram (p : ℕ) :
    ℕ ⥤ Formalization.«Books.SpacesGroupoids».Unit20.AlgebraicSpace BaseScheme :=
  pAdicLevelSchemeDiagram p ⋙ FppfTopologyOverIntegers.yoneda

/-- A formal-spectrum presentation records the fppf sheaf colimit of the
finite-level diagram.  Stating the colimit through `IsColimit` avoids requiring
a global `HasColimit` instance for the large fppf site. -/
structure FormalSpectrumPresentation (p : ℕ) (R : CommRingCat) where
  colimitCocone : Cocone (pAdicLevelSheafDiagram p)
  isColimit : IsColimit colimitCocone

/-- The fppf sheaf of points in a formal-spectrum presentation. -/
abbrev FormalSpectrumPresentation.points
    (P : FormalSpectrumPresentation p R) :
    Formalization.«Books.SpacesGroupoids».Unit20.AlgebraicSpace BaseScheme :=
  P.colimitCocone.pt

/-- The stack in sets associated to the sheaf of points of a presentation. -/
noncomputable abbrev FormalSpectrumPresentation.stack
    (P : FormalSpectrumPresentation p R) :
    Formalization.«Books.Stacks».Unit01.FiberedCategory SchemesOverIntegers :=
  Formalization.«Books.SpacesGroupoids».Unit20.spaceStack P.points

/-- The associated stack is, in particular, a stack in setoids.  We retain the
stronger stack-in-sets interface supplied by the sheaf construction. -/
def FormalSpectrumPresentation.isStackInSetoids
    (P : FormalSpectrumPresentation p R) : Prop :=
  Formalization.«Books.Stacks».Unit01.StackInSetoids P.stack
    FppfTopologyOverIntegers

/-- The declaration-level presentation of `X = Spf(ℤ_[p])`. -/
abbrev PAdicFormalSpectrum (p : ℕ) [Fact p.Prime] :=
  FormalSpectrumPresentation p (CommRingCat.of (pAdicIntegers p))

/-- Existence of the fppf sheaf represented by `Spf(ℤ_[p])` as the colimit of
the finite-level fppf sheaves. -/
theorem pAdicFormalSpectrum_exists (p : ℕ) [Fact p.Prime] :
    Nonempty (PAdicFormalSpectrum p) :=
  by
    sorry

/-- A chosen colimit presentation of `Spf(ℤ_[p])`. -/
noncomputable def pAdicFormalSpectrum (p : ℕ) [Fact p.Prime] :
    PAdicFormalSpectrum p :=
  Classical.choice (pAdicFormalSpectrum_exists p)

theorem pAdicFormalSpectrum_isSheafInSets (p : ℕ) [Fact p.Prime] :
    Presheaf.IsSheaf FppfTopologyOverIntegers
      (pAdicFormalSpectrum p).points.obj :=
  (pAdicFormalSpectrum p).points.property

theorem pAdicFormalSpectrum_isStackInSetoids (p : ℕ) [Fact p.Prime] :
    (pAdicFormalSpectrum p).isStackInSetoids :=
  by
    sorry

/-- The coordinate ring of `Spf(ℤ_[p])` is Noetherian. -/
theorem pAdicFormalSpectrum_isNoetherian (p : ℕ) [Fact p.Prime] :
    IsNoetherianRing (pAdicIntegers p) := by
  exact Examples.Unit10.padicIntegers_isNoetherianRing p

/-- A `ℤ`-module is p-adically complete in the sense of Mathlib. -/
def IsPAdicallyComplete (p : ℕ) (M : ModuleCat.{u} ℤ) : Prop :=
  IsAdicComplete (pAdicIdeal p) (M : Type u)

/-- The quotient `M / p^n M`, expressed with Mathlib's submodule quotient. -/
def pAdicQuotient (p n : ℕ) (M : ModuleCat.{u} ℤ) : ModuleCat.{u} ℤ :=
  let P := pAdicIdeal p ^ n • (⊤ : Submodule ℤ (M : Type u))
  letI : Module ℤ ((M : Type u) ⧸ P) := Submodule.Quotient.module P
  ModuleCat.of ℤ ((M : Type u) ⧸ P)

/-- The canonical projection to the p-adic quotient. -/
def pAdicQuotientProjection (p n : ℕ) (M : ModuleCat.{u} ℤ) :
    M ⟶ pAdicQuotient p n M :=
  let P := pAdicIdeal p ^ n • (⊤ : Submodule ℤ (M : Type u))
  letI : Module ℤ ((M : Type u) ⧸ P) := Submodule.Quotient.module P
  ModuleCat.ofHom P.mkQ

/-- The transition map of an inverse system indexed by `ℕᵒᵖ`. -/
def pAdicTransition {F : ℕᵒᵖ ⥤ ModuleCat.{u} ℤ} {m n : ℕ} (h : m ≤ n) :
    F.obj (op n) ⟶ F.obj (op m) :=
  F.map (homOfLE h).op

/-- The exact data carried by the modules `(M_n)` in the source.

The Lean index `n` denotes the source's positive level `n + 1`.  The first
conjunct says that `M_(n+1)` is annihilated by `p^(n+1)`.  The second says
that the transition to the preceding level is the quotient map modulo
`p^(n+1) M_(n+2)` followed by an isomorphism.

This module-level property is the formalization of the source's colimit
description by the schemes `Spec (ℤ / p^(n+1)ℤ)` together with its
levelwise quasi-coherence assertion.  No separate formal-spectrum colimit
API is available in the current project, and the later declarations use
exactly this module consequence.
-/
def pAdicModuleSystemProperty (p : ℕ)
    : ObjectProperty (ℕᵒᵖ ⥤ ModuleCat.{u} ℤ) :=
  fun F =>
    (∀ n (x : F.obj (op n)),
      (p : ℤ) ^ pAdicLevelExponent n • x = 0) ∧
      ∀ n, ∃ e :
          pAdicQuotient p (pAdicLevelExponent n) (F.obj (op (n + 1))) ≅
            F.obj (op n),
        pAdicQuotientProjection p (pAdicLevelExponent n)
            (F.obj (op (n + 1))) ≫ e.hom =
          pAdicTransition (F := F) (Nat.le_succ n)

/-- The category of compatible p-power-torsion module systems. -/
abbrev PAdicModuleSystems (p : ℕ) :=
  (pAdicModuleSystemProperty p).FullSubcategory

/- The category of p-adically complete abelian groups, represented as
`ℤ`-modules.  This reuses the generic complete-module subcategory from the
earlier complete-modules chapter. -/
abbrev PAdicCompleteAbelianGroups (p : ℕ) :=
  Examples.Unit10.CompleteModuleCat ℤ (pAdicIdeal p)

/-! ## The inverse limit and its level quotients -/

/-- The inverse limit `M = lim M_n` of a compatible module system. -/
noncomputable def inverseLimit (𝓜 : PAdicModuleSystems p) :
    ModuleCat.{u} ℤ :=
  limit 𝓜.obj

/-- The projection from the inverse limit to the `n`-th module. -/
noncomputable def inverseLimitProjection (𝓜 : PAdicModuleSystems p)
    (n : ℕ) : inverseLimit 𝓜 ⟶ 𝓜.obj.obj (op n) :=
  limit.π 𝓜.obj (op n)

/-- The inverse limit of the source system is p-adically complete. -/
theorem inverseLimit_isPAdicallyComplete
    (𝓜 : PAdicModuleSystems p) :
    IsPAdicallyComplete p (inverseLimit 𝓜) := by
  sorry

/-- Its source level `n + 1` is the quotient of the limit by `p^(n+1)`. -/
theorem inverseLimit_level_iso
    (𝓜 : PAdicModuleSystems p) (n : ℕ) :
    Nonempty
      (𝓜.obj.obj (op n) ≅
        pAdicQuotient p (pAdicLevelExponent n) (inverseLimit 𝓜)) := by
  sorry

/-! ## The module-system side of the equivalence -/

/-- The canonical adjacent transition on the quotients of a module. -/
def pAdicQuotientTransition (p n : ℕ) (M : ModuleCat.{u} ℤ) :
    pAdicQuotient p (pAdicLevelExponent (n + 1)) M ⟶
      pAdicQuotient p (pAdicLevelExponent n) M :=
  let Pn := pAdicIdeal p ^ pAdicLevelExponent n •
    (⊤ : Submodule ℤ (M : Type u))
  let Pnext := pAdicIdeal p ^ pAdicLevelExponent (n + 1) •
    (⊤ : Submodule ℤ (M : Type u))
  letI : Module ℤ ((M : Type u) ⧸ Pnext) := Submodule.Quotient.module Pnext
  letI : Module ℤ ((M : Type u) ⧸ Pn) := Submodule.Quotient.module Pn
  ModuleCat.ofHom
    (Submodule.factorPow (pAdicIdeal p) (M : Type u)
      (Nat.le_succ (pAdicLevelExponent n)))

/-- The canonical inverse system of quotients of a module. -/
def pAdicQuotientSystem (p : ℕ) (M : ModuleCat.{u} ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} ℤ :=
  Functor.ofOpSequence (X := fun n => pAdicQuotient p (pAdicLevelExponent n) M)
    (fun n => pAdicQuotientTransition p n M)

/-- The canonical quotient system satisfies the source's module-system
conditions for a p-adically complete module. -/
theorem pAdicQuotientSystem_property
    (M : PAdicCompleteAbelianGroups p) :
    pAdicModuleSystemProperty p
      (pAdicQuotientSystem p M.obj) := by
  sorry

/-- Turn a p-adically complete module into its compatible system of levels. -/
def completeModuleToSystem (M : PAdicCompleteAbelianGroups p) :
    PAdicModuleSystems p :=
  ⟨pAdicQuotientSystem p M.obj, pAdicQuotientSystem_property M⟩

/-- The category of compatible systems is equivalent to p-adically complete
abelian groups. -/
theorem pAdicModuleSystems_equivalent_to_completeAbelianGroups (p : ℕ)
    [Fact p.Prime] :
    Nonempty
      (PAdicModuleSystems p ≌ PAdicCompleteAbelianGroups p) := by
  sorry

/-! ## Quasi-coherent modules on the formal spectrum -/

/-- In this chapter's formal-spectrum model, quasi-coherent modules on
`Spf(ℤ_[p])` are the compatible systems of level modules. -/
abbrev QuasiCoherentModulesOnPAdicFormalSpectrum (p : ℕ) :=
  PAdicModuleSystems p

/-- The source's equivalence with p-adically complete abelian groups. -/
def pAdicFormalSpectrum_quasiCoherent_equivalence (p : ℕ) [Fact p.Prime] :
    QuasiCoherentModulesOnPAdicFormalSpectrum p ≌
      PAdicCompleteAbelianGroups p :=
  Classical.choice (pAdicModuleSystems_equivalent_to_completeAbelianGroups p)

/-- Quasi-coherent modules on this Noetherian affine formal algebraic space
do not form an abelian category. -/
theorem quasiCoherentModulesOnPAdicFormalSpectrum_not_abelian (p : ℕ)
    [Fact p.Prime] :
    ¬ Nonempty (Abelian (QuasiCoherentModulesOnPAdicFormalSpectrum p)) := by
  sorry

end Formalization.«Books.Examples».Unit13
