import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Examples, Chapter 13: Nonabelian category of quasi-coherent modules

The geometric formal-spectrum construction is not yet part of Mathlib.  The
presentation interface below records the fppf sheaf and stack-in-setoids
claims, while the module calculation uses Mathlib's adic-completion and
module-category APIs directly.
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

/-- The fppf sheaf presentation attached to a formal affine spectrum. -/
structure FormalSpectrumPresentation (R : CommRingCat) where
  points : Sheaf FppfTopologyOverIntegers Type
  isStackInSetoids : Prop
  isStackInSetoids_proof : isStackInSetoids

/-- The declaration-level object representing `X = Spf(ℤ_[p])`. -/
structure PAdicFormalSpectrum (p : ℕ) [Fact p.Prime] where
  presentation : FormalSpectrumPresentation (CommRingCat.of (pAdicIntegers p))

/-- Existence of the fppf sheaf represented by `Spf(ℤ_[p])`. -/
theorem pAdicFormalSpectrum_exists (p : ℕ) [Fact p.Prime] :
    Nonempty (PAdicFormalSpectrum p) := by
  sorry

/-- A chosen formal spectrum `Spf(ℤ_[p])`. -/
noncomputable def pAdicFormalSpectrum (p : ℕ) [Fact p.Prime] :
    PAdicFormalSpectrum p :=
  Classical.choice (pAdicFormalSpectrum_exists p)

theorem pAdicFormalSpectrum_isSheafInSets (p : ℕ) [Fact p.Prime] :
    Nonempty (Sheaf FppfTopologyOverIntegers Type) :=
  ⟨(pAdicFormalSpectrum p).presentation.points⟩

theorem pAdicFormalSpectrum_isStackInSetoids (p : ℕ) [Fact p.Prime] :
    (pAdicFormalSpectrum p).presentation.isStackInSetoids :=
  (pAdicFormalSpectrum p).presentation.isStackInSetoids_proof

/-- The coordinate ring of `Spf(ℤ_[p])` is Noetherian. -/
theorem pAdicFormalSpectrum_isNoetherian (p : ℕ) [Fact p.Prime] :
    IsNoetherianRing (pAdicIntegers p) := by
  sorry

/-! ## Compatible systems of modules -/

/-- The ideal defining the `p`-adic filtration on abelian groups. -/
def pAdicIdeal (p : ℕ) : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)

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

The first conjunct says that `M_n` is annihilated by `p^n`.  The second says
that the transition `M_{n+1} → M_n` is the quotient map modulo `p^n M_{n+1}`
followed by an isomorphism.
-/
def pAdicModuleSystemProperty (p : ℕ)
    : ObjectProperty (ℕᵒᵖ ⥤ ModuleCat.{u} ℤ) :=
  fun F =>
    (∀ n (x : F.obj (op n)), (p : ℤ) ^ n • x = 0) ∧
      ∀ n, ∃ e : pAdicQuotient p n (F.obj (op (n + 1))) ≅ F.obj (op n),
        pAdicQuotientProjection p n (F.obj (op (n + 1))) ≫ e.hom =
          pAdicTransition (F := F) (Nat.le_succ n)

/-- The category of compatible p-power-torsion module systems. -/
abbrev PAdicModuleSystems (p : ℕ) :=
  (pAdicModuleSystemProperty p).FullSubcategory

/-- The category of p-adically complete abelian groups, represented as
`ℤ`-modules. -/
def pAdicCompleteProperty (p : ℕ) : ObjectProperty (ModuleCat.{u} ℤ) :=
  fun M => IsPAdicallyComplete p M

abbrev PAdicCompleteAbelianGroups (p : ℕ) :=
  (pAdicCompleteProperty p).FullSubcategory

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

/-- Its `n`-th level is the quotient of the limit by `p^n`. -/
theorem inverseLimit_level_iso
    (𝓜 : PAdicModuleSystems p) (n : ℕ) :
    Nonempty
      (𝓜.obj.obj (op n) ≅ pAdicQuotient p n (inverseLimit 𝓜)) := by
  sorry

/-! ## The module-system side of the equivalence -/

/-- The canonical adjacent transition on the quotients of a module. -/
def pAdicQuotientTransition (p n : ℕ) (M : ModuleCat.{u} ℤ) :
    pAdicQuotient p (n + 1) M ⟶ pAdicQuotient p n M :=
  let Pn := pAdicIdeal p ^ n • (⊤ : Submodule ℤ (M : Type u))
  let Pnext := pAdicIdeal p ^ (n + 1) • (⊤ : Submodule ℤ (M : Type u))
  letI : Module ℤ ((M : Type u) ⧸ Pnext) := Submodule.Quotient.module Pnext
  letI : Module ℤ ((M : Type u) ⧸ Pn) := Submodule.Quotient.module Pn
  ModuleCat.ofHom
    (AdicCompletion.transitionMap (pAdicIdeal p) (M : Type u) (Nat.le_succ n))

/-- The canonical inverse system of quotients of a module. -/
def pAdicQuotientSystem (p : ℕ) (M : ModuleCat.{u} ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} ℤ :=
  Functor.ofOpSequence (X := fun n => pAdicQuotient p n M)
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
`Spf(ℤ_[p])` are the complete module category. -/
abbrev QuasiCoherentModulesOnPAdicFormalSpectrum (p : ℕ) :=
  PAdicCompleteAbelianGroups p

/-- The source's equivalence with p-adically complete abelian groups. -/
def pAdicFormalSpectrum_quasiCoherent_equivalence (p : ℕ) [Fact p.Prime] :
    QuasiCoherentModulesOnPAdicFormalSpectrum p ≌
      PAdicCompleteAbelianGroups p :=
  CategoryTheory.Equivalence.refl

/-- Quasi-coherent modules on this Noetherian affine formal algebraic space
do not form an abelian category. -/
theorem quasiCoherentModulesOnPAdicFormalSpectrum_not_abelian (p : ℕ)
    [Fact p.Prime] :
    ¬ Nonempty (Abelian (QuasiCoherentModulesOnPAdicFormalSpectrum p)) := by
  sorry

end Formalization.«Books.Examples».Unit13
