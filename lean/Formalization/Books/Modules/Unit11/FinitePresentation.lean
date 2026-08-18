import Formalization.Books.Modules.Unit09.FiniteType
import Formalization.Books.Modules.Unit10.QuasiCoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Sheaves of Modules, Chapter 11: Modules of finite presentation

This file formalizes the source section `Modules of finite presentation`.
Finite presentation itself is Mathlib's canonical `SheafOfModules.IsFinitePresentation`
condition.  The local finite-cokernel formulation and the categorical forms of
the source's exact sequence, colimit, and stalk statements are retained as
usable interfaces below.
-/

namespace Formalization.Books.Modules.Unit11

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit09
open Formalization.Books.Modules.Unit10
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

local notation "Mod" => Formalization.Books.Sheaves.Unit10.Mod

/-! ## Definition `definition-finite-presentation` -/

/-- The source's finite-presentation condition, using Mathlib's canonical
finite local presentation class for sheaves of modules. -/
abbrev IsFinitePresentation {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  SheafOfModules.IsFinitePresentation F

/-- A finite free cokernel presentation on an open subspace.  The two finite
index sets are represented by `ULift (Fin m)` and `ULift (Fin n)`, matching the source's
finite direct sums. -/
def HasFinitePresentationOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∃ (m n : ℕ)
    (φ : (SheafOfModules.free (ULift.{v} (Fin m)) :
      Mod (ringedOpenSubspace X U).structureSheaf) ⟶
      (SheafOfModules.free (ULift.{v} (Fin n)) :
        Mod (ringedOpenSubspace X U).structureSheaf)),
    Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ)

/-- The generators-and-relations form of a finite presentation on an open.

This is Mathlib's canonical packaging of the two clauses following the
source definition: finitely many sections generate the restriction, and
finitely many sections generate the kernel of the resulting epimorphism. -/
def HasFiniteGeneratorsAndRelationsOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∃ P : ((openModuleRestrictionFunctor X U).obj F).Presentation, P.IsFinite

/-- The pointwise local form of finite presentation. -/
def LocallyFinitePresentation {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ HasFinitePresentationOn F U

/-- The exact sequence attached to a finite free cokernel presentation. -/
def HasExactFinitePresentationOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∃ (m n : ℕ)
    (φ : (SheafOfModules.free (ULift.{v} (Fin m)) :
      Mod (ringedOpenSubspace X U).structureSheaf) ⟶
      (SheafOfModules.free (ULift.{v} (Fin n)) :
        Mod (ringedOpenSubspace X U).structureSheaf))
    (e : ((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ),
    (ShortComplex.mk φ (cokernel.π φ ≫ e.inv) (by simp)).Exact

/-- Finite presentation is equivalent to the source's local finite-cokernel
formulation. -/
theorem isFinitePresentation_iff_locallyFinitePresentation
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    IsFinitePresentation F ↔ LocallyFinitePresentation F := by
  sorry

/-- The finite-cokernel and finite-generators-and-relations descriptions on
an open are equivalent. -/
theorem hasFinitePresentationOn_iff_hasFiniteGeneratorsAndRelationsOn
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) (U : Opens X.carrier) :
    HasFinitePresentationOn F U ↔ HasFiniteGeneratorsAndRelationsOn F U := by
  sorry

/-- The displayed finite-cokernel sequence is exact, and conversely an exact
sequence of this form supplies the displayed cokernel presentation. -/
theorem hasFinitePresentationOn_iff_hasExactFinitePresentationOn
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) (U : Opens X.carrier) :
    HasFinitePresentationOn F U ↔ HasExactFinitePresentationOn F U := by
  sorry

/-! The two clauses in the source's explanation are represented by the finite
generators and finite relations in `SheafOfModules.Presentation.IsFinite`;
the local finite-cokernel interface above packages both clauses together. -/

/-! ## Lemma `lemma-finite-presentation-quasi-coherent` -/

/-- Every module of finite presentation is quasi-coherent. -/
theorem finitePresentation_isQuasiCoherent
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : IsFinitePresentation F) :
    IsQuasiCoherent F := by
  sorry

/-! ## Lemma `lemma-cokernel-finite-finite-presentation` -/

/-- The cokernel of a map from a finite-type module to a finitely presented
module is finitely presented. -/
theorem cokernel_finiteType_finitePresentation
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : G ⟶ F) (hF : IsFinitePresentation F) (hG : finiteType G) :
    IsFinitePresentation (cokernel φ) := by
  sorry

/-! ## Lemma `lemma-kernel-surjection-finite-free-onto-finite-presentation` -/

/-- The kernel of a surjection from a finite free module onto a finitely
presented module is of finite type. -/
theorem kernel_surjection_finiteFree_finiteType
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf} (r : ℕ)
    (ψ : (SheafOfModules.free (ULift.{v} (Fin r)) : Mod X.structureSheaf) ⟶ F)
    (hψ : Epi ψ) (hF : IsFinitePresentation F) :
    finiteType (kernel ψ) := by
  sorry

/-- The kernel of a surjection from a finite-type module onto a finitely
presented module is of finite type. -/
theorem kernel_surjection_finiteType_finiteType
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (θ : G ⟶ F) (hθ : Epi θ) (hG : finiteType G)
    (hF : IsFinitePresentation F) :
    finiteType (kernel θ) := by
  sorry

/-! ## Lemma `lemma-pullback-finite-presentation` -/

/-- Pullback along a morphism of ringed spaces preserves finite presentation. -/
theorem pullback_finitePresentation
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (hG : IsFinitePresentation G)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    IsFinitePresentation ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

/-! ## Lemma `lemma-quasi-coherent-limit-finite-presentation` -/

/-- A directed colimit of finite-presentation sheaves representing `F`. -/
structure DirectedFinitePresentationColimit
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) where
  I : Type v
  [preorder : Preorder I]
  [nonempty : Nonempty I]
  [directed : IsDirectedOrder I]
  diagram : I ⥤ Mod X.structureSheaf
  finitePresentation : ∀ i, IsFinitePresentation (diagram.obj i)
  iso : Nonempty (colimit diagram ≅ F)

/-- The associated sheaf of any global-sections module is a directed colimit
of finitely presented sheaves. -/
theorem associatedSheaf_is_directedColimit_finitePresentation
    {X : RingedSpace.{v}}
    (M : ModuleCat (globalSectionsRing X)) :
    Nonempty (DirectedFinitePresentationColimit
      (associatedSheafOfGlobalSections M)) := by
  sorry

/-! ## Lemma `lemma-finite-presentation-stalk-free` -/

/-- The finite free module over the stalk of the structure sheaf. -/
noncomputable abbrev stalkFreeModule {X : RingedSpace.{v}} (x : X) (r : ℕ) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat) X.structureSheaf.obj x) :=
  (ModuleCat.free
    (TopCat.Presheaf.stalk (C := RingCat) X.structureSheaf.obj x)).obj
      (ULift.{v} (Fin r))

/-- A finite-presentation module which is free at a stalk is free on a
neighbourhood of that point. -/
theorem finitePresentation_stalk_free
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : IsFinitePresentation F) (x : X) (r : ℕ)
    (hx : Nonempty ((sheafModuleStalkFunctor X.structureSheaf x).obj F ≅
      stalkFreeModule x r)) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅
        (SheafOfModules.free (ULift.{v} (Fin r)) :
          Mod (ringedOpenSubspace X U).structureSheaf)) := by
  sorry

end

end Formalization.Books.Modules.Unit11
