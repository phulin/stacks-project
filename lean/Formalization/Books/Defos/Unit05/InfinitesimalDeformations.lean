import Formalization.Books.Defos.Unit02.DeformationsOfRings
import Formalization.Books.Defos.Unit03.ThickeningsOfRingedSpaces
import Formalization.Books.Modules.Unit16.TensorProduct
import Formalization.Books.Modules.Unit20.FlatMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Torsor
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Deformation Theory, Chapter 5: Infinitesimal deformations of modules on ringed spaces

Formalizes books/defos.tex:1252--1579. Existing module categories,
pullback/pushforward functors, tensor products, flatness, kernels, Ext groups,
and torsors are reused from earlier chapters.
-/

namespace Formalization.Books.Defos.Unit05

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Defos.Unit02
open Formalization.Books.Defos.Unit03
open Formalization.Books.Defos.Unit03.MorphismOfThickenings
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit20
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## The reduction sequence -/

/-- The module i^* F' on the reduced ringed space. -/
abbrev reducedModule {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] (F' : Mod X'.structureSheaf) :
    Mod X.structureSheaf :=
  (ringedSpaceModulePullback i).obj F'

/-- The quotient map F' -> i_* i^* F'. -/
noncomputable def reducedModuleMap {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X')
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] (F' : Mod X'.structureSheaf) :
    F' ⟶ (ringedSpaceModulePushforward i).obj (reducedModule i F') :=
  (ringedSpaceModuleAdjunction i).unit.app F'

/-- The module I F', represented by the kernel of the quotient map. -/
noncomputable def idealTimesModule {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X')
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] (F' : Mod X'.structureSheaf) :
    Mod X'.structureSheaf :=
  kernel (reducedModuleMap i F')

/-- The short complex 0 -> I F' -> F' -> i_* i^* F' -> 0. -/
noncomputable def reducedModuleShortComplex {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X')
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] (F' : Mod X'.structureSheaf) :
    ShortComplex (Mod X'.structureSheaf) :=
  ShortComplex.mk (kernel.ι (reducedModuleMap i F'))
    (reducedModuleMap i F') (kernel.condition (reducedModuleMap i F'))

/-- The reduction sequence is short exact for a first-order thickening. -/
theorem reducedModuleShortComplex_shortExact
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i)
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] (F' : Mod X'.structureSheaf) :
    (reducedModuleShortComplex i F').ShortExact := by
  sorry

/-- The structure-sheaf sequence is the Chapter 3 kernel sequence. -/
abbrev structureSheafShortComplex {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') :
    ShortComplex (Mod X'.structureSheaf) :=
  thickeningKernelShortComplex i

theorem structureSheafShortComplex_shortExact
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsThickening i) :
    (structureSheafShortComplex i).ShortExact :=
  thickeningKernelShortComplex_shortExact i hi

/-! ## Lifts of maps -/

/-- The type of lifts of a map phi : i^* F' -> i^* G'. -/
def ModuleLift {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)]
    (F' G' : Mod X'.structureSheaf)
    (φ : reducedModule i F' ⟶ reducedModule i G') : Type v :=
  {φ' : F' ⟶ G' // (ringedSpaceModulePullback i).map φ' = φ}

/-- I G' regarded as a module on X. -/
abbrev idealTimesModuleOnReducedSpace
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] (G' : Mod X'.structureSheaf) :
    Mod X.structureSheaf :=
  reducedModule i (idealTimesModule i G')

/-- Lemma inf-map-special: the nonempty lift type is a torsor under
Hom_X(i^*F', I G'). -/
theorem inf_map_special
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i)
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)]
    (F' G' : Mod X'.structureSheaf)
    (φ : reducedModule i F' ⟶ reducedModule i G')
    (hφ : Nonempty (ModuleLift i F' G' φ)) :
    Nonempty (PrincipalHomogeneousSpace
      (reducedModule i F' ⟶ idealTimesModuleOnReducedSpace i G')
      (ModuleLift i F' G' φ)) := by
  sorry

/-! ## Relative flatness and lifting -/

/-- Flatness of a sheaf of modules over a ringed-space morphism. -/
abbrev FlatOver {X S : RingedSpace.{v}} (f : RingedSpaceHom X S)
    (F : Mod X.structureSheaf) : Prop :=
  Formalization.Books.Modules.Unit20.flatOver f F

/-- A chosen module presentation of the source square-zero ideal. -/
noncomputable def sourceIdealModule (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i) : Mod M.X.structureSheaf :=
  Classical.choose
    (Formalization.Books.Defos.Unit03.firstOrderThickening_kernel_is_module M.i hi)

/-- The chosen source-ideal presentation isomorphism. -/
noncomputable def sourceIdealModuleIso (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i) :
    (ringedSpaceModulePushforward M.i).obj (sourceIdealModule M hi) ≅
      M.sourceIdeal.carrier :=
  Classical.choice
    (Classical.choose_spec
      (Formalization.Books.Defos.Unit03.firstOrderThickening_kernel_is_module M.i hi))

/-- A chosen module presentation of the base square-zero ideal. -/
noncomputable def baseIdealModule (M : MorphismOfThickenings)
    (ht : IsFirstOrderThickening M.t) : Mod M.S.structureSheaf :=
  Classical.choose
    (Formalization.Books.Defos.Unit03.MorphismOfThickenings
      .firstOrder_baseIdeal_is_module M ht)

/-- The chosen base-ideal presentation isomorphism. -/
noncomputable def baseIdealModuleIso (M : MorphismOfThickenings)
    (ht : IsFirstOrderThickening M.t) :
    (ringedSpaceModulePushforward M.t).obj (baseIdealModule M ht) ≅
      M.baseIdeal.carrier :=
  Classical.choice
    (Classical.choose_spec
      (Formalization.Books.Defos.Unit03.MorphismOfThickenings
        .firstOrder_baseIdeal_is_module M ht))

/-- The coefficient G tensor f^* J in the relative lifting statement. -/
noncomputable abbrev relativeLiftCoefficient
    (M : MorphismOfThickenings) (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)] (G : Mod M.X.structureSheaf) :
    Mod M.X.structureSheaf :=
  tensorProductSheaf M.X.structureSheaf G
    ((ringedSpaceModulePullback M.f).obj (baseIdealModule M ht))

/-! ## Flatness criterion for a lifted module -/

/-- The three canonical maps used in Lemma inf-deform-module. The
factorization field records the displayed chain
f^*J tensor F -> I tensor F -> I F'. -/
structure FlatnessComparison
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    (F' : Mod M.X'.structureSheaf) where
  baseToIdeal :
    relativeLiftCoefficient M ht (reducedModule M.i F') ⟶
      idealTimesModuleOnReducedSpace M.i F'
  baseToSourceTensor :
    relativeLiftCoefficient M ht (reducedModule M.i F') ⟶
      tensorProductSheaf M.X.structureSheaf (sourceIdealModule M hi)
        (reducedModule M.i F')
  sourceTensorToIdeal :
    tensorProductSheaf M.X.structureSheaf (sourceIdealModule M hi)
        (reducedModule M.i F') ⟶ idealTimesModuleOnReducedSpace M.i F'
  factorization : baseToSourceTensor ≫ sourceTensorToIdeal = baseToIdeal

/-- Lemma inf-deform-module: flatness over S' is equivalent to the canonical
map f^*J tensor F -> I F' being an isomorphism. -/
theorem deform_module_iff
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (F' : Mod M.X'.structureSheaf)
    (hF : FlatOver M.f (reducedModule M.i F'))
    (c : FlatnessComparison M hi ht F') :
    FlatOver M.f' F' ↔ IsIso c.baseToIdeal := by
  sorry

/-- The moreover clause of Lemma inf-deform-module. -/
theorem deform_module_moreover
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (F' : Mod M.X'.structureSheaf)
    (hF : FlatOver M.f (reducedModule M.i F'))
    (hF' : FlatOver M.f' F')
    (c : FlatnessComparison M hi ht F') :
    IsIso c.baseToSourceTensor ∧ IsIso c.sourceTensorToIdeal := by
  sorry

/-- Lemma inf-map-rel. -/
theorem inf_map_rel
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (F' G' : Mod M.X'.structureSheaf)
    (hG' : FlatOver M.f' G')
    (φ : reducedModule M.i F' ⟶ reducedModule M.i G')
    (hφ : Nonempty (ModuleLift M.i F' G' φ)) :
    Nonempty (PrincipalHomogeneousSpace
      (reducedModule M.i F' ⟶
        relativeLiftCoefficient M ht (reducedModule M.i G'))
      (ModuleLift M.i F' G' φ)) := by
  sorry

/-! ## Obstruction classes -/

/-- Ext in the module category of a ringed space. -/
abbrev ModuleExt {X : RingedSpace.{v}} (F G : Mod X.structureSheaf)
    (n : ℕ) [CategoryTheory.HasExt.{v} (Mod X.structureSheaf)] : Type v :=
  CategoryTheory.Abelian.Ext F G n

/-- Lemma inf-obs-map-special. -/
theorem inf_obs_map_special
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i)
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)]
    [CategoryTheory.HasExt.{v} (Mod X.structureSheaf)]
    (F' G' : Mod X'.structureSheaf)
    (φ : reducedModule i F' ⟶ reducedModule i G') :
    ∃ o : ModuleExt (reducedModule i F')
        (idealTimesModuleOnReducedSpace i G') 1,
      (o = 0 ↔ Nonempty (ModuleLift i F' G' φ)) := by
  sorry

/-- Lemma inf-obs-map-rel. -/
theorem inf_obs_map_rel
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    [CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (F' G' : Mod M.X'.structureSheaf)
    (hF' : FlatOver M.f' F') (hG' : FlatOver M.f' G')
    (φ : reducedModule M.i F' ⟶ reducedModule M.i G') :
    ∃ o : ModuleExt (reducedModule M.i F')
        (relativeLiftCoefficient M ht (reducedModule M.i G')) 1,
      (o = 0 ↔ Nonempty (ModuleLift M.i F' G' φ)) := by
  sorry

/-! ## Flat extensions -/

/-- A flat lift of F to X', with its specified reduction isomorphism. -/
structure FlatModuleLift (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (F : Mod M.X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)] where
  module : Mod M.X'.structureSheaf
  flat : FlatOver M.f' module
  identification : reducedModule M.i module ≅ F

/-- Isomorphisms of flat lifts preserving the reduction identification. -/
structure FlatModuleLiftIso
    {M : MorphismOfThickenings} {hi : IsFirstOrderThickening M.i}
    {F : Mod M.X.structureSheaf}
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    (A B : FlatModuleLift M hi F) where
  hom : A.module ≅ B.module
  commutes :
    (ringedSpaceModulePullback M.i).map hom.hom ≫ B.identification.hom =
      A.identification.hom

namespace FlatModuleLiftIso

variable {M : MorphismOfThickenings} {hi : IsFirstOrderThickening M.i}
  {F : Mod M.X.structureSheaf}
  [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
    M.i.sharp).IsRightAdjoint)]

def refl (A : FlatModuleLift M hi F) : FlatModuleLiftIso A A where
  hom := Iso.refl _
  commutes := by simp

def symm {A B : FlatModuleLift M hi F} (e : FlatModuleLiftIso A B) :
    FlatModuleLiftIso B A where
  hom := e.hom.symm
  commutes := by
    apply (cancel_mono e.hom.hom).1
    simp only [Functor.map_comp, Iso.symm_hom, Category.assoc, e.commutes]
    simp

def trans {A B C : FlatModuleLift M hi F}
    (e₁ : FlatModuleLiftIso A B) (e₂ : FlatModuleLiftIso B C) :
    FlatModuleLiftIso A C where
  hom := e₁.hom ≪≫ e₂.hom
  commutes := by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [e₁.commutes, e₂.commutes]

end FlatModuleLiftIso

/-- The equivalence relation defining isomorphism classes of flat lifts. -/
def flatModuleLiftEquivalence
    (M : MorphismOfThickenings) (hi : IsFirstOrderThickening M.i)
    (F : Mod M.X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)] :
    Setoid (FlatModuleLift M hi F) where
  r A B := Nonempty (FlatModuleLiftIso A B)
  iseqv := {
    refl := fun A => ⟨FlatModuleLiftIso.refl A⟩
    symm := by
      intro A B h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro A B C hAB hBC
      rcases hAB with ⟨e₁⟩
      rcases hBC with ⟨e₂⟩
      exact ⟨e₁.trans e₂⟩ }

/-- The set of isomorphism classes of flat module lifts. -/
abbrev FlatModuleLiftClasses
    (M : MorphismOfThickenings) (hi : IsFirstOrderThickening M.i)
    (F : Mod M.X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)] :=
  Quotient (flatModuleLiftEquivalence M hi F)

/-- Lemma inf-ext-rel. -/
theorem inf_ext_rel
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    [CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (F : Mod M.X.structureSheaf) (hF : FlatOver M.f F)
    (hF' : Nonempty (FlatModuleLift M hi F)) :
    Nonempty (PrincipalHomogeneousSpace
      (ModuleExt F
        (tensorProductSheaf M.X.structureSheaf
          (sourceIdealModule M hi) F) 1)
      (FlatModuleLiftClasses M hi F)) := by
  sorry

/-! ## Flat-lift obstruction -/

/-- The source-facing map f^*J tensor F -> I tensor F. -/
structure CanonicalIdealTensorComparison
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    (F : Mod M.X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)] where
  map : tensorProductSheaf M.X.structureSheaf
      ((ringedSpaceModulePullback M.f).obj (baseIdealModule M ht)) F ⟶
    tensorProductSheaf M.X.structureSheaf (sourceIdealModule M hi) F

/-- The Ext2 obstruction group for a flat lift. -/
abbrev FlatLiftObstruction
    (M : MorphismOfThickenings) (hi : IsFirstOrderThickening M.i)
    (F : Mod M.X.structureSheaf)
    [CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)] : Type v :=
  ModuleExt F
    (tensorProductSheaf M.X.structureSheaf (sourceIdealModule M hi) F) 2

/-- Lemma inf-obs-ext-rel. -/
theorem inf_obs_ext_rel
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    [CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (F : Mod M.X.structureSheaf) (hF : FlatOver M.f F)
    (c : CanonicalIdealTensorComparison M hi ht F) :
    (Nonempty (FlatModuleLift M hi F) ↔
      (IsIso c.map ∧ ∃ o : FlatLiftObstruction M hi F, o = 0)) := by
  sorry

end

end Formalization.Books.Defos.Unit05
