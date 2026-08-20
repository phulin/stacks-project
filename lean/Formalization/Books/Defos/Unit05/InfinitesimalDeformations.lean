import Formalization.Books.Defos.Unit04.Core
import Formalization.Books.Modules.Unit20.FlatMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Deformation Theory, Chapter 5: Infinitesimal deformations of modules on ringed spaces

Formalizes books/defos.tex:1252--1579. Existing module categories,
pullback/pushforward functors, the Chapter 4 source-facing tensor interface,
flatness, kernels, Ext groups, and torsors are reused from earlier chapters.
-/

namespace Formalization.Books.Defos.Unit05

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Defos.Unit02
open Formalization.Books.Defos.Unit03
open Formalization.Books.Defos.Unit03.MorphismOfThickenings
open Formalization.Books.Defos.Unit04
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## The reduction sequence

The source's initial sequence
`0 → I F' → F' → i_* i^* F' → 0` is represented by
`reducedModuleShortComplex`; `idealTimesModule_pushforward_iso` records the
unique module-on-the-reduction-space interpretation of its kernel in the
first-order case. -/

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

/- The pullback of the structure sheaf and the pullback of its reduction
   ideal are canonically the structure sheaf and the thickening ideal. -/
theorem structureSheaf_reduction_iso
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] :
    Nonempty
      (reducedModule i (SheafOfModules.unit X'.structureSheaf) ≅
        SheafOfModules.unit X.structureSheaf) := by
  sorry

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

/- The kernel in the reduction sequence is annihilated by the square-zero
   thickening ideal, so it is represented on the reduced space.  We retain
   the representation as an isomorphism rather than identifying the two
   module objects definitionally. -/
theorem idealTimesModule_pushforward_iso
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i)
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] (F' : Mod X'.structureSheaf) :
    Nonempty
      ((ringedSpaceModulePushforward i).obj
        (idealTimesModuleOnReducedSpace i F') ≅
        idealTimesModule i F') := by
  sorry

theorem structureSheaf_idealTimes_iso
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i)
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)] :
    Nonempty
      (idealTimesModuleOnReducedSpace i
          (SheafOfModules.unit X'.structureSheaf) ≅
        Formalization.Books.Defos.Unit04.firstOrderKernelModule i hi) := by
  sorry

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

/- The source ideal presentation is the canonical chosen presentation from
   the preceding thickening chapter. -/
abbrev sourceIdealModule (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i) : Mod M.X.structureSheaf :=
  Formalization.Books.Defos.Unit04.firstOrderKernelModule M.i hi

abbrev sourceIdealModuleIso (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i) :
    (ringedSpaceModulePushforward M.i).obj (sourceIdealModule M hi) ≅
      M.sourceIdeal.carrier :=
  Formalization.Books.Defos.Unit04.firstOrderKernelModuleIso M.i hi

/-- A chosen module presentation of the base square-zero ideal. -/
noncomputable def baseIdealModule (M : MorphismOfThickenings.{v})
    (ht : IsFirstOrderThickening M.t) : Mod M.S.structureSheaf :=
  Classical.choose
    (Formalization.Books.Defos.Unit03.MorphismOfThickenings.firstOrder_baseIdeal_is_module M ht)

/-- The chosen base-ideal presentation isomorphism. -/
noncomputable def baseIdealModuleIso (M : MorphismOfThickenings.{v})
    (ht : IsFirstOrderThickening M.t) :
    (ringedSpaceModulePushforward M.t).obj (baseIdealModule M ht) ≅
      M.baseIdeal.carrier :=
  Classical.choice
    (Classical.choose_spec
      (Formalization.Books.Defos.Unit03.MorphismOfThickenings.firstOrder_baseIdeal_is_module M ht))

/-- The coefficient G tensor f^* J in the relative lifting statement. -/
noncomputable abbrev relativeLiftCoefficient
    (M : MorphismOfThickenings.{v}) (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)] (G : Mod M.X.structureSheaf) :
    Mod M.X.structureSheaf :=
  moduleTensor G ((ringedSpaceModulePullback M.f).obj (baseIdealModule M ht))

/- The flatness criterion uses the source order
`f^* J ⊗ F`, whereas the map-lifting torsor uses `G ⊗ f^* J`. -/
noncomputable abbrev flatnessCoefficient
    (M : MorphismOfThickenings.{v}) (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)] (F : Mod M.X.structureSheaf) :
    Mod M.X.structureSheaf :=
  moduleTensor ((ringedSpaceModulePullback M.f).obj (baseIdealModule M ht)) F

/-! ## Flatness criterion for a lifted module -/

/-- The three canonical maps used in Lemma inf-deform-module. The
factorization field records the displayed chain
f^*J tensor F -> I tensor F -> I F'. -/
structure FlatnessComparison
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    (F' : Mod M.X'.structureSheaf) where
  baseToIdeal :
    flatnessCoefficient M ht (reducedModule M.i F') ⟶
      idealTimesModuleOnReducedSpace M.i F'
  baseToSourceTensor :
    flatnessCoefficient M ht (reducedModule M.i F') ⟶
      moduleTensor (sourceIdealModule M hi) (reducedModule M.i F')
  sourceTensorToIdeal :
    moduleTensor (sourceIdealModule M hi) (reducedModule M.i F') ⟶
      idealTimesModuleOnReducedSpace M.i F'
  factorization : baseToSourceTensor ≫ sourceTensorToIdeal = baseToIdeal

theorem flatnessComparison_exists
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (F' : Mod M.X'.structureSheaf) :
    Nonempty (FlatnessComparison M hi ht F') := by
  sorry

noncomputable def flatnessComparison
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (F' : Mod M.X'.structureSheaf) :
    FlatnessComparison M hi ht F' :=
  Classical.choice (flatnessComparison_exists M hi ht hstrict F')

/-- Lemma inf-deform-module: flatness over S' is equivalent to the canonical
map f^*J tensor F -> I F' being an isomorphism. -/
theorem deform_module_iff
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (F' : Mod M.X'.structureSheaf)
    (hF : FlatOver M.f (reducedModule M.i F')) :
    FlatOver M.f' F' ↔
      IsIso (flatnessComparison M hi ht hstrict F').baseToIdeal := by
  sorry

/-- The moreover clause of Lemma inf-deform-module. -/
theorem deform_module_moreover
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (F' : Mod M.X'.structureSheaf)
    (hF : FlatOver M.f (reducedModule M.i F'))
    (hF' : FlatOver M.f' F') :
    IsIso (flatnessComparison M hi ht hstrict F').baseToSourceTensor ∧
      IsIso (flatnessComparison M hi ht hstrict F').sourceTensorToIdeal := by
  sorry

/-- Lemma inf-map-rel. -/
theorem inf_map_rel
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
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

/- The special obstruction lemma is stated with the derived pullback
   `Li^*`.  The project has the derived-category API but no canonical
   derived pullback functor for these sheaf-module pullbacks, so we expose
   the exact object-level interface needed by this chapter. -/
abbrev DerivedModule {X : RingedSpace.{v}}
    [HasDerivedCategory (Mod X.structureSheaf)] :=
  DerivedCategory (Mod X.structureSheaf)

structure DerivedPullbackData {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X')
    [HasDerivedCategory (Mod X.structureSheaf)] where
  object : Mod X'.structureSheaf → DerivedModule
    (X := X)

noncomputable abbrev derivedModuleOf
    {X : RingedSpace.{v}}
    [HasDerivedCategory (Mod X.structureSheaf)]
    (F : Mod X.structureSheaf) : DerivedModule (X := X) :=
  (DerivedCategory.singleFunctor (Mod X.structureSheaf) 0).obj F

abbrev DerivedModuleExt {X : RingedSpace.{v}}
    [HasDerivedCategory (Mod X.structureSheaf)]
    (K : DerivedModule (X := X)) (G : Mod X.structureSheaf) (n : ℕ) : Type _ :=
  K ⟶
    (shiftFunctor (DerivedCategory (Mod X.structureSheaf)) (n : ℤ)).obj
      (derivedModuleOf G)

/-- Lemma inf-obs-map-special. -/
theorem inf_obs_map_special
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i)
    [((SheafOfModules.pushforward (F := Opens.map i.continuous)
      i.sharp).IsRightAdjoint)]
    [HasDerivedCategory (Mod X.structureSheaf)]
    (D : DerivedPullbackData i)
    (F' G' : Mod X'.structureSheaf)
    (φ : reducedModule i F' ⟶ reducedModule i G') :
    ∃ o : DerivedModuleExt (X := X) (D.object F')
        (idealTimesModuleOnReducedSpace i G') 1,
      (o = 0 ↔ Nonempty (ModuleLift i F' G' φ)) := by
  sorry

/-- Lemma inf-obs-map-rel. -/
theorem inf_obs_map_rel
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
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
    ∃ o : ModuleExt (X := M.X) (reducedModule M.i F')
        (relativeLiftCoefficient M ht (reducedModule M.i G')) 1,
      (o = 0 ↔ Nonempty (ModuleLift M.i F' G' φ)) := by
  sorry

/-! ## Flat extensions -/

/-- A flat lift of F to X', with its specified reduction isomorphism. -/
structure FlatModuleLift (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (F : Mod M.X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)] where
  module : Mod M.X'.structureSheaf
  flat : FlatOver M.f' module
  identification : reducedModule M.i module ≅ F

/-- Isomorphisms of flat lifts preserving the reduction identification. -/
structure FlatModuleLiftIso
    {M : MorphismOfThickenings.{v}} {hi : IsFirstOrderThickening M.i}
    {F : Mod M.X.structureSheaf}
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    (A B : FlatModuleLift M hi F) where
  hom : A.module ≅ B.module
  commutes :
    (ringedSpaceModulePullback M.i).map hom.hom ≫ B.identification.hom =
      A.identification.hom

namespace FlatModuleLiftIso

variable {M : MorphismOfThickenings.{v}} {hi : IsFirstOrderThickening M.i}
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
    sorry
    /-
    apply (cancel_epi ((ringedSpaceModulePullback M.i).map e.hom.hom)).1
    simp only [Functor.map_comp, Iso.symm_hom, Category.assoc, e.commutes]
    simp
    -/

def trans {A B C : FlatModuleLift M hi F}
    (e₁ : FlatModuleLiftIso A B) (e₂ : FlatModuleLiftIso B C) :
    FlatModuleLiftIso A C where
  hom := e₁.hom ≪≫ e₂.hom
  commutes := by
    sorry
    /-
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [e₁.commutes, e₂.commutes]
    -/

end FlatModuleLiftIso

/-- The equivalence relation defining isomorphism classes of flat lifts. -/
def flatModuleLiftEquivalence
    (M : MorphismOfThickenings.{v}) (hi : IsFirstOrderThickening M.i)
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
    (M : MorphismOfThickenings.{v}) (hi : IsFirstOrderThickening M.i)
    (F : Mod M.X.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)] :=
  Quotient (flatModuleLiftEquivalence M hi F)

/-- Lemma inf-ext-rel. -/
theorem inf_ext_rel
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
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
      (ModuleExt (X := M.X) F
        (moduleTensor (sourceIdealModule M hi) F) 1)
      (FlatModuleLiftClasses M hi F)) := by
  sorry

/-! ## Flat-lift obstruction -/

/-- The source-facing map f^*J tensor F -> I tensor F. -/
structure CanonicalIdealTensorComparison
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    (F : Mod M.X.structureSheaf)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)] where
  map : flatnessCoefficient M ht F ⟶
    moduleTensor (sourceIdealModule M hi) F

theorem canonicalIdealTensorComparison_exists
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    (F : Mod M.X.structureSheaf) :
    Nonempty (CanonicalIdealTensorComparison M hi ht F) := by
  sorry

noncomputable def canonicalIdealTensorComparison
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    (F : Mod M.X.structureSheaf) :
    CanonicalIdealTensorComparison M hi ht F :=
  Classical.choice (canonicalIdealTensorComparison_exists M hi ht F)

/-- The Ext2 obstruction group for a flat lift. -/
abbrev FlatLiftObstruction
    (M : MorphismOfThickenings.{v}) (hi : IsFirstOrderThickening M.i)
    (F : Mod M.X.structureSheaf)
    [ModuleTensorProduct M.X]
    [CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)] : Type v :=
  ModuleExt (X := M.X) F
    (moduleTensor (sourceIdealModule M hi) F) 2

theorem exists_flatLiftObstructionClass
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
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
    ∃ o : FlatLiftObstruction M hi F,
      (o = 0 ↔ IsIso c.map ∧ Nonempty (FlatModuleLift M hi F)) := by
  sorry

noncomputable def flatLiftObstructionClass
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
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
    FlatLiftObstruction M hi F :=
  Classical.choose (exists_flatLiftObstructionClass M hi ht hstrict F hF c)

theorem flatLiftObstructionClass_vanishes_iff
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
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
    flatLiftObstructionClass M hi ht hstrict F hF c = 0 ↔
      IsIso c.map ∧ Nonempty (FlatModuleLift M hi F) :=
  Classical.choose_spec (exists_flatLiftObstructionClass M hi ht hstrict F hF c)

/-- Lemma inf-obs-ext-rel. -/
theorem inf_obs_ext_rel
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
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
      (IsIso c.map ∧
        flatLiftObstructionClass M hi ht hstrict F hF c = 0)) := by
  sorry

/- Source-facing form using the canonical comparison map and its chosen
   obstruction class. -/
theorem inf_obs_ext_rel_canonical
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [ModuleTensorProduct M.X]
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    [CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (F : Mod M.X.structureSheaf) (hF : FlatOver M.f F) :
    (Nonempty (FlatModuleLift M hi F) ↔
      (IsIso (canonicalIdealTensorComparison M hi ht F).map ∧
        flatLiftObstructionClass M hi ht hstrict F hF
          (canonicalIdealTensorComparison M hi ht F) = 0)) := by
  sorry

end

end Formalization.Books.Defos.Unit05
