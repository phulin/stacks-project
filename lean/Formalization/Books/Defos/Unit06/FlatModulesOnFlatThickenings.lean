import Formalization.Books.Defos.Unit05.InfinitesimalDeformations
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Deformation Theory, Chapter 6: Application to flat modules on flat thickenings

This file formalizes `books/defos.tex:1580--1700`.  The ringed-space
thickening, strictness, flatness, lift, Ext, torsor, and short-exact-complex
interfaces are reused from Chapters 3--5.
-/

namespace Formalization.Books.Defos.Unit06

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Defos.Unit02
open Formalization.Books.Defos.Unit03
open Formalization.Books.Defos.Unit03.MorphismOfThickenings
open Formalization.Books.Defos.Unit04
open Formalization.Books.Defos.Unit05
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## The flat-thickening diagram -/

abbrev FlatMorphism {X S : RingedSpace.{v}} (f : RingedSpaceHom X S) : Prop :=
  Formalization.Books.Modules.Unit20.flat f

/- The two rows of the source diagram are represented by the existing
   `FirstOrderThickeningComplex` interface.  The extra maps below record the
   three compatible morphisms to the lower row. -/
structure FlatThickeningShortExactData where
  X : RingedSpace.{v}
  S : RingedSpace.{v}
  f : RingedSpaceHom X S
  top : FirstOrderThickeningComplex X
  base : FirstOrderThickeningComplex S
  f₁' : RingedSpaceHom top.X₁ base.X₁
  f₂' : RingedSpaceHom top.X₂ base.X₂
  f₃' : RingedSpaceHom top.X₃ base.X₃
  square₁ : RingedSpaceHom.comp f base.i₁ =
    RingedSpaceHom.comp top.i₁ f₁'
  square₂ : RingedSpaceHom.comp f base.i₂ =
    RingedSpaceHom.comp top.i₂ f₂'
  square₃ : RingedSpaceHom.comp f base.i₃ =
    RingedSpaceHom.comp top.i₃ f₃'

namespace FlatThickeningShortExactData

abbrev morphism₁ (D : FlatThickeningShortExactData) : MorphismOfThickenings where
  X := D.X
  X' := D.top.X₁
  S := D.S
  S' := D.base.X₁
  i := D.top.i₁
  f := D.f
  f' := D.f₁'
  t := D.base.i₁
  commutes := D.square₁
  i_isThickening := D.top.firstOrder₁.toIsThickening
  t_isThickening := D.base.firstOrder₁.toIsThickening

abbrev morphism₂ (D : FlatThickeningShortExactData) : MorphismOfThickenings where
  X := D.X
  X' := D.top.X₂
  S := D.S
  S' := D.base.X₂
  i := D.top.i₂
  f := D.f
  f' := D.f₂'
  t := D.base.i₂
  commutes := D.square₂
  i_isThickening := D.top.firstOrder₂.toIsThickening
  t_isThickening := D.base.firstOrder₂.toIsThickening

abbrev morphism₃ (D : FlatThickeningShortExactData) : MorphismOfThickenings where
  X := D.X
  X' := D.top.X₃
  S := D.S
  S' := D.base.X₃
  i := D.top.i₃
  f := D.f
  f' := D.f₃'
  t := D.base.i₃
  commutes := D.square₃
  i_isThickening := D.top.firstOrder₃.toIsThickening
  t_isThickening := D.base.firstOrder₃.toIsThickening

end FlatThickeningShortExactData

/- The strictness fields quantify over the explicit right-adjoint instances
   required by the existing module pullback API.  This keeps the mathematical
   hypotheses independent of which instance is installed by a client. -/
structure FlatThickeningShortExactSituation extends FlatThickeningShortExactData where
  top_shortExact : toFlatThickeningShortExactData.top.IsShortExact
  base_shortExact : toFlatThickeningShortExactData.base.IsShortExact
  strict₁ : ∀ (h : ((SheafOfModules.pushforward
      (F := Opens.map f₁'.continuous) f₁'.sharp).IsRightAdjoint)),
    @MorphismOfThickenings.IsStrict
      (FlatThickeningShortExactData.morphism₁ toFlatThickeningShortExactData) h
  strict₂ : ∀ (h : ((SheafOfModules.pushforward
      (F := Opens.map f₂'.continuous) f₂'.sharp).IsRightAdjoint)),
    @MorphismOfThickenings.IsStrict
      (FlatThickeningShortExactData.morphism₂ toFlatThickeningShortExactData) h
  strict₃ : ∀ (h : ((SheafOfModules.pushforward
      (F := Opens.map f₃'.continuous) f₃'.sharp).IsRightAdjoint)),
    @MorphismOfThickenings.IsStrict
      (FlatThickeningShortExactData.morphism₃ toFlatThickeningShortExactData) h
  flat₁ : FlatMorphism f₁'
  flat₂ : FlatMorphism f₂'
  flat₃ : FlatMorphism f₃'

namespace FlatThickeningShortExactSituation

abbrev morphism₁ (D : FlatThickeningShortExactSituation.{v}) :=
  FlatThickeningShortExactData.morphism₁ D.toFlatThickeningShortExactData

abbrev morphism₂ (D : FlatThickeningShortExactSituation.{v}) :=
  FlatThickeningShortExactData.morphism₂ D.toFlatThickeningShortExactData

abbrev morphism₃ (D : FlatThickeningShortExactSituation.{v}) :=
  FlatThickeningShortExactData.morphism₃ D.toFlatThickeningShortExactData

noncomputable def canonicalSplitting
    (D : FlatThickeningShortExactSituation.{v}) :
    ThickeningTrivialization D.top.i₁ D.top.firstOrder₁ :=
  FirstOrderThickeningComplex.canonicalTrivialization D.top
    (Classical.choose D.top_shortExact)

end FlatThickeningShortExactSituation

/- The strict-flat hypothesis identifies the source and base square-zero
   ideals.  The canonical map is the induced ideal map already constructed in
   Chapter 3; this is the precise module-category form of `I = f^* J`. -/
theorem strict_flat_sourceIdeal_isIso
    (M : MorphismOfThickenings.{v})
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (hf' : FlatMorphism M.f') :
    IsIso (inducedIdealMap M) := by
  sorry

/-! ## The obstruction, torsor, and automorphism statements -/

theorem exists_flatModuleObstructionClass
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
    [hExt : CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (hf' : FlatMorphism M.f')
    (F : Mod M.X.structureSheaf)
    (hF : FlatOver M.f F) :
    ∃ o : ModuleExt (X := M.X) F
        (relativeLiftCoefficient M ht F) 2,
      (o = 0 ↔ Nonempty (FlatModuleLift M hi F)) := by
  sorry

noncomputable def flatModuleObstructionClass
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
    [hExt : CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (hf' : FlatMorphism M.f')
    (F : Mod M.X.structureSheaf)
    (hF : FlatOver M.f F) :
    ModuleExt (X := M.X) F (relativeLiftCoefficient M ht F) 2 :=
  Classical.choose (exists_flatModuleObstructionClass M hi ht hstrict hf' F hF)

theorem flatModuleObstructionClass_vanishes_iff
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
    [hExt : CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (hf' : FlatMorphism M.f')
    (F : Mod M.X.structureSheaf)
    (hF : FlatOver M.f F) :
    flatModuleObstructionClass M hi ht hstrict hf' F hF = 0 ↔
      Nonempty (FlatModuleLift M hi F) :=
  Classical.choose_spec (exists_flatModuleObstructionClass M hi ht hstrict hf' F hF)

theorem flatModuleLiftClasses_is_principalHomogeneousSpace
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
    [hExt : CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (hf' : FlatMorphism M.f')
    (F : Mod M.X.structureSheaf)
    (hF : FlatOver M.f F)
    (hLift : Nonempty (FlatModuleLift M hi F)) :
    Nonempty (PrincipalHomogeneousSpace
      (ModuleExt (X := M.X) F (relativeLiftCoefficient M ht F) 1)
      (FlatModuleLiftClasses M hi F)) := by
  sorry

abbrev FlatModuleLiftAutomorphisms
    {M : MorphismOfThickenings.{v}} {hi : IsFirstOrderThickening M.i}
    {F : Mod M.X.structureSheaf}
    [((SheafOfModules.pushforward (F := Opens.map M.i.continuous)
      M.i.sharp).IsRightAdjoint)]
    (A : FlatModuleLift M hi F) :=
  FlatModuleLiftIso A A

theorem flatModuleLiftAutomorphisms_equiv_ext_zero
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
    [hExt : CategoryTheory.HasExt.{v} (Mod M.X.structureSheaf)]
    (hstrict : MorphismOfThickenings.IsStrict M)
    (hf' : FlatMorphism M.f')
    (F : Mod M.X.structureSheaf)
    (hF : FlatOver M.f F)
    (A : FlatModuleLift M hi F) :
    Nonempty (FlatModuleLiftAutomorphisms A ≃
      ModuleExt (X := M.X) F (relativeLiftCoefficient M ht F) 0) := by
  sorry

/-! ## The short exact coefficient sequence and its boundary -/

noncomputable abbrev coefficient₁
  (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf) : Mod D.X.structureSheaf :=
  relativeLiftCoefficient D.morphism₁ D.base.firstOrder₁ F

noncomputable abbrev coefficient₂
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf) : Mod D.X.structureSheaf :=
  relativeLiftCoefficient D.morphism₂ D.base.firstOrder₂ F

noncomputable abbrev coefficient₃
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf) : Mod D.X.structureSheaf :=
  relativeLiftCoefficient D.morphism₃ D.base.firstOrder₃ F

structure FlatThickeningCoefficientSequence
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf) where
  k₃₂ : coefficient₃ D F ⟶ coefficient₂ D F
  k₂₁ : coefficient₂ D F ⟶ coefficient₁ D F
  zero : k₃₂ ≫ k₂₁ = 0
  shortExact : (ShortComplex.mk k₃₂ k₂₁ zero).ShortExact

namespace FlatThickeningCoefficientSequence

abbrev K₃
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf)
    (C : FlatThickeningCoefficientSequence D F) :=
  coefficient₃ D F

abbrev K₂
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf)
    (C : FlatThickeningCoefficientSequence D F) :=
  coefficient₂ D F

abbrev K₁
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf)
    (C : FlatThickeningCoefficientSequence D F) :=
  coefficient₁ D F

noncomputable def shortComplex
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf)
    (C : FlatThickeningCoefficientSequence D F) :
    ShortComplex (Mod D.X.structureSheaf) :=
  ShortComplex.mk C.k₃₂ C.k₂₁ C.zero

end FlatThickeningCoefficientSequence

theorem flatThickeningCoefficientSequence_exists
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf)
    (hF : FlatOver D.f F) :
    Nonempty (FlatThickeningCoefficientSequence D F) := by
  sorry

noncomputable def flatThickeningCoefficientSequence
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    (F : Mod D.X.structureSheaf)
    (hF : FlatOver D.f F) :
    FlatThickeningCoefficientSequence D F :=
  Classical.choice (flatThickeningCoefficientSequence_exists D F hF)

noncomputable def moduleExtBoundary
    {X : RingedSpace.{v}}
    [hExt : CategoryTheory.HasExt.{v} (Mod X.structureSheaf)]
    (F : Mod X.structureSheaf)
    (S : ShortComplex (Mod X.structureSheaf))
    (hS : S.ShortExact) :
    ModuleExt (X := X) F S.X₃ 1 → ModuleExt (X := X) F S.X₁ 2 :=
  fun ξ => CategoryTheory.Abelian.Ext.comp ξ hS.extClass (by decide)

noncomputable def flatThickeningCoefficientBoundary
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    [hExt : CategoryTheory.HasExt.{v} (Mod D.X.structureSheaf)]
    (F : Mod D.X.structureSheaf)
    (hF : FlatOver D.f F) :
    ModuleExt (X := D.X) F (coefficient₁ D F) 1 →
      ModuleExt (X := D.X) F (coefficient₃ D F) 2 :=
  moduleExtBoundary F
    (FlatThickeningCoefficientSequence.shortComplex D F
      (flatThickeningCoefficientSequence D F hF))
    (flatThickeningCoefficientSequence D F hF).shortExact

/-! ## The comparison assertion for a short exact sequence -/

noncomputable abbrev restrictedModule
    (D : FlatThickeningShortExactSituation.{v})
    [((SheafOfModules.pushforward (F := Opens.map D.top.i₂.continuous)
      D.top.i₂.sharp).IsRightAdjoint)]
    (F₂' : Mod D.top.X₂.structureSheaf) : Mod D.X.structureSheaf :=
  reducedModule D.morphism₂.i F₂'

theorem restrictedModule_flatOver
    (D : FlatThickeningShortExactSituation.{v})
    [((SheafOfModules.pushforward (F := Opens.map D.top.i₂.continuous)
      D.top.i₂.sharp).IsRightAdjoint)]
    (F₂' : Mod D.top.X₂.structureSheaf)
    (hF₂' : FlatOver D.f₂' F₂') :
    FlatOver D.f (restrictedModule D F₂') := by
  sorry

structure FlatThickeningComparison
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.top.i₁.continuous)
      D.top.i₁.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.top.i₂.continuous)
      D.top.i₂.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.top.h₁₂.continuous)
      D.top.h₁₂.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward
        (F := Opens.map (D.canonicalSplitting.projection).continuous)
        D.canonicalSplitting.projection.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.f₁'.continuous)
      D.f₁'.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.f₂'.continuous)
      D.f₂'.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.f₃'.continuous)
      D.f₃'.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.top.i₃.continuous)
      D.top.i₃.sharp).IsRightAdjoint)]
    [hExt : CategoryTheory.HasExt.{v} (Mod D.X.structureSheaf)]
    (F₂' : Mod D.top.X₂.structureSheaf)
    (hF₂' : FlatOver D.f₂' F₂') where
  piModule : Mod D.top.X₁.structureSheaf :=
    (ringedSpaceModulePullback D.canonicalSplitting.projection).obj
      (restrictedModule D F₂')
  hModule : Mod D.top.X₁.structureSheaf :=
    (ringedSpaceModulePullback D.top.h₁₂).obj F₂'
  piFlat : FlatOver D.f₁' piModule
  hFlat : FlatOver D.f₁' hModule
  piRestricts : Nonempty (reducedModule D.morphism₁.i piModule ≅
    restrictedModule D F₂')
  hRestricts : Nonempty (reducedModule D.morphism₁.i hModule ≅
    restrictedModule D F₂')
  difference : ModuleExt (X := D.X) (restrictedModule D F₂')
      (coefficient₁ D (restrictedModule D F₂')) 1
  boundary_eq_obstruction :
    flatThickeningCoefficientBoundary D (restrictedModule D F₂')
        (restrictedModule_flatOver D F₂' hF₂')
        difference =
      flatModuleObstructionClass D.morphism₃ D.top.firstOrder₃
        D.base.firstOrder₃ (D.strict₃ _) D.flat₃
        (restrictedModule D F₂')
        (restrictedModule_flatOver D F₂' hF₂')

theorem flatThickening_shortExact_comparison
    (D : FlatThickeningShortExactSituation.{v})
    [ModuleTensorProduct D.X]
    [((SheafOfModules.pushforward (F := Opens.map D.f.continuous)
      D.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.top.i₁.continuous)
      D.top.i₁.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.top.i₂.continuous)
      D.top.i₂.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.top.h₁₂.continuous)
      D.top.h₁₂.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward
        (F := Opens.map (D.canonicalSplitting.projection).continuous)
        D.canonicalSplitting.projection.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.f₁'.continuous)
      D.f₁'.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.f₂'.continuous)
      D.f₂'.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.f₃'.continuous)
      D.f₃'.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map D.top.i₃.continuous)
      D.top.i₃.sharp).IsRightAdjoint)]
    [hExt : CategoryTheory.HasExt.{v} (Mod D.X.structureSheaf)]
    (F₂' : Mod D.top.X₂.structureSheaf)
    (hF₂' : FlatOver D.f₂' F₂') :
    Nonempty (FlatThickeningComparison D F₂' hF₂') := by
  sorry

end

end Formalization.Books.Defos.Unit06
