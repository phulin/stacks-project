import Formalization.Books.Modules.Unit13.ClosedImmersions
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Homeomorph.Defs

/-!
# Deformation Theory, Chapter 3: Thickenings of ringed spaces

This file formalizes the source section `books/defos.tex:479-574`.  The
ringed-space and sheaf-module constructions are the canonical interfaces from
the Sheaves and Modules chapters.  In particular, the ideal of a morphism is
the kernel module already used for closed immersions, and epimorphisms are the
categorical form of surjective maps of sheaves.
-/

namespace Formalization.Books.Defos.Unit03

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Modules.Unit13

universe v

noncomputable section

/-! ## Locally nilpotent ideals and thickenings -/

/- A sheaf of ideals is represented by its underlying module together with its
   monomorphism into the unit module.  This is the source-facing wrapper around
   the canonical submodule/kernel interfaces. -/

/-- A sheaf of ideals in the structure sheaf of a ringed space. -/
structure IdealSheaf (X : RingedSpace.{v}) where
  carrier : Mod X.structureSheaf
  inclusion : carrier ⟶ SheafOfModules.unit X.structureSheaf
  inclusion_mono : Mono inclusion

/-- A section of an ideal sheaf is locally nilpotent. -/
def IsLocallyNilpotentIdeal {X : RingedSpace.{v}} (I : IdealSheaf X) : Prop :=
  ∀ (U : Opens X.carrier) (s : I.carrier.val.obj (op U)) (x : X),
    x ∈ U →
      ∃ (V : Opens X.carrier) (hVU : V ≤ U), x ∈ V ∧
        ∃ n : ℕ,
          (let a : X.structureSheaf.obj.obj (op V) :=
            (I.inclusion.val.app (op V)).hom
              ((I.carrier.val.map (homOfLE hVU).op) s)
           a ^ n = 0)

/-- The square of an ideal sheaf is zero. -/
def IsSquareZeroIdeal {X : RingedSpace.{v}} (I : IdealSheaf X) : Prop :=
  ∀ (U : Opens X.carrier) (a b : I.carrier.val.obj (op U)),
    (let a' : X.structureSheaf.obj.obj (op U) :=
      (I.inclusion.val.app (op U)).hom a
     let b' : X.structureSheaf.obj.obj (op U) :=
      (I.inclusion.val.app (op U)).hom b
     a' * b' = 0)

/-- The ideal sheaf cutting out a morphism of ringed spaces. -/
noncomputable def thickeningIdeal {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') : IdealSheaf X' where
  carrier := closedImmersionIdeal i
  inclusion := closedImmersionIdealInclusion i
  inclusion_mono := by
    change Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.sharp))
    infer_instance

/-- A morphism of ringed spaces is a thickening when its space map is a
homeomorphism, its structure-sheaf map is an epimorphism, and its kernel ideal
is locally nilpotent. -/
structure IsThickening {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') : Prop where
  underlying_homeomorph : IsHomeomorph i.continuous.hom
  structureSheaf_epi : Epi i.sharp
  kernel_locallyNilpotent : IsLocallyNilpotentIdeal (thickeningIdeal i)

/-- A first-order thickening is a thickening whose kernel ideal has square zero. -/
structure IsFirstOrderThickening {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') extends IsThickening i where
  kernel_square_zero : IsSquareZeroIdeal (thickeningIdeal i)

/-! The kernel sequence and the module-category observation -/

/-- The short complex
`0 → Ker(i♯) → 𝒪_{X'} → i_*𝒪_X → 0` attached to a ringed-space morphism. -/
noncomputable def thickeningKernelShortComplex {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') : ShortComplex (Mod X'.structureSheaf) :=
  ShortComplex.mk
    (closedImmersionIdealInclusion i)
    (SheafOfModules.unitToPushforwardObjUnit i.sharp)
    (kernel.condition (SheafOfModules.unitToPushforwardObjUnit i.sharp))

/-- The kernel sequence of a thickening is short exact. -/
theorem thickeningKernelShortComplex_shortExact
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsThickening i) :
    (thickeningKernelShortComplex i).ShortExact := by
  sorry

/-- A module on the thickened space is annihilated by the kernel ideal. -/
abbrev AnnihilatedByThickeningIdeal {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') (G : Mod X'.structureSheaf) : Prop :=
  sheafModuleAnnihilatedBy (G := G) (closedImmersionIdealInclusion i)

/-- The full subcategory of modules annihilated by a thickening ideal. -/
abbrev AnnihilatedByThickeningIdealCategory {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') :=
  ObjectProperty.FullSubcategory
    (AnnihilatedByThickeningIdeal i)

/-- The module category on the reduced space is equivalent to the full
subcategory of modules on the thickening annihilated by its ideal. -/
theorem thickening_module_category_equivalence
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsThickening i) :
    Nonempty
      (Mod X.structureSheaf ≌
        AnnihilatedByThickeningIdealCategory i) := by
  sorry

/-- Objectwise essential-image form of the module-category equivalence. -/
theorem thickening_module_essential_image
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsThickening i) (G : Mod X'.structureSheaf) :
    (∃ F : Mod X.structureSheaf,
      Nonempty ((ringedSpaceModulePushforward i).obj F ≅ G)) ↔
      AnnihilatedByThickeningIdeal i G := by
  sorry

/-- For a first-order thickening, the kernel ideal is an
`𝒪_X`-module, expressed through the module-category equivalence. -/
theorem firstOrderThickening_kernel_is_module
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) :
    ∃ I : Mod X.structureSheaf,
      Nonempty
        ((ringedSpaceModulePushforward i).obj I ≅
          (thickeningIdeal i).carrier) := by
  sorry

/-! ## Morphisms of thickenings -/

/-- The commutative square of ringed spaces whose horizontal maps are
thickenings. -/
structure MorphismOfThickenings where
  X : RingedSpace.{v}
  X' : RingedSpace.{v}
  S : RingedSpace.{v}
  S' : RingedSpace.{v}
  i : RingedSpaceHom X X'
  f : RingedSpaceHom X S
  f' : RingedSpaceHom X' S'
  t : RingedSpaceHom S S'
  commutes : RingedSpaceHom.comp f t = RingedSpaceHom.comp i f'
  i_isThickening : IsThickening i
  t_isThickening : IsThickening t

namespace MorphismOfThickenings

/-- The source kernel ideal `𝓘 = Ker(i♯)`. -/
abbrev sourceIdeal (M : MorphismOfThickenings) : IdealSheaf M.X' :=
  thickeningIdeal M.i

/-- The base kernel ideal `𝓙 = Ker(t♯)`. -/
abbrev baseIdeal (M : MorphismOfThickenings) : IdealSheaf M.S' :=
  thickeningIdeal M.t

/- The sheaf-module pullback below is the canonical `f^*` construction.  The
   right-adjoint instance is an explicit Mathlib hypothesis in the existing
   API.  First expose the map on the pushed-forward ideal (the module form of
   `f'^{-1}𝓙 → 𝓘`), then transpose it along the existing pullback/pushforward
   Hom equivalence. -/

/- The source's map `f'⁻¹𝓙 → 𝓘` is represented as an `f'`-map
   `𝓙 → f'_*𝓘`; extension of scalars gives the displayed map
   `(f')^*𝓙 → 𝓘`. -/
theorem exists_inducedIdealFMap
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    Nonempty
      (M.baseIdeal.carrier ⟶
        (ringedSpaceModulePushforward M.f').obj M.sourceIdeal.carrier) := by
  sorry

/- A chosen source-facing representative of the induced map before extension
   of scalars. -/
noncomputable def inducedIdealFMap
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    M.baseIdeal.carrier ⟶
      (ringedSpaceModulePushforward M.f').obj M.sourceIdeal.carrier :=
  Classical.choice (exists_inducedIdealFMap M)

/- The adjoint-transposed map is the source's map
   `(f')^*𝓙 → 𝓘`. -/
noncomputable def inducedIdealMap
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    (ringedSpaceModulePullback M.f').obj M.baseIdeal.carrier ⟶
      M.sourceIdeal.carrier :=
  (ringedSpaceModuleFMapPullbackHomEquiv M.f' M.baseIdeal.carrier
    M.sourceIdeal.carrier).symm (inducedIdealFMap M)

/-- The induced ideal map exists as a morphism of `𝒪_{X'}`-modules. -/
theorem exists_inducedIdealMap
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    Nonempty
      ((ringedSpaceModulePullback M.f').obj M.baseIdeal.carrier ⟶
        M.sourceIdeal.carrier) :=
  ⟨inducedIdealMap M⟩

/-- A morphism of thickenings is strict when its induced ideal map is an
epimorphism. -/
def IsStrict
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] : Prop :=
  Epi (inducedIdealMap M)

/-- The first-order base ideal is an `𝒪_S`-module. -/
theorem firstOrder_baseIdeal_is_module
    (M : MorphismOfThickenings)
    (ht : IsFirstOrderThickening M.t) :
    ∃ J : Mod M.S.structureSheaf,
      Nonempty
        ((ringedSpaceModulePushforward M.t).obj J ≅ M.baseIdeal.carrier) := by
  sorry

/-- After identifying the base ideal with its `𝒪_S`-module structure, the two
pullbacks in a first-order morphism are canonically identified. -/
theorem firstOrder_pullback_baseIdeal_iso
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    (J : Mod M.S.structureSheaf)
    (hJ : Nonempty
      ((ringedSpaceModulePushforward M.t).obj J ≅ M.baseIdeal.carrier))
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    Nonempty
      ((ringedSpaceModulePullback M.f').obj M.baseIdeal.carrier ≅
        (ringedSpaceModulePushforward M.i).obj
          ((ringedSpaceModulePullback M.f).obj J)) := by
  sorry

/-- In the first-order case the induced ideal map can be expressed as a map
`f^*𝓙 → 𝓘`, after the canonical first-order identification. -/
theorem exists_firstOrder_idealMap
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    (J : Mod M.S.structureSheaf)
    (hJ : Nonempty
      ((ringedSpaceModulePushforward M.t).obj J ≅ M.baseIdeal.carrier))
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)] :
    Nonempty
      ((ringedSpaceModulePushforward M.i).obj
          ((ringedSpaceModulePullback M.f).obj J) ⟶
        M.sourceIdeal.carrier) := by
  sorry

end MorphismOfThickenings

/-! ## Strictness and cartesian squares -/

/-- The strictness criterion: the square of ringed spaces is cartesian exactly
when the induced map of ideals is an epimorphism. -/
theorem strict_iff_cartesian
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    MorphismOfThickenings.IsStrict M ↔
      @IsPullback (RingedSpace.{v}) _ M.X M.X' M.S M.S'
        M.i M.f M.f' M.t := by
  sorry

end

end Formalization.Books.Defos.Unit03
