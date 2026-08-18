import Formalization.Books.Modules.Unit06.ClosedImmersions
import Formalization.Books.Modules.Unit09.FiniteType
import Formalization.Books.Modules.Unit10.QuasiCoherent
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Sheaves.Unit22.ClosedImmersions
import Formalization.Books.Sheaves.Unit22.RingedSpaceModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Sheaves of Modules, Chapter 13: Closed immersions of ringed spaces

The canonical sheaf-module pushforward and the canonical closed-subspace
sheaf restriction are used throughout. The source's ideal is represented by
the kernel of the map from the unit module to the pushed-forward unit module.
The supported-sections construction is packaged by the largest supported
subobject and the corresponding right-adjoint interface.
-/

namespace Formalization.Books.Modules.Unit13

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Modules.Unit04
open Formalization.Books.Modules.Unit05
open Formalization.Books.Modules.Unit08
open Formalization.Books.Modules.Unit09
open Formalization.Books.Modules.Unit10
open Formalization.Books.Categories.Unit23
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## Closed immersions of ringed spaces -/

/- The kernel is taken in the category of modules over the target structure
   sheaf. `unitToPushforwardObjUnit` is Mathlib's canonical conversion of a
   morphism of sheaves of rings to the corresponding module morphism. -/

/-- The ideal sheaf cutting out a morphism of ringed spaces. -/
noncomputable def closedImmersionIdeal {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : Mod Y.structureSheaf :=
  kernel (SheafOfModules.unitToPushforwardObjUnit f.sharp)

/-- The inclusion of the ideal sheaf into the target structure sheaf. -/
noncomputable def closedImmersionIdealInclusion {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    closedImmersionIdeal f ⟶ SheafOfModules.unit Y.structureSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.sharp)

/- The three conditions in the source definition are kept as fields so that
   later statements can use the topological, sheaf-theoretic, and local
   generation hypotheses independently. -/

/-- A closed immersion of ringed spaces in the sense of the source. -/
structure IsClosedImmersion {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : Prop where
  isClosedEmbedding : IsClosedEmbedding f.continuous
  structureSheaf_epi : Epi f.sharp
  ideal_locallyGenerated : locallyGenerated (closedImmersionIdeal f)

/-! ## Pushforward of quasi-coherent modules -/

/-- A module is locally a cokernel of quasi-coherent modules. -/
def IsLocallyCokernelOfQuasiCoherentModules {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ A B : Mod (ringedOpenSubspace X U).structureSheaf,
      IsQuasiCoherent A ∧ IsQuasiCoherent B ∧
        ∃ φ : A ⟶ B,
          Nonempty (cokernel φ ≅
            (openModuleRestrictionFunctor X U).obj F)

/-- Pushforward along a closed immersion is locally a cokernel of
quasi-coherent modules when the source module is quasi-coherent. -/
theorem closedImmersion_pushforward_isLocallyCokernelOfQuasiCoherentModules
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hf : IsClosedImmersion f) (F : Mod X.structureSheaf)
    (hF : IsQuasiCoherent F) :
    IsLocallyCokernelOfQuasiCoherentModules
      ((ringedSpaceModulePushforward f).obj F) := by
  sorry

/-! ## Finite type -/

/-- Pushforward along a closed embedding of spaces with a surjective
structure-sheaf map reflects finite type. -/
theorem closedImmersion_pushforward_finiteType_iff
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hclosed : IsClosedEmbedding f.continuous) (hepi : Epi f.sharp)
    (F : Mod X.structureSheaf) :
    finiteType ((ringedSpaceModulePushforward f).obj F) ↔ finiteType F := by
  sorry

/-! ## The module-category equivalence -/

/- The sectionwise formulation is a usable module-theoretic spelling of
   `I G = 0`: every local section of the ideal acts by zero on every local
   section of `G`. -/

/-- A sheaf of modules is annihilated by a submodule of the structure sheaf. -/
def sheafModuleAnnihilatedBy {X : RingedSpace.{v}}
    {I G : Mod X.structureSheaf}
    (ι : I ⟶ SheafOfModules.unit X.structureSheaf) : Prop :=
  ∀ U : Opens X.carrier,
    ∀ i : (I.val.obj (op U)), ∀ g : (G.val.obj (op U)),
      (let a : X.structureSheaf.obj.obj (op U) :=
        (ι.val.app (op U)).hom i
       a • g) = 0

/-- The essential-image predicate for a closed-immersion pushforward. -/
def IsInClosedImmersionPushforwardEssentialImage
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) : Prop :=
  sheafModuleAnnihilatedBy (G := G)
    (closedImmersionIdealInclusion f)

/-- The module pushforward along a closed immersion is exact. -/
theorem closedImmersion_pushforward_isExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hclosed : IsClosedEmbedding f.continuous) (hepi : Epi f.sharp) :
    IsExact (ringedSpaceModulePushforward f) := by
  sorry

/-- The module pushforward along a closed immersion is fully faithful. -/
theorem closedImmersion_pushforward_fullyFaithful
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hclosed : IsClosedEmbedding f.continuous) (hepi : Epi f.sharp) :
    Nonempty (ringedSpaceModulePushforward f).FullyFaithful := by
  sorry

/-- The essential image of a closed-immersion pushforward consists precisely
of modules annihilated by the ideal sheaf. -/
theorem closedImmersion_pushforward_essentialImage
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hclosed : IsClosedEmbedding f.continuous) (hepi : Epi f.sharp)
    (G : Mod Y.structureSheaf) :
    (∃ F, Nonempty ((ringedSpaceModulePushforward f).obj F ≅ G)) ↔
      IsInClosedImmersionPushforwardEssentialImage f G := by
  sorry

/-! ## Sections with support in a closed subset -/

/-- The ringed space on a closed subspace with the restricted structure sheaf. -/
noncomputable def ringedClosedSubspace (X : RingedSpace.{v}) (Z : Set X) :
    RingedSpace.{v} where
  carrier := Formalization.Books.Sheaves.Unit22.closedSubspace Z
  structureSheaf :=
    (TopCat.Sheaf.pullback RingCat
      (Formalization.Books.Sheaves.Unit22.closedInclusion Z)).obj X.structureSheaf

/-- The canonical morphism from the ringed closed subspace to the ambient
ringed space. -/
noncomputable def ringedClosedInclusion (X : RingedSpace.{v}) (Z : Set X) :
    RingedSpaceHom (ringedClosedSubspace X Z) X where
  continuous := Formalization.Books.Sheaves.Unit22.closedInclusion Z
  sharp :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
      (Formalization.Books.Sheaves.Unit22.closedInclusion Z)).unit.app X.structureSheaf

/-- A module section is supported in a closed subset. -/
def moduleSectionSupportedInClosed {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier)
    (s : F.val.obj (op U)) : Prop :=
  sectionSupport U s ⊆
    Formalization.Books.Modules.Unit06.closedSubsetInOpen Z U

/-- The sections of a module supported in a closed subset. -/
def moduleSectionsWithSupportInClosed {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier) :
    Set (F.val.obj (op U)) :=
  {s | moduleSectionSupportedInClosed Z U s}

/- The source observes that these sections are closed under the module
   operations.  The closure proof is deferred with the other proposition
   proofs, while the sectionwise submodule interface is made explicit. -/

/-- The sections supported in `Z` form a submodule on every open. -/
theorem moduleSectionsWithSupportInClosed_isSubmodule
    {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier) :
    ∃ S : Submodule (X.structureSheaf.obj.obj (op U))
        (F.val.obj (op U)),
      S.carrier = moduleSectionsWithSupportInClosed Z U := by
  sorry

/- The sectionwise module in the source is represented by the canonical
   submodule selected from the preceding closure statement. -/

/-- The submodule of sections supported in `Z` on an open subset. -/
noncomputable def moduleSectionsWithSupportInClosedSubmodule
    {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier) :
    Submodule (X.structureSheaf.obj.obj (op U)) (F.val.obj (op U)) :=
  Classical.choose
    (moduleSectionsWithSupportInClosed_isSubmodule (F := F) Z U)

/-- The selected supported-section submodule has the source's carrier. -/
theorem moduleSectionsWithSupportInClosedSubmodule_carrier
    {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier) :
    (moduleSectionsWithSupportInClosedSubmodule (F := F) Z U).carrier =
      moduleSectionsWithSupportInClosed (F := F) Z U :=
  Classical.choose_spec
    (moduleSectionsWithSupportInClosed_isSubmodule (F := F) Z U)

/-- A module subobject contains a section when that section lifts to it. -/
def moduleSubsheafContainsSection {X : RingedSpace.{v}}
    {F : Mod X.structureSheaf} (P : Subobject F) (U : Opens X.carrier)
    (s : F.val.obj (op U)) : Prop :=
  ∃ t : ((P : Mod X.structureSheaf).val.obj (op U)),
    P.arrow.val.app (op U) t = s

/-- Support containment for a sheaf of modules. -/
def moduleSupportContainedIn {X : RingedSpace.{v}} (Z : Set X)
    (F : Mod X.structureSheaf) : Prop :=
  moduleSupport F ⊆ Z

/-- There is a largest module subsheaf whose support is contained in `Z`. -/
theorem exists_closedSupportModuleSubsheaf {X : RingedSpace.{v}} (Z : Set X)
    (_hZ : IsClosed Z) (F : Mod X.structureSheaf) :
    ∃ P : Subobject F,
      moduleSupportContainedIn Z (P : Mod X.structureSheaf) ∧
        ∀ Q : Subobject F,
          moduleSupportContainedIn Z (Q : Mod X.structureSheaf) → Q ≤ P := by
  sorry

/-- The canonical largest module subsheaf supported in `Z`. -/
noncomputable def closedSupportModuleSubsheaf {X : RingedSpace.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Mod X.structureSheaf) : Subobject F :=
  Classical.choose (exists_closedSupportModuleSubsheaf Z hZ F)

/-- The canonical supported module subsheaf has support in `Z`. -/
theorem closedSupportModuleSubsheaf_supportContainedIn
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) :
    moduleSupportContainedIn Z
      (closedSupportModuleSubsheaf Z hZ F : Mod X.structureSheaf) := by
  exact (Classical.choose_spec (exists_closedSupportModuleSubsheaf Z hZ F)).1

/-- The canonical supported module subsheaf is largest among supported
subsheaves. -/
theorem closedSupportModuleSubsheaf_isLargest
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) (Q : Subobject F)
    (hQ : moduleSupportContainedIn Z (Q : Mod X.structureSheaf)) :
    Q ≤ closedSupportModuleSubsheaf Z hZ F := by
  exact (Classical.choose_spec (exists_closedSupportModuleSubsheaf Z hZ F)).2 Q hQ

/-- A section belongs to the canonical supported submodule exactly when it is
supported in `Z`. -/
theorem closedSupportModuleSubsheaf_section_iff
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) (U : Opens X.carrier)
    (s : F.val.obj (op U)) :
    moduleSubsheafContainsSection
      (closedSupportModuleSubsheaf Z hZ F) U s ↔
      s ∈ moduleSectionsWithSupportInClosed Z U := by
  sorry

/-! ## The supported-sections right adjoint -/

/-- The module-valued supported-sections functor exists as the right adjoint
to closed direct image. -/
theorem exists_moduleSectionsWithSupportFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    ∃ H : Mod X.structureSheaf ⥤
        Mod (ringedClosedSubspace X Z).structureSheaf,
      Nonempty (ringedSpaceModulePushforward (ringedClosedInclusion X Z) ⊣ H) ∧
        ∀ F : Mod X.structureSheaf,
          Nonempty ((ringedSpaceModulePushforward
            (ringedClosedInclusion X Z)).obj (H.obj F) ≅
            (closedSupportModuleSubsheaf Z hZ F : Mod X.structureSheaf)) := by
  sorry

/-- The sheaf of modules of sections supported in `Z`, viewed on the closed
subspace. -/
noncomputable def moduleSectionsWithSupportFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Mod X.structureSheaf ⥤ Mod (ringedClosedSubspace X Z).structureSheaf :=
  Classical.choose (exists_moduleSectionsWithSupportFunctor X Z hZ)

/-- The chosen supported-sections functor is right adjoint to closed direct
image. -/
noncomputable def moduleSectionsWithSupportFunctor_adjunction
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    ringedSpaceModulePushforward (ringedClosedInclusion X Z) ⊣
      moduleSectionsWithSupportFunctor X Z hZ :=
  Classical.choice
    (Classical.choose_spec (exists_moduleSectionsWithSupportFunctor X Z hZ)).1

/-- The chosen right adjoint realizes the largest supported submodule. -/
theorem moduleSectionsWithSupportFunctor_obj_iso
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) :
    Nonempty ((ringedSpaceModulePushforward
      (ringedClosedInclusion X Z)).obj
        ((moduleSectionsWithSupportFunctor X Z hZ).obj F) ≅
      (closedSupportModuleSubsheaf Z hZ F : Mod X.structureSheaf)) := by
  exact (Classical.choose_spec
    (exists_moduleSectionsWithSupportFunctor X Z hZ)).2 F

/-- The supported-sections functor is left exact. -/
theorem moduleSectionsWithSupportFunctor_isLeftExact
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    IsLeftExact (moduleSectionsWithSupportFunctor X Z hZ) := by
  sorry

/-- The source's warning that supported sections are not exact in general. -/
def AllModuleSupportedSectionsFunctorsExact : Prop :=
  ∀ (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z),
    IsExact (moduleSectionsWithSupportFunctor X Z hZ)

theorem not_allModuleSupportedSectionsFunctorsExact :
    ¬ AllModuleSupportedSectionsFunctorsExact := by
  sorry

end

end Formalization.Books.Modules.Unit13
