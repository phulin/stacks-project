import Formalization.Books.Defos.Unit03.ThickeningsOfRingedSpaces
import Formalization.Books.Defos.Unit02.DeformationsOfRings
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Torsor.Basic

/-!
# Deformation Theory, Chapter 4: Modules on first order thickenings of ringed spaces

This file formalizes `books/defos.tex:575-1251`.  Chapter 3 supplies the
ringed-space thickening, kernel ideal, pushforward, and kernel-module APIs.
The source tensor product is exposed through an explicit interface because
the project’s generic ringed spaces use `RingCat`; a tensor of two left
modules needs commutativity or a bimodule convention.
-/

namespace Formalization.Books.Defos.Unit04

open CategoryTheory CategoryTheory.Limits Opposite
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Defos.Unit03
open Formalization.Books.Defos.Unit02

universe u v

noncomputable section

/-! ## The tensor appearing in the source -/

abbrev RingedSpaceModule (X : RingedSpace.{v}) := Mod X.structureSheaf

/-- The tensor product of sheaf modules needed by the source-facing
deformation statements. -/
class ModuleTensorProduct (X : RingedSpace.{v}) where
  tensor : RingedSpaceModule X → RingedSpaceModule X → RingedSpaceModule X
  map : ∀ {I I' F F' : RingedSpaceModule X},
    (I ⟶ I') → (F ⟶ F') →
      @Quiver.Hom (RingedSpaceModule X) (inferInstance : Quiver (RingedSpaceModule X))
        (tensor I F) (tensor I' F')
  map_id : ∀ {I F : RingedSpaceModule X},
    map (𝟙 I) (𝟙 F) = 𝟙 (tensor I F)
  map_comp : ∀ {I₁ I₂ I₃ F₁ F₂ F₃ : RingedSpaceModule X}
    (u₁ : I₁ ⟶ I₂) (u₂ : I₂ ⟶ I₃)
    (v₁ : F₁ ⟶ F₂) (v₂ : F₂ ⟶ F₃),
    map (u₁ ≫ u₂) (v₁ ≫ v₂) = map u₁ v₁ ≫ map u₂ v₂

/-- The source notation `I ⊗_{O_X} F`. -/
abbrev moduleTensor {X : RingedSpace.{v}} [ModuleTensorProduct X]
    (I F : RingedSpaceModule X) : RingedSpaceModule X :=
  ModuleTensorProduct.tensor I F

/-- Functoriality of the source tensor notation. -/
abbrev moduleTensorMap {X : RingedSpace.{v}} [ModuleTensorProduct X]
    {I I' F F' : RingedSpaceModule X}
    (u : I ⟶ I') (v : F ⟶ F') :
      @Quiver.Hom (RingedSpaceModule X) (inferInstance : Quiver (RingedSpaceModule X))
        (moduleTensor I F) (moduleTensor I' F') :=
  ModuleTensorProduct.map u v

/-! The generic sheaf-module category in this project does not carry the
set-theoretic hypotheses required by Mathlib's derived Ext object.  This
chapter therefore exposes the source's Ext groups through a narrow theory
interface, while keeping their additive-group structure explicit. -/

class SheafExtTheory (X : RingedSpace.{v}) where
  ext : RingedSpaceModule X → RingedSpaceModule X → ℕ → Type (v + 1)
  group : ∀ (F K : RingedSpaceModule X) (n : ℕ),
    AddCommGroup (ext F K n)
  map : ∀ {F K L : RingedSpaceModule X} (n : ℕ),
    (K ⟶ L) → ext F K n → ext F L n
  map_id : ∀ {F K : RingedSpaceModule X} (n : ℕ) (x : ext F K n),
    map n (𝟙 K) x = x
  map_comp : ∀ {F K L M : RingedSpaceModule X} (n : ℕ)
    (f : K ⟶ L) (g : L ⟶ M) (x : ext F K n),
    map n (f ≫ g) x = map n g (map n f x)
  boundary : ∀ {F K₃ K₂ K₁ : RingedSpaceModule X}
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (zero : k₃₂ ≫ k₂₁ = 0)
    (_ : (ShortComplex.mk k₃₂ k₂₁ zero).ShortExact),
    ext F K₁ 1 → ext F K₃ 2

abbrev ExtGroup {X : RingedSpace.{v}} [SheafExtTheory X]
    (F K : RingedSpaceModule X) (n : ℕ) : Type (v + 1) :=
  SheafExtTheory.ext F K n

instance extGroup_addCommGroup {X : RingedSpace.{v}} [h : SheafExtTheory X]
    (F K : RingedSpaceModule X) (n : ℕ) : AddCommGroup (ExtGroup F K n) :=
  h.group F K n

/-! ## The kernel module and extensions -/

/-- The chosen `O_X`-module representing the first-order kernel ideal. -/
noncomputable def firstOrderKernelModule
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) : Mod X.structureSheaf :=
  Classical.choose (firstOrderThickening_kernel_is_module i hi)

/-- The pushforward realization of the chosen kernel module. -/
noncomputable def firstOrderKernelModuleIso
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) :
  (ringedSpaceModulePushforward i).obj (firstOrderKernelModule i hi) ≅
      (thickeningIdeal i).carrier :=
  Classical.choice (Classical.choose_spec (firstOrderThickening_kernel_is_module i hi))

/-- A short exact `O_{X'}`-module extension with fixed `O_X` end terms
and its infinitesimal action map retained as source-facing data. -/
structure ModuleExtension
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    (F K : Mod X.structureSheaf) where
  middle : Mod X'.structureSheaf
  inclusion : (ringedSpaceModulePushforward i).obj K ⟶ middle
  projection : middle ⟶ (ringedSpaceModulePushforward i).obj F
  zero : inclusion ≫ projection = 0
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact
  infinitesimalMap : moduleTensor (firstOrderKernelModule i hi) F ⟶ K

/-- The source notation `c_{F'}` for the infinitesimal action attached to an
extension.  The selected kernel-module representative is used to expose the
source's `I ⊗ F → K` map in the project’s module category. -/
abbrev ModuleExtension.c_F'
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    {F K : Mod X.structureSheaf} (E : ModuleExtension i hi F K) :=
  E.infinitesimalMap

/-- A map of two fixed-endpoint extension sequences. -/
structure CompatibleExtensionMap
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    {F K G L : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) (E' : ModuleExtension i hi G L)
    (φ : F ⟶ G) (ψ : K ⟶ L) where
  middle : E.middle ⟶ E'.middle
  comm_left : E.inclusion ≫ middle =
    (ringedSpaceModulePushforward i).map ψ ≫ E'.inclusion
  comm_right : middle ≫ E'.projection =
    E.projection ≫ (ringedSpaceModulePushforward i).map φ

/-- The commutative square of infinitesimal maps required for lifting a map
of extensions. -/
structure InfinitesimalCompatibility
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    {F K G L : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) (E' : ModuleExtension i hi G L)
    (φ : F ⟶ G) (ψ : K ⟶ L) where
  commutes : E.infinitesimalMap ≫ ψ =
    moduleTensorMap (𝟙 (firstOrderKernelModule i hi)) φ ≫
      E'.infinitesimalMap

/-! ## Maps between extensions and their obstruction -/

/-- A compatible map forces commutativity of the infinitesimal square. -/
theorem compatibleMap_infinitesimal_compatibility
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    {F K G L : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) (E' : ModuleExtension i hi G L)
    (φ : F ⟶ G) (ψ : K ⟶ L)
    (h : CompatibleExtensionMap E E' φ ψ) :
    InfinitesimalCompatibility E E' φ ψ := by
  sorry

/-- If one compatible map exists, compatible maps form a principal
homogeneous space under the Hom module from F to L. -/
theorem compatibleExtensionMaps_is_principalHomogeneousSpace
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    {F K G L : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) (E' : ModuleExtension i hi G L)
    (φ : F ⟶ G) (ψ : K ⟶ L)
    (h : Nonempty (CompatibleExtensionMap E E' φ ψ)) :
    Nonempty (PrincipalHomogeneousSpace
      (F ⟶ L) (CompatibleExtensionMap E E' φ ψ)) := by
  sorry

/-- Existence and vanishing criterion for the obstruction to lifting a map. -/
theorem exists_mapObstruction
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    [SheafExtTheory X]
    {F K G L : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) (E' : ModuleExtension i hi G L)
    (φ : F ⟶ G) (ψ : K ⟶ L)
    (h : InfinitesimalCompatibility E E' φ ψ) :
    ∃ o : ExtGroup F L 1,
      (o = 0 ↔ Nonempty (CompatibleExtensionMap E E' φ ψ)) := by
  sorry

/-- The obstruction class for lifting a map of extensions. -/
noncomputable def mapObstruction
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    [SheafExtTheory X]
    {F K G L : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) (E' : ModuleExtension i hi G L)
    (φ : F ⟶ G) (ψ : K ⟶ L)
    (h : InfinitesimalCompatibility E E' φ ψ) :
    ExtGroup F L 1 :=
  Classical.choose (exists_mapObstruction E E' φ ψ h)

theorem mapObstruction_vanishes_iff
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    [SheafExtTheory X]
    {F K G L : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) (E' : ModuleExtension i hi G L)
    (φ : F ⟶ G) (ψ : K ⟶ L)
    (h : InfinitesimalCompatibility E E' φ ψ) :
    mapObstruction E E' φ ψ h = 0 ↔
      Nonempty (CompatibleExtensionMap E E' φ ψ) :=
  Classical.choose_spec (exists_mapObstruction E E' φ ψ h)

/-! ## The classification and obstruction for extensions -/

/-- An isomorphism of extensions preserving the fixed end terms and their
infinitesimal maps. -/
structure ModuleExtensionIso
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    {F K : Mod X.structureSheaf}
    (E E' : ModuleExtension i hi F K) where
  middle : E.middle ≅ E'.middle
  comm_left : E.inclusion ≫ middle.hom = E'.inclusion
  comm_right : middle.hom ≫ E'.projection = E.projection
  comm_infinitesimal : E.infinitesimalMap = E'.infinitesimalMap

/-- The setoid used for isomorphism classes of fixed-action extensions. -/
def moduleExtensionIsoSetoid
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    (F K : Mod X.structureSheaf) : Setoid (ModuleExtension i hi F K) := by
  refine { r := fun E E' => Nonempty (ModuleExtensionIso E E'), iseqv := ?_ }
  refine ⟨?_, ?_, ?_⟩
  · intro E
    exact ⟨{
      middle := Iso.refl _
      comm_left := by simp
      comm_right := by simp
      comm_infinitesimal := rfl }⟩
  · intro E E' h
    rcases h with ⟨h⟩
    refine ⟨{
      middle := h.middle.symm
      comm_left := by
        rw [← h.comm_left]
        simp
      comm_right := by
        rw [← h.comm_right]
        simp
      comm_infinitesimal := h.comm_infinitesimal.symm }⟩
  · intro E E' E'' h₁ h₂
    rcases h₁ with ⟨h₁⟩
    rcases h₂ with ⟨h₂⟩
    refine ⟨{
      middle := h₁.middle ≪≫ h₂.middle
      comm_left := by
        change E.inclusion ≫ (h₁.middle.hom ≫ h₂.middle.hom) = E''.inclusion
        rw [← Category.assoc, h₁.comm_left, h₂.comm_left]
      comm_right := by
        change (h₁.middle.hom ≫ h₂.middle.hom) ≫ E''.projection = E.projection
        rw [Category.assoc, h₂.comm_right, h₁.comm_right]
      comm_infinitesimal := h₁.comm_infinitesimal.trans h₂.comm_infinitesimal }⟩

/-- Isomorphism classes of extensions with prescribed infinitesimal map. -/
abbrev ModuleExtensionClass
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    (F K : Mod X.structureSheaf) :=
  Quotient (moduleExtensionIsoSetoid (i := i) (hi := hi) F K)

/-- Once one extension exists, its isomorphism classes form a torsor under
Ext one for F and K. -/
theorem moduleExtensionClasses_is_principalHomogeneousSpace
    {X X' : RingedSpace.{v}} {i : RingedSpaceHom X X'}
    {hi : IsFirstOrderThickening i} [ModuleTensorProduct X]
    [SheafExtTheory X]
    {F K : Mod X.structureSheaf}
    (h : Nonempty (ModuleExtension i hi F K)) :
    Nonempty (PrincipalHomogeneousSpace
      (ExtGroup F K 1)
      (ModuleExtensionClass (i := i) (hi := hi) F K)) := by
  sorry

/-- Existence and vanishing criterion for the obstruction to realizing a
prescribed infinitesimal map. -/
theorem exists_extensionObstruction
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    [SheafExtTheory X]
    (F K : Mod X.structureSheaf)
    (c : moduleTensor (firstOrderKernelModule i hi) F ⟶ K) :
    ∃ o : ExtGroup F K 2,
      (o = 0 ↔ Nonempty (ModuleExtension i hi F K)) := by
  sorry

/-- The obstruction class for a prescribed infinitesimal map. -/
noncomputable def extensionObstruction
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    [SheafExtTheory X]
    (F K : Mod X.structureSheaf)
    (c : moduleTensor (firstOrderKernelModule i hi) F ⟶ K) :
    ExtGroup F K 2 :=
  Classical.choose (exists_extensionObstruction i hi F K c)

theorem extensionObstruction_vanishes_iff
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    [SheafExtTheory X]
    (F K : Mod X.structureSheaf)
    (c : moduleTensor (firstOrderKernelModule i hi) F ⟶ K) :
    extensionObstruction i hi F K c = 0 ↔
      Nonempty (ModuleExtension i hi F K) :=
  Classical.choose_spec (exists_extensionObstruction i hi F K c)

/-! ## Trivial thickenings and trivial extensions -/

/-- A trivialization is a retraction of a first-order thickening. -/
structure ThickeningTrivialization
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) where
  projection : RingedSpaceHom X' X
  left_inverse : RingedSpaceHom.comp i projection = RingedSpaceHom.id X

/-- A first-order thickening is trivial when it admits a trivialization. -/
def IsTrivialFirstOrderThickening
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) : Prop :=
  Nonempty (ThickeningTrivialization i hi)

/-- The splitting datum associated with a trivialization. -/
structure StructureSheafSplitting
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) where
  sectionMap : RingedSpaceHom X' X
  retraction : RingedSpaceHom.comp i sectionMap = RingedSpaceHom.id X

theorem trivialization_gives_structureSheaf_splitting
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) (π : ThickeningTrivialization i hi) :
    Nonempty (StructureSheafSplitting i hi) :=
  ⟨{ sectionMap := π.projection, retraction := π.left_inverse }⟩

def structureSheaf_splitting_gives_trivialization
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) (s : StructureSheafSplitting i hi) :
    ThickeningTrivialization i hi :=
  ⟨s.sectionMap, s.retraction⟩

/-- A trivialized first-order thickening, used in the categorical
equivalence assertion of the source. -/
structure TrivializedFirstOrderThickening (X : RingedSpace.{v}) where
  thickeningSpace : RingedSpace
  inclusion : RingedSpaceHom X thickeningSpace
  firstOrder : IsFirstOrderThickening inclusion
  trivialization : ThickeningTrivialization inclusion firstOrder

/-- A morphism of trivialized thickenings over the fixed base. -/
structure TrivializedFirstOrderThickeningHom
    {X : RingedSpace.{v}}
    (A B : TrivializedFirstOrderThickening X) where
  hom : RingedSpaceHom A.thickeningSpace B.thickeningSpace
  commutes : RingedSpaceHom.comp A.inclusion hom = B.inclusion
  trivializations_commute :
    RingedSpaceHom.comp hom B.trivialization.projection =
      A.trivialization.projection

instance (X : RingedSpace.{v}) :
    Category (TrivializedFirstOrderThickening X) where
  Hom A B := TrivializedFirstOrderThickeningHom A B
  id A :=
    { hom := RingedSpaceHom.id A.thickeningSpace
      commutes := by cases A.inclusion; rfl
      trivializations_commute := by
        cases A.trivialization.projection
        rfl }
  comp := fun {A B C} f g =>
    { hom := RingedSpaceHom.comp f.hom g.hom
      commutes := by
        rw [← g.commutes, ← f.commutes]
        exact (Category.assoc (obj := RingedSpace)
          (f := A.inclusion) (g := f.hom) (h := g.hom)).symm
      trivializations_commute := by
        rw [← f.trivializations_commute, ← g.trivializations_commute]
        exact Category.assoc (obj := RingedSpace) (f := f.hom) (g := g.hom)
          (h := C.trivialization.projection) }
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- The category of trivialized first-order thickenings is equivalent to the
category of modules on the base. -/
theorem trivializedThickenings_equivalent_to_modules
    (X : RingedSpace.{v}) :
    Nonempty (TrivializedFirstOrderThickening X ≌
      Mod X.structureSheaf) := by
  sorry

theorem exists_trivialExtension
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    (π : ThickeningTrivialization i hi)
    (F K : Mod X.structureSheaf)
    (c : moduleTensor (firstOrderKernelModule i hi) F ⟶ K) :
    ∃ E : ModuleExtension i hi F K, E.infinitesimalMap = c := by
  sorry

/-- The trivial extension attached to a trivialization and a prescribed map
from the tensor of the kernel with F to K. -/
noncomputable def trivialExtension
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    (π : ThickeningTrivialization i hi)
    {F K : Mod X.structureSheaf}
    (c : moduleTensor (firstOrderKernelModule i hi) F ⟶ K) :
    ModuleExtension i hi F K :=
  Classical.choose (exists_trivialExtension i hi π F K c)

/-- The Ext class obtained from an extension after choosing a trivialization
of the thickening. -/
theorem extensionClass_exists
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    [SheafExtTheory X]
    (π : ThickeningTrivialization i hi)
    {F K : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) :
    Nonempty (ExtGroup F K 1) := by
  sorry

noncomputable def extensionClass
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    [SheafExtTheory X]
    (π : ThickeningTrivialization i hi)
    {F K : Mod X.structureSheaf}
    (E : ModuleExtension i hi F K) :
    ExtGroup F K 1 :=
  Classical.choice (extensionClass_exists i hi π E)

/-- The classification bijection for extensions in a trivialized thickening.
-/
theorem trivializedExtensionClasses_equiv_ext
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    [SheafExtTheory X]
    (π : ThickeningTrivialization i hi)
    (F K : Mod X.structureSheaf) :
    Nonempty (ModuleExtensionClass (i := i) (hi := hi) F K ≃
      ExtGroup F K 1) := by
  sorry

/-- The trivial extension gives the zero Ext class after the trivialization
is used to regard the sequence as an extension over the base. -/
theorem trivialExtension_class_zero
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) [ModuleTensorProduct X]
    [SheafExtTheory X]
    (π : ThickeningTrivialization i hi)
    {F K : Mod X.structureSheaf}
    (c : moduleTensor (firstOrderKernelModule i hi) F ⟶ K) :
    extensionClass i hi π (trivialExtension i hi π c) = 0 := by
  sorry

/-! ## Functoriality in the thickening -/

/-- A morphism between two first-order thickenings of the same base. -/
structure FirstOrderThickeningMorphism (X : RingedSpace.{v}) where
  X₁ : RingedSpace
  X₂ : RingedSpace
  i₁ : RingedSpaceHom X X₁
  i₂ : RingedSpaceHom X X₂
  firstOrder₁ : IsFirstOrderThickening i₁
  firstOrder₂ : IsFirstOrderThickening i₂
  hom : RingedSpaceHom X₁ X₂
  commutes : RingedSpaceHom.comp i₁ hom = i₂
  kernelMapData : firstOrderKernelModule i₂ firstOrder₂ ⟶
    firstOrderKernelModule i₁ firstOrder₁

theorem FirstOrderThickeningMorphism.kernelMap_exists
    {X : RingedSpace.{v}} (M : FirstOrderThickeningMorphism X) :
    Nonempty (firstOrderKernelModule M.i₂ M.firstOrder₂ ⟶
      firstOrderKernelModule M.i₁ M.firstOrder₁) :=
  ⟨M.kernelMapData⟩

/-- The induced map on the chosen kernel modules. -/
noncomputable def FirstOrderThickeningMorphism.kernelMap
    {X : RingedSpace.{v}} (M : FirstOrderThickeningMorphism X) :
    firstOrderKernelModule M.i₂ M.firstOrder₂ ⟶
      firstOrderKernelModule M.i₁ M.firstOrder₁ :=
  M.kernelMapData

/-- Data for functoriality of extensions under a map of thickenings. -/
structure ExtensionFunctorialityData
    {X : RingedSpace.{v}} (M : FirstOrderThickeningMorphism X)
    [ModuleTensorProduct X] (F : Mod X.structureSheaf) where
  K₁ : Mod X.structureSheaf
  K₂ : Mod X.structureSheaf
  c₁ : moduleTensor (firstOrderKernelModule M.i₁ M.firstOrder₁) F ⟶ K₁
  c₂ : moduleTensor (firstOrderKernelModule M.i₂ M.firstOrder₂) F ⟶ K₂
  kernelMap : K₂ ⟶ K₁
  c_square : moduleTensorMap M.kernelMap (𝟙 F) ≫ c₁ = c₂ ≫ kernelMap

/-- Pushout along a morphism of thickenings preserves the prescribed
infinitesimal action. -/
theorem extensionFunctoriality_exists
    {X : RingedSpace.{v}} {M : FirstOrderThickeningMorphism X}
    [ModuleTensorProduct X] {F : Mod X.structureSheaf}
    (D : ExtensionFunctorialityData M F)
    (E₂ : ModuleExtension M.i₂ M.firstOrder₂ F D.K₂)
    (hE₂ : E₂.infinitesimalMap = D.c₂) :
    ∃ E₁ : ModuleExtension M.i₁ M.firstOrder₁ F D.K₁,
      E₁.infinitesimalMap = D.c₁ := by
  sorry

noncomputable def extensionFunctoriality
    {X : RingedSpace.{v}} {M : FirstOrderThickeningMorphism X}
    [ModuleTensorProduct X] {F : Mod X.structureSheaf}
    (D : ExtensionFunctorialityData M F)
    (E₂ : ModuleExtension M.i₂ M.firstOrder₂ F D.K₂)
    (hE₂ : E₂.infinitesimalMap = D.c₂) :
    ModuleExtension M.i₁ M.firstOrder₁ F D.K₁ :=
  Classical.choose (extensionFunctoriality_exists D E₂ hE₂)

theorem extensionFunctoriality_infinitesimalMap
    {X : RingedSpace.{v}} {M : FirstOrderThickeningMorphism X}
    [ModuleTensorProduct X] {F : Mod X.structureSheaf}
    (D : ExtensionFunctorialityData M F)
    (E₂ : ModuleExtension M.i₂ M.firstOrder₂ F D.K₂)
    (hE₂ : E₂.infinitesimalMap = D.c₂) :
    (extensionFunctoriality D E₂ hE₂).infinitesimalMap = D.c₁ :=
  Classical.choose_spec (extensionFunctoriality_exists D E₂ hE₂)

/-- Compatible trivializations for a morphism of thickenings. -/
structure TrivializedFirstOrderThickeningMorphism
    {X : RingedSpace.{v}} (M : FirstOrderThickeningMorphism X) where
  π₁ : ThickeningTrivialization M.i₁ M.firstOrder₁
  π₂ : ThickeningTrivialization M.i₂ M.firstOrder₂
  compatible : RingedSpaceHom.comp M.hom π₂.projection = π₁.projection

/-! ## Complexes and short exact sequences of thickenings -/

/-- A complex of three first-order thickenings, with maps on their kernel
modules displayed explicitly. -/
structure FirstOrderThickeningComplex (X : RingedSpace.{v}) where
  X₁ : RingedSpace
  X₂ : RingedSpace
  X₃ : RingedSpace
  i₁ : RingedSpaceHom X X₁
  i₂ : RingedSpaceHom X X₂
  i₃ : RingedSpaceHom X X₃
  firstOrder₁ : IsFirstOrderThickening i₁
  firstOrder₂ : IsFirstOrderThickening i₂
  firstOrder₃ : IsFirstOrderThickening i₃
  h₁₂ : RingedSpaceHom X₁ X₂
  h₂₃ : RingedSpaceHom X₂ X₃
  comm₁₂ : RingedSpaceHom.comp i₁ h₁₂ = i₂
  comm₂₃ : RingedSpaceHom.comp i₂ h₂₃ = i₃
  idealMap₂₁ : firstOrderKernelModule i₂ firstOrder₂ ⟶
    firstOrderKernelModule i₁ firstOrder₁
  idealMap₃₂ : firstOrderKernelModule i₃ firstOrder₃ ⟶
    firstOrderKernelModule i₂ firstOrder₂

/-- The first two terms of a complex of thickenings form the morphism used by
the extension-functoriality construction. -/
def FirstOrderThickeningComplex.toMorphism
    {X : RingedSpace.{v}} (C : FirstOrderThickeningComplex X) :
    FirstOrderThickeningMorphism X where
  X₁ := C.X₁
  X₂ := C.X₂
  i₁ := C.i₁
  i₂ := C.i₂
  firstOrder₁ := C.firstOrder₁
  firstOrder₂ := C.firstOrder₂
  hom := C.h₁₂
  commutes := C.comm₁₂
  kernelMapData := C.idealMap₂₁

/-- The ideal maps of a thickening sequence form a complex. -/
def FirstOrderThickeningComplex.IsComplex
    {X : RingedSpace.{v}} (C : FirstOrderThickeningComplex X) : Prop :=
  C.idealMap₃₂ ≫ C.idealMap₂₁ = 0

/-- The ideal maps form a short exact sequence. -/
def FirstOrderThickeningComplex.IsShortExact
    {X : RingedSpace.{v}} (C : FirstOrderThickeningComplex X) : Prop :=
  ∃ hC : C.IsComplex,
    (ShortComplex.mk C.idealMap₃₂ C.idealMap₂₁ hC).ShortExact

/-- A complex of first-order thickenings has a canonical trivialization of
its first term. -/
theorem complex_thickening_has_canonical_trivialization
    {X : RingedSpace.{v}} (C : FirstOrderThickeningComplex X)
    (hC : C.IsComplex) :
    Nonempty (ThickeningTrivialization C.i₁ C.firstOrder₁) := by
  sorry

noncomputable def FirstOrderThickeningComplex.canonicalTrivialization
    {X : RingedSpace.{v}} (C : FirstOrderThickeningComplex X)
    (hC : C.IsComplex) : ThickeningTrivialization C.i₁ C.firstOrder₁ :=
  Classical.choice (complex_thickening_has_canonical_trivialization C hC)

/-! ## Trivialized functoriality and the final Ext-boundary claim -/

/-- A source-facing commutative square of Ext classes for compatible
trivializations. -/
structure TrivializedExtClassSquare
    {X : RingedSpace.{v}} {M : FirstOrderThickeningMorphism X}
    [ModuleTensorProduct X] [SheafExtTheory X] {F : Mod X.structureSheaf}
    (D : ExtensionFunctorialityData M F) where
  class₂ : ExtGroup F D.K₂ 1
  class₁ : ExtGroup F D.K₁ 1
  commutes : SheafExtTheory.map 1 D.kernelMap class₂ = class₁

/-- The extension functoriality and the Ext-class map commute for compatible
trivializations. -/
theorem trivializedExtensionFunctoriality_ext_commutes
    {X : RingedSpace.{v}} {M : FirstOrderThickeningMorphism X}
    [ModuleTensorProduct X] [SheafExtTheory X] {F : Mod X.structureSheaf}
    (T : TrivializedFirstOrderThickeningMorphism M)
    (D : ExtensionFunctorialityData M F)
    (E₂ : ModuleExtension M.i₂ M.firstOrder₂ F D.K₂)
    (hE₂ : E₂.infinitesimalMap = D.c₂) :
    Nonempty (TrivializedExtClassSquare (D := D)) := by
  sorry

/-- The coefficient short exact sequence used in the final remark. -/
structure CoefficientShortExactSequence (X : RingedSpace.{v}) where
  K₃ : Mod X.structureSheaf
  K₂ : Mod X.structureSheaf
  K₁ : Mod X.structureSheaf
  k₃₂ : K₃ ⟶ K₂
  k₂₁ : K₂ ⟶ K₁
  zero : k₃₂ ≫ k₂₁ = 0
  shortExact : (ShortComplex.mk k₃₂ k₂₁ zero).ShortExact

/-- The connecting map on Ext groups associated to a coefficient short exact
sequence. -/
def extBoundary {X : RingedSpace.{v}} [SheafExtTheory X]
    (S : CoefficientShortExactSequence X) (F : Mod X.structureSheaf) :
    ExtGroup F S.K₁ 1 → ExtGroup F S.K₃ 2 :=
  SheafExtTheory.boundary S.k₃₂ S.k₂₁ S.zero S.shortExact

/-- A named package for the canonical connecting map used in the final
source remark.  The equality field prevents the map from being
unconstrained. -/
structure ExtBoundaryData {X : RingedSpace.{v}} [SheafExtTheory X]
    (S : CoefficientShortExactSequence X) (F : Mod X.structureSheaf) where
  boundary : ExtGroup F S.K₁ 1 → ExtGroup F S.K₃ 2
  boundary_eq_canonical : boundary = extBoundary S F

/-- Data for the last source remark, including the compatible coefficient
squares and an extension over the middle thickening. -/
structure ComplexThickeningModuleData
    {X : RingedSpace.{v}} (C : FirstOrderThickeningComplex X)
    [ModuleTensorProduct X] [SheafExtTheory X] (F : Mod X.structureSheaf)
    (S : CoefficientShortExactSequence X) where
  complex : C.IsComplex
  c₁ : moduleTensor (firstOrderKernelModule C.i₁ C.firstOrder₁) F ⟶ S.K₁
  c₂ : moduleTensor (firstOrderKernelModule C.i₂ C.firstOrder₂) F ⟶ S.K₂
  c₃ : moduleTensor (firstOrderKernelModule C.i₃ C.firstOrder₃) F ⟶ S.K₃
  square₂₁ : moduleTensorMap C.idealMap₂₁ (𝟙 F) ≫ c₁ = c₂ ≫ S.k₂₁
  square₃₂ : moduleTensorMap C.idealMap₃₂ (𝟙 F) ≫ c₂ = c₃ ≫ S.k₃₂
  middleExtension : ModuleExtension C.i₂ C.firstOrder₂ F S.K₂
  middleExtension_action : middleExtension.infinitesimalMap = c₂
  boundaryData : ExtBoundaryData S F

/-- The coefficient square in the last source remark, packaged for the
first-two-term thickening morphism. -/
def ComplexThickeningModuleData.functorialityData
    {X : RingedSpace.{v}} {C : FirstOrderThickeningComplex X}
    [ModuleTensorProduct X] [SheafExtTheory X] {F : Mod X.structureSheaf}
    {S : CoefficientShortExactSequence X}
    (D : ComplexThickeningModuleData C F S) :
    ExtensionFunctorialityData C.toMorphism F where
  K₁ := S.K₁
  K₂ := S.K₂
  c₁ := D.c₁
  c₂ := D.c₂
  kernelMap := S.k₂₁
  c_square := D.square₂₁

/-- The extension on the first thickening obtained from the middle extension
by the functoriality construction in the source. -/
noncomputable def ComplexThickeningModuleData.inducedExtension
    {X : RingedSpace.{v}} {C : FirstOrderThickeningComplex X}
    [ModuleTensorProduct X] [SheafExtTheory X] {F : Mod X.structureSheaf}
    {S : CoefficientShortExactSequence X}
    (D : ComplexThickeningModuleData C F S) :
    ModuleExtension C.i₁ C.firstOrder₁ F S.K₁ :=
  extensionFunctoriality D.functorialityData D.middleExtension
    D.middleExtension_action

theorem ComplexThickeningModuleData.inducedExtension_action
    {X : RingedSpace.{v}} {C : FirstOrderThickeningComplex X}
    [ModuleTensorProduct X] [SheafExtTheory X] {F : Mod X.structureSheaf}
    {S : CoefficientShortExactSequence X}
    (D : ComplexThickeningModuleData C F S) :
    D.inducedExtension.infinitesimalMap = D.c₁ :=
  extensionFunctoriality_infinitesimalMap D.functorialityData
    D.middleExtension D.middleExtension_action

/-- The Ext¹ class of the induced first extension, using the canonical
trivialization supplied by the complex of thickenings. -/
noncomputable def ComplexThickeningModuleData.ξ₁
    {X : RingedSpace.{v}} {C : FirstOrderThickeningComplex X}
    [ModuleTensorProduct X] [SheafExtTheory X] {F : Mod X.structureSheaf}
    {S : CoefficientShortExactSequence X}
    (D : ComplexThickeningModuleData C F S) : ExtGroup F S.K₁ 1 :=
  extensionClass C.i₁ C.firstOrder₁
    (C.canonicalTrivialization D.complex) D.inducedExtension

/-- The boundary of the induced first extension class is the obstruction
class of the third coefficient. -/
theorem ext_boundary_eq_extension_obstruction
    {X : RingedSpace.{v}} {C : FirstOrderThickeningComplex X}
    [ModuleTensorProduct X] [SheafExtTheory X] {F : Mod X.structureSheaf}
    {S : CoefficientShortExactSequence X}
    (D : ComplexThickeningModuleData C F S) :
    D.boundaryData.boundary D.ξ₁ =
      extensionObstruction C.i₃ C.firstOrder₃ F S.K₃ D.c₃ := by
  sorry

end
end Formalization.Books.Defos.Unit04
