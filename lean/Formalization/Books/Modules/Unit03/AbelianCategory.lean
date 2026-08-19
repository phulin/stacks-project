import Formalization.Books.Modules.Unit02.Pathology
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors

/-!
# Modules, Chapter 3: The abelian category of sheaves of modules

This file records the precise interfaces in the source section.  The
category of sheaves of modules, its additive structure, and its universal
constructions are Mathlib's canonical `SheafOfModules` constructions.  The
source-facing names below only package those constructions and state the
section, stalk, exactness, and functoriality assertions used in the chapter.
-/

namespace Formalization.Books.Modules.Unit03

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit03
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v u

noncomputable section

/-! ## Sections, addition, zero objects, and direct sums -/

/-- The module of sections over an open set. -/
abbrev sheafModuleSections {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (F : Mod O) (U : Opens X) : ModuleCat.{v} (O.obj.obj (op U)) :=
  (SheafOfModules.evaluation O (op U)).obj F

/-- The map on sections induced by a morphism of sheaves of modules. -/
abbrev sheafModuleSectionsMap {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (U : Opens X) :
    sheafModuleSections O F U ⟶ sheafModuleSections O G U :=
  (SheafOfModules.evaluation O (op U)).map φ

/-! Stalks use the canonical module structure from the earlier sheaves
chapter.  The abbreviation keeps the source-facing name used throughout the
Modules book without introducing a second stalk implementation. -/

abbrev sheafModuleStalkFunctor {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) (x : X) :
    Mod O ⥤ ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) :=
  moduleStalkFunctor O x

instance sheafModuleStalkFunctor_preservesZeroMorphisms {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) (x : X) :
    (sheafModuleStalkFunctor O x).PreservesZeroMorphisms where
  map_zero F G := by
    ext z
    change (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
      ((PresheafOfModules.toPresheaf O.obj).map (0 : F.val ⟶ G.val)) z = 0
    simp only [Functor.map_zero]
    change 0 = 0
    rfl

/-- Mathlib's canonical preadditive structure is the sectionwise addition in
the source. -/
theorem sheafModule_preadditive {X : TopCat.{v}} (O : RingSheaf.{v, v} X) :
    Nonempty (Preadditive (Mod O)) :=
  ⟨inferInstance⟩

/-- Addition of morphisms is computed sectionwise. -/
theorem sheafModuleSectionsMap_add {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ ψ : F ⟶ G) (U : Opens X) :
    sheafModuleSectionsMap O (φ + ψ) U =
      sheafModuleSectionsMap O φ U + sheafModuleSectionsMap O ψ U := by
  change (φ + ψ).val.app (op U) = φ.val.app (op U) + ψ.val.app (op U)
  rfl

/-- The project additive-category interface for sheaves of modules. -/
noncomputable instance sheafModule_additiveCategory {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) : AdditiveCategory (Mod O) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

/-- The zero sheaf of modules, using the canonical zero object. -/
noncomputable abbrev sheafModuleZero {X : TopCat.{v}} (O : RingSheaf.{v, v} X) : Mod O :=
  0

theorem sheafModuleZero_isZero {X : TopCat.{v}} (O : RingSheaf.{v, v} X) :
    IsZero (sheafModuleZero O) := by
  exact isZero_zero (Mod O)

theorem sheafModuleZero_isInitial {X : TopCat.{v}} (O : RingSheaf.{v, v} X) :
    Nonempty (IsInitial (sheafModuleZero O)) :=
  ⟨(sheafModuleZero_isZero O).isInitial⟩

theorem sheafModuleZero_isTerminal {X : TopCat.{v}} (O : RingSheaf.{v, v} X) :
    Nonempty (IsTerminal (sheafModuleZero O)) :=
  ⟨(sheafModuleZero_isZero O).isTerminal⟩

/-- Factoring through the zero sheaf. -/
def sheafModuleFactorsThroughZero {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) : Prop :=
  ∃ (a : F ⟶ sheafModuleZero O) (b : sheafModuleZero O ⟶ G), a ≫ b = φ

theorem sheafModuleFactorsThroughZero_iff {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) :
    sheafModuleFactorsThroughZero O φ ↔ φ = 0 := by
  change (∃ (a : F ⟶ sheafModuleZero O) (b : sheafModuleZero O ⟶ G),
    a ≫ b = φ) ↔ φ = 0
  exact factors_through_zero_iff (sheafModuleZero_isZero O) φ

/-- The four zero-morphism criteria in the source.  The section and stalk
maps are expressed as the canonical morphisms in the corresponding module
categories. -/
theorem sheafModule_zero_morphism_criteria {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) :
    φ = 0 ↔
      sheafModuleFactorsThroughZero O φ ∧
        (∀ U : Opens X, sheafModuleSectionsMap O φ U = 0) ∧
        (∀ x : X, (sheafModuleStalkFunctor O x).map φ = 0) := by
  constructor
  · intro h
    subst φ
    exact ⟨(sheafModuleFactorsThroughZero_iff O 0).2 rfl, by simp, by simp⟩
  · intro h
    exact (sheafModuleFactorsThroughZero_iff O φ).1 h.1

/-! The source's binary direct sum is Mathlib's binary biproduct. -/

noncomputable abbrev sheafModuleDirectSum {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (F G : Mod O) : Mod O := F ⊞ G

abbrev sheafModuleDirectSumInclusionLeft {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (F G : Mod O) : F ⟶ sheafModuleDirectSum O F G :=
  biprod.inl

abbrev sheafModuleDirectSumInclusionRight {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (F G : Mod O) : G ⟶ sheafModuleDirectSum O F G :=
  biprod.inr

abbrev sheafModuleDirectSumProjectionLeft {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (F G : Mod O) : sheafModuleDirectSum O F G ⟶ F :=
  biprod.fst

abbrev sheafModuleDirectSumProjectionRight {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (F G : Mod O) : sheafModuleDirectSum O F G ⟶ G :=
  biprod.snd

theorem sheafModuleDirectSum_total {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (F G : Mod O) :
    sheafModuleDirectSumProjectionLeft O F G ≫
          sheafModuleDirectSumInclusionLeft O F G +
        sheafModuleDirectSumProjectionRight O F G ≫
          sheafModuleDirectSumInclusionRight O F G =
      𝟙 (sheafModuleDirectSum O F G) := by
  exact biprod.total

noncomputable def sheafModuleDirectSumProductIso {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) (F G : Mod O) :
    sheafModuleDirectSum O F G ≅ F ⨯ G :=
  biprod.isoProd F G

noncomputable def sheafModuleDirectSumCoproductIso {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) (F G : Mod O) :
    F ⨿ G ≅ sheafModuleDirectSum O F G :=
  (biprod.isoCoprod F G).symm

/-! ## Kernels and cokernels -/

noncomputable abbrev sheafModuleKernel {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) : Mod O :=
  kernel φ

noncomputable abbrev sheafModuleKernelPresheaf {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {F G : Mod O} (φ : F ⟶ G) :
    PresheafOfModules O.obj :=
  kernel φ.val

theorem sheafModuleKernel_universal {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) :
    Nonempty (IsLimit
      (KernelFork.ofι (kernel.ι φ) (kernel.condition φ))) := by
  exact ⟨kernelIsKernel φ⟩

theorem sheafModuleKernel_factorization {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G H : Mod O} (φ : F ⟶ G) (α : H ⟶ F) (hα : α ≫ φ = 0) :
    ∃! β : H ⟶ sheafModuleKernel O φ, β ≫ kernel.ι φ = α := by
  refine ⟨kernel.lift φ α hα, kernel.lift_ι φ α hα, ?_⟩
  intro β hβ
  apply (cancel_mono (kernel.ι φ)).1
  rw [hβ, kernel.lift_ι]

theorem sheafModuleKernel_section_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (U : Opens X) :
    Nonempty (sheafModuleSections O (sheafModuleKernel O φ) U ≅
      kernel (sheafModuleSectionsMap O φ U)) := by
  exact ⟨PreservesKernel.iso (SheafOfModules.evaluation O (op U)) φ⟩

theorem sheafModuleKernel_stalk_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (x : X) :
    Nonempty ((sheafModuleStalkFunctor O x).obj (sheafModuleKernel O φ) ≅
      kernel ((sheafModuleStalkFunctor O x).map φ)) := by
  let : PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat) := by
    infer_instance
  let : PreservesLimits (CategoryTheory.forget AddCommGrpCat) := by
    infer_instance
  let : PreservesFiniteLimits (SheafOfModules.toSheaf O) := by
    infer_instance
  let : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) := by
    have hH_homology :
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).PreservesHomology := by
      simp only [(TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).exact_tfae.out 2 0]
      intro S hS
      have hcolim := ((TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).preservesFiniteColimits_tfae.out
          3 0).mp
        (inferInstance : PreservesFiniteColimits
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x))
      refine ShortComplex.ShortExact.mk' (hcolim S hS).left ?_ (hcolim S hS).right
      have := hS.2
      exact Functor.map_mono
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) _
    exact (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).preservesFiniteLimits_of_preservesHomology
  let : PreservesFiniteLimits
      (sheafModuleStalkFunctor O x ⋙
        forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
          AddCommGrpCat) := by
    change PreservesFiniteLimits
      (SheafOfModules.toSheaf O ⋙
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x))
    refine ⟨fun J _ _ => ?_⟩
    let : PreservesLimitsOfShape J (SheafOfModules.toSheaf O) := by
      exact PreservesFiniteLimits.preservesFiniteLimits J
    let : PreservesLimitsOfShape J
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) := by
      exact PreservesFiniteLimits.preservesFiniteLimits J
    have hF : PreservesLimitsOfShape J (SheafOfModules.toSheaf O) :=
      PreservesFiniteLimits.preservesFiniteLimits J
    have hG : PreservesLimitsOfShape J
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) :=
      PreservesFiniteLimits.preservesFiniteLimits J
    exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
      (SheafOfModules.toSheaf O)
      (TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x)
      hF hG
  let : PreservesLimit (parallelPair φ 0) (sheafModuleStalkFunctor O x) := by
    apply preservesLimit_of_reflects_of_preserves
      (sheafModuleStalkFunctor O x)
      (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
        AddCommGrpCat)
  exact ⟨PreservesKernel.iso (sheafModuleStalkFunctor O x) φ⟩

noncomputable abbrev sheafModuleCokernel {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) : Mod O :=
  cokernel φ

noncomputable abbrev sheafModuleCokernelPresheaf {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {F G : Mod O} (φ : F ⟶ G) :
    PresheafOfModules O.obj :=
  cokernel φ.val

noncomputable abbrev sheafModuleCokernelSheafification {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {F G : Mod O} (φ : F ⟶ G) : Mod O :=
  (PresheafOfModules.sheafification (R₀ := O.obj) (𝟙 O.obj)).obj
    (sheafModuleCokernelPresheaf O φ)

theorem sheafModuleCokernel_sheafification_iso {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {F G : Mod O} (φ : F ⟶ G) :
    Nonempty (sheafModuleCokernel O φ ≅
      sheafModuleCokernelSheafification O φ) := by
  let L := PresheafOfModules.sheafification (R₀ := O.obj) (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := O.obj) (R := O) (𝟙 O.obj)
  let hF : IsIso (adj.counit.app F) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (R₀ := O.obj) (R := O) (𝟙 O.obj)).counit.app F)
    infer_instance
  let hG : IsIso (adj.counit.app G) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (R₀ := O.obj) (R := O) (𝟙 O.obj)).counit.app G)
    infer_instance
  let eF : L.obj F.val ≅ F := @asIso _ _ _ _ (adj.counit.app F) hF
  let eG : L.obj G.val ≅ G := @asIso _ _ _ _ (adj.counit.app G) hG
  refine ⟨(PreservesCokernel.iso L φ.val ≪≫
    cokernel.mapIso (L.map φ.val) φ eF eG ?_).symm⟩
  change L.map φ.val ≫ (adj.counit.app G) = (adj.counit.app F) ≫ φ
  exact adj.counit.naturality φ

theorem sheafModuleCokernel_section_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (U : Opens X) :
    Nonempty ((sheafModuleCokernelPresheaf O φ).obj (op U) ≅
      cokernel (sheafModuleSectionsMap O φ U)) := by
  exact ⟨PreservesCokernel.iso (PresheafOfModules.evaluation O.obj (op U)) φ.val⟩

private lemma sheafModuleCokernel_stalk_hπ {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G)
    (adj : PresheafOfModules.sheafification (𝟙 O.obj) ⊣
      SheafOfModules.forget O ⋙
        PresheafOfModules.restrictScalars (𝟙 O.obj))
    (hadj : adj = PresheafOfModules.sheafificationAdjunction (𝟙 O.obj))
    (eG : (PresheafOfModules.sheafification (𝟙 O.obj)).obj G.val ≅ G)
    (heG : eG.hom = adj.counit.app G)
    (m : cokernel ((PresheafOfModules.sheafification (𝟙 O.obj)).map φ.val) ≅
      cokernel φ)
    (e : sheafModuleCokernel O φ ≅ sheafModuleCokernelSheafification O φ)
    (he : e =
      (PreservesCokernel.iso (PresheafOfModules.sheafification (𝟙 O.obj)) φ.val ≪≫ m).symm)
    (hproj :
      ((PresheafOfModules.sheafification (𝟙 O.obj)).map (cokernel.π φ.val) ≫
          (PreservesCokernel.iso (PresheafOfModules.sheafification (𝟙 O.obj))
            φ.val).hom) ≫ m.hom =
        eG.hom ≫ cokernel.π φ) :
    (PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val) ≫
          (PresheafOfModules.toPresheaf O.obj).map
            (adj.unit.app (cokernel φ.val)) ≫
        (PresheafOfModules.toPresheaf O.obj).map
          ((SheafOfModules.forget O).map e.inv) =
      (PresheafOfModules.toPresheaf O.obj).map
        ((SheafOfModules.forget O).map (cokernel.π φ)) := by
  let L := PresheafOfModules.sheafification (𝟙 O.obj)
  have hπMid :
      (cokernel.π φ.val ≫ adj.unit.app (cokernel φ.val)) ≫
          (SheafOfModules.forget O ⋙
            PresheafOfModules.restrictScalars (𝟙 O.obj)).map e.inv =
        adj.unit.app G.val ≫
          (SheafOfModules.forget O ⋙
            PresheafOfModules.restrictScalars (𝟙 O.obj)).map
            (eG.hom ≫ cokernel.π φ) := by
    have hu := adj.unit.naturality (cokernel.π φ.val)
    have hu' :
        cokernel.π φ.val ≫ adj.unit.app (cokernel φ.val) =
          adj.unit.app G.val ≫
            (SheafOfModules.forget O ⋙
              PresheafOfModules.restrictScalars (𝟙 O.obj)).map
              (L.map (cokernel.π φ.val)) := by
      simpa only [Functor.id_map, Functor.comp_map] using hu
    have he :
        L.map (cokernel.π φ.val) ≫ e.inv =
          (L.map (cokernel.π φ.val) ≫ (PreservesCokernel.iso L φ.val).hom) ≫
            m.hom := by
      rw [he]
      dsimp [L]
      simp only [Category.assoc]
    have hright := congrArg
      (SheafOfModules.forget O ⋙
        PresheafOfModules.restrictScalars (𝟙 O.obj)).map hproj
    calc
      (cokernel.π φ.val ≫ adj.unit.app (cokernel φ.val)) ≫
            (SheafOfModules.forget O ⋙
              PresheafOfModules.restrictScalars (𝟙 O.obj)).map e.inv =
          (adj.unit.app G.val ≫
            (SheafOfModules.forget O ⋙
              PresheafOfModules.restrictScalars (𝟙 O.obj)).map
              (L.map (cokernel.π φ.val))) ≫
            (SheafOfModules.forget O ⋙
              PresheafOfModules.restrictScalars (𝟙 O.obj)).map e.inv := by
        exact congrArg (fun q => q ≫
          (SheafOfModules.forget O ⋙
            PresheafOfModules.restrictScalars (𝟙 O.obj)).map e.inv) hu'
      _ = adj.unit.app G.val ≫
          (SheafOfModules.forget O ⋙
            PresheafOfModules.restrictScalars (𝟙 O.obj)).map
            (L.map (cokernel.π φ.val) ≫ e.inv) := by
        simp only [Category.assoc, Functor.map_comp]
      _ = adj.unit.app G.val ≫
          (SheafOfModules.forget O ⋙
            PresheafOfModules.restrictScalars (𝟙 O.obj)).map
          ((L.map (cokernel.π φ.val) ≫ (PreservesCokernel.iso L φ.val).hom) ≫
            m.hom) := by rw [he]
      _ = adj.unit.app G.val ≫
          (SheafOfModules.forget O ⋙
            PresheafOfModules.restrictScalars (𝟙 O.obj)).map
            (eG.hom ≫ cokernel.π φ) := by
        rw [hright]
  have hπMidP := congrArg (PresheafOfModules.toPresheaf O.obj).map hπMid
  have hRestrE :
      (PresheafOfModules.toPresheaf O.obj).map
          ((SheafOfModules.forget O ⋙
            PresheafOfModules.restrictScalars (𝟙 O.obj)).map e.inv) =
        (PresheafOfModules.toPresheaf O.obj).map
          ((SheafOfModules.forget O).map e.inv) := by
    rfl
  have hRestrComp :
      (PresheafOfModules.toPresheaf O.obj).map
          ((SheafOfModules.forget O ⋙
            PresheafOfModules.restrictScalars (𝟙 O.obj)).map
            (eG.hom ≫ cokernel.π φ)) =
        (PresheafOfModules.toPresheaf O.obj).map
            ((SheafOfModules.forget O).map eG.hom ≫
              (SheafOfModules.forget O).map (cokernel.π φ)) := by
    rfl
  have hGunitAdd :
      (PresheafOfModules.toPresheaf O.obj).map
            (adj.unit.app G.val) ≫
          (PresheafOfModules.toPresheaf O.obj).map
            ((SheafOfModules.forget O).map eG.hom) =
        𝟙 ((PresheafOfModules.toPresheaf O.obj).obj
          ((SheafOfModules.forget O).obj G)) := by
    cases hadj
    rw [heG]
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    change toSheafify (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf O.obj).obj G.val) ≫
      (CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) AddCommGrpCat).map
        ((SheafOfModules.toSheaf O).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).counit.app G)) = 𝟙 _
    rw [PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app]
    change toSheafify (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf O.obj).obj G.val) ≫
      ((CategoryTheory.sheafificationAdjunction
          (Opens.grothendieckTopology X) AddCommGrpCat).counit.app
        ((SheafOfModules.toSheaf O).obj G)).hom = 𝟙 _
    rw [CategoryTheory.sheafificationAdjunction_counit_app_val]
    exact CategoryTheory.toSheafify_sheafifyLift _ _ _
  have hRight :
      (PresheafOfModules.toPresheaf O.obj).map
          (adj.unit.app G.val ≫
            (SheafOfModules.forget O ⋙
              PresheafOfModules.restrictScalars (𝟙 O.obj)).map
              (eG.hom ≫ cokernel.π φ)) =
        ((PresheafOfModules.toPresheaf O.obj).map (adj.unit.app G.val) ≫
          (PresheafOfModules.toPresheaf O.obj).map
            ((SheafOfModules.forget O).map eG.hom)) ≫
          (PresheafOfModules.toPresheaf O.obj).map
            ((SheafOfModules.forget O).map (cokernel.π φ)) := by
    rw [Functor.map_comp]
    rw [hRestrComp]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hFinalAdd :
      (((PresheafOfModules.toPresheaf O.obj).map (adj.unit.app G.val) ≫
          (PresheafOfModules.toPresheaf O.obj).map
            ((SheafOfModules.forget O).map eG.hom)) ≫
        (PresheafOfModules.toPresheaf O.obj).map
          ((SheafOfModules.forget O).map (cokernel.π φ))) =
        (PresheafOfModules.toPresheaf O.obj).map
          ((SheafOfModules.forget O).map (cokernel.π φ)) := by
    have h := congrArg
      (fun q => q ≫
        (PresheafOfModules.toPresheaf O.obj).map
          ((SheafOfModules.forget O).map (cokernel.π φ))) hGunitAdd
    exact h.trans (Category.id_comp _)
  have hπLeft :
      (PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val) ≫
            (PresheafOfModules.toPresheaf O.obj).map
              (adj.unit.app (cokernel φ.val)) ≫
          (PresheafOfModules.toPresheaf O.obj).map
            ((SheafOfModules.forget O).map e.inv) =
        (PresheafOfModules.toPresheaf O.obj).map
          ((cokernel.π φ.val ≫ adj.unit.app (cokernel φ.val)) ≫
            (SheafOfModules.forget O ⋙
              PresheafOfModules.restrictScalars (𝟙 O.obj)).map e.inv) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hRestrE]
    rfl
  exact hπLeft.trans (hπMidP.trans (hRight.trans hFinalAdd))

theorem sheafModuleCokernel_stalk_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (x : X) :
    Nonempty ((sheafModuleStalkFunctor O x).obj (sheafModuleCokernel O φ) ≅
      cokernel ((sheafModuleStalkFunctor O x).map φ)) := by
  let cP₀ : CokernelCofork
      ((PresheafOfModules.toPresheaf O.obj).map φ.val) :=
    CokernelCofork.ofπ
      ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) (by
        rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])
  have hcP₀ : IsColimit cP₀ := by
    exact (CokernelCofork.isColimitMapCoconeEquiv
      (CokernelCofork.ofπ (cokernel.π φ.val) (cokernel.condition φ.val))
      (PresheafOfModules.toPresheaf O.obj)).1
      (isColimitOfPreserves (PresheafOfModules.toPresheaf O.obj)
        (cokernelIsCokernel φ.val))
  let stalk :=
    TopCat.Presheaf.stalkFunctor (X := X) (C := AddCommGrpCat) x
  let : stalk.PreservesZeroMorphisms := by
    refine { map_zero := ?_ }
    intro A B
    ext z
    simp
  let cStalk := cP₀.map stalk
  have hcStalk : IsColimit cStalk := by
    exact (CokernelCofork.isColimitMapCoconeEquiv cP₀ stalk).1
      (isColimitOfPreserves stalk hcP₀)
  let L := PresheafOfModules.sheafification (R₀ := O.obj) (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := O.obj) (R := O) (𝟙 O.obj)
  let hF : IsIso (adj.counit.app F) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (R₀ := O.obj) (R := O) (𝟙 O.obj)).counit.app F)
    infer_instance
  let hG : IsIso (adj.counit.app G) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (R₀ := O.obj) (R := O) (𝟙 O.obj)).counit.app G)
    infer_instance
  let eF : L.obj F.val ≅ F := @asIso _ _ _ _ (adj.counit.app F) hF
  let eG : L.obj G.val ≅ G := @asIso _ _ _ _ (adj.counit.app G) hG
  have hNat : L.map φ.val ≫ eG.hom = eF.hom ≫ φ := by
    change L.map φ.val ≫ (adj.counit.app G) = (adj.counit.app F) ≫ φ
    exact adj.counit.naturality φ
  let m := cokernel.mapIso (L.map φ.val) φ eF eG hNat
  let e : sheafModuleCokernel O φ ≅ sheafModuleCokernelSheafification O φ :=
    (PreservesCokernel.iso L φ.val ≪≫ m).symm
  let u := CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (sheafModuleCokernelPresheaf O φ).presheaf
  let : IsIso (stalk.map u) := by
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      (p₀ := x) (C := AddCommGrpCat)
        (𝓕 := (sheafModuleCokernelPresheaf O φ).presheaf)
  let eStalk := stalk.mapIso
    ((CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso
      ((SheafOfModules.toSheaf O).mapIso e))
  let eAdd : cStalk.pt ≅
      stalk.obj
        ((CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
          ((SheafOfModules.toSheaf O).obj (sheafModuleCokernel O φ))) := by
    change stalk.obj (sheafModuleCokernelPresheaf O φ).presheaf ≅ _
    exact asIso (stalk.map u) ≪≫ eStalk.symm
  let cStalk' : CokernelCofork
      (stalk.map ((PresheafOfModules.toPresheaf O.obj).map φ.val)) :=
    CokernelCofork.ofπ
      (cStalk.π ≫ eAdd.hom)
      (by
        rw [← Category.assoc, cStalk.condition, zero_comp])
  have hcStalk' : IsColimit cStalk' := by
    refine CokernelCofork.IsColimit.ofπ _ _
      (fun {_} q hq => by
        exact eAdd.inv ≫ hcStalk.desc
          (CokernelCofork.ofπ q hq)) ?_ ?_
    · intro Z' q hq
      change (cStalk.π ≫ eAdd.hom) ≫
          (eAdd.inv ≫ hcStalk.desc (CokernelCofork.ofπ q hq)) = q
      calc
        _ = cStalk.π ≫ hcStalk.desc (CokernelCofork.ofπ q hq) := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
        _ = q := by
          change cStalk.ι.app WalkingParallelPair.one ≫
            hcStalk.desc (CokernelCofork.ofπ q hq) = q
          exact hcStalk.fac (CokernelCofork.ofπ q hq) WalkingParallelPair.one
    · intro Z' q hq m hm
      apply (cancel_epi eAdd.hom).1
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      apply Cofork.IsColimit.hom_ext hcStalk
      calc
        _ = (cStalk.π ≫ eAdd.hom) ≫ m := by simp only [Category.assoc]
        _ = q := hm
        _ = cStalk.π ≫ hcStalk.desc (CokernelCofork.ofπ q hq) := by
          calc
            q = (CokernelCofork.ofπ q hq).ι.app WalkingParallelPair.one := by rfl
            _ = cStalk.ι.app WalkingParallelPair.one ≫
                hcStalk.desc (CokernelCofork.ofπ q hq) :=
              (hcStalk.fac (CokernelCofork.ofπ q hq) WalkingParallelPair.one).symm
            _ = cStalk.π ≫ hcStalk.desc (CokernelCofork.ofπ q hq) := by rfl
  refine ⟨?_⟩
  let forgetStalk :=
    forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x)) AddCommGrpCat
  let cTargetAdd := forgetStalk.mapCocone
    ((sheafModuleStalkFunctor O x).mapCocone
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ)))
  let e₀ :
      forgetStalk.obj ((sheafModuleStalkFunctor O x).obj F) ≅
        stalk.obj ((PresheafOfModules.toPresheaf O.obj).obj F.val) := by
    refine
      { hom := AddCommGrpCat.ofHom (AddMonoidHom.id _)
        inv := AddCommGrpCat.ofHom (AddMonoidHom.id _)
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · ext z
      rfl
    · ext z
      rfl
  let e₁ :
      forgetStalk.obj ((sheafModuleStalkFunctor O x).obj G) ≅
        stalk.obj ((PresheafOfModules.toPresheaf O.obj).obj G.val) := by
    refine
      { hom := AddCommGrpCat.ofHom (AddMonoidHom.id _)
        inv := AddCommGrpCat.ofHom (AddMonoidHom.id _)
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · ext z
      rfl
    · ext z
      rfl
  have comm1 :
      forgetStalk.map ((sheafModuleStalkFunctor O x).map φ) ≫ e₁.hom =
        e₀.hom ≫ stalk.map ((PresheafOfModules.toPresheaf O.obj).map φ.val) := by
    rfl
  have comm2 :
      forgetStalk.map ((sheafModuleStalkFunctor O x).map (0 : F ⟶ G)) ≫ e₁.hom =
        e₀.hom ≫ (0 : stalk.obj ((PresheafOfModules.toPresheaf O.obj).obj F.val) ⟶
          stalk.obj ((PresheafOfModules.toPresheaf O.obj).obj G.val)) := by
    simp only [Functor.map_zero, zero_comp, comp_zero]
  let ePair :
      ((parallelPair φ 0 ⋙ sheafModuleStalkFunctor O x) ⋙ forgetStalk) ≅
        parallelPair (stalk.map ((PresheafOfModules.toPresheaf O.obj).map φ.val)) 0 :=
    parallelPair.ext e₀ e₁ comm1 comm2
  have hproj :
      (L.map (cokernel.π φ.val) ≫
          (PreservesCokernel.iso L φ.val).hom) ≫
        m.hom =
      eG.hom ≫ cokernel.π φ := by
    dsimp [m]
    rw [PreservesCokernel.π_iso_hom]
    simp [cokernel.map]
  have hπ := sheafModuleCokernel_stalk_hπ O φ adj rfl eG rfl m e rfl hproj
  have comm3 :
      ePair.inv.app WalkingParallelPair.one ≫ cTargetAdd.ι.app WalkingParallelPair.one =
        cStalk'.ι.app WalkingParallelPair.one := by
    dsimp [ePair, cTargetAdd, cStalk', eAdd, eStalk, u]
    change e₁.inv ≫ forgetStalk.map ((sheafModuleStalkFunctor O x).map (cokernel.π φ)) =
      stalk.map ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) ≫
        stalk.map (toSheafify (Opens.grothendieckTopology X)
          ((PresheafOfModules.toPresheaf O.obj).obj (cokernel φ.val))) ≫
        stalk.map ((PresheafOfModules.toPresheaf O.obj).map
          ((SheafOfModules.forget O).map e.inv))
    have hleft :
        e₁.inv ≫ forgetStalk.map ((sheafModuleStalkFunctor O x).map (cokernel.π φ)) =
          stalk.map ((PresheafOfModules.toPresheaf O.obj).map
            ((SheafOfModules.forget O).map (cokernel.π φ))) := by
      dsimp [e₁]
      ext z
      rfl
    rw [hleft]
    have hπStalk := congrArg stalk.map hπ
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app] at hπStalk
    simp only [Functor.map_comp] at hπStalk
    exact hπStalk.symm.trans (congrArg
      (fun q => stalk.map ((PresheafOfModules.toPresheaf O.obj).map
        (cokernel.π φ.val)) ≫ q) (stalk.map_comp _ _))
  let pointIso : ((Cocone.precompose ePair.inv).obj cTargetAdd).pt ≅ cStalk'.pt :=
    Iso.refl _
  let w : (Cocone.precompose ePair.inv).obj cTargetAdd ≅ cStalk' :=
    Cocone.ext pointIso (by
      intro j
      cases j
      · simp [cTargetAdd, cStalk']
      · dsimp [Cocone.precompose, pointIso]
        exact comm3)
  have hAdd : IsColimit cTargetAdd := by
    exact (IsColimit.equivOfNatIsoOfIso ePair cTargetAdd cStalk' w).symm hcStalk'
  let cTargetComp :=
    (sheafModuleStalkFunctor O x ⋙ forgetStalk).mapCocone
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ))
  let targetIso : cTargetComp ≅ cTargetAdd :=
    Cocone.ext (Iso.refl _) (by
      intro j
      rfl)
  have hComp : IsColimit cTargetComp := by
    exact hAdd.ofIsoColimit targetIso.symm
  letI : PreservesColimit (parallelPair φ 0)
      (sheafModuleStalkFunctor O x ⋙ forgetStalk) := by
    exact preservesColimit_of_preserves_colimit_cocone
      (K := parallelPair φ 0)
      (F := sheafModuleStalkFunctor O x ⋙ forgetStalk)
      (cokernelIsCokernel φ) hComp
  letI : PreservesColimit (parallelPair φ 0) (sheafModuleStalkFunctor O x) := by
    exact preservesColimit_of_reflects_of_preserves
      (K := parallelPair φ 0)
      (F := sheafModuleStalkFunctor O x)
      (G := forgetStalk)
  exact PreservesCokernel.iso (sheafModuleStalkFunctor O x) φ

theorem sheafModuleCokernel_universal {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) :
    Nonempty (IsColimit
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ))) := by
  exact ⟨cokernelIsCokernel φ⟩

theorem sheafModuleCokernel_factorization {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G H : Mod O} (φ : F ⟶ G) (β : G ⟶ H) (hβ : φ ≫ β = 0) :
    ∃! γ : sheafModuleCokernel O φ ⟶ H, cokernel.π φ ≫ γ = β := by
  refine ⟨cokernel.desc φ β hβ, cokernel.π_desc φ β hβ, ?_⟩
  intro γ hγ
  apply (cancel_epi (cokernel.π φ)).1
  rw [hγ, cokernel.π_desc]

/-- Categorical local surjectivity is the sheaf-of-sets surjectivity used in
the source for the map into a cokernel. -/
theorem sheafModuleCokernel_π_locallySurjective {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {F G : Mod O} (φ : F ⟶ G) :
    PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology X) (cokernel.π φ).val := by
  let L := PresheafOfModules.sheafification (R₀ := O.obj) (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := O.obj) (R := O) (𝟙 O.obj)
  let hF : IsIso (adj.counit.app F) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (R₀ := O.obj) (R := O) (𝟙 O.obj)).counit.app F)
    infer_instance
  let hG : IsIso (adj.counit.app G) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (R₀ := O.obj) (R := O) (𝟙 O.obj)).counit.app G)
    infer_instance
  let eF : L.obj F.val ≅ F := @asIso _ _ _ _ (adj.counit.app F) hF
  let eG : L.obj G.val ≅ G := @asIso _ _ _ _ (adj.counit.app G) hG
  have hNat : L.map φ.val ≫ eG.hom = eF.hom ≫ φ := by
    change L.map φ.val ≫ (adj.counit.app G) = (adj.counit.app F) ≫ φ
    exact adj.counit.naturality φ
  let m := cokernel.mapIso (L.map φ.val) φ eF eG hNat
  let e : sheafModuleCokernel O φ ≅ sheafModuleCokernelSheafification O φ :=
    (PreservesCokernel.iso L φ.val ≪≫ m).symm
  have hproj :
      (L.map (cokernel.π φ.val) ≫
          (PreservesCokernel.iso L φ.val).hom) ≫ m.hom =
        eG.hom ≫ cokernel.π φ := by
    dsimp [m]
    rw [PreservesCokernel.π_iso_hom]
    simp [cokernel.map]
  have hπ := sheafModuleCokernel_stalk_hπ O φ adj rfl eG rfl m e rfl hproj
  have hπPresheaf :
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) := by
    let eπ := PreservesCokernel.iso (PresheafOfModules.toPresheaf O.obj) φ.val
    haveI : Epi (cokernel.π
        ((PresheafOfModules.toPresheaf O.obj).map φ.val)) := inferInstance
    haveI : Epi ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) := by
      apply (epi_comp_iff_of_isIso
        ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) eπ.hom).1
      rw [PreservesCokernel.π_iso_hom]
      infer_instance
    apply Presheaf.isLocallySurjective_of_surjective _
    intro U
    rw [← AddCommGrpCat.epi_iff_surjective]
    exact (NatTrans.epi_iff_epi_app _).1 inferInstance U
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) := hπPresheaf
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O.obj).map
        (adj.unit.app (cokernel φ.val))) := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (R₀ := O.obj) (R := O) (𝟙 O.obj)).unit.app (cokernel φ.val)))
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (Opens.grothendieckTopology X).W_toSheafify
      (cokernel φ.val).presheaf |>.isLocallySurjective
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O.obj).map
        ((SheafOfModules.forget O).map e.inv)) := by
    infer_instance
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf O.obj).map
      ((SheafOfModules.forget O).map (cokernel.π φ)))
  rw [← hπ]
  let f := (PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)
  let u := (PresheafOfModules.toPresheaf O.obj).map
    (adj.unit.app (cokernel φ.val))
  let e' := (PresheafOfModules.toPresheaf O.obj).map
    ((SheafOfModules.forget O).map e.inv)
  have hfu : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (f ≫ u) := by
    exact Presheaf.isLocallySurjective_comp (J := Opens.grothendieckTopology X) f u
  have he' : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e' := by
    exact this
  dsimp [e'] at he' ⊢
  exact @Presheaf.isLocallySurjective_comp
    (Opens X) inferInstance (Opens.grothendieckTopology X)
    (AddCommGrpCat.{v}) inferInstance _ _ inferInstance inferInstance
    _ _ _ (f ≫ u)
      ((PresheafOfModules.toPresheaf O.obj).map
        ((SheafOfModules.forget O).map e.inv)) hfu he'
/-
  let L := PresheafOfModules.sheafification (R₀ := O.obj) (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := O.obj) (R := O) (𝟙 O.obj)
  let hF : IsIso (adj.counit.app F) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (R₀ := O.obj) (R := O) (𝟙 O.obj)).counit.app F)
    infer_instance
  let hG : IsIso (adj.counit.app G) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (R₀ := O.obj) (R := O) (𝟙 O.obj)).counit.app G)
    infer_instance
  let eF : L.obj F.val ≅ F := @asIso _ _ _ _ (adj.counit.app F) hF
  let eG : L.obj G.val ≅ G := @asIso _ _ _ _ (adj.counit.app G) hG
  have hNat : L.map φ.val ≫ eG.hom = eF.hom ≫ φ := by
    change L.map φ.val ≫ (adj.counit.app G) = (adj.counit.app F) ≫ φ
    exact adj.counit.naturality φ
  let m := cokernel.mapIso (L.map φ.val) φ eF eG hNat
  let e : sheafModuleCokernel O φ ≅ sheafModuleCokernelSheafification O φ :=
    (PreservesCokernel.iso L φ.val ≪≫ m).symm
  have hproj :
      (L.map (cokernel.π φ.val) ≫
          (PreservesCokernel.iso L φ.val).hom) ≫ m.hom =
        eG.hom ≫ cokernel.π φ := by
    dsimp [m]
    rw [PreservesCokernel.π_iso_hom]
    simp [cokernel.map]
  have hπ := sheafModuleCokernel_stalk_hπ O φ adj rfl eG rfl m e rfl hproj
  have hπPresheaf :
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) := by
    let eπ := PreservesCokernel.iso (PresheafOfModules.toPresheaf O.obj) φ.val
    haveI : Epi (cokernel.π
        ((PresheafOfModules.toPresheaf O.obj).map φ.val)) := inferInstance
    haveI : Epi ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) := by
      apply (epi_comp_iff_of_isIso
        ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) eπ.hom).2
      rw [PreservesCokernel.π_iso_hom]
      infer_instance
    apply Presheaf.isLocallySurjective_of_surjective _
    intro U
    rw [← epi_iff_surjective]
    exact (NatTrans.epi_iff_epi_app _).1 inferInstance U
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O.obj).map (cokernel.π φ.val)) := hπPresheaf
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O.obj).map
        (adj.unit.app (cokernel φ.val))) := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (R₀ := O.obj) (R := O) (𝟙 O.obj)).unit.app (cokernel φ.val)))
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (Opens.grothendieckTopology X).W_toSheafify
      (cokernel φ.val).presheaf |>.isLocallySurjective
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf O.obj).map
        ((SheafOfModules.forget O).map e.inv)) := by
    infer_instance
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf O.obj).map
      ((SheafOfModules.forget O).map (cokernel.π φ)))
  rw [← hπ]
  infer_instance

-/
/-! ## Abelian structure and exactness on stalks -/

theorem sheafModule_abelian {X : TopCat.{v}} (O : RingSheaf.{v, v} X) :
    Nonempty (Abelian (Mod O)) :=
  ⟨inferInstance⟩

abbrev sheafModuleShortComplex {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G H : Mod O} (f : F ⟶ G) (g : G ⟶ H) (h : f ≫ g = 0) :
    ShortComplex (Mod O) :=
  ShortComplex.mk f g h

theorem sheafModule_exact_iff_stalkwise {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G H : Mod O} (f : F ⟶ G) (g : G ⟶ H) (h : f ≫ g = 0) :
    (sheafModuleShortComplex O f g h).Exact ↔
      ∀ x : X, ((sheafModuleShortComplex O f g h).map
        (sheafModuleStalkFunctor O x)).Exact := by
  let stalkPreservesHomology (x : X) :
      (sheafModuleStalkFunctor O x).PreservesHomology := by
    let : PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat) := by
      infer_instance
    let : PreservesLimits (CategoryTheory.forget AddCommGrpCat) := by
      infer_instance
    let : PreservesFiniteLimits (SheafOfModules.toSheaf O) := by
      infer_instance
    let : PreservesFiniteLimits
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) := by
      have hH_homology :
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).PreservesHomology := by
        simp only [(TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).exact_tfae.out 2 0]
        intro S hS
        let hcolim := ((TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).preservesFiniteColimits_tfae.out
            3 0).mp
          (inferInstance : PreservesFiniteColimits
            (TopCat.Sheaf.forget AddCommGrpCat X ⋙
              TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x))
        refine ShortComplex.ShortExact.mk' (hcolim S hS).left ?_ (hcolim S hS).right
        have := hS.2
        exact Functor.map_mono
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) _
      exact (TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).preservesFiniteLimits_of_preservesHomology
    letI : PreservesFiniteLimits
        (sheafModuleStalkFunctor O x ⋙
          forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
            AddCommGrpCat) := by
      change PreservesFiniteLimits
        (SheafOfModules.toSheaf O ⋙
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x))
      refine ⟨fun J _ _ => ?_⟩
      let : PreservesLimitsOfShape J (SheafOfModules.toSheaf O) := by
        exact PreservesFiniteLimits.preservesFiniteLimits J
      let : PreservesLimitsOfShape J
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) := by
        exact PreservesFiniteLimits.preservesFiniteLimits J
      have hF : PreservesLimitsOfShape J (SheafOfModules.toSheaf O) :=
        PreservesFiniteLimits.preservesFiniteLimits J
      have hG : PreservesLimitsOfShape J
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) :=
        PreservesFiniteLimits.preservesFiniteLimits J
      exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
        (SheafOfModules.toSheaf O)
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x)
        hF hG
    letI : PreservesFiniteLimits (sheafModuleStalkFunctor O x) := by
      apply preservesFiniteLimits_of_reflects_of_preserves
        (sheafModuleStalkFunctor O x)
        (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
          AddCommGrpCat)
    letI : Functor.IsLeftAdjoint (sheafModuleStalkFunctor O x) :=
      (Classical.choice
        (Formalization.Books.Sheaves.Unit22.exists_moduleStalkSkyscraperAdjunction
          O x)).isLeftAdjoint
    infer_instance
  constructor
  · intro hS x
    letI : (sheafModuleStalkFunctor O x).PreservesHomology :=
      stalkPreservesHomology x
    exact hS.map (sheafModuleStalkFunctor O x)
  · intro hS
    have hq_stalk (x : X) :
        (sheafModuleStalkFunctor O x).map
            (kernel.ι g ≫ cokernel.π f) = 0 := by
      letI : (sheafModuleStalkFunctor O x).PreservesHomology :=
        stalkPreservesHomology x
      letI : PreservesLimit (parallelPair g 0)
          (sheafModuleStalkFunctor O x) :=
        Functor.PreservesHomology.preservesKernel
          (sheafModuleStalkFunctor O x) g
      letI : PreservesColimit (parallelPair f 0)
          (sheafModuleStalkFunctor O x) :=
        Functor.PreservesHomology.preservesCokernel
          (sheafModuleStalkFunctor O x) f
      let eK := PreservesKernel.iso (sheafModuleStalkFunctor O x) g
      let eC := PreservesCokernel.iso (sheafModuleStalkFunctor O x) f
      have hzero :=
        (ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero
          (S := (sheafModuleShortComplex O f g h).map
            (sheafModuleStalkFunctor O x))).1 (hS x)
      have hrel :
          eK.inv ≫ (sheafModuleStalkFunctor O x).map
              (kernel.ι g ≫ cokernel.π f) ≫ eC.hom =
            kernel.ι ((sheafModuleStalkFunctor O x).map g) ≫
              cokernel.π ((sheafModuleStalkFunctor O x).map f) := by
        dsimp [eK, eC]
        simp only [Functor.map_comp, Category.assoc,
          PreservesKernel.iso_inv_ι, PreservesKernel.iso_inv_ι_assoc,
          PreservesCokernel.π_iso_hom]
      apply (cancel_mono eC.hom).1
      apply (cancel_epi eK.inv).1
      rw [hrel]
      simp only [Functor.map_zero, zero_comp, comp_zero]
      exact hzero
    rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    apply (SheafOfModules.toSheaf O).map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro s
    apply TopCat.Presheaf.section_ext _ _
    intro x hx
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
      ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
      AddCommGrpCat).map
        ((sheafModuleStalkFunctor O x).map (kernel.ι g ≫ cokernel.π f)) _ = _
    rw [hq_stalk x]
    have hz :
        ((SheafOfModules.toSheaf O).map
          (0 : kernel (sheafModuleShortComplex O f g h).g ⟶
            cokernel (sheafModuleShortComplex O f g h).f)).hom = 0 := by
      apply NatTrans.ext
      funext U
      rfl
    rw [hz]
    simp only [Functor.map_zero, AddCommGrpCat.hom_zero]
    rfl
/-
  let stalkPreservesHomology (x : X) :
      (sheafModuleStalkFunctor O x).PreservesHomology := by
    let : PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat) := by
      infer_instance
    let : PreservesLimits (CategoryTheory.forget AddCommGrpCat) := by
      infer_instance
    let : PreservesFiniteLimits (SheafOfModules.toSheaf O) := by
      infer_instance
    let : PreservesFiniteLimits
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) := by
      have hH_homology :
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).PreservesHomology := by
        simp only [(TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).exact_tfae.out 2 0]
        intro S hS
        have hcolim := ((TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).preservesFiniteColimits_tfae.out
            3 0).mp
          (inferInstance : PreservesFiniteColimits
            (TopCat.Sheaf.forget AddCommGrpCat X ⋙
              TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x))
        refine ShortComplex.ShortExact.mk' (hcolim S hS).left ?_ (hcolim S hS).right
        have := hS.2
        exact Functor.map_mono
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) _
      exact (TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x).preservesFiniteLimits_of_preservesHomology
    letI : PreservesFiniteLimits
        (sheafModuleStalkFunctor O x ⋙
          forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
            AddCommGrpCat) := by
      change PreservesFiniteLimits
        (SheafOfModules.toSheaf O ⋙
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x))
      refine ⟨fun J _ _ => ?_⟩
      let : PreservesLimitsOfShape J (SheafOfModules.toSheaf O) := by
        exact PreservesFiniteLimits.preservesFiniteLimits J
      let : PreservesLimitsOfShape J
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) := by
        exact PreservesFiniteLimits.preservesFiniteLimits J
      have hF : PreservesLimitsOfShape J (SheafOfModules.toSheaf O) :=
        PreservesFiniteLimits.preservesFiniteLimits J
      have hG : PreservesLimitsOfShape J
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x) :=
        PreservesFiniteLimits.preservesFiniteLimits J
      exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
        (SheafOfModules.toSheaf O)
        (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x)
        hF hG
    letI : PreservesFiniteLimits (sheafModuleStalkFunctor O x) := by
      apply preservesFiniteLimits_of_reflects_of_preserves
        (sheafModuleStalkFunctor O x)
        (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
          AddCommGrpCat)
    letI : IsLeftAdjoint (sheafModuleStalkFunctor O x) :=
      (Classical.choice
        (Formalization.Books.Sheaves.Unit22.exists_moduleStalkSkyscraperAdjunction
          O x)).isLeftAdjoint
    infer_instance
  constructor
  · intro hS x
    letI : (sheafModuleStalkFunctor O x).PreservesHomology :=
      stalkPreservesHomology x
    exact hS.map (sheafModuleStalkFunctor O x)
  · intro hS
    have hq_stalk (x : X) :
        (sheafModuleStalkFunctor O x).map
            (kernel.ι g ≫ cokernel.π f) = 0 := by
      letI : (sheafModuleStalkFunctor O x).PreservesHomology :=
        stalkPreservesHomology x
      letI : PreservesLimit (parallelPair g 0)
          (sheafModuleStalkFunctor O x) :=
        Functor.PreservesHomology.preservesKernel g
      letI : PreservesColimit (parallelPair f 0)
          (sheafModuleStalkFunctor O x) :=
        Functor.PreservesHomology.preservesCokernel f
      let eK := PreservesKernel.iso (sheafModuleStalkFunctor O x) g
      let eC := PreservesCokernel.iso (sheafModuleStalkFunctor O x) f
      have hzero :=
        (ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero
          (S := (sheafModuleShortComplex O f g h).map
            (sheafModuleStalkFunctor O x))).1 (hS x)
      have hrel :
          eK.inv ≫ (sheafModuleStalkFunctor O x).map
              (kernel.ι g ≫ cokernel.π f) ≫ eC.hom =
            kernel.ι ((sheafModuleStalkFunctor O x).map g) ≫
              cokernel.π ((sheafModuleStalkFunctor O x).map f) := by
        dsimp [eK, eC]
        simp only [Functor.map_comp, Category.assoc,
          PreservesKernel.iso_inv_ι, PreservesCokernel.π_iso_hom]
      apply (cancel_mono eC.hom).1
      apply (cancel_epi eK.inv).1
      rw [hrel, hzero, zero_comp]
    rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    apply (SheafOfModules.toSheaf O).map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro s
    apply TopCat.Presheaf.section_ext _ _
    intro x hx
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
      ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
      AddCommGrpCat).map
        ((sheafModuleStalkFunctor O x).map (kernel.ι g ≫ cokernel.π f)) _ = _
    rw [hq_stalk x]
    simp

-/
/-! ## Products, coproducts, limits, and colimits -/

noncomputable abbrev sheafModuleProduct {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {I : Type v} (F : I → Mod O) : Mod O :=
  limit (Discrete.functor F)

abbrev sheafModuleProductProjection {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {I : Type v} (F : I → Mod O) (i : I) :
    sheafModuleProduct O F ⟶ F i :=
  limit.π (Discrete.functor F) ⟨i⟩

theorem sheafModuleProduct_isLimit {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {I : Type v} (F : I → Mod O) :
    Nonempty (IsLimit (limit.cone (Discrete.functor F))) := by
  exact ⟨limit.isLimit _⟩

theorem sheafModuleProduct_sections {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {I : Type v} (F : I → Mod O) (U : Opens X) :
    Nonempty (sheafModuleSections O (sheafModuleProduct O F) U ≅
      limit (Discrete.functor (fun i => sheafModuleSections O (F i) U))) := by
  exact ⟨by
    change (SheafOfModules.evaluation O (op U)).obj (limit (Discrete.functor F)) ≅
      limit (Discrete.functor (fun i =>
        (SheafOfModules.evaluation O (op U)).obj (F i)))
    have hD : Discrete.functor F ⋙ SheafOfModules.evaluation O (op U) =
        Discrete.functor (fun i =>
          (SheafOfModules.evaluation O (op U)).obj (F i)) := by
      refine CategoryTheory.Functor.ext (fun i => rfl) ?_
      intro i Y f
      cases i with
      | mk i =>
        cases Y with
        | mk Y =>
          cases f
          simp [Discrete.functor, eqToHom_map]
    rw [← hD]
    exact preservesLimitIso (SheafOfModules.evaluation O (op U))
      (Discrete.functor F)⟩
/-
  exact ⟨by
    simpa [sheafModuleProduct, sheafModuleSections] using
      (limitObjIsoLimitCompEvaluation (Discrete.functor F) (op U))⟩

-/
noncomputable abbrev sheafModuleCoproduct {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {I : Type v} (F : I → Mod O) : Mod O :=
  colimit (Discrete.functor F)

abbrev sheafModuleCoproductInjection {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {I : Type v} (F : I → Mod O) (i : I) :
    F i ⟶ sheafModuleCoproduct O F :=
  colimit.ι (Discrete.functor F) ⟨i⟩

theorem sheafModuleCoproduct_isColimit {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {I : Type v} (F : I → Mod O) :
    Nonempty (IsColimit (colimit.cocone (Discrete.functor F))) := by
  exact ⟨colimit.isColimit _⟩

noncomputable abbrev sheafModulePresheafLimit {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {J : Type v} [Category.{v} J] (D : J ⥤ Mod O) :
    PresheafOfModules O.obj :=
  limit (D ⋙ SheafOfModules.forget O)

theorem sheafModule_limit_presheaf_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {J : Type v} [Category.{v} J] (D : J ⥤ Mod O) :
    Nonempty ((limit D).val ≅ sheafModulePresheafLimit O D) := by
  exact ⟨preservesLimitIso (SheafOfModules.forget O) D⟩

noncomputable abbrev sheafModulePresheafColimit {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {J : Type v} [Category.{v} J] (D : J ⥤ Mod O) :
    PresheafOfModules O.obj :=
  colimit (D ⋙ SheafOfModules.forget O)

noncomputable abbrev sheafModuleColimitSheafification {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {J : Type v} [Category.{v} J] (D : J ⥤ Mod O) : Mod O :=
  (PresheafOfModules.sheafification (R₀ := O.obj) (𝟙 O.obj)).obj
    (sheafModulePresheafColimit O D)

theorem sheafModule_colimit_sheafification_iso {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {J : Type v} [Category.{v} J] (D : J ⥤ Mod O) :
    Nonempty (colimit D ≅ sheafModuleColimitSheafification O D) := by
  sorry

theorem sheafModule_colimit_stalk_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {J : Type v} [Category.{v} J] (D : J ⥤ Mod O) (x : X) :
    Nonempty ((sheafModuleStalkFunctor O x).obj (colimit D) ≅
      colimit (D ⋙ sheafModuleStalkFunctor O x)) := by
  sorry

theorem sheafModule_hasLimits {X : TopCat.{v}} (O : RingSheaf.{v, v} X) :
    HasLimitsOfSize.{v, v} (Mod O) := by
  infer_instance

theorem sheafModule_limits_commute_with_presheaf {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) :
    PreservesLimitsOfSize.{v, v} (SheafOfModules.forget.{v} O) := by
  infer_instance

theorem sheafModule_sections_preserve_limits {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) (U : Opens X) :
    PreservesLimitsOfSize.{v, v} (SheafOfModules.evaluation.{v} O (op U)) := by
  infer_instance

theorem sheafModule_hasColimits {X : TopCat.{v}} (O : RingSheaf.{v, v} X) :
    HasColimitsOfSize.{v, v} (Mod O) := by
  infer_instance

theorem sheafModule_hasExactFilteredColimits {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {J : Type v} [Category.{v} J] [IsFiltered J] :
    HasExactColimitsOfShape J (Mod O) := by
  sorry

theorem sheafModule_finite_direct_sums_are_presheaf_direct_sums
    {X : TopCat.{v}} (O : RingSheaf.{v, v} X) {I : Type v} [Finite I]
    (F : I → Mod O) :
    Nonempty ((sheafModuleCoproduct O F).val ≅
      colimit (Discrete.functor (fun i => (F i).val))) := by
  sorry

/-! The module functors attached to a ringed-space morphism use the canonical
constructions from the earlier sheaves chapter, with the source's names
retained for later Modules chapters. -/

noncomputable abbrev sheafModuleRingedSpacePushforward
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Mod X.structureSheaf ⥤ Mod Y.structureSheaf :=
  ringedSpaceModulePushforward f

noncomputable abbrev sheafModuleRingedSpacePullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    Mod Y.structureSheaf ⥤ Mod X.structureSheaf :=
  ringedSpaceModulePullback f

/-! ## Exactness of the standard geometric functors -/

theorem sheafModuleRingedSpacePushforward_isLeftExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    IsLeftExact (sheafModuleRingedSpacePushforward f) := by
  sorry

theorem sheafModuleRingedSpacePushforward_preserves_all_limits
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    PreservesLimitsOfSize.{v, v} (sheafModuleRingedSpacePushforward f) := by
  sorry

theorem sheafModuleRingedSpacePullback_isRightExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    IsRightExact (sheafModuleRingedSpacePullback f) := by
  sorry

theorem sheafModuleRingedSpacePullback_preserves_all_colimits
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    PreservesColimitsOfSize.{v, v} (sheafModuleRingedSpacePullback f) := by
  sorry

theorem abelianSheafPullback_isExact {X Y : TopCat.{v}} (f : X ⟶ Y) :
    IsExact (abelianSheafPullback f) := by
  sorry

theorem unit03OpenAbelianSheafExtension_isExact {X : TopCat.{v}}
    (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    IsExact (openAbelianSheafExtensionFunctor U) := by
  sorry

/-! ## Sections of arbitrary direct sums on quasi-compact opens -/

noncomputable def sheafModuleSectionsDirectSumMap {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {I : Type v} (F : I → Mod O) (U : Opens X) :
    colimit (Discrete.functor (fun i => sheafModuleSections O (F i) U)) ⟶
      sheafModuleSections O (sheafModuleCoproduct O F) U :=
  colimit.desc _ (Cofan.mk _ fun i =>
    (SheafOfModules.evaluation O (op U)).map
      (sheafModuleCoproductInjection O F i))

theorem sheafModuleSectionsDirectSumMap_bijective {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {I : Type v} (F : I → Mod O) (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    Function.Bijective (sheafModuleSectionsDirectSumMap O F U).hom := by
  sorry

end

end Formalization.Books.Modules.Unit03
