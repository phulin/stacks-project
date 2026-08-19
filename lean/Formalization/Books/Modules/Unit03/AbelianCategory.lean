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
  sorry

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
  sorry

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
  sorry

theorem sheafModuleKernel_section_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (U : Opens X) :
    Nonempty (sheafModuleSections O (sheafModuleKernel O φ) U ≅
      kernel (sheafModuleSectionsMap O φ U)) := by
  exact ⟨PreservesKernel.iso (SheafOfModules.evaluation O (op U)) φ⟩

theorem sheafModuleKernel_stalk_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (x : X) :
    Nonempty ((sheafModuleStalkFunctor O x).obj (sheafModuleKernel O φ) ≅
      kernel ((sheafModuleStalkFunctor O x).map φ)) := by
  sorry

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
  sorry

theorem sheafModuleCokernel_section_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (U : Opens X) :
    Nonempty ((sheafModuleCokernelPresheaf O φ).obj (op U) ≅
      cokernel (sheafModuleSectionsMap O φ U)) := by
  exact ⟨PreservesCokernel.iso (PresheafOfModules.evaluation O.obj (op U)) φ.val⟩

theorem sheafModuleCokernel_stalk_iso {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) (x : X) :
    Nonempty ((sheafModuleStalkFunctor O x).obj (sheafModuleCokernel O φ) ≅
      cokernel ((sheafModuleStalkFunctor O x).map φ)) := by
  sorry

theorem sheafModuleCokernel_universal {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G : Mod O} (φ : F ⟶ G) :
    Nonempty (IsColimit
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ))) := by
  sorry

theorem sheafModuleCokernel_factorization {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    {F G H : Mod O} (φ : F ⟶ G) (β : G ⟶ H) (hβ : φ ≫ β = 0) :
    ∃! γ : sheafModuleCokernel O φ ⟶ H, cokernel.π φ ≫ γ = β := by
  sorry

/-- Categorical local surjectivity is the sheaf-of-sets surjectivity used in
the source for the map into a cokernel. -/
theorem sheafModuleCokernel_π_locallySurjective {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) {F G : Mod O} (φ : F ⟶ G) :
    PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology X) (cokernel.π φ).val := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
