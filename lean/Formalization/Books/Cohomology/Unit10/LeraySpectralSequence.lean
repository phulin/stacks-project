import Formalization.Books.Cohomology.Unit09
import Formalization.Books.Derived.Unit22

/-!
# Cohomology of Sheaves, Chapter 10: the Leray spectral sequence

This file records the comparison, module/abelian, Leray, degeneration, and
composition statements in the source section.  The spectral-sequence data
reuse the filtered-complex Grothendieck interface from Derived Categories.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit07
open Formalization.Books.Cohomology.Unit09
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Derived.Unit22
open Formalization.Books.Homology.Unit24
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v u

namespace Formalization.Books.Cohomology.Unit10

/-! ## Before the Leray spectral sequence -/

/-- The additive group underlying a module-valued cohomology object. -/
noncomputable abbrev moduleCohomologyAsAbelian
    {R : Type v} [Ring R] (M : ModuleCat.{v} R) : AddCommGrpCat.{v} :=
  (forget₂ (ModuleCat.{v} R) AddCommGrpCat).obj M

/-- The underlying abelian sheaf of a sheaf of modules. -/
noncomputable abbrev moduleSheafAsAbelian
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    TopCat.Sheaf AddCommGrpCat.{v} X.carrier :=
  ⟨F.val.presheaf, F.isSheaf⟩

/-- Restriction of scalars on sections over `V`, induced by the ringed-space
map `f♯`. -/
noncomputable def ringedSpaceOpenSectionsRestriction
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    ModuleCat.{v} (X.structureSheaf.obj.obj
      (op ((Opens.map f.continuous).obj V))) ⥤
      ModuleCat.{v} (Y.structureSheaf.obj.obj (op V)) :=
  ModuleCat.restrictScalars (f.sharp.hom.app (op V)).hom

/-- Restriction of scalars on sections preserves finite limits. -/
theorem ringedSpaceOpenSectionsRestriction_isLeftExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    IsLeftExact (ringedSpaceOpenSectionsRestriction f V) := by
  sorry

/-- The induced restriction functor on bounded-below derived categories. -/
noncomputable def ringedSpaceOpenSectionsRestrictionDerived
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (V : Opens Y.carrier) :
    DPlus (ModuleCat.{v} (X.structureSheaf.obj.obj
      (op ((Opens.map f.continuous).obj V)))) ⥤
      DPlus (ModuleCat.{v} (Y.structureSheaf.obj.obj (op V))) :=
  rightDerivedFunctorOfLeftExact
    (ringedSpaceOpenSectionsRestriction f V)
    (ringedSpaceOpenSectionsRestriction_isLeftExact f V)

/-- The right-acyclicity condition used by the Grothendieck realization of
the Leray spectral sequence. -/
def LerayRightAcyclic
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) : Prop :=
  RightAcyclicOnInjectiveImages
    (sheafModuleRingedSpacePushforward f)
    (ringedSpaceModuleGlobalSections Y)
    (ringedSpaceModuleGlobalSections_isLeftExact Y)

/-- Injective modules on `X` become acyclic for global sections after
pushforward to `Y`, the acyclicity input to the Leray comparison. -/
theorem leray_rightAcyclic
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    LerayRightAcyclic f := by
  sorry

/-- The two commutative derived-category squares used before the Leray
spectral sequence is introduced.  The restriction functors are retained as
fields so that their source-induced scalar action remains explicit. -/
structure LerayDerivedSectionsComparisonData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) where
  global_restriction :
    DPlus (ModuleCat.{v} (X.structureSheaf.obj.obj
      (op (⊤ : Opens X.carrier)))) ⥤
      DPlus (ModuleCat.{v} (Y.structureSheaf.obj.obj
        (op (⊤ : Opens Y.carrier))))
  global_commutes :
    ringedSpaceModuleTotalDerivedSections X (⊤ : Opens X.carrier) ⋙
        global_restriction =
      ringedSpaceModuleDerivedPushforward f ⋙
        ringedSpaceModuleTotalDerivedSections Y (⊤ : Opens Y.carrier)
  open_restriction : ∀ V : Opens Y.carrier,
    DPlus (ModuleCat.{v} (X.structureSheaf.obj.obj
      (op ((Opens.map f.continuous).obj V)))) ⥤
      DPlus (ModuleCat.{v} (Y.structureSheaf.obj.obj (op V)))
  open_restriction_canonical :
    open_restriction = fun V => ringedSpaceOpenSectionsRestrictionDerived f V
  open_commutes : ∀ V : Opens Y.carrier,
    ringedSpaceModuleTotalDerivedSections X ((Opens.map f.continuous).obj V) ⋙
        open_restriction V =
      ringedSpaceModuleDerivedPushforward f ⋙
        ringedSpaceModuleTotalDerivedSections Y V

/-- The derived-sections comparison supplied by the resolution calculation. -/
theorem exists_lerayDerivedSectionsComparisonData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    Nonempty (LerayDerivedSectionsComparisonData f) := by
  sorry

/-! ## Modules versus abelian sheaves -/

/-- Module and abelian-sheaf cohomology agree after forgetting scalars. -/
theorem module_cohomology_eq_abelian
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℕ) :
    Nonempty (
      moduleCohomologyAsAbelian
          ((ringedSpaceModuleCohomology X (i : ℤ)).obj F) ≅
        (abelianSheafCohomology X.carrier (i : ℤ)).obj
          (moduleSheafAsAbelian F)) := by
  sorry

/-- Higher direct images agree after forgetting the module structures. -/
theorem higher_direct_image_eq_abelian
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℕ) :
    Nonempty (
      moduleSheafAsAbelian
          ((ringedSpaceModuleHigherDirectImage f (i : ℤ)).obj F) ≅
        (abelianSheafHigherDirectImage f.continuous (i : ℤ)).obj
          (moduleSheafAsAbelian F)) := by
  sorry

/-! ## The Leray spectral sequence -/

/-- The filtered-complex Grothendieck data specialized to
`Γ(Y, -) ∘ f_*`; its `E₂` page is the Leray page and its abutment is the
cohomology of `RΓ(X, -)`. -/
abbrev LeraySpectralSequenceData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf))
    (T : FilteredComplex
      (ModuleCat.{v} (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier))))) :=
  GrothendieckSpectralSequenceData
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)
    (ringedSpaceModuleGlobalSections Y)
    (ringedSpaceModuleGlobalSections_isLeftExact Y)
    ((DerivedCategory.Plus.Q (C := Mod X.structureSheaf)).obj K) T

/-- Existence of the Leray spectral sequence for a bounded-below complex. -/
theorem exists_leraySpectralSequence
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf)) :
    ∃ T : FilteredComplex
        (ModuleCat.{v} (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier)))),
      Nonempty (LeraySpectralSequenceData f K T) := by
  exact grothendieckSpectralSequence_exists
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)
    (ringedSpaceModuleGlobalSections Y)
    (ringedSpaceModuleGlobalSections_isLeftExact Y)
    (leray_rightAcyclic f)
    ((DerivedCategory.Plus.Q (C := Mod X.structureSheaf)).obj K)

/-- The object-level Leray spectral-sequence data for a sheaf `F`. -/
abbrev LerayObjectSpectralSequenceData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf)
    (T : FilteredComplex
      (ModuleCat.{v} (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier))))) :=
  GrothendieckObjectSpectralSequenceData
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)
    (ringedSpaceModuleGlobalSections Y)
    (ringedSpaceModuleGlobalSections_isLeftExact Y)
    F T

/-- Existence of the Leray spectral sequence for a sheaf. -/
theorem exists_lerayObjectSpectralSequence
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) :
    ∃ T : FilteredComplex
        (ModuleCat.{v} (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier)))),
      Nonempty (LerayObjectSpectralSequenceData f F T) := by
  exact grothendieckObjectSpectralSequence_exists
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)
    (ringedSpaceModuleGlobalSections Y)
    (ringedSpaceModuleGlobalSections_isLeftExact Y)
    (leray_rightAcyclic f) F

/-- Pagewise extra `Γ(X, O_X)`-module structures on a Leray spectral
sequence.  The scalar map and pagewise restriction isomorphisms retain the
additional structure mentioned in the source remark. -/
structure LerayAdditionalModuleStructureData
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf))
    (T : FilteredComplex
      (ModuleCat.{v} (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier)))))
    (S : LeraySpectralSequenceData f K T)
    where
  scalar_map :
    RingCat.of (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier))) ⟶
      RingCat.of (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)))
  page : ∀ (r : ℕ) (i : ℤ × ℤ),
    ModuleCat.{v} (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)))
  page_iso : ∀ (r : ℕ) (i : ℤ × ℤ),
    Nonempty ((ModuleCat.restrictScalars scalar_map.hom).obj (page r i) ≅
      S.spectralSequence.page r i)

/-- The Leray spectral sequence carries the extra module structures described
in the source remark. -/
theorem leray_has_additional_module_structure
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (K : CompPlus (Mod X.structureSheaf))
    (T : FilteredComplex
      (ModuleCat.{v} (Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier)))))
    (hT : Nonempty (LeraySpectralSequenceData f K T)) :
    Nonempty (LerayAdditionalModuleStructureData f K T (Classical.choice hT)) := by
  sorry

/-! ## Degeneration criteria -/

/-- The first standard hypothesis forcing the Leray page to degenerate at
`E₂`, with the resulting cohomology identification. -/
theorem apply_leray
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) :
    (∀ q : ℕ, 0 < q →
      IsZero ((ringedSpaceModuleHigherDirectImage f (q : ℤ)).obj F)) →
    (∀ p : ℕ, Nonempty (
      moduleCohomologyAsAbelian
          (ringedSpaceModuleCohomologyObject X F (p : ℤ)) ≅
        moduleCohomologyAsAbelian
          (ringedSpaceModuleCohomologyObject Y
            ((ringedSpaceModuleHigherDirectImage f 0).obj F) (p : ℤ)))) := by
  sorry

/-- The second Leray degeneration criterion, identifying cohomology on `X`
with global sections of the higher direct image. -/
theorem apply_leray_of_base_cohomology_vanishes
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) :
    (∀ p q : ℕ, 0 < p →
      IsZero ((ringedSpaceModuleCohomology Y (p : ℤ)).obj
        ((ringedSpaceModuleHigherDirectImage f (q : ℤ)).obj F))) →
    (∀ q : ℕ, Nonempty (
      moduleCohomologyAsAbelian
          (ringedSpaceModuleCohomologyObject X F (q : ℤ)) ≅
        moduleCohomologyAsAbelian
          (ringedSpaceModuleCohomologyObject Y
            ((ringedSpaceModuleHigherDirectImage f (q : ℤ)).obj F) 0))) := by
  sorry

/-! ## Composition and relative Leray -/

/-- Total derived pushforward is compatible with composition. -/
theorem higher_direct_images_compose
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) :
    Nonempty (ringedSpaceModuleDerivedPushforward f ⋙
        ringedSpaceModuleDerivedPushforward g ≅
      ringedSpaceModuleDerivedPushforward (RingedSpaceHom.comp f g)) := by
  sorry

/-- The object-level relative Leray spectral-sequence data. -/
abbrev RelativeLeraySpectralSequenceData
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) (F : Mod X.structureSheaf)
    (T : FilteredComplex (Mod Z.structureSheaf)) :=
  GrothendieckObjectSpectralSequenceData
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)
    (sheafModuleRingedSpacePushforward g)
    (sheafModuleRingedSpacePushforward_isLeftExact g)
    F T

/-- The bounded-below-complex relative Leray data, using the same
filtered-complex Grothendieck interface as the absolute Leray construction. -/
abbrev RelativeLerayComplexSpectralSequenceData
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) (K : CompPlus (Mod X.structureSheaf))
    (T : FilteredComplex (Mod Z.structureSheaf)) :=
  GrothendieckSpectralSequenceData
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)
    (sheafModuleRingedSpacePushforward g)
    (sheafModuleRingedSpacePushforward_isLeftExact g)
    ((DerivedCategory.Plus.Q (C := Mod X.structureSheaf)).obj K) T

/-- Relative Leray has `E₂^{p,q} = R^p g_* R^q f_* F` and abuts to
`R^{p+q}(g ∘ f)_*F`. -/
theorem exists_relativeLeraySpectralSequence
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) (F : Mod X.structureSheaf) :
    ∃ T : FilteredComplex (Mod Z.structureSheaf),
      Nonempty (RelativeLeraySpectralSequenceData f g F T) := by
  sorry

/-- Existence of the relative Leray spectral sequence for a bounded-below
complex of sheaves. -/
theorem exists_relativeLerayComplexSpectralSequence
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) (K : CompPlus (Mod X.structureSheaf)) :
    ∃ T : FilteredComplex (Mod Z.structureSheaf),
      Nonempty (RelativeLerayComplexSpectralSequenceData f g K T) := by
  sorry

/-- Functoriality of the relative Leray spectral sequence in the coefficient
sheaf is recorded by a spectral-sequence morphism over every coefficient map.
-/
structure RelativeLerayFunctorialityData
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) where
  source : FilteredComplex (Mod Z.structureSheaf)
  source_data : RelativeLeraySpectralSequenceData f g F source
  target : FilteredComplex (Mod Z.structureSheaf)
  target_data : RelativeLeraySpectralSequenceData f g G target
  filteredMap : source ⟶ target
  map : FilteredComplexSpectralSequenceHom
    filteredMap
    source_data.spectralSequence target_data.spectralSequence

theorem relativeLeray_functorial
    {X Y Z : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (g : RingedSpaceHom Y Z) {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) :
    Nonempty (RelativeLerayFunctorialityData f g φ) := by
  sorry

/- The source also states the bounded-below-complex relative version; the
filtered-complex data above are the canonical bounded-below interface. -/

end Formalization.Books.Cohomology.Unit10
