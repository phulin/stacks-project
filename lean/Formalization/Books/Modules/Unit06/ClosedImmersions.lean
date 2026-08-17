import Formalization.Books.Modules.Unit05.Supports
import Formalization.Books.Homology.Unit10.SerreSubcategories
import Formalization.Books.Sheaves.Unit22.ClosedImmersions
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic

/-!
# Sheaves of Modules, Chapter 6: Closed immersions and abelian sheaves

The source chapter is `books/modules.tex:548-1812`.  Closed and open
immersions, sheaf-module restrictions, stalks, colimits, and exactness are
the canonical constructions from the earlier chapters.  This file records
the chapter-facing predicates and theorem interfaces in source order.
-/

namespace Formalization.Books.Modules.Unit06

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.ObjectProperty
open Formalization.Books.Categories.Unit23
open Formalization.Books.Categories.Unit21
open Formalization.Books.Homology.Unit10
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit04
open Formalization.Books.Modules.Unit05
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit22

universe u v

noncomputable section

/-! ## Sections with support in a closed subset -/

/- The source regards an abelian sheaf as a sheaf of modules over the constant
   sheaf of integers.  `Ab X` is the canonical `AddCommGrpCat`-valued sheaf
   category, which is the existing project representation of that convention. -/

/-- The germ of an abelian-sheaf section at a point of its domain. -/
noncomputable def abelianSectionGerm {X : TopCat.{v}} {F : Ab X}
    (U : Opens X) (s : F.presheaf.obj (op U)) (x : U) :
    F.presheaf.stalk x.1 :=
  TopCat.Presheaf.germ (C := AddCommGrpCat.{v}) F.presheaf U x.1 x.property s

/-- The support of a section of an abelian sheaf, inside its open domain. -/
def abelianSectionSupport {X : TopCat.{v}} {F : Ab X} (U : Opens X)
    (s : F.presheaf.obj (op U)) : Set U :=
  {x | abelianSectionGerm U s x ≠ 0}

/-- The part of a closed subset seen inside an open subset. -/
def closedSubsetInOpen {X : TopCat.{v}} (Z : Set X) (U : Opens X) : Set U :=
  (Subtype.val : U → X) ⁻¹' Z

/-- The source's section predicate for support in a closed subset. -/
def abelianSectionSupportedInClosed {X : TopCat.{v}} (Z : Set X)
    {F : Ab X} (U : Opens X) (s : F.presheaf.obj (op U)) : Prop :=
  abelianSectionSupport U s ⊆ closedSubsetInOpen Z U

/-- The sections of `F` over `U` whose support is contained in `Z ∩ U`. -/
def abelianSectionsWithSupportInClosed {X : TopCat.{v}} (Z : Set X)
    {F : Ab X} (U : Opens X) : Set (F.presheaf.obj (op U)) :=
  {s | abelianSectionSupportedInClosed Z U s}

/-- The support of an abelian sheaf is contained in a subset. -/
def abelianSheafSupportContainedIn {X : TopCat.{v}} (Z : Set X)
    (F : Ab X) : Prop :=
  additiveSheafSupport F ⊆ Z

/-- A section belongs to a categorical subsheaf when it has a lift to it. -/
def abelianSubsheafContainsSection {X : TopCat.{v}} {F : Ab X}
    (P : Subobject F) (U : Opens X) (s : F.presheaf.obj (op U)) : Prop :=
  ∃ t : (P : Ab X).presheaf.obj (op U),
    P.arrow.hom.app (op U) t = s

/- The largest subsheaf is recorded as a property of a subobject.  This uses
   the canonical complete lattice of categorical subobjects rather than a
   parallel sheaf or module construction. -/

/-- Existence of the largest abelian subsheaf supported in `Z`. -/
theorem exists_closedSupportSubsheaf {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) :
    ∃ P : Subobject F,
      abelianSheafSupportContainedIn Z (P : Ab X) ∧
        ∀ Q : Subobject F,
          abelianSheafSupportContainedIn Z (Q : Ab X) → Q ≤ P := by
  sorry

/-- The canonical largest abelian subsheaf supported in `Z`. -/
noncomputable def closedSupportSubsheaf {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) : Subobject F :=
  Classical.choose (exists_closedSupportSubsheaf Z hZ F)

theorem closedSupportSubsheaf_supportContainedIn {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) :
    abelianSheafSupportContainedIn Z
      (closedSupportSubsheaf Z hZ F : Ab X) := by
  exact (Classical.choose_spec (exists_closedSupportSubsheaf Z hZ F)).1

theorem closedSupportSubsheaf_isLargest {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) (Q : Subobject F)
    (hQ : abelianSheafSupportContainedIn Z (Q : Ab X)) :
    Q ≤ closedSupportSubsheaf Z hZ F := by
  exact (Classical.choose_spec (exists_closedSupportSubsheaf Z hZ F)).2 Q hQ

/-- The sections of the largest subsheaf are exactly the source's supported
sections. -/
theorem closedSupportSubsheaf_section_iff {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) (U : Opens X)
    (s : F.presheaf.obj (op U)) :
    abelianSubsheafContainsSection (closedSupportSubsheaf Z hZ F) U s ↔
      s ∈ abelianSectionsWithSupportInClosed Z U := by
  sorry

/-! ## The right adjoint on abelian sheaves -/

/-- The right-adjoint functor whose value is the sheaf of sections supported in
`Z`, viewed as a sheaf on the closed subspace. -/
theorem exists_closedSupportSectionsFunctor {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    ∃ H : Ab X ⥤ Ab (closedSubspace Z),
      Nonempty (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⊣ H) := by
  sorry

noncomputable def closedSupportSectionsFunctor {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) : Ab X ⥤ Ab (closedSubspace Z) :=
  Classical.choose (exists_closedSupportSectionsFunctor Z hZ)

noncomputable def closedSupportSectionsFunctor_adjunction {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⊣
      closedSupportSectionsFunctor Z hZ :=
  Classical.choice (Classical.choose_spec
    (exists_closedSupportSectionsFunctor Z hZ))

/-- The sheaf `H_Z(F)` from the source, on the closed subspace. -/
abbrev sectionsWithSupportInClosed {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) : Ab (closedSubspace Z) :=
  (closedSupportSectionsFunctor Z hZ).obj F

/-- The chosen right-adjoint value is the sheaf on `Z` corresponding to the
largest supported subsheaf of `F` on `X`. -/
theorem closedSupportSectionsFunctor_obj_iso_closedSupportSubsheaf
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    Nonempty ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj
      (sectionsWithSupportInClosed Z hZ F) ≅
        (closedSupportSubsheaf Z hZ F : Ab X)) := by
  sorry

/-- The adjunction Hom correspondence for sections with support. -/
noncomputable abbrev closedSupportSectionsHomEquiv {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (G : Ab (closedSubspace Z)) (F : Ab X) :
    ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj G ⟶ F) ≃
      (G ⟶ sectionsWithSupportInClosed Z hZ F) :=
  (closedSupportSectionsFunctor_adjunction Z hZ).homEquiv G F

/-- The supported-sections functor is left exact. -/
theorem closedSupportSectionsFunctor_isLeftExact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    IsLeftExact (closedSupportSectionsFunctor Z hZ) := by
  sorry

/-! ## The closed direct image on abelian sheaves -/

/-- The closed direct image is exact on abelian sheaves. -/
theorem closedAbelianSheafDirectImage_isExact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    IsExact (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ) := by
  sorry

/-- The closed direct image is fully faithful. -/
theorem closedAbelianSheafDirectImage_fullyFaithful {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).FullyFaithful := by
  exact Formalization.Books.Sheaves.Unit22.closedAbelianSheafDirectImage_fullFaithful
    Z hZ

/-- The essential image of the closed direct image consists exactly of
abelian sheaves supported in `Z`. -/
theorem closedAbelianSheafDirectImage_essentialImage_support
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (G : Ab X) :
    (∃ F, Nonempty
      ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj F ≅ G)) ↔
      abelianSheafSupportContainedIn Z G := by
  sorry

/-- Zero stalks off `Z` are equivalent to support containment in `Z`. -/
theorem abelianSheafSupportContainedIn_iff_closedZeroStalkCondition
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (G : Ab X) :
    abelianSheafSupportContainedIn Z G ↔
      ClosedZeroStalkCondition Z hZ G := by
  sorry

/-- Inverse image is a left inverse to closed direct image. -/
theorem closedAbelianSheafRestriction_leftInverse {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab (closedSubspace Z)) :
    Nonempty ((closedAbelianSheafRestriction Z hZ).obj
      ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj F) ≅ F) := by
  exact Formalization.Books.Sheaves.Unit22.closedAbelianSheafRestriction_directImage_iso
    Z hZ F

/-- Functorial form of the left-inverse statement. -/
theorem closedAbelianSheafRestriction_leftInverse_functor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty
      (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⋙
          closedAbelianSheafRestriction Z hZ ≅
        𝟭 (Ab (closedSubspace Z))) := by
  sorry

/-- The closed direct image preserves colimits of every size. -/
theorem closedAbelianSheafDirectImage_preserves_all_colimits
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    PreservesColimitsOfSize.{v, v}
      (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ) := by
  sorry

/-! ## The pointed-sheaf comparison from the source remark -/

/-- Germs of sections for a sheaf of pointed sets. -/
noncomputable def pointedSectionGerm {X : TopCat.{v}}
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X)
    (s : F.presheaf.obj (op U)) (x : U) :
    TopCat.Presheaf.stalk (C := Type v)
      (F.presheaf ⋙ CategoryTheory.forget Pointed) x.1 :=
  TopCat.Presheaf.germ (C := Type v)
    (F.presheaf ⋙ CategoryTheory.forget Pointed) U x.1 x.property s

/-- The germ of the distinguished point of a pointed-sheaf section space. -/
noncomputable def pointedSectionBaseGerm {X : TopCat.{v}}
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X) (x : U) :
    TopCat.Presheaf.stalk (C := Type v)
      (F.presheaf ⋙ CategoryTheory.forget Pointed) x.1 :=
  TopCat.Presheaf.germ (C := Type v)
    (F.presheaf ⋙ CategoryTheory.forget Pointed) U x.1 x.property
      (F.presheaf.obj (op U)).point

/-- The support of a pointed-sheaf section, relative to its distinguished
point. -/
def pointedSectionSupport {X : TopCat.{v}}
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X)
    (s : F.presheaf.obj (op U)) : Set U :=
  {x | pointedSectionGerm U s x ≠ pointedSectionBaseGerm U x}

/-- Pointed-sheaf sections supported in a closed subset. -/
def pointedSectionsWithSupportInClosed {X : TopCat.{v}} (Z : Set X)
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X) :
    Set (F.presheaf.obj (op U)) :=
  {s | pointedSectionSupport U s ⊆ closedSubsetInOpen Z U}

/-- Closed direct image for sheaves of pointed sets. -/
abbrev closedPointedSheafDirectImage {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    TopCat.Sheaf (Pointed.{v}) (closedSubspace Z) ⥤
      TopCat.Sheaf (Pointed.{v}) X :=
  closedSheafDirectImage (Pointed.{v}) Z hZ

/-- The pointed-sheaf direct image is exact. -/
theorem closedPointedSheafDirectImage_isExact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z)
    [HasFiniteLimits (TopCat.Sheaf (Pointed.{v}) (closedSubspace Z))]
    [HasFiniteColimits (TopCat.Sheaf (Pointed.{v}) (closedSubspace Z))]
    [HasFiniteLimits (TopCat.Sheaf (Pointed.{v}) X)]
    [HasFiniteColimits (TopCat.Sheaf (Pointed.{v}) X)] :
    IsExact (closedPointedSheafDirectImage Z hZ) := by
  sorry

/-- The supported-sections functor for pointed sheaves, as a right adjoint to
closed direct image. -/
theorem exists_closedPointedSupportSectionsFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    ∃ H : TopCat.Sheaf (Pointed.{v}) X ⥤
        TopCat.Sheaf (Pointed.{v}) (closedSubspace Z),
      Nonempty (closedPointedSheafDirectImage Z hZ ⊣ H) := by
  sorry

noncomputable def closedPointedSupportSectionsFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    TopCat.Sheaf (Pointed.{v}) X ⥤
      TopCat.Sheaf (Pointed.{v}) (closedSubspace Z) :=
  Classical.choose (exists_closedPointedSupportSectionsFunctor Z hZ)

noncomputable def closedPointedSupportSectionsFunctor_adjunction
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    closedPointedSheafDirectImage Z hZ ⊣
      closedPointedSupportSectionsFunctor Z hZ :=
  Classical.choice (Classical.choose_spec
    (exists_closedPointedSupportSectionsFunctor Z hZ))

/-! ## The set-valued warning -/

/-- The assertion that the set-valued closed direct image has a right adjoint. -/
def closedSetSheafDirectImageHasRightAdjoint {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) : Prop :=
  ∃ H : TopCat.Sheaf (Type v) X ⥤
      TopCat.Sheaf (Type v) (closedSubspace Z),
    Nonempty (closedSheafDirectImage (Type v) Z hZ ⊣ H)

/-- When the complement is nonempty, the set-valued closed direct image has
no right adjoint, as witnessed by its failure to preserve finite colimits. -/
theorem closedSetSheafDirectImage_no_rightAdjoint {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (hcomp : ∃ x : X, x ∉ Z) :
    ¬ closedSetSheafDirectImageHasRightAdjoint Z hZ := by
  sorry

/-! ## A canonical exact sequence -/

def canonicalClosedSubset {X : TopCat.{v}} (U : Opens X) : Set X :=
  (U : Set X)ᶜ

theorem canonicalClosedSubset_isClosed {X : TopCat.{v}} (U : Opens X) :
    IsClosed (canonicalClosedSubset U) := by
  exact U.2.isClosed_compl

noncomputable abbrev canonicalExactSequenceLeft {X : TopCat.{v}}
    (U : Opens X) (F : Ab X) :
    (openAbelianSheafExtensionFunctor U).obj
        ((openSheafRestriction AddCommGrpCat U).obj F) ⟶ F :=
  (openSheafExtensionAdjunction AddCommGrpCat U).counit.app F

noncomputable abbrev canonicalExactSequenceRight {X : TopCat.{v}}
    (U : Opens X) (F : Ab X) :
    F ⟶
      (closedSheafDirectImage AddCommGrpCat (canonicalClosedSubset U)
        (canonicalClosedSubset_isClosed U)).obj
        ((closedAbelianSheafRestriction (canonicalClosedSubset U)
          (canonicalClosedSubset_isClosed U)).obj F) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
    (closedInclusion (canonicalClosedSubset U))).unit.app F

theorem canonicalExactSequence_zero {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    canonicalExactSequenceLeft U F ≫ canonicalExactSequenceRight U F = 0 := by
  sorry

noncomputable def canonicalExactSequence {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    ShortComplex (Ab X) :=
  ShortComplex.mk (canonicalExactSequenceLeft U F)
    (canonicalExactSequenceRight U F) (canonicalExactSequence_zero U F)

theorem canonicalExactSequence_shortExact {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    (canonicalExactSequence U F).ShortExact := by
  sorry

noncomputable def canonicalExactSequenceMap {X : TopCat.{v}} (U : Opens X)
    {F G : Ab X} (φ : F ⟶ G) :
    canonicalExactSequence U F ⟶ canonicalExactSequence U G :=
  { τ₁ := (openAbelianSheafExtensionFunctor U).map
      ((openSheafRestriction AddCommGrpCat U).map φ)
    τ₂ := φ
    τ₃ := (closedSheafDirectImage AddCommGrpCat (canonicalClosedSubset U)
      (canonicalClosedSubset_isClosed U)).map
      ((closedAbelianSheafRestriction (canonicalClosedSubset U)
        (canonicalClosedSubset_isClosed U)).map φ)
    comm₁₂ := by
      exact (openSheafExtensionAdjunction AddCommGrpCat U).counit.naturality φ
    comm₂₃ := by
      exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (closedInclusion (canonicalClosedSubset U))).unit.naturality φ }

/-! ## Modules locally generated by sections -/

def locallyGenerated {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    globallyGenerated ((openModuleRestrictionFunctor X U).obj F)

theorem locallyGenerated_iff_exists_free_surjection
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    locallyGenerated F ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ (I : Type v)
          (s : I → ((openModuleRestrictionFunctor X U).obj F).sections),
          Epi (globalGenerationMap s) := by
  constructor
  · intro h x
    rcases h x with ⟨U, hxU, hU⟩
    rcases (globallyGenerated_iff ((openModuleRestrictionFunctor X U).obj F)).mp hU
      with ⟨I, s, hs⟩
    exact ⟨U, hxU, I, s, hs⟩
  · intro h x
    rcases h x with ⟨U, hxU, I, s, hs⟩
    refine ⟨U, hxU, ?_⟩
    apply (globallyGenerated_iff ((openModuleRestrictionFunctor X U).obj F)).mpr
    exact ⟨I, s, hs⟩

noncomputable def integralConstantAdditiveSheaf {X : TopCat.{v}} :
    Ab X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))

noncomputable def additiveGlobalGenerationMap
    {X : TopCat.{v}} {F : Ab X} {I : Type v}
    (s : I → (integralConstantAdditiveSheaf (X := X) ⟶ F)) :
    (∐ fun _ : I => integralConstantAdditiveSheaf (X := X)) ⟶ F :=
  Cofan.IsColimit.desc (coproductIsCoproduct _) s

def additiveGloballyGenerated {X : TopCat.{v}} (F : Ab X) : Prop :=
  ∃ (I : Type v) (s : I → (integralConstantAdditiveSheaf (X := X) ⟶ F)),
    Epi (additiveGlobalGenerationMap s)

def additiveLocallyGenerated {X : TopCat.{v}} (F : Ab X) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    additiveGloballyGenerated
      ((openSheafRestriction AddCommGrpCat U).obj F)

abbrev locallyGeneratedRealLine : TopCat := TopCat.of ℝ

def locallyGeneratedPositiveHalfLine : Opens locallyGeneratedRealLine :=
  ⟨Set.Ioi (0 : ℝ), isOpen_Ioi⟩

noncomputable def locallyGeneratedPositiveHalfLineExtension :
    Ab locallyGeneratedRealLine :=
  (openAbelianSheafExtensionFunctor locallyGeneratedPositiveHalfLine).obj
    (integerConstantAbelianSheaf
      (X := openSubspace locallyGeneratedPositiveHalfLine))

theorem locallyGeneratedPositiveHalfLineExtension_stalk_zero :
    Nonempty
      (locallyGeneratedPositiveHalfLineExtension.presheaf.stalk (0 : locallyGeneratedRealLine)
        ≅ (⊥_ AddCommGrpCat)) := by
  sorry

theorem locallyGeneratedPositiveHalfLineExtension_interval_sections_zero
    (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    IsZero
      (locallyGeneratedPositiveHalfLineExtension.presheaf.obj
        (op (⟨Set.Ioo a b, isOpen_Ioo⟩ : Opens locallyGeneratedRealLine))) := by
  sorry

theorem locallyGeneratedPositiveHalfLineExtension_not_locally_generated :
    ¬ additiveLocallyGenerated locallyGeneratedPositiveHalfLineExtension := by
  sorry

theorem locallyGenerated_pullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    locallyGenerated ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

/-! ## Modules of finite type -/

def finiteType {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ (I : Type v), ∃ (_ : Finite I),
      ∃ s : I → ((openModuleRestrictionFunctor X U).obj F).sections,
        Epi (globalGenerationMap
          (O := (ringedOpenSubspace X U).structureSheaf)
          (F := (openModuleRestrictionFunctor X U).obj F) s)

theorem finiteType_pullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    finiteType G → finiteType ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

theorem finiteType_image {X : RingedSpace.{v}}
    {F G : Mod X.structureSheaf} (φ : F ⟶ G)
    (hF : finiteType F) :
    finiteType (image φ) := by
  sorry

theorem finiteType_of_shortExact {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (h₁ : finiteType F₁) (h₃ : finiteType F₃) :
    finiteType F₂ := by
  sorry

def moduleMapSurjectiveOnOpen {X : RingedSpace.{v}}
    {F G : Mod X.structureSheaf} (φ : F ⟶ G) (U : Opens X.carrier) : Prop :=
  Epi ((openModuleRestrictionFunctor X U).map φ)

theorem finiteType_surjective_on_stalk
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : G ⟶ F) (x : X)
    (hF : finiteType F)
    (hφ : Function.Surjective ((sheafModuleStalkFunctor X.structureSheaf x).map φ).hom) :
    ∃ U : Opens X.carrier, x ∈ U ∧ moduleMapSurjectiveOnOpen φ U := by
  sorry

theorem finiteType_stalk_zero {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (x : X) (hF : finiteType F)
    (hFx : IsZero ((sheafModuleStalkFunctor X.structureSheaf x).obj F)) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      IsZero ((openModuleRestrictionFunctor X U).obj F) := by
  sorry

theorem finiteType_support_isClosed {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (hF : finiteType F) :
    IsClosed (moduleSupport F) := by
  sorry

theorem finiteType_directed_colimit_exists_surjective_index
    {X : RingedSpace.{v}} (I : Type v) [Preorder I]
    (D : I ⥤ Mod X.structureSheaf) (hI : IsDirectedSet I)
    [CompactSpace (X : Type v)] (hF : finiteType (colimit D)) :
    ∃ i : I, Epi (colimit.ι D i) := by
  sorry

theorem finiteType_directed_colimit_stabilizes
    {X : RingedSpace.{v}} (I : Type v) [Preorder I]
    (D : I ⥤ Mod X.structureSheaf) (hI : IsDirectedSet I)
    [CompactSpace (X : Type v)] (hF : finiteType (colimit D))
    (hinj : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f)) :
    ∃ i : I, Nonempty (colimit D ≅ D.obj i) := by
  sorry

theorem exists_set_of_finiteType_representatives
    {X : RingedSpace.{v}} :
    ∃ S : Set (Mod X.structureSheaf),
      (∀ F, F ∈ S → finiteType F) ∧
        ∀ F, finiteType F → ∃! G, G ∈ S ∧ Nonempty (F ≅ G) := by
  sorry

/-! ## Quasi-coherent modules -/

def hasModulePresentationOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∃ (I J : Type v),
    ∃ φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
      (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf),
      Nonempty
        ((openModuleRestrictionFunctor X U).obj F ≅ cokernel φ)

def quasiCoherent {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasModulePresentationOn F U

abbrev QCoh {X : RingedSpace.{v}} :=
  ObjectProperty.FullSubcategory (quasiCoherent (X := X))

def allQuasiCoherentCategoriesAbelian : Prop :=
  ∀ X : RingedSpace.{v}, Nonempty (Abelian (QCoh (X := X)))

theorem not_allQuasiCoherentCategoriesAbelian :
    ¬ allQuasiCoherentCategoriesAbelian := by
  sorry

theorem quasiCoherent_iff_local_presentation {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) :
    quasiCoherent F ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasModulePresentationOn F U := by
  rfl

theorem quasiCoherent_directSum {X : RingedSpace.{v}}
    {F G : Mod X.structureSheaf} (hF : quasiCoherent F)
    (hG : quasiCoherent G) : quasiCoherent (F ⊞ G) := by
  sorry

def infiniteDirectSumsPreserveQuasiCoherent : Prop :=
  ∀ (X : RingedSpace.{v}) (I : Type v) (F : I → Mod X.structureSheaf),
    (∀ i, quasiCoherent (F i)) →
      quasiCoherent (colimit (Discrete.functor F))

theorem not_infiniteDirectSumsPreserveQuasiCoherent :
    ¬ infiniteDirectSumsPreserveQuasiCoherent := by
  sorry

theorem quasiCoherent_pullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    quasiCoherent G → quasiCoherent ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

noncomputable def associatedStalkScalarMap
    {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {R : Type v} [Ring R]
    (α : R →+* (O.obj.obj (op ⊤) : Type v)) (x : X) :
    R →+* (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x : Type v) :=
  (TopCat.Presheaf.Γgerm (C := RingCat.{v}) O.obj x).hom.comp α

/-!
The source writes the stalk construction as a tensor product.  The version of
Mathlib used here has `ModuleCat.extendScalars` only for commutative rings,
whereas a ringed space in the preceding chapters is a sheaf of (possibly
noncommutative) rings.  The following universal-property interface is the
canonical ring-theoretic meaning of that tensor product and works for the
generality of the source's ringed spaces.
-/
structure RingMapTensorProductData
    {R S : Type v} [Ring R] [Ring S]
    (α : R →+* S) (M : Type v) [AddCommGroup M] [Module R M] where
  obj : ModuleCat S
  hom_equiv : ∀ N : ModuleCat S,
    Nonempty
      ((obj ⟶ N) ≃
        (ModuleCat.of R M ⟶ (ModuleCat.restrictScalars α).obj N))

theorem exists_ringMapTensorProductData
    {R S : Type v} [Ring R] [Ring S]
    (α : R →+* S) (M : Type v) [AddCommGroup M] [Module R M] :
    Nonempty (RingMapTensorProductData α M) := by
  sorry

noncomputable def associatedStalkTensorModule
    {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {R : Type v} [Ring R] (α : R →+* (O.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] (x : X) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) :=
  (Classical.choice
    (exists_ringMapTensorProductData (associatedStalkScalarMap α x) M)).obj

noncomputable def associatedGlobalSectionsModule
    {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {R : Type v} [Ring R]
    (α : R →+* (O.obj.obj (op ⊤) : Type v)) (G : Mod O) : ModuleCat R :=
  (ModuleCat.restrictScalars α).obj
    ((SheafOfModules.evaluation O (op ⊤)).obj G)

noncomputable def ringedSpaceGlobalSectionsMap
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom X Y) :
    (Y.structureSheaf.obj.obj (op ⊤) : Type v) →+*
      (X.structureSheaf.obj.obj (op ⊤) : Type v) :=
  (g.sharp.hom.app (op ⊤)).hom

noncomputable def associatedScalarExtensionModule
    {R S : Type v} [Ring R] [Ring S]
    (β : R →+* S) (M : ModuleCat R) : ModuleCat S :=
  (Classical.choice
    (exists_ringMapTensorProductData β (M : Type v))).obj

structure AssociatedSheafConstruction
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v)) where
  functor : ModuleCat R ⥤ Mod X.structureSheaf
  quasiCoherent_obj : ∀ M, quasiCoherent (functor.obj M)
  stalk_iso : ∀ (M : ModuleCat R) (x : X),
    Nonempty
      ((sheafModuleStalkFunctor X.structureSheaf x).obj (functor.obj M) ≅
        associatedStalkTensorModule α (M : Type v) x)
  preserves_colimits : PreservesColimitsOfSize.{v, v} functor
  hom_equiv : ∀ (M : ModuleCat R) (G : Mod X.structureSheaf),
    Nonempty
      ((functor.obj M ⟶ G) ≃
        (M ⟶ associatedGlobalSectionsModule α G))

theorem exists_associatedSheafConstruction
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v)) :
    Nonempty (AssociatedSheafConstruction α) := by
  sorry

noncomputable def associatedSheafConstruction
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v)) :
    AssociatedSheafConstruction α :=
  Classical.choice (exists_associatedSheafConstruction α)

abbrev associatedSheafFunctor
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v)) :
    ModuleCat R ⥤ Mod X.structureSheaf :=
  (associatedSheafConstruction α).functor

noncomputable abbrev associatedSheafModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : ModuleCat R) : Mod X.structureSheaf :=
  (associatedSheafFunctor α).obj M

noncomputable abbrev associatedSheaf
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] : Mod X.structureSheaf :=
  (associatedSheafFunctor α).obj (ModuleCat.of R M)

theorem associatedSheaf_quasiCoherent
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] :
    quasiCoherent (associatedSheaf α M) := by
  exact (associatedSheafConstruction α).quasiCoherent_obj (ModuleCat.of R M)

theorem associatedSheaf_stalk_iso
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] (x : X) :
    Nonempty
      ((sheafModuleStalkFunctor X.structureSheaf x).obj (associatedSheaf α M) ≅
        associatedStalkTensorModule α M x) := by
  exact (associatedSheafConstruction α).stalk_iso (ModuleCat.of R M) x

theorem associatedSheaf_preserves_colimits
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v)) :
    PreservesColimitsOfSize.{v, v} (associatedSheafFunctor α) := by
  exact (associatedSheafConstruction α).preserves_colimits

theorem associatedSheaf_hom_equiv
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] (G : Mod X.structureSheaf) :
    Nonempty
      ((associatedSheaf α M ⟶ G) ≃
        (ModuleCat.of R M ⟶ associatedGlobalSectionsModule α G)) := by
  exact (associatedSheafConstruction α).hom_equiv (ModuleCat.of R M) G

theorem associatedSheaf_restrict
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom X Y)
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    {R : Type v} [Ring R]
    (α : R →+* (Y.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : ModuleCat R) :
    Nonempty
      ((sheafModuleRingedSpacePullback g).obj (associatedSheafModule α M) ≅
        associatedSheafModule (RingHom.id
          (X.structureSheaf.obj.obj (op ⊤) : Type v))
          (associatedScalarExtensionModule
            ((ringedSpaceGlobalSectionsMap g).comp α) M)) := by
  sorry

def hasQuasiCompactNeighborhoodBasis {X : RingedSpace.{v}} (x : X) : Prop :=
  ∀ V : Opens X.carrier, x ∈ V →
    ∃ K : Set X, x ∈ K ∧ IsCompact K ∧ K ⊆ (V : Set X)

theorem quasiCoherent_locally_associated
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) (x : X)
    (hx : hasQuasiCompactNeighborhoodBasis x)
    (hF : quasiCoherent F) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ M : ModuleCat
          ((ringedOpenSubspace X U).structureSheaf.obj.obj (op ⊤)),
        Nonempty
          ((openModuleRestrictionFunctor X U).obj F ≅
            associatedSheafModule
              (RingHom.id
                ((ringedOpenSubspace X U).structureSheaf.obj.obj (op ⊤) : Type v))
              M) := by
  sorry

theorem associatedSheaf_has_free_presentation
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] :
    ∃ (I J : Type v),
      ∃ φ : (SheafOfModules.free J : Mod X.structureSheaf) ⟶
        (SheafOfModules.free I : Mod X.structureSheaf),
        Nonempty (cokernel φ ≅ associatedSheaf α M) := by
  sorry

def associatedSheafWarningAboutLocalMatrices : Prop :=
  ∃ (X : RingedSpace.{v}) (F : Mod X.structureSheaf),
    quasiCoherent F ∧
      ¬ ∀ U : Opens X.carrier, ∃ (I J : Type v),
        ∃ φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf),
          Nonempty
            ((openModuleRestrictionFunctor X U).obj F ≅ cokernel φ)

theorem exists_associatedSheafWarningAboutLocalMatrices :
    associatedSheafWarningAboutLocalMatrices := by
  sorry

/-! ## Modules of finite presentation -/

def hasFinitePresentationOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∃ (I J : Type v), ∃ (_ : Finite I), ∃ (_ : Finite J),
    ∃ φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
      (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf),
      Nonempty
        ((openModuleRestrictionFunctor X U).obj F ≅ cokernel φ)

def finitePresentation {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasFinitePresentationOn F U

theorem finitePresentation_iff_local_presentation
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    finitePresentation F ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasFinitePresentationOn F U := by
  rfl

theorem finitePresentation_quasiCoherent
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : finitePresentation F) : quasiCoherent F := by
  sorry

theorem finitePresentation_cokernel_of_finiteType
    {X : RingedSpace.{v}}
    {F G : Mod X.structureSheaf} (φ : G ⟶ F)
    (hF : finitePresentation F) (hG : finiteType G) :
    finitePresentation (cokernel φ) := by
  sorry

theorem finitePresentation_kernel_of_surjection_from_free
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (I : Type v) [Finite I]
    (ψ : (SheafOfModules.free I : Mod X.structureSheaf) ⟶ F)
    (hF : finitePresentation F) (hψ : Epi ψ) :
    finiteType (kernel ψ) := by
  sorry

theorem finitePresentation_kernel_of_surjection
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (θ : G ⟶ F) (hF : finitePresentation F)
    (hG : finiteType G) (hθ : Epi θ) :
    finiteType (kernel θ) := by
  sorry

theorem finitePresentation_pullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    finitePresentation G →
      finitePresentation ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

structure DirectedFinitePresentationColimit
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) where
  I : Type v
  [preorder : Preorder I]
  diagram : I ⥤ Mod X.structureSheaf
  directed : IsDirectedSet I
  finitePresented : ∀ i, finitePresentation (diagram.obj i)
  colimit_iso : Nonempty (colimit diagram ≅ F)

theorem associatedSheaf_is_directed_colimit_of_finitePresentation
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] :
    Nonempty (DirectedFinitePresentationColimit (associatedSheaf α M)) := by
  sorry

theorem finitePresentation_stalk_free
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : finitePresentation F) (I : Type v) [Finite I] (x : X)
    (hIso : Nonempty
      ((sheafModuleStalkFunctor X.structureSheaf x).obj F ≅
        (sheafModuleStalkFunctor X.structureSheaf x).obj
          (SheafOfModules.free I : Mod X.structureSheaf))) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty
        ((openModuleRestrictionFunctor X U).obj F ≅
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)) := by
  sorry

/-! ## Coherent modules -/

def coherent {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  finiteType F ∧
    ∀ (U : Opens X.carrier) (I : Type v) (_ : Finite I)
      (s : I → ((openModuleRestrictionFunctor X U).obj F).sections),
      finiteType
        (kernel
          (globalGenerationMap
            (O := (ringedOpenSubspace X U).structureSheaf)
            (F := (openModuleRestrictionFunctor X U).obj F) s))

abbrev Coh {X : RingedSpace.{v}} :=
  ObjectProperty.FullSubcategory (coherent (X := X))

theorem coherent_iff_finiteType_and_finite_relations
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    coherent F ↔
      finiteType F ∧
        ∀ (U : Opens X.carrier) (I : Type v) (_ : Finite I)
          (s : I → ((openModuleRestrictionFunctor X U).obj F).sections),
          finiteType
            (kernel
              (globalGenerationMap
                (O := (ringedOpenSubspace X U).structureSheaf)
                (F := (openModuleRestrictionFunctor X U).obj F) s)) := by
  rfl

def coherentRingAsSelfModule (R : Type u) [CommRing R] : Prop :=
  ∀ I : Ideal R, I.FG → Module.FinitePresentation R I

def noetherianRingAsSelfModule (R : Type u) [CommRing R] : Prop :=
  ∀ I : Ideal R, I.FG

theorem infinitePolynomialRing_coherent_not_noetherian :
    coherentRingAsSelfModule (MvPolynomial ℕ ℂ) ∧
      ¬ noetherianRingAsSelfModule (MvPolynomial ℕ ℂ) := by
  sorry

theorem coherent_subobject_of_finiteType
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (P : Subobject F) (hF : coherent F)
    (hP : finiteType (P : Mod X.structureSheaf)) :
    coherent (P : Mod X.structureSheaf) := by
  sorry

theorem finiteType_kernel_to_coherent
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) (hF : finiteType F) (hG : coherent G) :
    finiteType (kernel φ) := by
  sorry

theorem coherent_kernel_cokernel
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) (hF : coherent F) (hG : coherent G) :
    coherent (kernel φ) ∧ coherent (cokernel φ) := by
  sorry

theorem coherent_right_of_shortExact
    {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (h₁ : coherent F₁) (h₂ : coherent F₂) :
    coherent F₃ := by
  sorry

theorem coherent_middle_of_shortExact
    {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (h₁ : coherent F₁) (h₃ : coherent F₃) :
    coherent F₂ := by
  sorry

theorem coherent_left_of_shortExact
    {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (h₂ : coherent F₂) (h₃ : coherent F₃) :
    coherent F₁ := by
  sorry

instance coherent_isWeakSerreClass
    {X : RingedSpace.{v}} :
    CategoryTheory.ObjectProperty.IsWeakSerreClass
      (coherent (X := X)) := by
  sorry

theorem coherent_subcategory_is_abelian_and_inclusion_exact
    {X : RingedSpace.{v}} :
    Nonempty (Abelian (Coh (X := X))) ∧
      exactFunctor (Coh (X := X)) (Mod X.structureSheaf)
        (CategoryTheory.ObjectProperty.ι (coherent (X := X))) := by
  exact weak_serre_subcategory_is_abelian_and_inclusion_exact
    (coherent (X := X))

theorem coherent_iff_finitePresentation_of_coherent_structureSheaf
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf)
    (hO : coherent (SheafOfModules.unit X.structureSheaf)) :
    coherent F ↔ finitePresentation F := by
  sorry

theorem finiteType_to_coherent_injective_on_stalk
    {X : RingedSpace.{v}} {G F : Mod X.structureSheaf}
    (φ : G ⟶ F) (x : X) (hG : finiteType G) (hF : coherent F)
    (hφ : Function.Injective
      ((sheafModuleStalkFunctor X.structureSheaf x).map φ).hom) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      Mono ((openModuleRestrictionFunctor X U).map φ) := by
  sorry

end

end Formalization.Books.Modules.Unit06
