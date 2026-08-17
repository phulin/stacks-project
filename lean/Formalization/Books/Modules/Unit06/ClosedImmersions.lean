import Formalization.Books.Modules.Unit05.Supports
import Formalization.Books.Homology.Unit10.SerreSubcategories
import Formalization.Books.Sheaves.Unit22.ClosedImmersions
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Formalization.Books.Topology.Unit02.BasicNotions
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
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
open scoped BigOperators

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
    (_hZ : IsClosed Z) (F : Ab X) :
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
    (Z : Set X) (hZ : IsClosed Z) (_hcomp : ∃ x : X, x ∉ Z) :
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
    (a b : ℝ) (_ha : a < 0) (_hb : 0 < b) :
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
    (_hF : finiteType F) :
    finiteType (image φ) := by
  sorry

theorem finiteType_of_shortExact {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (_h₁ : finiteType F₁) (_h₃ : finiteType F₃) :
    finiteType F₂ := by
  sorry

def moduleMapSurjectiveOnOpen {X : RingedSpace.{v}}
    {F G : Mod X.structureSheaf} (φ : F ⟶ G) (U : Opens X.carrier) : Prop :=
  Epi ((openModuleRestrictionFunctor X U).map φ)

theorem finiteType_surjective_on_stalk
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : G ⟶ F) (x : X)
    (_hF : finiteType F)
    (_hφ : Function.Surjective ((sheafModuleStalkFunctor X.structureSheaf x).map φ).hom) :
    ∃ U : Opens X.carrier, x ∈ U ∧ moduleMapSurjectiveOnOpen φ U := by
  sorry

theorem finiteType_stalk_zero {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (x : X) (_hF : finiteType F)
    (_hFx : IsZero ((sheafModuleStalkFunctor X.structureSheaf x).obj F)) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      IsZero ((openModuleRestrictionFunctor X U).obj F) := by
  sorry

theorem finiteType_support_isClosed {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (_hF : finiteType F) :
    IsClosed (moduleSupport F) := by
  sorry

theorem finiteType_directed_colimit_exists_surjective_index
    {X : RingedSpace.{v}} (I : Type v) [Preorder I]
    (D : I ⥤ Mod X.structureSheaf) (_hI : IsDirectedSet I)
    [CompactSpace (X : Type v)] (_hF : finiteType (colimit D)) :
    ∃ i : I, Epi (colimit.ι D i) := by
  sorry

theorem finiteType_directed_colimit_stabilizes
    {X : RingedSpace.{v}} (I : Type v) [Preorder I]
    (D : I ⥤ Mod X.structureSheaf) (_hI : IsDirectedSet I)
    [CompactSpace (X : Type v)] (_hF : finiteType (colimit D))
    (_hinj : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f)) :
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

/-- A witness that quasi-coherent modules fail to form an abelian category on
some ringed space. -/
def hasNonabelianQuasiCoherentCategory : Prop :=
  ∃ X : RingedSpace.{v}, ¬ Nonempty (Abelian (QCoh (X := X)))

theorem not_allQuasiCoherentCategoriesAbelian :
    ¬ allQuasiCoherentCategoriesAbelian := by
  sorry

theorem exists_nonabelianQuasiCoherentCategory :
    hasNonabelianQuasiCoherentCategory := by
  sorry

theorem quasiCoherent_iff_local_presentation {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) :
    quasiCoherent F ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasModulePresentationOn F U := by
  rfl

theorem quasiCoherent_directSum {X : RingedSpace.{v}}
    {F G : Mod X.structureSheaf} (_hF : quasiCoherent F)
    (_hG : quasiCoherent G) : quasiCoherent (F ⊞ G) := by
  sorry

def infiniteDirectSumsPreserveQuasiCoherent : Prop :=
  ∀ (X : RingedSpace.{v}) (I : Type v) (F : I → Mod X.structureSheaf),
    (∀ i, quasiCoherent (F i)) →
      quasiCoherent (colimit (Discrete.functor F))

/-- A witness that an infinite direct sum of quasi-coherent modules need not
be quasi-coherent. -/
def hasInfiniteDirectSumQuasiCoherentFailure : Prop :=
  ∃ (X : RingedSpace.{v}) (I : Type v), Infinite I ∧
    ∃ F : I → Mod X.structureSheaf,
      (∀ i, quasiCoherent (F i)) ∧
        ¬ quasiCoherent (colimit (Discrete.functor F))

theorem not_infiniteDirectSumsPreserveQuasiCoherent :
    ¬ infiniteDirectSumsPreserveQuasiCoherent := by
  sorry

theorem exists_infiniteDirectSumQuasiCoherentFailure :
    hasInfiniteDirectSumQuasiCoherentFailure := by
  sorry

theorem quasiCoherent_pullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    quasiCoherent G → quasiCoherent ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

/-! ## The sheaf associated to a module -/

/- The source gives three descriptions of the associated sheaf.  The
   sectionwise tensor-product presheaf and its sheafification are the
   canonical construction; the presentation and one-point descriptions below
   record the other two source-facing realizations. -/

/-- The ring of global sections of a ringed space. -/
abbrev globalSectionsRing (X : RingedSpace.{v}) : Type v :=
  X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))

/-- The constant presheaf of rings with value `R`. -/
abbrev constantRingPresheaf (X : RingedSpace.{v}) (R : Type v) [Ring R] :
    TopCat.Presheaf RingCat X.carrier :=
  (Functor.const (Opens X.carrier)ᵒᵖ).obj (RingCat.of R)

/-- The constant presheaf of `R`-modules with value `M`. -/
noncomputable def constantModulePresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R] (M : ModuleCat R) :
    PresheafOfModules (constantRingPresheaf X R) :=
  (PresheafOfModules.constFunctor
      (Limits.constCocone (Opens X.carrier)ᵒᵖ (RingCat.of R))).obj M

/-- The canonical map from the constant ring presheaf to the structure
sheaf induced by a ring map from global sections. -/
noncomputable def globalSectionsPresheafMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    constantRingPresheaf X R ⟶ X.structureSheaf.obj := by
  refine {
    app := fun U => RingCat.ofHom
      ((X.structureSheaf.obj.map
        (homOfLE (show U.unop ≤ (⊤ : Opens X.carrier) from le_top)).op).hom.comp α)
    naturality := ?_ }
  intro U V f
  apply RingCat.hom_ext
  ext r
  change ((X.structureSheaf.obj.map
      (homOfLE (show V.unop ≤ (⊤ : Opens X.carrier) from le_top)).op).hom (α r)) =
    (X.structureSheaf.obj.map f).hom
      ((X.structureSheaf.obj.map
        (homOfLE (show U.unop ≤ (⊤ : Opens X.carrier) from le_top)).op).hom (α r))
  rw [← RingCat.comp_apply, ← X.structureSheaf.obj.map_comp]
  have h :
      (homOfLE (show V.unop ≤ (⊤ : Opens X.carrier) from le_top)).op =
        (homOfLE (show U.unop ≤ (⊤ : Opens X.carrier) from le_top)).op ≫ f :=
    Subsingleton.elim _ _
  rw [h]

/-- The presheaf tensor product underlying the associated sheaf. -/
noncomputable def associatedSheafPresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    PresheafOfModules X.structureSheaf.obj :=
  Formalization.Books.Sheaves.Unit06.tensorProductPresheaf
    (globalSectionsPresheafMap α) (constantModulePresheaf M)

/-- The associated-sheaf functor, obtained by sheafifying the sectionwise
tensor product `U ↦ O_X(U) ⊗_R M`. -/
noncomputable def associatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    ModuleCat R ⥤ Mod X.structureSheaf :=
  (PresheafOfModules.constFunctor
      (Limits.constCocone (Opens X.carrier)ᵒᵖ (RingCat.of R))) ⋙
    Formalization.Books.Sheaves.Unit06.changeOfRings
      (globalSectionsPresheafMap α) ⋙
    PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)

/-- The sheaf associated to a module over `R` and a map `R → Γ(X, O_X)`. -/
noncomputable abbrev associatedSheafModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Mod X.structureSheaf :=
  (associatedSheafFunctor α).obj M

/-- The source notation `\mathcal F_M` for an associated sheaf. -/
noncomputable abbrev associatedSheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (M : Type v) [AddCommGroup M] [Module R M] : Mod X.structureSheaf :=
  associatedSheafModule α (ModuleCat.of R M)

theorem associatedSheafFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    (associatedSheafFunctor α).obj M = associatedSheafModule α M := by
  rfl

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

/-! The one-point and free-presentation descriptions in the source are
    packaged together so that all three constructions have usable Lean
    interfaces. -/

/-- The one-point ringed space whose ring of sections is `R`. -/
noncomputable def onePointRingedSpace (R : Type v) [Ring R] : RingedSpace.{v} where
  carrier := TopCat.of PUnit
  structureSheaf :=
    (CategoryTheory.constantSheaf
      (Opens.grothendieckTopology (TopCat.of PUnit)) RingCat.{v}).obj (RingCat.of R)

/-- The global sections of the chosen one-point structure sheaf identify with
the coefficient ring. -/
theorem exists_onePointGlobalSectionsEquiv
    (R : Type v) [Ring R] :
    Nonempty (globalSectionsRing (onePointRingedSpace R) ≃+* R) := by
  sorry

noncomputable def onePointGlobalSectionsEquiv
    (R : Type v) [Ring R] : globalSectionsRing (onePointRingedSpace R) ≃+* R :=
  Classical.choice (exists_onePointGlobalSectionsEquiv R)

/-- A map to the one-point ringed space induces `α` on global sections. -/
def onePointRingedSpaceHomInduces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (f : RingedSpaceHom X (onePointRingedSpace R)) : Prop :=
  (ringedSpaceGlobalSectionsMap f).comp
      (onePointGlobalSectionsEquiv R).symm.toRingHom = α

/-- A morphism to the one-point ringed space inducing a prescribed map on
global sections. -/
theorem exists_onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    ∃ f : RingedSpaceHom X (onePointRingedSpace R),
      onePointRingedSpaceHomInduces α f := by
  sorry

noncomputable def onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    RingedSpaceHom X (onePointRingedSpace R) :=
  Classical.choose (exists_onePointRingedSpaceHom α)

theorem onePointRingedSpaceHom_induces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    onePointRingedSpaceHomInduces α (onePointRingedSpaceHom α) := by
  exact Classical.choose_spec (exists_onePointRingedSpaceHom α)

/-- A module on the one-point ringed space corresponding to an `R`-module. -/
structure PointModuleDescription {R : Type v} [Ring R] (M : ModuleCat R) where
  pointModule : Mod (onePointRingedSpace R).structureSheaf
  correspondence :
    ∃ e : (Mod (onePointRingedSpace R).structureSheaf) ≌ ModuleCat R,
      Nonempty (pointModule ≅ e.inverse.obj M)

/-- The one-point pullback realization of the associated sheaf. -/
structure PullbackDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) where
  projection : RingedSpaceHom X (onePointRingedSpace R)
  projection_is_canonical : projection = onePointRingedSpaceHom α
  pointModule : PointModuleDescription M
  pullbackToAssociated :
    ∀ [_h : ((SheafOfModules.pushforward (F := Opens.map projection.continuous)
      projection.sharp).IsRightAdjoint)],
      Nonempty
        ((sheafModuleRingedSpacePullback projection).obj pointModule.pointModule ≅
          associatedSheafModule α M)

/-- A presentation of a module by free modules. -/
structure ModulePresentation {R : Type v} [Ring R] (M : ModuleCat R) where
  generators : Type v
  relations : Type v
  relationMap : (ModuleCat.free R).obj relations ⟶
    (ModuleCat.free R).obj generators
  quotientIso : Nonempty (cokernel relationMap ≅ M)

/-- The coefficient of a relation generator in a free presentation. -/
def ModulePresentation.matrixEntry {R : Type v} [Ring R] {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations) (i : P.generators) : R :=
  let z : P.generators →₀ R := P.relationMap.hom (ModuleCat.freeMk j)
  z i

/-- The section of a free sheaf obtained from one column of presentation
coefficients. -/
noncomputable def ModulePresentation.matrixSection
    {X : RingedSpace.{v}} {R : Type v} [Ring R] {M : ModuleCat R}
    (P : ModulePresentation M)
    (entries : P.relations → P.generators → globalSectionsRing X)
    (j : P.relations) :
    sheafModuleSections X.structureSheaf
      (SheafOfModules.free P.generators : Mod X.structureSheaf)
      (⊤ : Opens X.carrier) := by
  let z : P.generators →₀ R := P.relationMap.hom (ModuleCat.freeMk j)
  exact ∑ i ∈ z.support,
    entries j i •
      (SheafOfModules.freeSection (R := X.structureSheaf) i).eval
        (op (⊤ : Opens X.carrier))

/-- The presentation, matrix, and one-point descriptions of `F_M` are
canonically identified. -/
structure AssociatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) where
  modulePresentation : ModulePresentation M
  matrixEntries : modulePresentation.relations → modulePresentation.generators →
    globalSectionsRing X
  matrixEntries_eq : matrixEntries = fun j i ↦
    α (modulePresentation.matrixEntry j i)
  presentationMap :
    (SheafOfModules.free modulePresentation.relations : Mod X.structureSheaf) ⟶
      (SheafOfModules.free modulePresentation.generators : Mod X.structureSheaf)
  presentationMap_matrix :
    ∀ j, sheafModuleSectionsMap X.structureSheaf presentationMap
        (⊤ : Opens X.carrier)
        ((SheafOfModules.freeSection (R := X.structureSheaf) j).eval
          (op (⊤ : Opens X.carrier))) =
      modulePresentation.matrixSection matrixEntries j
  presentationCokernel : Mod X.structureSheaf
  presentationCokernelIso : Nonempty
    (cokernel presentationMap ≅ presentationCokernel)
  pullbackDescription : PullbackDescription α M
  presentationToAssociated : Nonempty
    (presentationCokernel ≅ associatedSheafModule α M)

theorem exists_associatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty (AssociatedSheafDescriptions α M) := by
  sorry

theorem associatedSheaf_quasiCoherent
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] :
    quasiCoherent (associatedSheaf α M) := by
  sorry

theorem associatedSheaf_stalk_iso
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] (x : X) :
    Nonempty
      ((sheafModuleStalkFunctor X.structureSheaf x).obj (associatedSheaf α M) ≅
        associatedStalkTensorModule α M x) := by
  sorry

theorem associatedSheaf_preserves_colimits
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v)) :
    PreservesColimitsOfSize.{v, v} (associatedSheafFunctor α) := by
  sorry

theorem associatedSheaf_hom_equiv
    {X : RingedSpace.{v}}
    {R : Type v} [Ring R]
    (α : R →+* (X.structureSheaf.obj.obj (op ⊤) : Type v))
    (M : Type v) [AddCommGroup M] [Module R M] (G : Mod X.structureSheaf) :
    Nonempty
      ((associatedSheaf α M ⟶ G) ≃
        (ModuleCat.of R M ⟶ associatedGlobalSectionsModule α G)) := by
  sorry

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
    (_hx : hasQuasiCompactNeighborhoodBasis x)
    (_hF : quasiCoherent F) :
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

abbrev CountableIndex : Type v := ULift.{v} ℕ

abbrev CountablePairIndex : Type v := ULift.{v} (ℕ × ℕ)

/-- A free-sheaf morphism is not locally a finite matrix on the indicated
neighbourhood basis. -/
def NotLocallyFiniteLinearCombination {X : RingedSpace.{v}}
    (φ : (SheafOfModules.free CountableIndex : Mod X.structureSheaf) ⟶
      (SheafOfModules.free CountablePairIndex : Mod X.structureSheaf))
    (U : ℕ → Opens X.carrier) : Prop :=
  ∀ (n j : ℕ), 2 * n < j →
    ¬ ∃ K : Finset ℕ,
      sheafModuleSectionsMap X.structureSheaf φ (U n)
          ((SheafOfModules.freeSection (R := X.structureSheaf)
            (⟨j⟩ : CountableIndex)).eval (op (U n))) ∈
        Submodule.span (X.structureSheaf.obj.obj (op (U n)))
          ((fun i : ℕ ↦
              ((SheafOfModules.freeSection (R := X.structureSheaf)
                (⟨(j, i)⟩ : CountablePairIndex)).eval (op (U n)))) '' (K : Set ℕ))

/-- A cutoff function for the countable wedge-of-lines example. -/
structure CutoffFunction where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  vanishes_on : ∀ x, x ∈ Set.Ioo (-1 : ℝ) 1 → toFun x = 0
  is_one_on : ∀ x, x < -2 ∨ 2 < x → toFun x = 1

instance : CoeFun CutoffFunction (fun _ ↦ ℝ → ℝ) :=
  ⟨CutoffFunction.toFun⟩

/-- The rescaled cutoff functions used on the individual lines. -/
def scaledCutoff (f : CutoffFunction) (n : ℕ) : ℝ → ℝ :=
  fun x ↦ f ((n : ℝ) * x)

/-- Local finiteness of the branch coefficients at the wedge point. -/
def LocallyFiniteBranchCoefficients {X : RingedSpace.{v}}
    (c : ℕ → ℕ → X → ℝ) : Prop :=
  ∀ j x, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ K : Finset ℕ, ∀ z : X, z ∈ U → ∀ i, i ∉ K → c j i z = 0

/-- The countable wedge of real lines and the coefficient data from the
source's non-matrix example. -/
structure WedgeOfLinesExample where
  X : RingedSpace.{v}
  origin : X
  branch : ℕ → ℝ → X
  branch_cover : ∀ z : X, z = origin ∨ ∃ i x, x ≠ 0 ∧ z = branch i x
  branch_zero : ∀ i, branch i 0 = origin
  branch_separated : ∀ {i j : ℕ} {x y : ℝ},
    branch i x = branch j y → (x = 0 ∧ y = 0) ∨ (i = j ∧ x = y)
  wedge_topology : ∀ V : Set X,
    IsOpen V ↔ ∀ i, IsOpen (branch i ⁻¹' V)
  continuous_function_sections : ∀ U : Opens X.carrier,
    Nonempty (X.structureSheaf.obj.obj (op U) ≃+*
      ContinuousMap (U : Set X) ℝ)
  cutoff : CutoffFunction
  neighbourhood : ℕ → Opens X.carrier
  neighbourhood_basis :
    IsFundamentalSystemOfNeighborhoods origin
      (fun n ↦ (neighbourhood n : Set X))
  neighbourhood_on_branch : ∀ n i x,
    branch i x ∈ neighbourhood n ↔
      -(1 : ℝ) / (n + 1 : ℝ) < x ∧ x < (1 : ℝ) / (n + 1 : ℝ)
  coefficient : ℕ → ℕ → X → ℝ
  coefficient_at_origin : ∀ j i, coefficient j i origin = 0
  coefficient_continuous : ∀ j i, Continuous (coefficient j i)
  coefficient_on_branch : ∀ j i x, x ≠ 0 →
    coefficient j i (branch i x) = scaledCutoff cutoff j x
  coefficient_off_branch : ∀ j i k x, x ≠ 0 → k ≠ i →
    coefficient j k (branch i x) = 0
  coefficient_locally_finite : LocallyFiniteBranchCoefficients coefficient
  matrixMap :
    (SheafOfModules.free CountableIndex : Mod X.structureSheaf) ⟶
      (SheafOfModules.free CountablePairIndex : Mod X.structureSheaf)
  matrixMap_not_finite :
    NotLocallyFiniteLinearCombination matrixMap neighbourhood

def associatedSheafWarningAboutLocalMatrices : Prop :=
  Nonempty WedgeOfLinesExample

theorem exists_associatedSheafWarningAboutLocalMatrices :
    associatedSheafWarningAboutLocalMatrices := by
  sorry

/- The source's final suggestions that there should be a quasi-coherent module
   not locally of the form `F_M`, and locally non-module-induced maps between
   associated sheaves, are explicitly conjectural remarks rather than stated
   mathematical assertions. -/

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
    (_hF : finitePresentation F) : quasiCoherent F := by
  sorry

theorem finitePresentation_cokernel_of_finiteType
    {X : RingedSpace.{v}}
    {F G : Mod X.structureSheaf} (φ : G ⟶ F)
    (_hF : finitePresentation F) (_hG : finiteType G) :
    finitePresentation (cokernel φ) := by
  sorry

theorem finitePresentation_kernel_of_surjection_from_free
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (I : Type v) [Finite I]
    (ψ : (SheafOfModules.free I : Mod X.structureSheaf) ⟶ F)
    (_hF : finitePresentation F) (_hψ : Epi ψ) :
    finiteType (kernel ψ) := by
  sorry

theorem finitePresentation_kernel_of_surjection
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (θ : G ⟶ F) (_hF : finitePresentation F)
    (_hG : finiteType G) (_hθ : Epi θ) :
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
    (_hF : finitePresentation F) (I : Type v) [Finite I] (x : X)
    (_hIso : Nonempty
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

/-- A coherent module has a finite local presentation, and hence is
quasi-coherent. -/
theorem coherent_finitePresentation
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (_hF : coherent F) : finitePresentation F ∧ quasiCoherent F := by
  sorry

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
    (P : Subobject F) (_hF : coherent F)
    (_hP : finiteType (P : Mod X.structureSheaf)) :
    coherent (P : Mod X.structureSheaf) := by
  sorry

theorem finiteType_kernel_to_coherent
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) (_hF : finiteType F) (_hG : coherent G) :
    finiteType (kernel φ) := by
  sorry

theorem coherent_kernel_cokernel
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) (_hF : coherent F) (_hG : coherent G) :
    coherent (kernel φ) ∧ coherent (cokernel φ) := by
  sorry

theorem coherent_right_of_shortExact
    {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (_h₁ : coherent F₁) (_h₂ : coherent F₂) :
    coherent F₃ := by
  sorry

theorem coherent_middle_of_shortExact
    {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (_h₁ : coherent F₁) (_h₃ : coherent F₃) :
    coherent F₂ := by
  sorry

theorem coherent_left_of_shortExact
    {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (_h₂ : coherent F₂) (_h₃ : coherent F₃) :
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
    (_hO : coherent (SheafOfModules.unit X.structureSheaf)) :
    coherent F ↔ finitePresentation F := by
  sorry

theorem finiteType_to_coherent_injective_on_stalk
    {X : RingedSpace.{v}} {G F : Mod X.structureSheaf}
    (φ : G ⟶ F) (x : X) (_hG : finiteType G) (_hF : coherent F)
    (_hφ : Function.Injective
      ((sheafModuleStalkFunctor X.structureSheaf x).map φ).hom) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      Mono ((openModuleRestrictionFunctor X U).map φ) := by
  sorry

end

end Formalization.Books.Modules.Unit06
