import Formalization.Books.Modules.Unit05.Supports
import Formalization.Books.Sheaves.Unit22.ClosedImmersions
import Mathlib.CategoryTheory.Category.Pointed

/-!
# Sheaves of Modules, Chapter 6: Closed immersions and abelian sheaves

The source section is `books/modules.tex:548-649`.  Closed direct images,
inverse images, stalk calculations, full faithfulness, and the essential-image
criterion are reused from the canonical closed-immersion API in
`Sheaves.Unit22`.  This file adds the source-facing support predicates and
the right-adjoint interfaces for abelian and pointed sheaves.
-/

namespace Formalization.Books.Modules.Unit06

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Modules.Unit05
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit22

universe v

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

end

end Formalization.Books.Modules.Unit06
