import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves of Modules, Chapter 6: Closed immersions and abelian sheaves

This file formalizes the source section `books/modules.tex:548-649`.
The notation `Ab X` is the existing `AddCommGrpCat`-valued sheaf category,
so abelian sheaves are represented by the source's sheaves of
`\underline{ℤ}_X`-modules.
-/

namespace Formalization.Books.Modules.Unit06

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.ObjectProperty
open scoped ZeroObject
open Formalization.Books.Categories.Unit23
open Formalization.Books.Sheaves.Unit08

universe v u

noncomputable section

/-! ## The closed subspace and its canonical sheaf functors -/

/- These are the canonical Mathlib constructions used by the source's closed
   immersion.  They are kept local to this chapter so that the formalization
   depends only on the general sheaf functor and stalk APIs. -/

/-- The topological space carried by a closed subset. -/
abbrev closedSubspace {X : TopCat.{v}} (Z : Set X) : TopCat.{v} :=
  TopCat.of Z

/-- The inclusion of a subset as a topological subspace. -/
abbrev closedInclusion {X : TopCat.{v}} (Z : Set X) : closedSubspace Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Direct image along the inclusion of a closed subset. -/
abbrev closedSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) :
    TopCat.Sheaf C (closedSubspace Z) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (closedInclusion Z)

/-- Inverse image along the inclusion of a closed subset for abelian sheaves. -/
noncomputable abbrev closedAbelianSheafRestriction {X : TopCat.{v}}
    (Z : Set X) (_hZ : IsClosed Z) :
    Ab X ⥤ Ab (closedSubspace Z) :=
  TopCat.Sheaf.pullback (AddCommGrpCat.{v}) (closedInclusion Z)

/-- The support of an abelian sheaf, as the set of points with nonzero stalk. -/
def additiveSheafSupport {X : TopCat.{v}} (F : Ab X) : Set X :=
  {x | Nontrivial (F.presheaf.stalk x)}

/-- Vanishing of all stalks outside a closed subset. -/
def ClosedZeroStalkCondition {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z)
    (G : Ab X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≅ (0 : AddCommGrpCat.{v}))

/- The site-level colimit API is stated for `CategoryTheory.Sheaf`; this
   bridge exposes that existing instance for the topological specialization. -/
noncomputable instance topCatSheaf_hasFiniteColimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (X : TopCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    HasFiniteColimits (TopCat.Sheaf C X) := by
  change HasFiniteColimits (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) C)
  infer_instance

/- The additive-group colimits are constructed in Mathlib at arbitrary small
   sizes; this specializes that API to the finite-colimit class needed above. -/
theorem addCommGrpCat_hasColimitsOfSize :
    HasColimitsOfSize.{0, 0} (AddCommGrpCat.{v}) := by
  infer_instance

noncomputable instance addCommGrpCat_hasFiniteColimits :
    HasFiniteColimits (AddCommGrpCat.{v}) := by
  exact @hasFiniteColimits_of_hasColimitsOfSize (AddCommGrpCat.{v})
    inferInstance addCommGrpCat_hasColimitsOfSize

/-! ## Sections with support in a closed subset -/

/- The support of a section is the support of its germ, as in the preceding
   Modules chapter.  We spell out the additive version here because an
   abelian sheaf is not presented as a module over a chosen structure sheaf. -/

/-- The germ of an abelian-sheaf section at a point of its domain. -/
noncomputable def abelianSectionGerm {X : TopCat.{v}} {F : Ab X}
    (U : Opens X) (s : F.presheaf.obj (op U)) (x : U) :
    F.presheaf.stalk x.1 :=
  TopCat.Presheaf.germ (C := AddCommGrpCat.{v}) F.presheaf U x.1 x.property s

/-- The support of a section of an abelian sheaf, inside its open domain. -/
def abelianSectionSupport {X : TopCat.{v}} {F : Ab X} (U : Opens X)
    (s : F.presheaf.obj (op U)) : Set U :=
  {x | abelianSectionGerm U s x ≠ 0}

/-- The part of a subset of `X` seen inside an open subset `U`. -/
def closedSubsetInOpen {X : TopCat.{v}} (Z : Set X) (U : Opens X) : Set U :=
  (Subtype.val : U → X) ⁻¹' Z

/-- A section is supported in `Z` when its support is contained in `Z ∩ U`. -/
def abelianSectionSupportedInClosed {X : TopCat.{v}} (Z : Set X)
    {F : Ab X} (U : Opens X) (s : F.presheaf.obj (op U)) : Prop :=
  abelianSectionSupport U s ⊆ closedSubsetInOpen Z U

/-- The sections over `U` supported in the closed subset `Z`. -/
def abelianSectionsWithSupportInClosed {X : TopCat.{v}} (Z : Set X)
    {F : Ab X} (U : Opens X) : Set (F.presheaf.obj (op U)) :=
  {s | abelianSectionSupportedInClosed Z U s}

/-- The support of an abelian sheaf is contained in a subset of its space. -/
def abelianSheafSupportContainedIn {X : TopCat.{v}} (Z : Set X)
    (F : Ab X) : Prop :=
  additiveSheafSupport F ⊆ Z

/-- A section belongs to a categorical subsheaf when it has a lift to it. -/
def abelianSubsheafContainsSection {X : TopCat.{v}} {F : Ab X}
    (P : Subobject F) (U : Opens X) (s : F.presheaf.obj (op U)) : Prop :=
  ∃ t : (P : Ab X).presheaf.obj (op U),
    P.arrow.hom.app (op U) t = s

/-! ## The largest supported subsheaf -/

/-- There is a largest abelian subsheaf whose support is contained in `Z`. -/
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

/-- Sections of the largest subsheaf are exactly the supported sections. -/
theorem closedSupportSubsheaf_section_iff {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) (U : Opens X)
    (s : F.presheaf.obj (op U)) :
    abelianSubsheafContainsSection (closedSupportSubsheaf Z hZ F) U s ↔
      s ∈ abelianSectionsWithSupportInClosed Z U := by
  sorry

/-! ## The right adjoint on abelian sheaves -/

/-- Existence of the sheaf of sections supported in `Z`, on `Z`. -/
theorem exists_closedSupportSectionsFunctor {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    ∃ H : Ab X ⥤ Ab (closedSubspace Z),
      Nonempty (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⊣ H) := by
  sorry

/-- The sheaf-valued functor `F ↦ H_Z(F)`. -/
noncomputable def closedSupportSectionsFunctor {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) : Ab X ⥤ Ab (closedSubspace Z) :=
  Classical.choose (exists_closedSupportSectionsFunctor Z hZ)

/-- The chosen adjunction between closed direct image and `H_Z`. -/
noncomputable def closedSupportSectionsFunctor_adjunction
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⊣
      closedSupportSectionsFunctor Z hZ :=
  Classical.choice (Classical.choose_spec
    (exists_closedSupportSectionsFunctor Z hZ))

/-- The source notation `H_Z(F)`, viewed as a sheaf on `Z`. -/
abbrev sectionsWithSupportInClosed {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X) : Ab (closedSubspace Z) :=
  (closedSupportSectionsFunctor Z hZ).obj F

/-- `H_Z(F)` is the sheaf corresponding to the largest supported subsheaf. -/
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

/-! ## Closed direct image -/

/-- Closed direct image is exact on abelian sheaves. -/
theorem closedAbelianSheafDirectImage_isExact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    IsExact (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ) := by
  sorry

/-- Closed direct image is fully faithful. -/
theorem closedAbelianSheafDirectImage_fullyFaithful {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).FullyFaithful := by
  sorry

/-- The essential image of closed direct image consists of sheaves supported in
`Z`. -/
theorem closedAbelianSheafDirectImage_essentialImage_support
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (G : Ab X) :
    (∃ F, Nonempty
      ((closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ).obj F ≅ G)) ↔
      abelianSheafSupportContainedIn Z G := by
  sorry

/-- Support containment is equivalent to vanishing stalks off `Z`. -/
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
  sorry

/-- Functorial form of the left-inverse statement. -/
theorem closedAbelianSheafRestriction_leftInverse_functor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty
      (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ ⋙
          closedAbelianSheafRestriction Z hZ ≅
        𝟭 (Ab (closedSubspace Z))) := by
  sorry

/-- Closed direct image preserves colimits of every size represented here. -/
theorem closedAbelianSheafDirectImage_preserves_all_colimits
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    PreservesColimitsOfSize.{v, v}
      (closedSheafDirectImage (AddCommGrpCat.{v}) Z hZ) := by
  sorry

/-! ## The set-valued warning -/

/-- Closed direct image for sheaves of sets. -/
abbrev closedSetSheafDirectImage {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) :
    TopCat.Sheaf (Type v) (closedSubspace Z) ⥤ TopCat.Sheaf (Type v) X :=
  closedSheafDirectImage (Type v) Z hZ

/-- A proper closed inclusion's set-valued direct image is not right exact. -/
theorem closedSetSheafDirectImage_not_right_exact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (hproper : ∃ x : X, x ∉ Z) :
    ¬ PreservesFiniteColimits (closedSetSheafDirectImage Z hZ) := by
  sorry

/-- Consequently, a proper closed inclusion's set-valued direct image has no
right adjoint. -/
theorem closedSetSheafDirectImage_no_right_adjoint {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (hproper : ∃ x : X, x ∉ Z) :
    ¬ ∃ H : TopCat.Sheaf (Type v) X ⥤
        TopCat.Sheaf (Type v) (closedSubspace Z),
      Nonempty (closedSetSheafDirectImage Z hZ ⊣ H) := by
  sorry

/-! ## The pointed-sheaf warning -/

/-- Germs of sections for a sheaf of pointed sets. -/
noncomputable def pointedSectionGerm {X : TopCat.{v}}
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X)
    (s : F.presheaf.obj (op U)) (x : U) :
    TopCat.Presheaf.stalk (C := Type v)
      (F.presheaf ⋙ CategoryTheory.forget Pointed) x.1 :=
  TopCat.Presheaf.germ (C := Type v)
    (F.presheaf ⋙ CategoryTheory.forget Pointed) U x.1 x.property s

/-- The germ of the distinguished point of a pointed-sheaf section. -/
noncomputable def pointedSectionBaseGerm {X : TopCat.{v}}
    {F : TopCat.Sheaf (Pointed.{v}) X} (U : Opens X) (x : U) :
    TopCat.Presheaf.stalk (C := Type v)
      (F.presheaf ⋙ CategoryTheory.forget Pointed) x.1 :=
  TopCat.Presheaf.germ (C := Type v)
    (F.presheaf ⋙ CategoryTheory.forget Pointed) U x.1 x.property
      (F.presheaf.obj (op U)).point

/-- The support of a pointed-sheaf section, relative to the basepoint. -/
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

/-- Closed direct image is exact for pointed sheaves whenever the relevant
finite limits and colimits are available. -/
theorem closedPointedSheafDirectImage_isExact {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z)
    [HasFiniteLimits (TopCat.Sheaf (Pointed.{v}) (closedSubspace Z))]
    [HasFiniteColimits (TopCat.Sheaf (Pointed.{v}) (closedSubspace Z))]
    [HasFiniteLimits (TopCat.Sheaf (Pointed.{v}) X)]
    [HasFiniteColimits (TopCat.Sheaf (Pointed.{v}) X)] :
    IsExact (closedPointedSheafDirectImage Z hZ) := by
  sorry

/-- The pointed-sheaf supported-sections functor is right adjoint to closed
direct image. -/
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

end

end Formalization.Books.Modules.Unit06
