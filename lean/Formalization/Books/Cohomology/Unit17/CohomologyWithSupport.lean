import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Derived.Unit22.CompositionRightDerivedFunctors
import Formalization.Books.Modules.Unit06.ClosedImmersions
import Formalization.Books.Sheaves.Unit31.Infrastructure

/-!
# Cohomology of Sheaves, Chapter 17: cohomology with support in a closed subset

This file formalizes the precise assertions in the source section
`Cohomology with support in a closed subset`.  The canonical Sections-with-
support sheaf and its adjunction are supplied by Modules 6; this chapter
records the global-sections, derived, localization, and spectral-sequence
interfaces used by the source.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open Set
open TopologicalSpace
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Derived.Unit22
open Formalization.Books.Homology.Unit24
open Formalization.Books.Modules.Unit06
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Cohomology.Unit17

/-! ## `Γ_Z(X, F)` and its right-derived functors -/

/-- The subset of sections over `X` whose support is contained in `Z`. -/
def sectionsWithSupportInClosedAtTop {X : TopCat.{v}} (Z : Set X)
    (_hZ : IsClosed Z) {F : Ab X} :
    Set (F.presheaf.obj (op (⊤ : Opens X))) :=
  abelianSectionsWithSupportInClosed Z (F := F) (⊤ : Opens X)

/-- The supported global sections form an additive subgroup. -/
theorem sectionsWithSupportInClosedAtTop_isAddSubgroup
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    ∃ H : AddSubgroup (F.presheaf.obj (op (⊤ : Opens X)) : Type v),
      (H : Set (F.presheaf.obj (op (⊤ : Opens X)) : Type v)) =
        sectionsWithSupportInClosedAtTop Z hZ (F := F) := by
  sorry

/-- A chosen additive group realizing the source's `Γ_Z(X, F)`. -/
noncomputable def sectionsWithSupportInClosedGroup
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    AddCommGrpCat.{v} :=
  let H : AddSubgroup (F.presheaf.obj (op (⊤ : Opens X)) : Type v) :=
    Classical.choose (sectionsWithSupportInClosedAtTop_isAddSubgroup Z hZ F)
  AddCommGrpCat.of H

/-- The functor `F ↦ Γ_Z(X, F)`, identified with global sections of `𝓗_Z(F)`.
-/
noncomputable def sectionsWithSupportFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) : Ab X ⥤ AddCommGrpCat.{v} :=
  closedSupportSectionsFunctor Z hZ ⋙
    abelianSheafGlobalSections (closedSubspace Z)

/-- The subgroup presentation and the global-sections presentation of
`Γ_Z(X, F)` are naturally isomorphic. -/
theorem sectionsWithSupportFunctor_obj_iso
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    Nonempty ((sectionsWithSupportInClosedGroup Z hZ F) ≅
      (sectionsWithSupportFunctor Z hZ).obj F) := by
  sorry

/-- `Γ_Z(X, -)` is left exact. -/
theorem sectionsWithSupportFunctor_isLeftExact {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    IsLeftExact (sectionsWithSupportFunctor Z hZ) := by
  exact isLeftExact_comp _ _
    (closedSupportSectionsFunctor_isLeftExact Z hZ)
    (abelianSheafGlobalSections_isLeftExact (closedSubspace Z))

/-- The source's warning that supported sections are not exact in general. -/
theorem sectionsWithSupportFunctor_not_exact_in_general :
    ∃ (X : TopCat.{v}) (Z : Set X) (hZ : IsClosed Z),
      ¬ IsExact (sectionsWithSupportFunctor Z hZ) := by
  sorry

/-- The bounded-below right-derived functor `RΓ_Z(X, -)`. -/
noncomputable def sectionsWithSupportRightDerivedFunctor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    DPlus (Ab X) ⥤ DPlus AddCommGrpCat.{v} :=
  rightDerivedFunctorOfLeftExact
    (sectionsWithSupportFunctor Z hZ)
    (sectionsWithSupportFunctor_isLeftExact Z hZ)

/-- The integer-indexed higher supported-sections functor `R^qΓ_Z(X, -)`. -/
noncomputable def sectionsWithSupportCohomologyFunctor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (q : ℤ) :
    Ab X ⥤ AddCommGrpCat.{v} :=
  higherRightDerivedFunctor
    (sectionsWithSupportFunctor Z hZ)
    (sectionsWithSupportFunctor_isLeftExact Z hZ) q

/-- The group `H^q_Z(X, F)`. -/
abbrev sectionsWithSupportCohomologyObject
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) (q : ℤ) :
    AddCommGrpCat.{v} :=
  (sectionsWithSupportCohomologyFunctor Z hZ q).obj F

/-- The cohomology object `H^q_Z(X, K)` of a bounded-below derived object. -/
abbrev derivedSectionsWithSupportCohomologyObject
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z)
    (K : DPlus (Ab X)) (q : ℤ) : AddCommGrpCat.{v} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat q).obj
    ((sectionsWithSupportRightDerivedFunctor Z hZ).obj K)

/-- Applying supported sections to a bounded-below complex and passing to the
derived category. -/
noncomputable def sectionsWithSupportOnComplexes
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    CompPlus (Ab X) ⥤ DPlus AddCommGrpCat.{v} :=
  rightDerivedFunctorOfLeftExactOnComplexes
    (sectionsWithSupportFunctor Z hZ)
    (sectionsWithSupportFunctor_isLeftExact Z hZ)

/-- A bounded-below termwise-injective complex representing `K` and computing
the right-derived supported sections on `K`. -/
def sectionsWithSupportComputedByInjectiveResolution
    {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) (K : DPlus (Ab X)) : Prop :=
  ∃ I : CompPlus (Ab X),
    IsTermwiseInjectiveComplex I ∧
      Nonempty ((DerivedCategory.Plus.Qh (C := Ab X)).obj
        ((HomotopyCategory.Plus.quotient (Ab X)).obj I) ≅ K) ∧
      Nonempty ((sectionsWithSupportOnComplexes Z _hZ).obj I ≅
        (sectionsWithSupportRightDerivedFunctor Z _hZ).obj K)

theorem sectionsWithSupport_computed_by_injective_resolution
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) :
    sectionsWithSupportComputedByInjectiveResolution Z hZ K := by
  sorry

/-- Degree zero recovers `Γ_Z(X, -)`. -/
theorem sectionsWithSupportCohomologyFunctor_zero
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (sectionsWithSupportCohomologyFunctor Z hZ 0 ≅
      sectionsWithSupportFunctor Z hZ) := by
  exact higherRightDerivedFunctor_zero_iso
    (sectionsWithSupportFunctor Z hZ)
    (sectionsWithSupportFunctor_isLeftExact Z hZ)

/-! ## The complement and the localization triangle -/

/-- The open complement of a closed subset. -/
def supportComplement {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- Restriction of global sections to `X \ Z`. -/
def restrictionToSupportComplement {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X)
    (s : F.presheaf.obj (op (⊤ : Opens X))) :
    F.presheaf.obj (op (supportComplement Z hZ)) :=
  F.presheaf.map (homOfLE (show supportComplement Z hZ ≤ ⊤ by simp)).op s

/-- For an injective sheaf, restriction to `X \ Z` is surjective and has
kernel `Γ_Z(X, I)`. -/
theorem injective_restriction_to_supportComplement
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (I : Ab X)
    [Injective I] :
    Function.Surjective (restrictionToSupportComplement Z hZ I) ∧
      {s | restrictionToSupportComplement Z hZ I s = 0} =
        sectionsWithSupportInClosedAtTop Z hZ (F := I) := by
  sorry

/-- The right-derived global-sections functor on `X`. -/
noncomputable def globalSectionsRightDerivedFunctor {X : TopCat.{v}} :
    DPlus (Ab X) ⥤ DPlus AddCommGrpCat.{v} :=
  rightDerivedFunctorOfLeftExact
    (abelianSheafGlobalSections X)
    (abelianSheafGlobalSections_isLeftExact X)

/-- Global sections on the complement, regarded as a functor on sheaves on
`X`. -/
noncomputable def supportComplementGlobalSectionsFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) : Ab X ⥤ AddCommGrpCat.{v} :=
  openSheafRestriction AddCommGrpCat (supportComplement Z hZ) ⋙
    abelianSheafGlobalSections (openSubspace (supportComplement Z hZ))

theorem supportComplementGlobalSectionsFunctor_isLeftExact
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    IsLeftExact (supportComplementGlobalSectionsFunctor Z hZ) := by
  sorry

/-- The right-derived global-sections functor on `X \ Z`. -/
noncomputable def supportComplementRightDerivedFunctor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    DPlus (Ab X) ⥤ DPlus AddCommGrpCat.{v} :=
  rightDerivedFunctorOfLeftExact
    (supportComplementGlobalSectionsFunctor Z hZ)
    (supportComplementGlobalSectionsFunctor_isLeftExact Z hZ)

/-- The distinguished triangle
`RΓ_Z(X,K) → RΓ(X,K) → RΓ(X \ Z,K) → RΓ_Z(X,K)[1]`. -/
structure SupportDistinguishedTriangleData
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) where
  triangle : Triangle (DPlus AddCommGrpCat.{v})
  obj₁ : triangle.obj₁ = (sectionsWithSupportRightDerivedFunctor Z hZ).obj K
  obj₂ : triangle.obj₂ = globalSectionsRightDerivedFunctor.obj K
  obj₃ : triangle.obj₃ = (supportComplementRightDerivedFunctor Z hZ).obj K
  distinguished : triangle ∈ distTriang (DPlus AddCommGrpCat.{v})

theorem support_distinguished_triangle
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) :
    Nonempty (SupportDistinguishedTriangleData Z hZ K) := by
  sorry

/-- A finite window of the long cohomology sequence associated to a support
triangle. -/
noncomputable def supportHomologySequenceWindow
    {X : TopCat.{v}} {Z : Set X} {hZ : IsClosed Z} {K : DPlus (Ab X)}
    (T : SupportDistinguishedTriangleData Z hZ K) (n : ℤ) :
    ComposableArrows AddCommGrpCat.{v} 5 :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).homologySequenceComposableArrows₅
    T.triangle n (n + 1) rfl

theorem support_long_exact_cohomology_sequence
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) :
    ∃ T : SupportDistinguishedTriangleData Z hZ K,
      ∀ n : ℤ, (supportHomologySequenceWindow T n).Exact := by
  sorry

/-! ## The sheaf `𝓗_Z(F)` and the Grothendieck spectral sequence -/

/-- The sheaf `𝓗_Z(F)` of sections supported in `Z`, viewed on `Z`. -/
noncomputable abbrev sectionsWithSupportSheaf {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab X) : Ab (closedSubspace Z) :=
  sectionsWithSupportInClosed Z hZ F

/-- The sheaf-valued functor `𝓗_Z`. -/
noncomputable abbrev sectionsWithSupportSheafFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) : Ab X ⥤ Ab (closedSubspace Z) :=
  closedSupportSectionsFunctor Z hZ

theorem sectionsWithSupportSheafFunctor_isLeftExact
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    IsLeftExact (sectionsWithSupportSheafFunctor Z hZ) := by
  exact closedSupportSectionsFunctor_isLeftExact Z hZ

/-- The source's warning that `𝓗_Z` is not exact in general. -/
theorem sectionsWithSupportSheafFunctor_not_exact_in_general :
    ∃ (X : TopCat.{v}) (Z : Set X) (hZ : IsClosed Z),
      ¬ IsExact (sectionsWithSupportSheafFunctor Z hZ) := by
  sorry

/-- The sheaf-valued right-derived functor `R𝓗_Z`. -/
noncomputable def sectionsWithSupportSheafRightDerivedFunctor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    DPlus (Ab X) ⥤ DPlus (Ab (closedSubspace Z)) :=
  rightDerivedFunctorOfLeftExact
    (closedSupportSectionsFunctor Z hZ)
    (closedSupportSectionsFunctor_isLeftExact Z hZ)

/-- The sheaf `𝓗^q_Z(F)`. -/
noncomputable def sectionsWithSupportSheafCohomologyFunctor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (q : ℤ) :
    Ab X ⥤ Ab (closedSubspace Z) :=
  higherRightDerivedFunctor
    (closedSupportSectionsFunctor Z hZ)
    (closedSupportSectionsFunctor_isLeftExact Z hZ) q

abbrev sectionsWithSupportSheafCohomologyObject
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) (q : ℤ) :
    Ab (closedSubspace Z) :=
  (sectionsWithSupportSheafCohomologyFunctor Z hZ q).obj F

theorem sectionsWithSupportSheafCohomologyFunctor_zero
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (sectionsWithSupportSheafCohomologyFunctor Z hZ 0 ≅
      closedSupportSectionsFunctor Z hZ) := by
  exact higherRightDerivedFunctor_zero_iso
    (closedSupportSectionsFunctor Z hZ)
    (closedSupportSectionsFunctor_isLeftExact Z hZ)

/-- The sections with support in `Z` over an open `U`. -/
def sectionsWithSupportOnOpen {X : TopCat.{v}} (Z : Set X)
    (_hZ : IsClosed Z) {F : Ab X} (U : Opens X) :
    Set (F.presheaf.obj (op U)) :=
  abelianSectionsWithSupportInClosed Z (F := F) U

/-! ### Injectivity and the spectral sequence -/

/-- `𝓗_Z` sends injective abelian sheaves on `X` to injective sheaves on `Z`.
-/
theorem sectionsWithSupportSheaf_preserves_injective
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (I : Ab X)
    [Injective I] : Injective (sectionsWithSupportSheaf Z hZ I) := by
  sorry

/-- The right-acyclicity condition for applying global sections on `Z` after
`𝓗_Z`. -/
theorem sectionsWithSupportSheaf_rightAcyclicOnInjectiveImages
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    RightAcyclicOnInjectiveImages
      (closedSupportSectionsFunctor Z hZ)
      (abelianSheafGlobalSections (closedSubspace Z))
      (abelianSheafGlobalSections_isLeftExact (closedSubspace Z)) := by
  sorry

/-- The acyclicity comparison identifies the derived composite used by the
Grothendieck package with `RΓ_Z(X, -)`. -/
theorem sectionsWithSupport_rightDerivedComposition_iso
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) :
    Nonempty ((sectionsWithSupportRightDerivedFunctor Z hZ).obj K ≅
      (rightDerivedCompositionFunctor
        (closedSupportSectionsFunctor Z hZ)
        (closedSupportSectionsFunctor_isLeftExact Z hZ)
        (abelianSheafGlobalSections (closedSubspace Z))
          (abelianSheafGlobalSections_isLeftExact (closedSubspace Z))).obj K) := by
  sorry

/- The source also records that the spectral sequence is functorial in the
   derived object.  The filtered-complex package supplies the page-level
   morphism type; this family packages that assertion together with a
   functorial choice of filtered complexes and Grothendieck data. -/
structure SupportGrothendieckSpectralSequenceFamily
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) where
  complexes : DPlus (Ab X) ⥤ FilteredComplex AddCommGrpCat.{v}
  spectralData : ∀ K : DPlus (Ab X),
    GrothendieckSpectralSequenceData
      (closedSupportSectionsFunctor Z hZ)
      (closedSupportSectionsFunctor_isLeftExact Z hZ)
      (abelianSheafGlobalSections (closedSubspace Z))
      (abelianSheafGlobalSections_isLeftExact (closedSubspace Z))
      K (complexes.obj K)
  spectralMap : ∀ {K L : DPlus (Ab X)} (_f : K ⟶ L),
    Nonempty (FilteredComplexSpectralSequenceHom
      (spectralData K).spectralSequence
      (spectralData L).spectralSequence)

theorem sectionsWithSupport_grothendieck_spectral_sequence_functorial
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (SupportGrothendieckSpectralSequenceFamily Z hZ) := by
  sorry

/-- The convergent Grothendieck spectral sequence
`E₂^{p,q} = H^p(Z, 𝓗^q_Z(K) ) ⇒ H^{p+q}_Z(X,K)`. -/
theorem sectionsWithSupport_grothendieck_spectral_sequence
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) :
    ∃ C : FilteredComplex AddCommGrpCat.{v},
      Nonempty (GrothendieckSpectralSequenceData
        (closedSupportSectionsFunctor Z hZ)
        (closedSupportSectionsFunctor_isLeftExact Z hZ)
        (abelianSheafGlobalSections (closedSubspace Z))
        (abelianSheafGlobalSections_isLeftExact (closedSubspace Z))
        K C) ∧
      Nonempty ((sectionsWithSupportRightDerivedFunctor Z hZ).obj K ≅
        (rightDerivedCompositionFunctor
          (closedSupportSectionsFunctor Z hZ)
          (closedSupportSectionsFunctor_isLeftExact Z hZ)
          (abelianSheafGlobalSections (closedSubspace Z))
          (abelianSheafGlobalSections_isLeftExact (closedSubspace Z))).obj K) := by
  sorry

end Formalization.Books.Cohomology.Unit17
