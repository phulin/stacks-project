import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Derived.Unit22.CompositionRightDerivedFunctors
import Formalization.Books.Modules.Unit06.ClosedImmersions
import Formalization.Books.Sheaves.Unit22.OpenImmersions

/-!
# Cohomology of Sheaves, Chapter 17: cohomology with support in a closed subset

The source section introduces sections supported on a closed subset, their
right-derived functors, the localization triangle, and the Grothendieck
spectral sequence obtained by first forming the sheaf of supported sections.
The canonical closed-immersion API from Modules 6 supplies the sheaf-valued
functor; the declarations below add the source-facing global-section and
derived-category interfaces.
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
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit20
open Formalization.Books.Derived.Unit22
open Formalization.Books.Homology.Unit24
open Formalization.Books.Modules.Unit06
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Cohomology.Unit17

/-! ## Sections with support and their right-derived functors -/

/-- The open complement of a closed subset. -/
def supportComplement {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The source's subset of global sections whose support is contained in `Z`.

This is the underlying set of `Γ_Z(X, F)`; the subgroup statement is recorded
below, while the categorical functor is transported through the canonical
sheaf `H_Z(F)` supplied by the closed-immersion API.
-/
def sectionsWithSupportInClosedAtTop {X : TopCat.{v}} (Z : Set X)
    {F : Ab X} : Set (F.presheaf.obj (op (⊤ : Opens X))) :=
  abelianSectionsWithSupportInClosed Z (F := F) (⊤ : Opens X)

/-- The supported global sections form an additive subgroup. -/
theorem sectionsWithSupportInClosedAtTop_isAddSubgroup
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    ∃ H : AddSubgroup (F.presheaf.obj (op (⊤ : Opens X)) : Type v),
      (H : Set (F.presheaf.obj (op (⊤ : Opens X)) : Type v)) =
        sectionsWithSupportInClosedAtTop Z (F := F) := by
  sorry

/-- A chosen additive group realizing `Γ_Z(X, F)`. -/
noncomputable def sectionsWithSupportInClosedGroup
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
  AddCommGrpCat.{v} :=
    by
  let H : AddSubgroup (F.presheaf.obj (op (⊤ : Opens X)) : Type v) :=
    Classical.choose (sectionsWithSupportInClosedAtTop_isAddSubgroup Z hZ F)
  exact AddCommGrpCat.of H

/- The functor is the canonical composite `F ↦ Γ(Z, H_Z(F))`; the
   carrier-level description above is identified with it by the source's
   equality `Γ_Z(X,F) = Γ(Z,H_Z(F))`. -/
noncomputable def sectionsWithSupportFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) : Ab X ⥤ AddCommGrpCat.{v} :=
  closedSupportSectionsFunctor Z hZ ⋙
    abelianSheafGlobalSections (closedSubspace Z)

theorem sectionsWithSupportFunctor_obj_iso
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) :
    Nonempty ((sectionsWithSupportInClosedGroup Z hZ F) ≅
      (sectionsWithSupportFunctor Z hZ).obj F) := by
  sorry

/-- `Γ_Z(X,-)` is left exact. -/
theorem sectionsWithSupportFunctor_isLeftExact {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) :
    IsLeftExact (sectionsWithSupportFunctor Z hZ) := by
  exact isLeftExact_comp _ _
    (closedSupportSectionsFunctor_isLeftExact Z hZ)
    (abelianSheafGlobalSections_isLeftExact (closedSubspace Z))

/-- The failure of exactness is a genuine general warning, not a failure of
the left-exactness assertion. -/
theorem sectionsWithSupportFunctor_not_exact_in_general :
    ∃ (X : TopCat.{v}) (Z : Set X) (hZ : IsClosed Z),
      ¬ IsExact (sectionsWithSupportFunctor Z hZ) := by
  sorry

/-- The bounded-below right-derived functor `RΓ_Z(X,-)`. -/
noncomputable def sectionsWithSupportRightDerivedFunctor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    DPlus (Ab X) ⥤ DPlus AddCommGrpCat.{v} :=
  rightDerivedFunctorOfLeftExact
    (sectionsWithSupportFunctor Z hZ)
    (sectionsWithSupportFunctor_isLeftExact Z hZ)

/-- The integer-indexed cohomology functor `R^qΓ_Z(X,-)`. -/
noncomputable def sectionsWithSupportCohomologyFunctor
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (q : ℤ) :
    Ab X ⥤ AddCommGrpCat.{v} :=
  higherRightDerivedFunctor
    (sectionsWithSupportFunctor Z hZ)
    (sectionsWithSupportFunctor_isLeftExact Z hZ) q

/-- The group `H^q_Z(X,F)`. -/
abbrev sectionsWithSupportCohomologyObject
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (F : Ab X) (q : ℤ) :
    AddCommGrpCat.{v} :=
  (sectionsWithSupportCohomologyFunctor Z hZ q).obj F

/-- Cohomology with support of a bounded-below derived object. -/
abbrev derivedSectionsWithSupportCohomologyObject
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z)
    (K : DPlus (Ab X)) (q : ℤ) : AddCommGrpCat.{v} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat q).obj
    ((sectionsWithSupportRightDerivedFunctor Z hZ).obj K)

/-- Applying supported sections termwise to a bounded-below complex and then
passing to the derived category.  This is the source's
`Γ_Z(X, I^•)` computation interface. -/
noncomputable def sectionsWithSupportOnComplexes
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    CompPlus (Ab X) ⥤ DPlus AddCommGrpCat.{v} :=
  rightDerivedFunctorOfLeftExactOnComplexes
    (sectionsWithSupportFunctor Z hZ)
    (sectionsWithSupportFunctor_isLeftExact Z hZ)

/-- The source's injective-resolution computation interface. -/
def sectionsWithSupportComputedByInjectiveResolution
    {X : TopCat.{v}} (Z : Set X) (_hZ : IsClosed Z) (K : DPlus (Ab X)) : Prop :=
  ∃ I : CompPlus (Ab X),
    isBoundedBelowInjectiveComplex I.1 ∧
      Nonempty ((DerivedCategory.Plus.Qh (C := Ab X)).obj
        ((HomotopyCategory.Plus.quotient (Ab X)).obj I) ≅ K)

theorem sectionsWithSupport_computed_by_injective_resolution
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) :
    sectionsWithSupportComputedByInjectiveResolution Z hZ K := by
  sorry

/-- Degree zero recovers the supported-sections functor. -/
theorem sectionsWithSupportCohomologyFunctor_zero
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    Nonempty (sectionsWithSupportCohomologyFunctor Z hZ 0 ≅
      sectionsWithSupportFunctor Z hZ) := by
  sorry

/-! ## The restriction map and the localization triangle -/

/-- Restriction of global sections to the complement of `Z`. -/
def restrictionToSupportComplement {X : TopCat.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Ab X)
    (s : F.presheaf.obj (op (⊤ : Opens X))) :
    F.presheaf.obj (op (supportComplement Z hZ)) :=
  F.presheaf.map (homOfLE (show supportComplement Z hZ ≤ ⊤ by simp)).op s

/-- For an injective sheaf, restriction to the complement is surjective and
its kernel is exactly `Γ_Z(X,I)`. -/
theorem injective_restriction_to_supportComplement
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (I : Ab X)
    [Injective I] :
    Function.Surjective (restrictionToSupportComplement Z hZ I) ∧
      {s | restrictionToSupportComplement Z hZ I s = 0} =
        sectionsWithSupportInClosedAtTop Z (F := I) := by
  sorry

/-- The right-derived global-sections functor on `X`. -/
noncomputable def globalSectionsRightDerivedFunctor {X : TopCat.{v}} :
    DPlus (Ab X) ⥤ DPlus AddCommGrpCat.{v} :=
  rightDerivedFunctorOfLeftExact
    (abelianSheafGlobalSections X)
    (abelianSheafGlobalSections_isLeftExact X)

/-- Global sections on the complement, as a functor on sheaves on `X`. -/
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

/-- A distinguished triangle with the three derived-section objects in the
order `RΓ_Z(X,K) → RΓ(X,K) → RΓ(X\Z,K)`. -/
structure SupportDistinguishedTriangleData
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) where
  triangle : Triangle (DPlus AddCommGrpCat.{v})
  obj₁ : triangle.obj₁ = (sectionsWithSupportRightDerivedFunctor Z hZ).obj K
  obj₂ : triangle.obj₂ = (globalSectionsRightDerivedFunctor.obj K)
  obj₃ : triangle.obj₃ = (supportComplementRightDerivedFunctor Z hZ).obj K
  distinguished : triangle ∈ distTriang (DPlus AddCommGrpCat.{v})

theorem support_distinguished_triangle
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) :
    Nonempty (SupportDistinguishedTriangleData Z hZ K) := by
  sorry

/-- The finite windows of the long cohomology sequence attached to a support
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

/-! ## The sheaf of sections with support -/

/-- The sheaf `H_Z(F)` of sections supported in `Z`, viewed on `Z`. -/
noncomputable abbrev sectionsWithSupportSheaf {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Ab X) : Ab (closedSubspace Z) :=
  sectionsWithSupportInClosed Z hZ F

/-- The source's sheaf-valued functor `𝓗_Z`. -/
noncomputable abbrev sectionsWithSupportSheafFunctor {X : TopCat.{v}}
    (Z : Set X) (hZ : IsClosed Z) : Ab X ⥤ Ab (closedSubspace Z) :=
  closedSupportSectionsFunctor Z hZ

theorem sectionsWithSupportSheafFunctor_isLeftExact
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    IsLeftExact (sectionsWithSupportSheafFunctor Z hZ) := by
  exact closedSupportSectionsFunctor_isLeftExact Z hZ

/-- The sheaf-valued supported-sections functor is not exact in general. -/
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
  sorry

/-- The sheafwise description of supported sections on an open. -/
def sectionsWithSupportOnOpen {X : TopCat.{v}} (Z : Set X)
    {F : Ab X} (U : Opens X) : Set (F.presheaf.obj (op U)) :=
  abelianSectionsWithSupportInClosed Z (F := F) U

/-! ## The Grothendieck spectral sequence and injectivity -/

/-- The sheaf of supported sections carries injectives to injectives. -/
theorem sectionsWithSupportSheaf_preserves_injective
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (I : Ab X)
    [Injective I] :
    Injective ((sectionsWithSupportSheaf Z hZ I)) := by
  sorry

/-- The acyclicity condition used by the Grothendieck spectral-sequence API. -/
theorem sectionsWithSupportSheaf_rightAcyclicOnInjectiveImages
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) :
    RightAcyclicOnInjectiveImages
      (closedSupportSectionsFunctor Z hZ)
      (abelianSheafGlobalSections (closedSubspace Z))
      (abelianSheafGlobalSections_isLeftExact (closedSubspace Z)) := by
  sorry

/-- The convergent Grothendieck spectral sequence
`E₂^{p,q} = H^p(Z, 𝓗^q_Z(K)) ⇒ H^{p+q}_Z(X,K)`. -/
theorem sectionsWithSupport_grothendieck_spectral_sequence
    {X : TopCat.{v}} (Z : Set X) (hZ : IsClosed Z) (K : DPlus (Ab X)) :
    ∃ C : FilteredComplex AddCommGrpCat.{v},
      Nonempty (GrothendieckSpectralSequenceData
        (closedSupportSectionsFunctor Z hZ)
        (closedSupportSectionsFunctor_isLeftExact Z hZ)
        (abelianSheafGlobalSections (closedSubspace Z))
        (abelianSheafGlobalSections_isLeftExact (closedSubspace Z))
        K C) := by
  sorry

end Formalization.Books.Cohomology.Unit17
