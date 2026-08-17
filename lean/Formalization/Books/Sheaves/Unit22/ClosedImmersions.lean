import Formalization.Books.Sheaves.Unit22.OpenImmersions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 22, Section 11: Closed immersions

The direct image along a closed inclusion is represented by Mathlib's
pushforward functor.  The stalk and essential-image descriptions from the
source are recorded as interfaces, while the functorial constructions use
the canonical presheaf and sheaf APIs.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open scoped ZeroObject

universe v u

noncomputable section

/-! ## The closed subspace and its direct/inverse images -/

/-- The topological space carried by a closed subset. -/
abbrev closedSubspace {X : TopCat.{v}} (Z : Set X) : TopCat.{v} :=
  TopCat.of Z

/-- The canonical inclusion of a subset as a topological subspace. -/
abbrev closedInclusion {X : TopCat.{v}} (Z : Set X) : closedSubspace Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Direct image of presheaves along a closed inclusion. -/
abbrev closedPresheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) :
    TopCat.Presheaf C (closedSubspace Z) ⥤ TopCat.Presheaf C X :=
  TopCat.Presheaf.pushforward C (closedInclusion Z)

/-- Inverse image of presheaves along a closed inclusion. -/
noncomputable abbrev closedPresheafRestriction (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (Z : Set X) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C (closedSubspace Z) :=
  TopCat.Presheaf.pullback C (closedInclusion Z)

/-- Direct image of sheaves along a closed inclusion. -/
abbrev closedSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) :
    TopCat.Sheaf C (closedSubspace Z) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (closedInclusion Z)

/-- Inverse image of set-valued sheaves along a closed inclusion. -/
noncomputable abbrev closedSetSheafRestriction {X : TopCat.{v}} (Z : Set X) :
    TopCat.Sheaf (Type v) X ⥤ TopCat.Sheaf (Type v) (closedSubspace Z) :=
  TopCat.Sheaf.pullback (Type v) (closedInclusion Z)

/-- Inverse image of abelian sheaves along a closed inclusion. -/
noncomputable abbrev closedAbelianSheafRestriction {X : TopCat.{v}} (Z : Set X) :
    TopCat.Sheaf (AddCommGrpCat.{v}) X ⥤
      TopCat.Sheaf (AddCommGrpCat.{v}) (closedSubspace Z) :=
  TopCat.Sheaf.pullback (AddCommGrpCat.{v}) (closedInclusion Z)

@[simp]
theorem closedPresheafDirectImage_obj (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X)
    (F : TopCat.Presheaf C (closedSubspace Z)) (V : Opens X) :
    ((closedPresheafDirectImage C Z).obj F).obj (op V) =
      F.obj (op ((Opens.map (closedInclusion Z)).obj V)) := rfl

/-! ## Stalks and restriction identities -/

/-- The set-valued direct image has a singleton stalk off the closed subset. -/
theorem closedSetSheafDirectImage_stalk_outside {X : TopCat.{v}} (Z : Set X)
    (F : TopCat.Sheaf (Type v) (closedSubspace Z)) (x : X) (hx : x ∉ Z) :
    Nonempty (((closedSheafDirectImage (Type v) Z).obj F).presheaf.stalk x ≃
      PUnit.{v}) := by
  sorry

/-- On the closed subset, the direct-image stalk is the original stalk. -/
theorem closedSetSheafDirectImage_stalk_inside {X : TopCat.{v}} (Z : Set X)
    (F : TopCat.Sheaf (Type v) (closedSubspace Z)) (x : X) (hx : x ∈ Z) :
    Nonempty (((closedSheafDirectImage (Type v) Z).obj F).presheaf.stalk x ≃
      F.presheaf.stalk ⟨x, hx⟩) := by
  sorry

/-- Inverse image followed by direct image is the identity for set-valued sheaves. -/
theorem closedSetSheafRestriction_directImage_iso {X : TopCat.{v}} (Z : Set X)
    (F : TopCat.Sheaf (Type v) (closedSubspace Z)) :
    Nonempty ((closedSetSheafRestriction Z).obj
      ((closedSheafDirectImage (Type v) Z).obj F) ≅ F) := by
  sorry

/-- Inverse image followed by direct image is the identity for abelian sheaves. -/
theorem closedAbelianSheafRestriction_directImage_iso {X : TopCat.{v}} (Z : Set X)
    (F : TopCat.Sheaf (AddCommGrpCat.{v}) (closedSubspace Z)) :
    Nonempty ((closedAbelianSheafRestriction Z).obj
      ((closedSheafDirectImage (AddCommGrpCat.{v}) Z).obj F) ≅ F) := by
  sorry

/-! ## Essential images -/

/-- The set-valued stalk condition characterizing a closed direct image. -/
def ClosedSingletonStalkCondition {X : TopCat.{v}} (Z : Set X)
    (G : TopCat.Sheaf (Type v) X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≃ PUnit.{v})

/-- Direct image along a closed inclusion is fully faithful on sheaves of sets. -/
theorem closedSetSheafDirectImage_fullFaithful {X : TopCat.{v}} (Z : Set X) :
    (closedSheafDirectImage (Type v) Z).Full := by
  sorry

/-- The essential image of a closed direct image is characterized by singleton stalks
outside the closed subset. -/
theorem closedSetSheafDirectImage_essentialImage {X : TopCat.{v}} (Z : Set X)
    (G : TopCat.Sheaf (Type v) X) :
    (∃ F, Nonempty ((closedSheafDirectImage (Type v) Z).obj F ≅ G)) ↔
      ClosedSingletonStalkCondition Z G := by
  sorry

/-- Direct image along a closed inclusion is fully faithful on abelian sheaves. -/
theorem closedAbelianSheafDirectImage_fullFaithful {X : TopCat.{v}} (Z : Set X) :
    (closedSheafDirectImage (AddCommGrpCat.{v}) Z).Full := by
  sorry

/-- The abelian essential image is characterized by zero stalks off the closed subset. -/
def ClosedZeroStalkCondition {X : TopCat.{v}} (Z : Set X)
    (G : TopCat.Sheaf (AddCommGrpCat.{v}) X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty
    (G.presheaf.stalk x ≅ (0 : AddCommGrpCat.{v}))

theorem closedAbelianSheafDirectImage_essentialImage {X : TopCat.{v}} (Z : Set X)
    (G : TopCat.Sheaf (AddCommGrpCat.{v}) X) :
    (∃ F, Nonempty ((closedSheafDirectImage (AddCommGrpCat.{v}) Z).obj F ≅ G)) ↔
      ClosedZeroStalkCondition Z G := by
  sorry

/-! ## Category-valued algebraic structures -/

/-- Direct image of sheaves valued in a category of algebraic structures. -/
abbrev closedAlgebraicSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (Z : Set X) :
    TopCat.Sheaf C (closedSubspace Z) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (closedInclusion Z)

/-- The generic final-stalk condition for a closed direct image. -/
def ClosedFinalStalkCondition (C : Type u) [Category.{v} C]
    [HasColimits C] [HasTerminal C] {X : TopCat.{v}} (Z : Set X)
    (G : TopCat.Sheaf C X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≅ (⊤_ C))

/-- The generic closed direct image has final stalks off the closed subset. -/
theorem closedAlgebraicSheafDirectImage_stalk_outside
    (C : Type u) [Category.{v} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{v}} (Z : Set X)
    (F : TopCat.Sheaf C (closedSubspace Z)) (x : X) (hx : x ∉ Z) :
    Nonempty (((closedAlgebraicSheafDirectImage C Z).obj F).presheaf.stalk x ≅
      (⊤_ C)) := by
  sorry

/-- The generic closed direct image is fully faithful. -/
theorem closedAlgebraicSheafDirectImage_fullFaithful
    (C : Type u) [Category.{v} C] {X : TopCat.{v}} (Z : Set X) :
    (closedAlgebraicSheafDirectImage C Z).Full := by
  sorry

/-- The generic essential image is characterized by final stalks off the closed subset. -/
theorem closedAlgebraicSheafDirectImage_essentialImage
    (C : Type u) [Category.{v} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{v}} (Z : Set X) (G : TopCat.Sheaf C X) :
    (∃ F, Nonempty ((closedAlgebraicSheafDirectImage C Z).obj F ≅ G)) ↔
      ClosedFinalStalkCondition C Z G := by
  sorry

/-! ## Exactness warning -/

/-- A nonempty complement prevents the set-valued closed direct image from being right exact. -/
theorem closedSetSheafDirectImage_not_right_exact {X : TopCat.{v}} (Z : Set X)
    (hZ : ∃ x : X, x ∉ Z) :
    ¬ PreservesFiniteColimits (closedSheafDirectImage (Type v) Z) := by
  sorry

end

end Formalization.Books.Sheaves.Unit22
