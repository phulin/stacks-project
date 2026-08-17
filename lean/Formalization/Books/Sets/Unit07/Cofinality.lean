import Formalization.Books.Sets.Unit06
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Set Theory, Chapter 7: Cofinality

Mathlib provides the cofinal-subset predicate `IsCofinal` and the
cardinal-valued cofinality `Ordinal.cof`.  The source uses the corresponding
initial ordinal as its ordinal-valued cofinality, so this file records that
small bridge and keeps the source's order-type formulation visible.
-/

universe u

namespace Formalization.Books.Sets.Unit07

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Ordinal
open Set

/-! ### Cofinal subsets and ordinal cofinality -/

/-- The ordinal-valued cofinality used by the source. -/
def cofinality (α : Ordinal.{u}) : Ordinal.{u} :=
  (Ordinal.cof α).ord

/-- A subset of an ordinal inherits its well-order from the ambient ordinal. -/
theorem cofinal_subset_isWellOrder (α : Ordinal.{u}) (S : Set α.ToType) :
    IsWellOrder S ((· < ·) : S → S → Prop) := by
  infer_instance

/-- An ordinal has a cofinal subset of order type its ordinal cofinality. -/
theorem exists_cofinal_subset_orderType (α : Ordinal.{u}) :
    ∃ S : Set α.ToType, IsCofinal S ∧ typeLT S = cofinality α := by
  simpa [cofinality] using (Ordinal.exists_ord_cof_eq α.ToType)

/-- The source's ordinal cofinality is least among order types of cofinal sets. -/
theorem cofinality_isLeast_orderType (α : Ordinal.{u}) :
    IsLeast {β : Ordinal.{u} |
      ∃ S : Set α.ToType, IsCofinal S ∧ typeLT S = β} (cofinality α) := by
  sorry

/-- The cofinality of an ordinal is a cardinal, represented by an initial ordinal. -/
theorem cofinality_isCardinal (α : Ordinal.{u}) :
    (cofinality α).IsInitial := by
  exact Ordinal.isInitial_ord _

/-- The cardinal represented by the source's ordinal cofinality. -/
theorem cofinality_card (α : Ordinal.{u}) :
    (cofinality α).card = Ordinal.cof α := by
  simp [cofinality]

/-- The cardinal-valued formulation is least among cardinalities of cofinal sets. -/
theorem cofinality_isLeast_cardinality (α : Ordinal.{u}) :
    IsLeast {κ : Cardinal.{u} |
      ∃ S : Set α.ToType, IsCofinal S ∧ Cardinal.mk S = κ} (Ordinal.cof α) := by
  sorry

/-! ### Suprema below a cofinality -/

/-- A family indexed by fewer than `cf β` elements has supremum below `β`. -/
theorem ordinal_iSup_lt_of_card_lt_cof (β : Ordinal.{u}) (S : Type u)
    (hS : Cardinal.mk S < Ordinal.cof β) (f : S → Ordinal.{u})
    (hf : ∀ s, f s < β) : ⨆ s, f s < β := by
  exact Ordinal.iSup_lt_of_lt_cof hS hf

/-! ### Lifting maps through ordinal-indexed colimits -/

/-- A chosen colimit of a diagram of types indexed by the ordinals below `β`. -/
structure OrdinalSetColimit (β : Ordinal.{u}) where
  diagram : Set.Iio β ⥤ Type u
  cocone : Cocone diagram
  isColimit : IsColimit cocone

/-- The map from a stage of an ordinal-indexed colimit to its colimit point. -/
def OrdinalSetColimit.stageMap {β : Ordinal.{u}} (C : OrdinalSetColimit β)
    (i : Set.Iio β) : C.diagram.obj i → C.cocone.pt :=
  fun x => C.cocone.ι.app i x

/-- A map from a small source lifts to one stage of an ordinal-indexed colimit. -/
theorem map_from_set_lifts {β : Ordinal.{u}} (C : OrdinalSetColimit β)
    (S : Type u) (φ : S → C.cocone.pt)
    (hS : Cardinal.mk S < Ordinal.cof β) :
    ∃ i : Set.Iio β, ∃ ψ : S → C.diagram.obj i,
      ∀ s : S, C.stageMap i (ψ s) = φ s := by
  sorry

/-! ### Arbitrarily large cofinalities -/

/-- There are ordinals with cofinality larger than any given cardinal. -/
theorem exists_ordinal_cofinality_gt (κ : Cardinal.{u}) :
    ∃ α : Ordinal.{u}, κ < Ordinal.cof α := by
  sorry

end

end Formalization.Books.Sets.Unit07
