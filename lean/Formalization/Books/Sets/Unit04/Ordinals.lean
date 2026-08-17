import Formalization.Books.Sets.Unit03.Classes
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Set Theory, Chapter 4: Ordinals

Mathlib already provides the von Neumann-set interfaces used by this section:
`ZFSet.IsTransitive`, `ZFSet.IsOrdinal`, `ZFSet.omega`, and the theorem that
the ordinals form a proper class.  This file adds only the source-facing
successor, limit, countability, supremum, and first-uncountable interfaces
that are not part of that canonical API.

The order-type statement at the end uses Mathlib's type-theoretic `Ordinal`
and its canonical carrier `Ordinal.ToType`.  This is the existing reusable
representation of the unique order type; `Ordinal.toZFSet` is the established
equivalence with von Neumann ordinals.
-/

universe u

namespace ZFSet

/-! ### Basic ordinal terminology -/

instance : Zero ZFSet.{u} where
  zero := ∅

@[simp]
theorem zero_eq_empty : (0 : ZFSet.{u}) = ∅ :=
  rfl

/-! The successor of a von Neumann ordinal is its union with its singleton. -/

def successor (α : ZFSet.{u}) : ZFSet.{u} :=
  α ∪ {α}

theorem successor_eq_insert (α : ZFSet.{u}) : successor α = insert α α := by
  ext x
  simp [successor, ZFSet.insert_eq, or_comm]

theorem isOrdinal_successor {α : ZFSet.{u}} (hα : α.IsOrdinal) :
    (successor α).IsOrdinal := by
  rw [successor_eq_insert]
  exact isOrdinal_succ hα

def IsSuccessorOrdinal (α : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ ∃ β : ZFSet.{u}, β.IsOrdinal ∧ α = successor β

theorem isSuccessorOrdinal_successor {β : ZFSet.{u}} (hβ : β.IsOrdinal) :
    IsSuccessorOrdinal (successor β) := by
  exact ⟨isOrdinal_successor hβ, β, hβ, rfl⟩

def IsLimitOrdinal (α : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ α ≠ (0 : ZFSet.{u}) ∧ ¬IsSuccessorOrdinal α

theorem isOrdinal_zero : (0 : ZFSet.{u}).IsOrdinal := by
  change (∅ : ZFSet.{u}).IsOrdinal
  exact isOrdinal_empty

theorem zero_is_least_ordinal {α : ZFSet.{u}} (_hα : α.IsOrdinal) :
    (0 : ZFSet.{u}) ⊆ α := by
  exact empty_subset α

/-! ### Limit ordinals and the first infinite ordinal -/

theorem IsLimitOrdinal.eq_sUnion {α : ZFSet.{u}} (_hα : IsLimitOrdinal α) :
    α = ZFSet.sUnion α := by
  sorry

theorem omega_is_first_limit_ordinal :
    IsLimitOrdinal (ZFSet.omega : ZFSet.{u}) ∧
      ∀ α : ZFSet.{u}, IsLimitOrdinal α → (ZFSet.omega : ZFSet.{u}) ⊆ α := by
  sorry

def IsInfiniteOrdinal (α : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ Cardinal.aleph0 ≤ α.card

theorem omega_is_first_infinite_ordinal :
    IsInfiniteOrdinal (ZFSet.omega : ZFSet.{u}) ∧
      ∀ α : ZFSet.{u}, IsInfiniteOrdinal α → (ZFSet.omega : ZFSet.{u}) ⊆ α := by
  sorry

/-! ### The first uncountable ordinal -/

def IsCountableOrdinal (α : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ α.card ≤ Cardinal.aleph0

def IsUncountableOrdinal (α : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ ¬IsCountableOrdinal α

noncomputable def omegaOne : ZFSet.{u} :=
  Ordinal.toZFSet (Ordinal.omega (1 : Ordinal.{u}))

theorem omegaOne_eq_countable_ordinals :
    ∀ α : ZFSet.{u}, α ∈ omegaOne ↔ IsCountableOrdinal α := by
  sorry

theorem omegaOne_is_first_uncountable_ordinal :
    IsUncountableOrdinal omegaOne ∧
      ∀ α : ZFSet.{u}, IsUncountableOrdinal α → omegaOne ⊆ α := by
  sorry

/-! ### The class of ordinals and least elements -/

/- The class is represented by the predicate supplied to `Class`. -/
def ordinalClass : Class.{u} :=
  {α | α.IsOrdinal}

theorem ordinalClass_is_proper : Class.IsProper (ordinalClass : Class.{u}) := by
  change (fun α : ZFSet.{u} => α.IsOrdinal) ∉ Class.univ
  exact ZFSet.isOrdinal_notMem_univ

theorem exists_least_ordinal_of_set {A : ZFSet.{u}}
    (hA : ∃ α : ZFSet.{u}, α ∈ A)
    (hOrd : ∀ α : ZFSet.{u}, α ∈ A → α.IsOrdinal) :
    ∃ α : ZFSet.{u}, α ∈ A ∧
      ∀ β : ZFSet.{u}, β ∈ A → α = β ∨ α ∈ β := by
  sorry

theorem exists_least_ordinal_of_class {C : Class.{u}}
    (hC : ∃ α : ZFSet.{u}, C α)
    (hOrd : ∀ α : ZFSet.{u}, C α → α.IsOrdinal) :
    ∃ α : ZFSet.{u}, C α ∧
      ∀ β : ZFSet.{u}, C β → α = β ∨ α ∈ β := by
  sorry

/-! ### Suprema -/

def ordinalSupremum (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion A

theorem ordinalSupremum_eq_sUnion (A : ZFSet.{u}) :
    ordinalSupremum A = ZFSet.sUnion A :=
  rfl

theorem ordinalSupremum_spec {A : ZFSet.{u}}
    (hA : ∀ α : ZFSet.{u}, α ∈ A → α.IsOrdinal) :
    (ordinalSupremum A).IsOrdinal ∧
      (∀ α : ZFSet.{u}, α ∈ A → α ⊆ ordinalSupremum A) ∧
      ∀ β : ZFSet.{u}, β.IsOrdinal →
        (∀ α : ZFSet.{u}, α ∈ A → α ⊆ β) → ordinalSupremum A ⊆ β := by
  sorry

end ZFSet

namespace Formalization.Books.Sets.Unit04

/-! ### Order types -/

theorem exists_unique_order_type (S : Type u) (r : S → S → Prop)
    [IsWellOrder S r] :
    ∃! α : Ordinal.{u},
      Nonempty (r ≃r (· < · : α.ToType → α.ToType → Prop)) := by
  sorry

end Formalization.Books.Sets.Unit04
