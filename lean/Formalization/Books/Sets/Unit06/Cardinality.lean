import Formalization.Books.Sets.Unit05

/-!
# Set Theory, Chapter 6: Cardinality

The source uses ordinals as representatives of cardinals.  Mathlib's
`Cardinal.ord` is the canonical least-ordinal representative of a cardinal,
while `Cardinal` itself is the canonical quotient type on which cardinal
arithmetic is defined.  This file keeps both views visible: `cardinality`
records the source's ordinal-valued cardinality of a `ZFSet`, and the
arithmetic statements use Mathlib's canonical `Cardinal` operations.
-/

universe u

namespace Formalization.Books.Sets.Unit06

noncomputable section

/-! ### Cardinality and cardinal ordinals -/

/-- The least ordinal equinumerous with the ZFC set `A`. -/
def cardinality (A : ZFSet.{u}) : Ordinal.{u} :=
  (ZFSet.card A).ord

scoped[SetsUnit06] notation "|" A "|" =>
  Formalization.Books.Sets.Unit06.cardinality A

/-- The ordinal-valued cardinality has the same cardinal as the original set. -/
theorem cardinality_card (A : ZFSet.{u}) :
    (cardinality A).card = ZFSet.card A := by
  change ((ZFSet.card A).ord).card = ZFSet.card A
  exact Cardinal.card_ord _

/-- A set's cardinality is an initial ordinal. -/
theorem cardinality_isInitial (A : ZFSet.{u}) :
    (cardinality A).IsInitial := by
  change ((ZFSet.card A).ord).IsInitial
  exact Ordinal.isInitial_ord _

/-- `cardinality A` is least among the ordinals bijective with `A`. -/
theorem cardinality_isLeast (A : ZFSet.{u}) :
    IsLeast {α : Ordinal.{u} | Nonempty (Shrink A ≃ α.ToType)} (cardinality A) := by
  sorry

/-- An ordinal is a cardinal exactly when it is the cardinality of a set. -/
theorem isCardinal_iff_exists_cardinality (α : Ordinal.{u}) :
    α.IsInitial ↔ ∃ A : ZFSet.{u}, cardinality A = α := by
  sorry

/-! ### The first infinite cardinal and countable sets -/

/-- The ordinal representative of `ℵ₀` is the first infinite ordinal `ω`. -/
theorem aleph0_ord_eq_omega :
    (Cardinal.aleph0 : Cardinal.{u}).ord = Ordinal.omega0 := by
  exact Cardinal.ord_aleph0

/-- `ω` is the least ordinal whose cardinality is infinite. -/
theorem omega_is_first_infinite_cardinal :
    Ordinal.omega0.IsInitial ∧
      ∀ α : Ordinal.{u}, Cardinal.aleph0 ≤ α.card → Ordinal.omega0 ≤ α := by
  sorry

/-- A ZFC set is countable when its cardinality is at most `ℵ₀`. -/
def IsCountable (A : ZFSet.{u}) : Prop :=
  cardinality A ≤ (Cardinal.aleph0 : Cardinal.{u}).ord

/-- The ordinal and cardinal formulations of countability agree. -/
theorem isCountable_iff_card_le_aleph0 (A : ZFSet.{u}) :
    IsCountable A ↔ ZFSet.card A ≤ Cardinal.aleph0 := by
  sorry

/-! ### Successor cardinals and alephs -/

/-- The least cardinal strictly larger than an ordinal `α`. -/
def cardinalSuccessor (α : Ordinal.{u}) : Cardinal.{u} :=
  Order.succ α.card

/-- The cardinal successor is initial when represented by its least ordinal. -/
theorem cardinalSuccessor_ord_isInitial (α : Ordinal.{u}) :
    (cardinalSuccessor α).ord.IsInitial := by
  change (Order.succ α.card).ord.IsInitial
  exact Ordinal.isInitial_ord _

/-- `cardinalSuccessor α` is the least cardinal whose ordinal representative is above `α`. -/
theorem cardinalSuccessor_isLeast (α : Ordinal.{u}) :
    IsLeast {κ : Cardinal.{u} | α < κ.ord} (cardinalSuccessor α) := by
  sorry

/-- Mathlib's aleph function supplies the transfinite successor-cardinal recursion. -/
theorem aleph_successor (α : Ordinal.{u}) :
    Order.succ (Cardinal.aleph α) = Cardinal.aleph (α + 1) := by
  exact Cardinal.succ_aleph α

/-- The first successor aleph is the successor of `ℵ₀`. -/
theorem aleph_one_eq_succ_aleph0 :
    Cardinal.aleph (1 : Ordinal.{u}) =
      Order.succ (Cardinal.aleph0 : Cardinal.{u}) := by
  sorry

/-- The next successor aleph is the successor of `ℵ₁`. -/
theorem aleph_two_eq_succ_aleph_one :
    Cardinal.aleph (2 : Ordinal.{u}) =
      Order.succ (Cardinal.aleph (1 : Ordinal.{u})) := by
  sorry

/-- At a limit ordinal, the aleph function is the supremum of its earlier values. -/
theorem aleph_limit (α : Ordinal.{u}) (hα : Order.IsSuccLimit α) :
    Cardinal.aleph α =
      ⨆ β : Set.Iio α, Cardinal.aleph β.1 := by
  sorry

/-- The ordinal representative of `ℵ₁` is the first uncountable ordinal `ω₁`. -/
theorem aleph_one_ord_eq_omega_one :
    (Cardinal.aleph (1 : Ordinal.{u})).ord =
      Ordinal.omega (1 : Ordinal.{u}) := by
  sorry

/-! ### Cardinal arithmetic -/

/-- Cardinal addition is the cardinality of a disjoint sum. -/
theorem cardinal_add_eq_mk_sum (κ μ : Cardinal.{u}) :
    κ + μ = Cardinal.mk (κ.out ⊕ μ.out) := by
  sorry

/-- Cardinal multiplication is the cardinality of a Cartesian product. -/
theorem cardinal_mul_eq_mk_prod (κ μ : Cardinal.{u}) :
    κ * μ = Cardinal.mk (κ.out × μ.out) := by
  sorry

/-- Two infinite cardinals have sum and product equal to their maximum. -/
theorem infinite_cardinal_add_mul_eq_max {κ μ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hμ : Cardinal.aleph0 ≤ μ) :
    κ + μ = max κ μ ∧ κ * μ = max κ μ := by
  exact ⟨Cardinal.add_eq_max hκ, Cardinal.mul_eq_max hκ hμ⟩

/-- Cardinal exponentiation is the cardinality of the function type `λ → κ`. -/
theorem cardinal_pow_eq_mk_fun (κ μ : Cardinal.{u}) :
    κ ^ μ = Cardinal.mk (μ.out → κ.out) := by
  sorry

/-! ### Suprema of cardinals -/

/-- The supremum of a set of cardinals is represented by the union of their initial ordinals. -/
theorem cardinal_supremum_eq_union (K : Set Cardinal.{u}) :
    (sSup K).ord = sSup (Cardinal.ord '' K) := by
  sorry

/-- The supremum of a set of cardinals is itself a cardinal. -/
theorem cardinal_supremum_isCardinal (K : Set Cardinal.{u}) :
    (sSup K).ord.IsInitial := by
  exact Ordinal.isInitial_ord _

end

end Formalization.Books.Sets.Unit06
