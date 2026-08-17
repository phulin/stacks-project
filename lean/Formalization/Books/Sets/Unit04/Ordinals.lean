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
  ext x
  constructor
  · intro hx
    have hsub : insert x x ⊆ α := by
      intro y hy
      rcases mem_insert_iff.mp hy with rfl | hy
      · exact hx
      · exact _hα.1.subset_of_mem hx hy
    have hxs : (insert x x).IsOrdinal := isOrdinal_succ (_hα.1.mem hx)
    rcases hxs.eq_or_mem_of_subset _hα.1 hsub with heq | hsucc
    · exfalso
      apply _hα.2.2
      exact ⟨_hα.1, x, _hα.1.mem hx, by rw [successor_eq_insert]; exact heq.symm⟩
    · exact mem_sUnion.2 ⟨insert x x, hsucc, by simp⟩
  · intro hx
    exact _hα.1.isTransitive.sUnion_subset hx

theorem omega_is_first_limit_ordinal :
    IsLimitOrdinal (ZFSet.omega : ZFSet.{u}) ∧
      ∀ α : ZFSet.{u}, IsLimitOrdinal α → (ZFSet.omega : ZFSet.{u}) ⊆ α := by
  have hnat : ∀ n : ℕ, (ZFSet.mk (PSet.ofNat n) : ZFSet.{u}).IsOrdinal := by
    intro n
    induction n with
    | zero =>
        change (∅ : ZFSet.{u}).IsOrdinal
        exact isOrdinal_empty
    | succ n ih =>
        change (insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n))).IsOrdinal
        exact isOrdinal_succ ih
  have hmemNat : ∀ n : ℕ, (ZFSet.mk (PSet.ofNat n) : ZFSet.{u}) ∈ ZFSet.omega := by
    intro n
    induction n with
    | zero =>
        change (∅ : ZFSet.{u}) ∈ ZFSet.omega
        exact omega_zero
    | succ n ih =>
        change insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n)) ∈ ZFSet.omega
        exact omega_succ ih
  have hsubNat : ∀ n : ℕ, (ZFSet.mk (PSet.ofNat n) : ZFSet.{u}) ⊆ ZFSet.omega := by
    intro n
    induction n with
    | zero =>
        change (∅ : ZFSet.{u}) ⊆ ZFSet.omega
        exact empty_subset _
    | succ n ih =>
        change insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n)) ⊆ ZFSet.omega
        intro x hx
        rcases mem_insert_iff.mp hx with rfl | hx
        · exact hmemNat n
        · exact ih hx
  have hmem : ∀ x : ZFSet.{u}, x ∈ ZFSet.omega → x.IsOrdinal := by
    intro x hx
    induction x using Quotient.inductionOn with
    | _ x =>
        change ZFSet.mk x ∈ ZFSet.mk PSet.omega at hx
        rw [mk_mem_iff] at hx
        change ∃ i : ULift.{u} ℕ, PSet.Equiv x (PSet.ofNat i.down) at hx
        rcases hx with ⟨i, hi⟩
        change (ZFSet.mk x).IsOrdinal
        rw [ZFSet.sound hi]
        exact hnat i.down
  have hsubset : ∀ x : ZFSet.{u}, x ∈ ZFSet.omega → x ⊆ ZFSet.omega := by
    intro x hx
    induction x using Quotient.inductionOn with
    | _ x =>
        change ZFSet.mk x ∈ ZFSet.mk PSet.omega at hx
        rw [mk_mem_iff] at hx
        change ∃ i : ULift.{u} ℕ, PSet.Equiv x (PSet.ofNat i.down) at hx
        rcases hx with ⟨i, hi⟩
        change (ZFSet.mk x) ⊆ ZFSet.omega
        rw [ZFSet.sound hi]
        exact hsubNat i.down
  have hω : (ZFSet.omega : ZFSet.{u}).IsOrdinal := by
    apply isOrdinal_iff_forall_mem_isOrdinal.2
    exact ⟨fun x hx => hsubset x hx, hmem⟩
  have hne : (ZFSet.omega : ZFSet.{u}) ≠ (0 : ZFSet.{u}) := by
    intro h
    have h' : (∅ : ZFSet.{u}) ∈ ZFSet.omega := omega_zero
    rw [h] at h'
    exact notMem_empty _ h'
  have hnotSucc : ¬IsSuccessorOrdinal (ZFSet.omega : ZFSet.{u}) := by
    rintro ⟨hβ, β, hβo, hEq⟩
    have hβmem : β ∈ (ZFSet.omega : ZFSet.{u}) := by
      rw [hEq, successor_eq_insert]
      exact mem_insert _ _
    have hs : successor β ∈ (ZFSet.omega : ZFSet.{u}) := by
      rw [successor_eq_insert]
      exact omega_succ hβmem
    have hself : (ZFSet.omega : ZFSet.{u}) ∈ ZFSet.omega := hEq.symm ▸ hs
    exact mem_irrefl _ hself
  have hlim : IsLimitOrdinal (ZFSet.omega : ZFSet.{u}) := ⟨hω, hne, hnotSucc⟩
  refine ⟨hlim, ?_⟩
  intro α hα
  have hzero : (∅ : ZFSet.{u}) ∈ α := by
    have hsub : (∅ : ZFSet.{u}) ⊆ α := empty_subset _
    rcases isOrdinal_empty.eq_or_mem_of_subset hα.1 hsub with heq | hmem
    · exact False.elim (hα.2.1 (by simpa [zero_eq_empty] using heq.symm))
    · exact hmem
  have hfinite : ∀ n : ℕ, (ZFSet.mk (PSet.ofNat n) : ZFSet.{u}) ∈ α := by
    intro n
    induction n with
    | zero =>
        change (∅ : ZFSet.{u}) ∈ α
        exact hzero
    | succ n ih =>
        have hsub : insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n)) ⊆ α := by
          intro x hx
          rcases mem_insert_iff.mp hx with rfl | hx
          · exact ih
          · exact hα.1.subset_of_mem ih hx
        have hnext : (insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n))).IsOrdinal :=
          isOrdinal_succ (hα.1.mem ih)
        rcases hnext.eq_or_mem_of_subset hα.1 hsub with heq | hmem
        · exfalso
          exact hα.2.2 ⟨hα.1, ZFSet.mk (PSet.ofNat n), hα.1.mem ih,
            by rw [successor_eq_insert]; exact heq.symm⟩
        · exact hmem
  intro x hx
  induction x using Quotient.inductionOn with
  | _ x =>
      change ZFSet.mk x ∈ ZFSet.mk PSet.omega at hx
      rw [mk_mem_iff] at hx
      change ∃ i : ULift.{u} ℕ, PSet.Equiv x (PSet.ofNat i.down) at hx
      rcases hx with ⟨i, hi⟩
      change ZFSet.mk x ∈ α
      rw [ZFSet.sound hi]
      exact hfinite i.down

def IsInfiniteOrdinal (α : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ Cardinal.aleph0 ≤ α.card

theorem omega_is_first_infinite_ordinal :
    IsInfiniteOrdinal (ZFSet.omega : ZFSet.{u}) ∧
      ∀ α : ZFSet.{u}, IsInfiniteOrdinal α → (ZFSet.omega : ZFSet.{u}) ⊆ α := by
  have hnat_eq : ∀ n : ℕ, (ZFSet.mk (PSet.ofNat n) : ZFSet.{u}) =
      Ordinal.toZFSet (n : Ordinal.{u}) := by
    intro n
    induction n with
    | zero =>
        change (∅ : ZFSet.{u}) = Ordinal.toZFSet (0 : Ordinal.{u})
        rw [Ordinal.toZFSet_zero]
    | succ n ih =>
        change insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n)) =
          Ordinal.toZFSet (Nat.succ n : Ordinal.{u})
        rw [Nat.cast_succ, Ordinal.toZFSet_add_one, ih]
  have hmemNat : ∀ n : ℕ, (ZFSet.mk (PSet.ofNat n) : ZFSet.{u}) ∈ ZFSet.omega := by
    intro n
    induction n with
    | zero =>
        change (∅ : ZFSet.{u}) ∈ ZFSet.omega
        exact omega_zero
    | succ n ih =>
        change insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n)) ∈ ZFSet.omega
        exact omega_succ ih
  have hωeq : (ZFSet.omega : ZFSet.{u}) =
      Ordinal.toZFSet (Ordinal.omega0 : Ordinal.{u}) := by
    ext x
    constructor
    · intro hx
      induction x using Quotient.inductionOn with
      | _ x =>
          change ZFSet.mk x ∈ ZFSet.mk PSet.omega at hx
          rw [mk_mem_iff] at hx
          change ∃ i : ULift.{u} ℕ, PSet.Equiv x (PSet.ofNat i.down) at hx
          rcases hx with ⟨i, hi⟩
          change ZFSet.mk x ∈ Ordinal.toZFSet (Ordinal.omega0 : Ordinal.{u})
          rw [ZFSet.sound hi, hnat_eq]
          exact Ordinal.toZFSet_mem_toZFSet_iff.2 (Ordinal.natCast_lt_omega0 i.down)
    · intro hx
      rw [Ordinal.mem_toZFSet_iff] at hx
      rcases hx with ⟨a, ha, rfl⟩
      rcases Ordinal.lt_omega0.1 ha with ⟨n, hn⟩
      rw [hn, ← hnat_eq]
      exact hmemNat n
  have hωlim : IsLimitOrdinal (ZFSet.omega : ZFSet.{u}) :=
    omega_is_first_limit_ordinal.1
  have hωord : (ZFSet.omega : ZFSet.{u}).IsOrdinal := hωlim.1
  have hcard : (ZFSet.omega : ZFSet.{u}).card = Cardinal.aleph0 := by
    rw [hωeq, Ordinal.card_toZFSet, Ordinal.card_omega0]
  have hfiniteCard : ∀ n : ℕ, (ZFSet.mk (PSet.ofNat n) : ZFSet.{u}).card <
      Cardinal.aleph0 := by
    intro n
    induction n with
    | zero =>
        change (∅ : ZFSet.{u}).card < Cardinal.aleph0
        simpa using (Cardinal.natCast_lt_aleph0 (n := 0))
    | succ n ih =>
        change (insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n))).card <
          Cardinal.aleph0
        rw [card_insert (mem_irrefl _)]
        exact Cardinal.add_lt_aleph0 ih (by simp)
  have hcardMem : ∀ x : ZFSet.{u}, x ∈ ZFSet.omega → x.card < Cardinal.aleph0 := by
    intro x hx
    induction x using Quotient.inductionOn with
    | _ x =>
        change ZFSet.mk x ∈ ZFSet.mk PSet.omega at hx
        rw [mk_mem_iff] at hx
        change ∃ i : ULift.{u} ℕ, PSet.Equiv x (PSet.ofNat i.down) at hx
        rcases hx with ⟨i, hi⟩
        change (ZFSet.mk x).card < Cardinal.aleph0
        rw [ZFSet.sound hi]
        exact hfiniteCard i.down
  refine ⟨⟨hωord, hcard.ge⟩, ?_⟩
  intro α hα
  rcases hωord.subset_total hα.1 with hsub | hsub
  · exact hsub
  · rcases hα.1.eq_or_mem_of_subset hωord hsub with heq | hmem
    · simp [heq]
    · exact False.elim ((not_lt_of_ge hα.2) (hcardMem α hmem))

/-! ### The first uncountable ordinal -/

def IsCountableOrdinal (α : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ α.card ≤ Cardinal.aleph0

def IsUncountableOrdinal (α : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ ¬IsCountableOrdinal α

noncomputable def omegaOne : ZFSet.{u} :=
  Ordinal.toZFSet (Ordinal.omega (1 : Ordinal.{u}))

theorem omegaOne_eq_countable_ordinals :
    ∀ α : ZFSet.{u}, α ∈ omegaOne ↔ IsCountableOrdinal α := by
  intro α
  constructor
  · intro hα
    rw [omegaOne, Ordinal.mem_toZFSet_iff] at hα
    rcases hα with ⟨a, ha, rfl⟩
    refine ⟨isOrdinal_toZFSet a, ?_⟩
    rw [Ordinal.card_toZFSet]
    exact Cardinal.lt_aleph_one_iff.1 (Cardinal.lt_omega_iff_card_lt.1 ha)
  · rintro ⟨hα, hcard⟩
    rw [omegaOne, Ordinal.mem_toZFSet_iff]
    refine ⟨α.rank, ?_, hα.toZFSet_rank_eq⟩
    apply Cardinal.lt_omega_iff_card_lt.2
    apply Cardinal.lt_aleph_one_iff.2
    calc
      α.rank.card = (Ordinal.toZFSet α.rank).card := (Ordinal.card_toZFSet _).symm
      _ = α.card := by rw [hα.toZFSet_rank_eq]
      _ ≤ Cardinal.aleph0 := hcard

theorem omegaOne_is_first_uncountable_ordinal :
    IsUncountableOrdinal omegaOne ∧
      ∀ α : ZFSet.{u}, IsUncountableOrdinal α → omegaOne ⊆ α := by
  refine ⟨?_, ?_⟩
  · constructor
    · rw [omegaOne]
      exact isOrdinal_toZFSet _
    · intro hcount
      apply mem_irrefl _
      exact (omegaOne_eq_countable_ordinals _).2 hcount
  · have hωOneOrd : (omegaOne : ZFSet.{u}).IsOrdinal := by
      rw [omegaOne]
      exact isOrdinal_toZFSet _
    intro α hα
    rcases hωOneOrd.subset_total hα.1 with hsub | hsub
    · exact hsub
    · rcases hα.1.eq_or_mem_of_subset hωOneOrd hsub with heq | hmem
      · simp [heq]
      · exact False.elim (hα.2 ((omegaOne_eq_countable_ordinals α).1 hmem))

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
