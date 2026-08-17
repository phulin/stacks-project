import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Zorn
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.WithTopology

/-!
# Topology, Chapter 11: Codimension and catenary spaces

The source defines codimension for irreducible closed subsets and then studies
catenary spaces.  Mathlib's `IrreducibleCloseds` is the canonical ordered type
of irreducible closed subsets, and `Order.coheight` is precisely the supremum
of the lengths of strict chains beginning at one of its elements.  Relative
codimension is represented by the same coheight in the order interval below
the ambient irreducible closed subset.
-/

namespace Formalization.Books.Topology.Unit11

open Set Function Order TopologicalSpace
open TopologicalSpace.IrreducibleCloseds

universe u v

section CodimensionAndCatenary

variable {X : Type u} [TopologicalSpace X]

/-! ## Codimension -/

/-
  The source's `codim(Y, X)` is `Order.coheight Y` in the ordered type of
  irreducible closed subsets of `X`.  Its codomain `ℕ∞` is Mathlib's canonical
  notation for the nonnegative naturals with an added infinity.
-/
noncomputable def codimension (Y : IrreducibleCloseds X) : ℕ∞ :=
  Order.coheight Y

theorem codimension_eq_iSup_length (Y : IrreducibleCloseds X) :
    codimension Y =
      ⨆ (p : LTSeries (IrreducibleCloseds X)) (_ : p.head = Y),
        (p.length : ℕ∞) := by
  simpa [codimension] using Order.coheight_eq_iSup_head_eq Y

/-
  This is the source's maximal-chain observation.  `Flag` is Mathlib's
  canonical maximal-chain interface; the source's warning that maximal
  extensions need not have a common length is reflected by the fact that no
  equal-length conclusion is included here.  The finite-codimension
  hypothesis is retained because it is part of the source assertion.
-/
theorem exists_maximal_chain_extension
    (Y : IrreducibleCloseds X) (p : LTSeries (Set.Ici Y))
    (_hp : p.head = (⟨Y, Set.mem_Ici.mpr le_rfl⟩ : Set.Ici Y))
    (_hfinite : codimension Y < ⊤) :
    ∃ F : Flag (Set.Ici Y), Set.range p ⊆ F := by
  exact p.strictMono.monotone.isChain_range.exists_subset_flag

/-! ## Restriction to an open subset -/

/-
  Mathlib's `orderIsoOfIsOpenEmbedding` gives the exact order isomorphism
  between irreducible closed subsets of an open subspace and the irreducible
  closed subsets of the ambient space that meet it.  This is the canonical
  realization of the source's `Y ↦ Y ∩ U` correspondence.
-/
noncomputable def restrictIrreducibleClosedToOpen
    {U : Set X} (hU : IsOpen U) (Y : IrreducibleCloseds X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : IrreducibleCloseds U := by
  let f : U → X := (↑)
  have hf : _root_.Topology.IsOpenEmbedding f := hU.isOpenEmbedding_subtypeVal
  have hmem : (f ⁻¹' (Y : Set X)).Nonempty := by
    rcases hYU with ⟨x, hxY, hxU⟩
    exact ⟨⟨x, hxU⟩, hxY⟩
  exact (orderIsoOfIsOpenEmbedding f hf).symm ⟨Y, hmem⟩

theorem restrictIrreducibleClosedToOpen_coe
    {U : Set X} (hU : IsOpen U) (Y : IrreducibleCloseds X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    (restrictIrreducibleClosedToOpen hU Y hYU : Set U) =
      (Subtype.val : U → X) ⁻¹' (Y : Set X) := by
  rfl

theorem codimension_at_generic_point
    (Y : IrreducibleCloseds X) {U : Set X} (hU : IsOpen U)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    codimension Y = codimension (restrictIrreducibleClosedToOpen hU Y hYU) := by
  let f : U → X := (↑)
  have hf : _root_.Topology.IsOpenEmbedding f := hU.isOpenEmbedding_subtypeVal
  have hmem : (f ⁻¹' (Y : Set X)).Nonempty := by
    rcases hYU with ⟨x, hxY, hxU⟩
    exact ⟨⟨x, hxU⟩, hxY⟩
  have hmap :
      IrreducibleCloseds.map f hf.continuous
        (restrictIrreducibleClosedToOpen hU Y hYU) = Y := by
    have h := (orderIsoOfIsOpenEmbedding f hf).apply_symm_apply
      (⟨Y, hmem⟩ : {V : IrreducibleCloseds X | (f ⁻¹' V).Nonempty})
    exact congrArg Subtype.val h
  unfold codimension
  exact (congrArg Order.coheight hmap).symm.trans
    (Topology.IsOpenEmbedding.coheight_map hf _)

/-! ## Catenary spaces -/

/-
  The order interval `Set.Iic T'` is the ordered collection of irreducible
  closed subsets contained in `T'`.  Its coheight at `T` is the source's
  `codim(T, T')`, since `T'` is the top irreducible closed subset of its
  subspace.
-/
noncomputable def relativeCodimension
    {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') : ℕ∞ :=
  Order.coheight (⟨T, hTT'⟩ : Set.Iic T')

theorem relativeCodimension_eq_iSup_length
    {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    relativeCodimension hTT' =
      ⨆ (p : LTSeries (Set.Iic T'))
        (_ : p.head = (⟨T, hTT'⟩ : Set.Iic T')),
        (p.length : ℕ∞) := by
  simpa [relativeCodimension] using
    Order.coheight_eq_iSup_head_eq (⟨T, hTT'⟩ : Set.Iic T')

/-
  A source chain between two endpoints is a finite strict series in the
  interval below the upper endpoint.  Maximality is expressed by saying that
  every other such series containing its range has the same range.
-/
def IsMaximalChainBetween {α : Type u} [Preorder α]
    (a b : α) (hab : a ≤ b) (p : LTSeries (Set.Iic b)) : Prop :=
  p.head = (⟨a, hab⟩ : Set.Iic b) ∧
    p.last = (⟨b, le_rfl⟩ : Set.Iic b) ∧
      ∀ q : LTSeries (Set.Iic b),
        q.head = (⟨a, hab⟩ : Set.Iic b) →
        q.last = (⟨b, le_rfl⟩ : Set.Iic b) →
        Set.range p ⊆ Set.range q →
        Set.range q ⊆ Set.range p

private def IsMaximalSeriesBetween {α : Type*} [Preorder α]
    (a b : α) (p : LTSeries α) : Prop :=
  p.head = a ∧ p.last = b ∧
    ∀ q : LTSeries α,
      q.head = a → q.last = b →
        Set.range p ⊆ Set.range q → Set.range q ⊆ Set.range p

private def liftSeriesToIci {α : Type*} [Preorder α] {a : α}
    (p : LTSeries α) (hhead : p.head = a) : LTSeries (Set.Ici a) :=
  { length := p.length
    toFun := fun i => ⟨p i, by
      rw [← hhead]
      exact p.head_le i⟩
    step := fun i => by
      apply p.strictMono
      change i.val < i.val + 1
      omega }

private lemma isMaximalSeriesBetween_lift
    {α : Type*} [PartialOrder α] {a b : α} {hab : a ≤ b}
    {p : LTSeries α} (hphead : p.head = a) (hplast : p.last = b)
    (hp : IsMaximalSeriesBetween a b p) :
    IsMaximalSeriesBetween
      (⟨a, le_rfl⟩ : Set.Ici a) (⟨b, hab⟩ : Set.Ici a)
      (liftSeriesToIci p hphead) := by
  let lp := liftSeriesToIci p hphead
  have hlphead : lp.head = (⟨a, le_rfl⟩ : Set.Ici a) := by
    apply Subtype.ext
    dsimp [lp, liftSeriesToIci]
    exact hphead
  have hlplast : lp.last = (⟨b, hab⟩ : Set.Ici a) := by
    apply Subtype.ext
    dsimp [lp, liftSeriesToIci]
    exact hplast
  refine ⟨hlphead, hlplast, ?_⟩
  intro q hqhead hqlast hpq
  let q' : LTSeries α := q.map (fun x : Set.Ici a => (x : α)) (by
    intro x y hxy
    exact hxy)
  have hq'head : q'.head = a := by
    change (q.head : α) = a
    exact congrArg Subtype.val hqhead
  have hq'last : q'.last = b := by
    change (q.last : α) = b
    exact congrArg Subtype.val hqlast
  have hpq' : Set.range p ⊆ Set.range q' := by
    rintro x ⟨i, hi⟩
    let i' : Fin (lp.length + 1) := ⟨i, by
      dsimp [lp, liftSeriesToIci]
      omega⟩
    have hmem : lp i' ∈ Set.range q := hpq ⟨i', rfl⟩
    rcases hmem with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hj' := congrArg Subtype.val hj
    change (q j : α) = x
    have hli : (lp i' : α) = x := by
      simpa [lp, liftSeriesToIci, i'] using hi
    exact hj'.trans hli
  have hq'p : Set.range q' ⊆ Set.range p := hp.2.2 q' hq'head hq'last hpq'
  rintro x ⟨i, hi⟩
  let i' : Fin (q'.length + 1) := ⟨i, by
    change i.val < q.length + 1
    omega⟩
  rcases hq'p ⟨i', rfl⟩ with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  apply Subtype.ext
  change (p j : α) = x
  have hi' : (q' i' : α) = x := by
    change (q i : α) = x
    exact congrArg Subtype.val hi
  exact hj.trans hi'

private lemma isMaximalSeriesBetween_lower
    {α : Type*} [PartialOrder α] {a b : α} {hab : a ≤ b}
    {q : LTSeries (Set.Ici a)}
    (hq : IsMaximalSeriesBetween
      (⟨a, le_rfl⟩ : Set.Ici a) (⟨b, hab⟩ : Set.Ici a) q) :
    IsMaximalSeriesBetween a b
      (q.map (fun x : Set.Ici a => (x : α)) (by
        intro x y hxy
        exact hxy)) := by
  let q' : LTSeries α := q.map (fun x : Set.Ici a => (x : α)) (by
    intro x y hxy
    exact hxy)
  have hq'head : q'.head = a := by
    change (q.head : α) = a
    exact congrArg Subtype.val hq.1
  have hq'last : q'.last = b := by
    change (q.last : α) = b
    exact congrArg Subtype.val hq.2.1
  refine ⟨hq'head, hq'last, ?_⟩
  intro p hphead hplast hq'p
  let lp := liftSeriesToIci p hphead
  have hlphead : lp.head = (⟨a, le_rfl⟩ : Set.Ici a) := by
    apply Subtype.ext
    dsimp [lp, liftSeriesToIci]
    exact hphead
  have hlplast : lp.last = (⟨b, hab⟩ : Set.Ici a) := by
    apply Subtype.ext
    dsimp [lp, liftSeriesToIci]
    exact hplast
  have hq_lp : Set.range q ⊆ Set.range lp := by
    rintro y ⟨i, hi⟩
    have hmem : (q i : α) ∈ Set.range p := by
      apply hq'p
      refine ⟨i, ?_⟩
      rfl
    rcases hmem with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    have hi' := congrArg Subtype.val hi
    simpa [lp, liftSeriesToIci] using hj.trans hi'
  have hlp_q : Set.range lp ⊆ Set.range q :=
    hq.2.2 lp hlphead hlplast hq_lp
  intro x hx
  rcases hx with ⟨j, hj⟩
  rcases hlp_q ⟨j, rfl⟩ with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  have hi' := congrArg Subtype.val hi
  change (q i : α) = x
  simpa [lp, liftSeriesToIci] using hi'.trans hj

private lemma isMaximalSeriesBetween_map_orderIso
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    {a b : α} {e : α ≃o β} {p : LTSeries α}
    (hp : IsMaximalSeriesBetween a b p) :
    IsMaximalSeriesBetween (e a) (e b) (p.map e e.strictMono) := by
  refine ⟨?_, ?_, ?_⟩
  · change e p.head = e a
    exact congrArg e hp.1
  · change e p.last = e b
    exact congrArg e hp.2.1
  · intro q hqhead hqlast hpq
    let q' : LTSeries α := q.map e.symm e.symm.strictMono
    have hq'head : q'.head = a := by
      change e.symm q.head = a
      rw [hqhead]
      exact e.symm_apply_apply a
    have hq'last : q'.last = b := by
      change e.symm q.last = b
      rw [hqlast]
      exact e.symm_apply_apply b
    have hpq' : Set.range p ⊆ Set.range q' := by
      rintro x ⟨i, rfl⟩
      have hmem : e (p i) ∈ Set.range q := hpq ⟨i, rfl⟩
      rcases hmem with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      change e.symm (q j) = p i
      exact (congrArg e.symm hj).trans (e.symm_apply_apply _)
    have hq'p : Set.range q' ⊆ Set.range p := hp.2.2 q' hq'head hq'last hpq'
    rintro y ⟨j, hj⟩
    rcases hq'p ⟨j, rfl⟩ with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change e (p i) = y
    have hmap : e (q' j) = q j := by
      change e (e.symm (q j)) = q j
      exact e.apply_symm_apply _
    exact (congrArg e hi).trans (hmap.trans hj)

private lemma coheight_eq_of_upperIntervalOrderIso
    {α β : Type*} [Preorder α] [Preorder β]
    {a : α} {b : β} (e : Set.Ici a ≃o Set.Ici b) :
    Order.coheight a = Order.coheight b := by
  apply WithBot.coe_injective
  rw [Order.coheight_eq_krullDim_Ici, Order.coheight_eq_krullDim_Ici,
    Order.krullDim_eq_of_orderIso e]

private noncomputable def upperIntervalOrderIsoNormalized
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    {P : β → Prop} (e : α ≃o {x : β // P x})
    (hP : ∀ ⦃x y : β⦄, x ≤ y → P x → P y)
    {A B : β} (hAB : A ≤ B) (hPA : P A) (hPB : P B)
    {a b : α} (hab : a ≤ b)
    (ha : e a = ⟨A, hPA⟩) (hb : e b = ⟨B, hPB⟩) :
    Set.Ici (⟨A, hAB⟩ : Set.Iic B) ≃o
      Set.Ici (⟨a, hab⟩ : Set.Iic b) := by
  let F : Set.Ici (⟨A, hAB⟩ : Set.Iic B) →
      Set.Ici (⟨a, hab⟩ : Set.Iic b) := fun x =>
    let hxP : P (x : β) := hP x.property hPA
    let hx : {x : β // P x} := ⟨x, hxP⟩
    let y : Set.Iic b :=
      ⟨e.symm hx, by
        calc
          e.symm hx ≤ e.symm ⟨B, hPB⟩ := e.symm.monotone x.1.property
          _ = e.symm (e b) := by rw [hb]
          _ = b := e.symm_apply_apply b⟩
    ⟨y, by
      change a ≤ e.symm hx
      calc
        a = e.symm (e a) := (e.symm_apply_apply a).symm
        _ = e.symm ⟨A, hPA⟩ := by rw [ha]
        _ ≤ e.symm hx := e.symm.monotone x.property⟩
  let G : Set.Ici (⟨a, hab⟩ : Set.Iic b) →
      Set.Ici (⟨A, hAB⟩ : Set.Iic B) := fun y =>
    let x : Set.Iic B :=
      ⟨e y.1, by
        calc
          e y.1 ≤ e b := e.monotone y.1.property
          _ = ⟨B, hPB⟩ := hb⟩
    ⟨x, by
      change A ≤ (e y.1 : β)
      have h := e.monotone y.property
      have h' : (e a : β) ≤ (e y.1 : β) := h
      have ha' : (e a : β) = A := congrArg Subtype.val ha
      rw [ha'] at h'
      exact h'⟩
  have hF : Monotone F := by
    intro x y hxy
    dsimp [F]
    apply e.symm.monotone
    exact hxy
  have hG : Monotone G := by
    intro x y hxy
    dsimp [G]
    apply e.monotone
    exact hxy
  have hGF : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    simp [F, G]
  have hFG : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    simp [F, G]
  exact
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      map_rel_iff' := by
        intro x y
        constructor
        · intro hxy
          change F x ≤ F y at hxy
          have h := hG hxy
          change G (F x) ≤ G (F y) at h
          simpa only [hGF x, hGF y] using h
        · intro hxy
          have h := hF hxy
          change F x ≤ F y
          exact h }

private lemma range_cons_eq_insert {α : Type*} [Preorder α]
    {p : LTSeries α} {a : α} (h : a < p.head) :
    Set.range (p.cons a h) = insert a (Set.range p) := by
  ext x
  change x ∈ p.cons a h ↔ x = a ∨ x ∈ p
  rw [← RelSeries.mem_toList, ← RelSeries.mem_toList]
  simp [RelSeries.toList_cons]

private lemma length_le_of_range_subset {α : Type*} [Preorder α]
    {p q : LTSeries α} (hpq : Set.range p ⊆ Set.range q) :
    p.length ≤ q.length := by
  have hcard := Set.ncard_le_ncard hpq
  rw [Set.ncard_range_of_injective p.strictMono.injective,
    Set.ncard_range_of_injective q.strictMono.injective] at hcard
  simpa using hcard

private lemma range_subset_of_range_subset_of_length_le {α : Type*} [Preorder α]
    {p q : LTSeries α} (hpq : Set.range p ⊆ Set.range q) (hqlen : q.length ≤ p.length) :
    Set.range q ⊆ Set.range p := by
  have hcard : (Set.range q).ncard ≤ (Set.range p).ncard := by
    rw [Set.ncard_range_of_injective p.strictMono.injective,
      Set.ncard_range_of_injective q.strictMono.injective]
    simpa using hqlen
  have hfinq : (Set.range q).Finite := Set.finite_range q
  have heq : Set.range p = Set.range q :=
    Set.eq_of_subset_of_ncard_le hpq hcard hfinq
  rw [heq]

private lemma range_eq_insert_head_tail {α : Type*} [Preorder α]
    {p : LTSeries α} (hp0 : p.length ≠ 0) :
    Set.range p = insert p.head (Set.range (p.tail hp0)) := by
  have hp_eq : (p.tail hp0).cons p.head
      (p.3 ⟨0, Nat.zero_lt_of_ne_zero hp0⟩) = p := p.cons_self_tail hp0
  calc
    Set.range p = Set.range ((p.tail hp0).cons p.head
        (p.3 ⟨0, Nat.zero_lt_of_ne_zero hp0⟩)) :=
      congrArg (fun s : LTSeries α => Set.range s) hp_eq.symm
    _ = insert p.head (Set.range (p.tail hp0)) :=
      range_cons_eq_insert (p := p.tail hp0) (a := p.head)
        (p.3 ⟨0, Nat.zero_lt_of_ne_zero hp0⟩)

private lemma coheight_Iic_eq_one_of_no_between
    {α : Type*} [PartialOrder α] {a b : α} (hab : a < b)
    (hno : ∀ z : α, a < z → z < b → False) :
    Order.coheight (⟨a, le_of_lt hab⟩ : Set.Iic b) = 1 := by
  let x : Set.Iic b := ⟨a, le_of_lt hab⟩
  have hle : Order.coheight x ≤ (1 : ℕ∞) := by
    apply Order.coheight_le_iff'.mpr
    intro p hphead
    by_contra hlen
    have hlenNat : ¬ p.length ≤ 1 := by
      intro h
      apply hlen
      exact_mod_cast h
    have hlen' : 2 ≤ p.length := by omega
    let i₁ : Fin (p.length + 1) := ⟨1, by omega⟩
    let i₂ : Fin (p.length + 1) := ⟨2, by omega⟩
    have h01 : (0 : Fin (p.length + 1)) < i₁ := by
      change (0 : Nat) < 1
      omega
    have h12 : i₁ < i₂ := by
      change (1 : Nat) < 2
      omega
    have hai : a < (p i₁ : α) := by
      have h := p.strictMono h01
      have h' : (p 0 : α) < (p i₁ : α) := h
      have hp0 : (p 0 : α) = a := by
        have h0 := congrArg Subtype.val hphead
        change (p.head : α) = a
        simpa [x] using h0
      rw [hp0] at h'
      exact h'
    have hib : (p i₁ : α) < b := by
      have h := p.strictMono h12
      have h' : (p i₁ : α) < (p i₂ : α) := h
      exact lt_of_lt_of_le h' (p i₂).property
    exact hno _ hai hib
  have hge : (1 : ℕ∞) ≤ Order.coheight x := by
    let p : LTSeries (Set.Iic b) :=
      (RelSeries.singleton _ x).snoc (⟨b, le_rfl⟩ : Set.Iic b) (by
        change a < b
        exact hab)
    have h := Order.length_le_coheight_head (p := p)
    simpa [p, x] using h
  exact le_antisymm hle hge

private def prefixSeries {α : Type*} [Preorder α]
    (p : LTSeries α) (i : Fin (p.length + 1)) : LTSeries (Set.Iic (p i)) :=
  { length := i
    toFun := fun j => ⟨p ⟨j, by
      exact lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩, by
      apply p.monotone
      rw [Fin.le_iff_val_le_val]
      have hj_le : j.val ≤ i.val := Nat.le_of_lt_succ j.isLt
      simpa using hj_le⟩
    step := fun j => by
      change p ⟨j, lt_trans j.isLt i.isLt⟩ <
        p ⟨j + 1, by exact lt_of_le_of_lt (Nat.succ_le_of_lt j.isLt) i.isLt⟩
      apply p.strictMono
      change j.val < j.val + 1
      omega }

private lemma range_right_smash_subset {α : Type*} [Preorder α]
    {p q : LTSeries α} {h : p.last = q.head} :
    Set.range q ⊆ Set.range (p.smash q h) := by
  rintro x ⟨i, hi⟩
  revert hi
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro hi
    refine ⟨Fin.last (p.length + q.length), ?_⟩
    have hi' : q.last = x := by
      change q (Fin.last q.length) = x
      exact hi
    rw [← hi']
    change (p.smash q h).last = q.last
    exact RelSeries.last_smash h
  · intro hi
    refine ⟨(j.natAdd p.length).castSucc, ?_⟩
    have hi' : q j.castSucc = x := by simpa using hi
    rw [← hi']
    exact RelSeries.smash_natAdd h j

private lemma range_left_smash_subset {α : Type*} [Preorder α]
    {p q : LTSeries α} {h : p.last = q.head} :
    Set.range p ⊆ Set.range (p.smash q h) := by
  rintro x ⟨i, rfl⟩
  refine ⟨i.castLE (by simp), ?_⟩
  exact RelSeries.smash_castLE h i

private lemma mem_range_prefixSeries {α : Type*} [Preorder α]
    {p : LTSeries α} {i : Fin (p.length + 1)} {k : Fin (p.length + 1)}
    (hki : k ≤ i) :
    (⟨p k, p.monotone hki⟩ : Set.Iic (p i)) ∈ Set.range (prefixSeries p i) := by
  let j : Fin (i + 1) := ⟨k, by omega⟩
  refine ⟨j, ?_⟩
  rfl

private lemma mem_range_drop {α : Type*} [Preorder α]
    {p : LTSeries α} {i k : Fin (p.length + 1)} (hik : i ≤ k) :
    p k ∈ Set.range (p.drop i) := by
  let j : Fin ((p.drop i).length + 1) := ⟨k - i, by
    dsimp [RelSeries.drop]
    omega⟩
  refine ⟨j, ?_⟩
  apply congrArg p
  apply Fin.ext
  dsimp [RelSeries.drop, j]
  omega

private lemma exists_maximal_chain_smash
    {α : Type*} [PartialOrder α] {a b c : α}
    {hab : a ≤ b} {hbc : b ≤ c}
    {p : LTSeries (Set.Iic b)} {q : LTSeries (Set.Iic c)}
    (hp : IsMaximalChainBetween a b hab p)
    (hq : IsMaximalChainBetween b c hbc q) :
    ∃ r : LTSeries (Set.Iic c),
      IsMaximalChainBetween a c (hab.trans hbc) r ∧
        r.length = p.length + q.length := by
  let f : Set.Iic b → Set.Iic c := fun x => ⟨x, x.property.trans hbc⟩
  have hf : StrictMono f := by
    intro x y hxy
    exact hxy
  let p' : LTSeries (Set.Iic c) := p.map f hf
  have hp'head : p'.head = (⟨a, hab.trans hbc⟩ : Set.Iic c) := by
    change f p.head = (⟨a, hab.trans hbc⟩ : Set.Iic c)
    apply Subtype.ext
    change (p.head : α) = a
    exact congrArg Subtype.val hp.1
  have hp'last : p'.last = (⟨b, hbc⟩ : Set.Iic c) := by
    change f p.last = (⟨b, hbc⟩ : Set.Iic c)
    apply Subtype.ext
    change (p.last : α) = b
    exact congrArg Subtype.val hp.2.1
  have hconnect : p'.last = q.head := hp'last.trans hq.1.symm
  let r : LTSeries (Set.Iic c) := p'.smash q hconnect
  have hrhead : r.head = (⟨a, hab.trans hbc⟩ : Set.Iic c) := by
    dsimp [r]
    rw [RelSeries.head_smash, hp'head]
  have hrlast : r.last = (⟨c, le_rfl⟩ : Set.Iic c) := by
    dsimp [r]
    rw [RelSeries.last_smash, hq.2.1]
  have hrmax : IsMaximalChainBetween a c (hab.trans hbc) r := by
    refine ⟨hrhead, hrlast, ?_⟩
    intro s hshead hslast hrs
    let z : Set.Iic c := ⟨b, hbc⟩
    have hp'last_z : p'.last = z := hp'last
    have hz_r : z ∈ Set.range r := by
      refine ⟨(Fin.last p'.length).castLE (by
        change p'.length + 1 ≤ (p'.length + q.length) + 1
        omega), ?_⟩
      calc
        r ((Fin.last p'.length).castLE (by
          change p'.length + 1 ≤ (p'.length + q.length) + 1
          omega)) = p'.last :=
          RelSeries.smash_castLE hconnect _
        _ = z := hp'last_z
    have hz_s : z ∈ Set.range s := hrs hz_r
    rcases hz_s with ⟨j, hjs⟩
    let g : Set.Iic (s j) → Set.Iic b := fun x =>
      ⟨(x : Set.Iic c), by
        have hx : (x : Set.Iic c) ≤ s j := x.property
        change ((x : Set.Iic c) : α) ≤ b
        have hx' : ((x : Set.Iic c) : α) ≤ (s j : Set.Iic c) := hx
        have hzval : (s j : α) = b := congrArg Subtype.val hjs
        rw [hzval] at hx'
        exact hx'⟩
    have hg : StrictMono g := by
      intro x y hxy
      change ((x : Set.Iic c) : α) < ((y : Set.Iic c) : α)
      exact hxy
    let u : LTSeries (Set.Iic b) :=
      (prefixSeries s j).map g hg
    have huhead : u.head = (⟨a, hab⟩ : Set.Iic b) := by
      change g (prefixSeries s j).head = (⟨a, hab⟩ : Set.Iic b)
      apply Subtype.ext
      change (s.head : α) = a
      exact congrArg Subtype.val hshead
    have hulast : u.last = (⟨b, le_rfl⟩ : Set.Iic b) := by
      change g (prefixSeries s j).last = (⟨b, le_rfl⟩ : Set.Iic b)
      apply Subtype.ext
      change (s j : α) = b
      exact congrArg Subtype.val hjs
    have hpu : Set.range u ⊆ Set.range p := by
      apply hp.2.2 u
      · exact huhead
      · exact hulast
      · intro x hx
        rcases hx with ⟨i, rfl⟩
        have hpr : f (p i) ∈ Set.range r :=
          (range_left_smash_subset (p := p') (q := q) (h := hconnect)) ⟨i, rfl⟩
        rcases hrs hpr with ⟨l, hl⟩
        have hslj : s l ≤ s j := by
          change (s l : α) ≤ (s j : α)
          have hsl : (s l : α) = (p i : α) := by
            have h := congrArg Subtype.val hl
            simpa [f] using h
          have hsj : (s j : α) = b := congrArg Subtype.val hjs
          rw [hsl, hsj]
          exact (p i).property
        have hlj : l ≤ j := by
          by_contra hnot
          have hlt : j < l := lt_of_not_ge hnot
          exact (not_lt_of_ge hslj) (s.strictMono hlt)
        have hmem := mem_range_prefixSeries hlj
        rcases hmem with ⟨m, hm⟩
        refine ⟨m, ?_⟩
        change g ((prefixSeries s j) m) = p i
        apply Subtype.ext
        change ((prefixSeries s j) m : α) = (p i : α)
        have hml := congrArg Subtype.val hm
        have hsl : (s l : α) = (p i : α) := by
          have h := congrArg Subtype.val hl
          simpa [f] using h
        exact (congrArg Subtype.val hml).trans hsl
    have hqv : Set.range q ⊆ Set.range (s.drop j) := by
      intro x hx
      rcases hx with ⟨k, rfl⟩
      have hqr : q k ∈ Set.range r :=
        (range_right_smash_subset (p := p') (q := q) (h := hconnect)) ⟨k, rfl⟩
      rcases hrs hqr with ⟨l, hl⟩
      have hzq : z ≤ q k := by
        change (⟨b, hbc⟩ : Set.Iic c) ≤ q k
        rw [← hq.1]
        exact q.head_le k
      have hsj_sl : s j ≤ s l := by
        rw [hjs, hl]
        exact hzq
      have hjl : j ≤ l := by
        by_contra hnot
        have hlt : l < j := lt_of_not_ge hnot
        exact (not_lt_of_ge hsj_sl) (s.strictMono hlt)
      have hmem := mem_range_drop hjl
      rw [← hl]
      exact (Set.mem_range.mp hmem).elim (fun i hi => ⟨i, hi⟩)
    have hvhead : (s.drop j).head = z := by
      rw [RelSeries.head_drop]
      exact hjs
    have hvlast : (s.drop j).last = (⟨c, le_rfl⟩ : Set.Iic c) := by
      rw [RelSeries.last_drop, hslast]
    have hvq : Set.range (s.drop j) ⊆ Set.range q := by
      apply hq.2.2 (s.drop j)
      · simpa [z] using hvhead
      · exact hvlast
      · exact hqv
    intro x hx
    rcases hx with ⟨l, rfl⟩
    by_cases hlj : l ≤ j
    · have hmem :
          (⟨s l, s.monotone hlj⟩ : Set.Iic (s j)) ∈ Set.range (prefixSeries s j) :=
        mem_range_prefixSeries hlj
      have hu_mem : g (⟨s l, s.monotone hlj⟩ : Set.Iic (s j)) ∈ Set.range u := by
        rcases hmem with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        change g ((prefixSeries s j) i) = g (⟨s l, s.monotone hlj⟩ : Set.Iic (s j))
        rw [hi]
      have hp_mem : g (⟨s l, s.monotone hlj⟩ : Set.Iic (s j)) ∈ Set.range p :=
        hpu hu_mem
      rcases hp_mem with ⟨k, hk⟩
      have hpr : f (p k) ∈ Set.range r :=
        (range_left_smash_subset (p := p') (q := q) (h := hconnect)) ⟨k, rfl⟩
      rcases hpr with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hks : f (p k) = s l := by
        apply Subtype.ext
        change (p k : α) = (s l : α)
        have h := congrArg Subtype.val hk
        simpa [g] using h
      exact hi.trans hks
    · have hjl : j ≤ l := le_of_not_ge hlj
      exact (range_right_smash_subset (p := p') (q := q) (h := hconnect))
        (hvq (mem_range_drop hjl))
  exact ⟨r, hrmax, by simp [r, p']⟩

private lemma maximal_tail
    {α : Type*} [PartialOrder α] {a b : α} {hab : a ≤ b}
    {p : LTSeries (Set.Iic b)} (hp : IsMaximalChainBetween a b hab p)
    (hp0 : p.length ≠ 0) :
    let i : Fin (p.length + 1) := ⟨1, by omega⟩
    IsMaximalChainBetween (p i : α) b (p i).property (p.tail hp0) := by
  let i : Fin (p.length + 1) := ⟨1, by omega⟩
  have hi : (0 : Fin (p.length + 1)) < i := by
    change (0 : Nat) < 1
    omega
  have hhead_lt : p.head < p i := p.strictMono hi
  have htail_head : (p.tail hp0).head = p i := by
    rw [RelSeries.head_tail]
    apply congrArg p
    apply Fin.ext
    simp [i]
    omega
  have htail_last : (p.tail hp0).last = (⟨b, le_rfl⟩ : Set.Iic b) := by
    rw [RelSeries.last_tail, hp.2.1]
  refine ⟨?_, htail_last, ?_⟩
  · simp [htail_head, i]
  · intro q hqhead hqlast hqrange
    have hcons : p.head < q.head := by
      rw [hqhead, ← htail_head]
      exact hhead_lt
    let r := q.cons p.head hcons
    have hqr : Set.range q ⊆ Set.range r := by
      change Set.range q ⊆ Set.range (q.cons p.head hcons)
      rw [range_cons_eq_insert]
      exact fun x hx => Set.mem_insert_iff.mpr (Or.inr hx)
    have hp_range : Set.range p = insert p.head (Set.range (p.tail hp0)) :=
      range_eq_insert_head_tail hp0
    have hpr : Set.range p ⊆ Set.range r := by
      rw [hp_range]
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact RelSeries.head_mem r
      · exact hqr (hqrange hx)
    have hrp : Set.range r ⊆ Set.range p := by
      apply hp.2.2 r
      · simpa [r] using hp.1
      · simpa [r] using hqlast
      · exact hpr
    intro x hx
    have hx' : x ∈ Set.range p := hrp (hqr hx)
    rw [hp_range] at hx'
    rcases Set.mem_insert_iff.mp hx' with rfl | hx'
    · have hqle : q.head ≤ p.head := by
        rcases hx with ⟨j, hj⟩
        rw [← hj]
        exact q.head_le j
      have hqi : q.head = p i := by
        simpa [i] using hqhead
      exact False.elim (not_le_of_gt hhead_lt (hqi ▸ hqle))
    · exact hx'

private lemma exists_maximal_chain_between
    {α : Type*} [PartialOrder α] {a b : α} (hab : a < b)
    (hfin : Order.coheight (⟨a, le_of_lt hab⟩ : Set.Iic b) < ⊤) :
    ∃ p : LTSeries (Set.Iic b),
      IsMaximalChainBetween a b (le_of_lt hab) p ∧
        p.length = Order.coheight (⟨a, le_of_lt hab⟩ : Set.Iic b) := by
  let x : Set.Iic b := ⟨a, le_of_lt hab⟩
  let z : Set.Iic b := ⟨b, le_rfl⟩
  cases hc : Order.coheight x with
  | top => exact (hfin.ne hc).elim
  | coe n =>
      obtain ⟨p, hphead, hplen⟩ :=
        Order.exists_series_of_coheight_eq_coe x hc
      have hplast : p.last = z := by
        apply le_antisymm
        · exact p.last.property
        · by_contra hne
          have hne' : p.last ≠ z := by
            intro heq
            exact hne (heq ▸ le_rfl)
          have hlt : p.last < z := lt_of_le_of_ne p.last.property hne'
          let q := p.snoc z hlt
          have hqle : q.length ≤ Order.coheight q.head :=
            Order.length_le_coheight_head
          rw [RelSeries.head_snoc, hphead, hc] at hqle
          have hcontra : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
            simpa [q, hplen] using hqle
          have hnlt : (n : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by
            exact_mod_cast Nat.lt_succ_self n
          exact (not_le_of_gt hnlt) hcontra
      have hpmax : IsMaximalChainBetween a b (le_of_lt hab) p := by
        refine ⟨?_, hplast, ?_⟩
        · simpa [x] using hphead
        · intro q hqhead hqlast hpq
          have hqle : q.length ≤ Order.coheight q.head :=
            Order.length_le_coheight_head
          have hqle' : q.length ≤ p.length := by
            rw [hqhead, hc] at hqle
            have hqleEnat : (q.length : ℕ∞) ≤ (p.length : ℕ∞) := by
              simpa [hplen] using hqle
            exact_mod_cast hqleEnat
          exact range_subset_of_range_subset_of_length_le hpq hqle'
      exact ⟨p, hpmax, by simpa [hc] using hplen⟩

/- The source's definition of a catenary space. -/
def IsCatenary (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ ⦃T T' : IrreducibleCloseds X⦄ (hTT' : T < T'),
    relativeCodimension (le_of_lt hTT') < ⊤ ∧
      ∀ p : LTSeries (Set.Iic T'),
        IsMaximalChainBetween T T' (le_of_lt hTT') p →
          p.length = relativeCodimension (le_of_lt hTT')

private lemma isIrreducible_preimage_of_isInducing
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : β → α} (hf : _root_.Topology.IsInducing f) {s : Set α}
    (hs : IsIrreducible s) (hsrange : s ⊆ Set.range f) :
    IsIrreducible (f ⁻¹' s) := by
  refine ⟨?_, ?_⟩
  · rcases hs.nonempty with ⟨x, hx⟩
    rcases hsrange hx with ⟨y, rfl⟩
    exact ⟨y, hx⟩
  · intro u v hu hv hU hV
    rcases hf.isOpen_iff.mp hu with ⟨u', huopen, hu_eq⟩
    rcases hf.isOpen_iff.mp hv with ⟨v', hvopen, hv_eq⟩
    have hsu : (s ∩ u').Nonempty := by
      rw [← hu_eq] at hU
      rcases hU with ⟨y, hyS, hyU⟩
      exact ⟨f y, hyS, hyU⟩
    have hsv : (s ∩ v').Nonempty := by
      rw [← hv_eq] at hV
      rcases hV with ⟨y, hyS, hyV⟩
      exact ⟨f y, hyS, hyV⟩
    rcases hs.2 u' v' huopen hvopen hsu hsv with ⟨x, hxs, hxu, hxv⟩
    rcases hsrange hxs with ⟨y, rfl⟩
    refine ⟨y, hxs, ?_⟩
    constructor
    · rw [← hu_eq]
      exact hxu
    · rw [← hv_eq]
      exact hxv

private noncomputable def orderIsoOfIsClosedSubtype
    {Z : Set X} (hZ : IsClosed Z) :
    IrreducibleCloseds Z ≃o
      {V : IrreducibleCloseds X // (V : Set X) ⊆ Z} := by
  let f : Z → X := (↑)
  have hf : _root_.Topology.IsClosedEmbedding f := hZ.isClosedEmbedding_subtypeVal
  let F : IrreducibleCloseds Z →
      {V : IrreducibleCloseds X // (V : Set X) ⊆ Z} := fun c =>
    ⟨IrreducibleCloseds.map f hf.continuous c, by
      change closure (f '' (c : Set Z)) ⊆ Z
      apply closure_minimal
      rintro x ⟨z, hz, rfl⟩
      exact z.property
      exact hZ⟩
  let G : {V : IrreducibleCloseds X // (V : Set X) ⊆ Z} →
      IrreducibleCloseds Z := fun V =>
    ⟨f ⁻¹' (V : Set X),
      isIrreducible_preimage_of_isInducing hf.isInducing V.1.isIrreducible
        (by
          intro x hx
          exact ⟨⟨x, V.2 hx⟩, rfl⟩),
      V.1.isClosed.preimage hf.continuous⟩
  have hGF : Function.LeftInverse G F := by
    intro c
    apply IrreducibleCloseds.ext
    change f ⁻¹' closure (f '' (c : Set Z)) = (c : Set Z)
    rw [← hf.isInducing.closure_eq_preimage_closure_image, c.isClosed.closure_eq]
  have hFG : Function.RightInverse G F := by
    intro V
    apply Subtype.ext
    apply IrreducibleCloseds.ext
    change closure (f '' (f ⁻¹' (V : Set X))) = (V : Set X)
    have hVr : (V : Set X) ⊆ Set.range f := by
      intro x hx
      exact ⟨⟨x, V.2 hx⟩, rfl⟩
    rw [Set.image_preimage_eq_of_subset hVr, V.1.isClosed.closure_eq]
  exact
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      map_rel_iff' := by
        intro a b
        constructor
        · intro hab
          simpa [F, ← hf.isInducing.closure_eq_preimage_closure_image,
            a.isClosed.closure_eq, b.isClosed.closure_eq] using
            Set.preimage_mono (f := f) hab
        · intro hab
          exact IrreducibleCloseds.map_mono hf.continuous hab }

private noncomputable def lowerIntervalOrderIsoNormalized
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    {P : β → Prop} (e : α ≃o {x : β // P x})
    (hP : ∀ ⦃x y : β⦄, x ≤ y → P y → P x)
    {A B : β} (hAB : A ≤ B) (hPA : P A) (hPB : P B)
    {a b : α} (hab : a ≤ b)
    (ha : e a = ⟨A, hPA⟩) (hb : e b = ⟨B, hPB⟩) :
    Set.Ici (⟨A, hAB⟩ : Set.Iic B) ≃o
      Set.Ici (⟨a, hab⟩ : Set.Iic b) := by
  let F : Set.Ici (⟨A, hAB⟩ : Set.Iic B) →
      Set.Ici (⟨a, hab⟩ : Set.Iic b) := fun x =>
    let hxP : P (x : β) := hP x.1.property hPB
    let hx : {x : β // P x} := ⟨x, hxP⟩
    let y : Set.Iic b :=
      ⟨e.symm hx, by
        calc
          e.symm hx ≤ e.symm ⟨B, hPB⟩ := e.symm.monotone x.1.property
          _ = e.symm (e b) := by rw [hb]
          _ = b := e.symm_apply_apply b⟩
    ⟨y, by
      change a ≤ e.symm hx
      calc
        a = e.symm (e a) := (e.symm_apply_apply a).symm
        _ = e.symm ⟨A, hPA⟩ := by rw [ha]
        _ ≤ e.symm hx := e.symm.monotone x.property⟩
  let G : Set.Ici (⟨a, hab⟩ : Set.Iic b) →
      Set.Ici (⟨A, hAB⟩ : Set.Iic B) := fun y =>
    let x : Set.Iic B :=
      ⟨e y.1, by
        calc
          e y.1 ≤ e b := e.monotone y.1.property
          _ = ⟨B, hPB⟩ := hb⟩
    ⟨x, by
      change A ≤ (e y.1 : β)
      have h := e.monotone y.property
      have h' : (e a : β) ≤ (e y.1 : β) := h
      have ha' : (e a : β) = A := congrArg Subtype.val ha
      rw [ha'] at h'
      exact h'⟩
  have hF : Monotone F := by
    intro x y hxy
    dsimp [F]
    apply e.symm.monotone
    exact hxy
  have hG : Monotone G := by
    intro x y hxy
    dsimp [G]
    apply e.monotone
    exact hxy
  have hGF : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    simp [F, G]
  have hFG : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    simp [F, G]
  exact
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      map_rel_iff' := by
        intro x y
        constructor
        · intro hxy
          change F x ≤ F y at hxy
          have h := hG hxy
          change G (F x) ≤ G (F y) at h
          simpa only [hGF x, hGF y] using h
        · intro hxy
          have h := hF hxy
          change F x ≤ F y
          exact h }

private theorem isCatenary_of_isClosed
    {Z : Set X} (hZ : IsClosed Z) (hX : IsCatenary X) : IsCatenary Z := by
  intro T T' hTT'
  let e := orderIsoOfIsClosedSubtype hZ
  let A : IrreducibleCloseds X := (e T).1
  let B : IrreducibleCloseds X := (e T').1
  have hAB : A ≤ B := by
    exact e.monotone hTT'.le
  have hABlt : A < B := by
    exact e.strictMono hTT'
  have hPA : ((A : Set X) ⊆ Z) := (e T).property
  have hPB : ((B : Set X) ⊆ Z) := (e T').property
  have hP : ∀ ⦃V W : IrreducibleCloseds X⦄, V ≤ W →
      (W : Set X) ⊆ Z → (V : Set X) ⊆ Z := by
    intro V W hVW hW x hx
    exact hW (hVW hx)
  have ha : e T = ⟨A, hPA⟩ := by
    apply Subtype.ext
    rfl
  have hb : e T' = ⟨B, hPB⟩ := by
    apply Subtype.ext
    rfl
  let E := lowerIntervalOrderIsoNormalized e hP hAB hPA hPB hTT'.le ha hb
  have hcodim :
      Order.coheight (⟨A, hAB⟩ : Set.Iic B) =
        Order.coheight (⟨T, hTT'.le⟩ : Set.Iic T') :=
    coheight_eq_of_upperIntervalOrderIso E
  have hcodim' :
      relativeCodimension (X := X) hAB =
        relativeCodimension (X := Z) hTT'.le := by
    simpa [relativeCodimension] using hcodim
  refine ⟨?_, ?_⟩
  · rw [← hcodim']
    exact (hX hABlt).1
  · intro p hp
    let lp := liftSeriesToIci p hp.1
    have hpgen : IsMaximalSeriesBetween
        (⟨T, hTT'.le⟩ : Set.Iic T')
        (⟨T', (by simp : T' ∈ Set.Iic T')⟩ : Set.Iic T') p := hp
    have hlp := isMaximalSeriesBetween_lift (α := Set.Iic T')
      (a := (⟨T, hTT'.le⟩ : Set.Iic T'))
      (b := (⟨T', (by simp : T' ∈ Set.Iic T')⟩ : Set.Iic T'))
      (hab := hTT'.le) hpgen.1 hpgen.2.1 hpgen
    let mp := lp.map E.symm E.symm.strictMono
    have hmp := isMaximalSeriesBetween_map_orderIso (e := E.symm) hlp
    let q := mp.map (fun x : Set.Ici (⟨A, hAB⟩ : Set.Iic B) =>
        (x : Set.Iic B)) (by
          intro x y hxy
          exact hxy)
    have hqgen : IsMaximalSeriesBetween
        (⟨A, hAB⟩ : Set.Iic B)
        (⟨B, (by simp : B ∈ Set.Iic B)⟩ : Set.Iic B) q := by
      exact isMaximalSeriesBetween_lower hmp
    have hq : IsMaximalChainBetween A B hAB q := hqgen
    have hqeq : q.length = Order.coheight (⟨A, hAB⟩ : Set.Iic B) :=
      (hX hABlt).2 q hq
    calc
      (p.length : ℕ∞) = (q.length : ℕ∞) := by
        change (p.length : ℕ∞) = (p.length : ℕ∞)
        rfl
      _ = relativeCodimension hTT'.le := by
        rw [← hcodim']
        simpa [relativeCodimension] using hqeq

private theorem isCatenary_of_irreducibleClosedOrderIso
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : IrreducibleCloseds A ≃o IrreducibleCloseds B)
    (hA : IsCatenary A) : IsCatenary B := by
  intro T T' hTT'
  let a : IrreducibleCloseds A := e.symm T
  let b : IrreducibleCloseds A := e.symm T'
  have hab : a ≤ b := by
    exact e.symm.monotone hTT'.le
  have hablt : a < b := by
    exact e.symm.strictMono hTT'
  let e' : IrreducibleCloseds A ≃o
      {V : IrreducibleCloseds B // True} :=
    e.trans (OrderIso.Set.univ (α := IrreducibleCloseds B)).symm
  have hP : ∀ ⦃V W : IrreducibleCloseds B⦄, V ≤ W → True → True := by
    intro V W hVW hV
    trivial
  have ha : e' a = ⟨T, True.intro⟩ := by
    apply Subtype.ext
    change e (e.symm T) = T
    exact e.apply_symm_apply _
  have hb : e' b = ⟨T', True.intro⟩ := by
    apply Subtype.ext
    change e (e.symm T') = T'
    exact e.apply_symm_apply _
  let E := upperIntervalOrderIsoNormalized e' hP hTT'.le True.intro True.intro
    hab ha hb
  have hcodim :
      Order.coheight (⟨T, hTT'.le⟩ : Set.Iic T') =
        Order.coheight (⟨a, hab⟩ : Set.Iic b) :=
    coheight_eq_of_upperIntervalOrderIso E
  have hcodim' :
      relativeCodimension (X := B) hTT'.le =
        relativeCodimension (X := A) hab := by
    simpa [relativeCodimension] using hcodim
  refine ⟨?_, ?_⟩
  · rw [hcodim']
    exact (hA hablt).1
  · intro p hp
    let lp := liftSeriesToIci p hp.1
    have hpgen : IsMaximalSeriesBetween
        (⟨T, hTT'.le⟩ : Set.Iic T')
        (⟨T', (by simp : T' ∈ Set.Iic T')⟩ : Set.Iic T') p := hp
    have hlp := isMaximalSeriesBetween_lift (α := Set.Iic T')
      (a := (⟨T, hTT'.le⟩ : Set.Iic T'))
      (b := (⟨T', (by simp : T' ∈ Set.Iic T')⟩ : Set.Iic T'))
      (hab := hTT'.le) hpgen.1 hpgen.2.1 hpgen
    let mp := lp.map E E.strictMono
    have hmp := isMaximalSeriesBetween_map_orderIso (e := E) hlp
    let q := mp.map (fun x : Set.Ici (⟨a, hab⟩ : Set.Iic b) =>
        (x : Set.Iic b)) (by
          intro x y hxy
          exact hxy)
    have hqgen : IsMaximalSeriesBetween
        (⟨a, hab⟩ : Set.Iic b)
        (⟨b, (by simp : b ∈ Set.Iic b)⟩ : Set.Iic b) q := by
      exact isMaximalSeriesBetween_lower hmp
    have hq : IsMaximalChainBetween a b hab q := hqgen
    have hqeq : q.length = Order.coheight (⟨a, hab⟩ : Set.Iic b) :=
      (hA hablt).2 q hq
    calc
      (p.length : ℕ∞) = (q.length : ℕ∞) := by
        change (p.length : ℕ∞) = (p.length : ℕ∞)
        rfl
      _ = relativeCodimension (le_of_lt hTT') := by
        rw [hcodim']
        simpa [relativeCodimension] using hqeq

private def locallyClosedSubtypeHomeomorph
    {U Z : Set X} :
    ↥(U ∩ Z) ≃ₜ ↥((Subtype.val : Z → X) ⁻¹' U) := by
  let e : ↥(U ∩ Z) ≃ ↥((Subtype.val : Z → X) ⁻¹' U) :=
    { toFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      invFun := fun x => ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  refine { toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · change Continuous (fun x : ↥(U ∩ Z) =>
      (⟨⟨x.1, x.2.2⟩, x.2.1⟩ : ↥((Subtype.val : Z → X) ⁻¹' U)))
    exact (continuous_subtype_val.subtype_mk (fun x => x.2.2)).subtype_mk
      (fun x => x.2.1)
  · change Continuous (fun x : ↥((Subtype.val : Z → X) ⁻¹' U) =>
      (⟨x.1.1, ⟨x.2, x.1.2⟩⟩ : ↥(U ∩ Z)))
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun x => ⟨x.2, x.1.2⟩)

private noncomputable def irreducibleClosedOrderIsoOfHomeomorph
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) : IrreducibleCloseds α ≃o IrreducibleCloseds β := by
  let F : IrreducibleCloseds α → IrreducibleCloseds β :=
    IrreducibleCloseds.map e e.continuous
  let G : IrreducibleCloseds β → IrreducibleCloseds α :=
    IrreducibleCloseds.map e.symm e.symm.continuous
  have hGF : Function.LeftInverse G F := by
    intro c
    apply IrreducibleCloseds.ext
    change closure (e.symm '' closure (e '' (c : Set α))) = (c : Set α)
    rw [e.symm.image_closure]
    rw [Set.image_image]
    simp [c.isClosed.closure_eq]
  have hFG : Function.RightInverse G F := by
    intro c
    apply IrreducibleCloseds.ext
    change closure (e '' closure (e.symm '' (c : Set β))) = (c : Set β)
    rw [e.image_closure]
    rw [Set.image_image]
    simp [c.isClosed.closure_eq]
  exact
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      map_rel_iff' := by
        intro a b
        constructor
        · intro hab
          change closure (e '' (a : Set α)) ⊆ closure (e '' (b : Set α)) at hab
          have h := Set.image_mono (f := e.symm) hab
          simpa [e.symm.image_closure, Set.image_image, a.isClosed.closure_eq,
            b.isClosed.closure_eq] using h
        · intro hab
          change closure (e '' (a : Set α)) ⊆ closure (e '' (b : Set α))
          exact IrreducibleCloseds.map_mono e.continuous hab }

private theorem isCatenary_of_isOpen
    {U : Set X} (hU : IsOpen U) (hX : IsCatenary X) : IsCatenary U := by
  intro T T' hTT'
  let f : U → X := (↑)
  have hf : _root_.Topology.IsOpenEmbedding f := hU.isOpenEmbedding_subtypeVal
  let e := orderIsoOfIsOpenEmbedding f hf
  let A : IrreducibleCloseds X := (e T).1
  let B : IrreducibleCloseds X := (e T').1
  have hAB : A ≤ B := by
    exact e.monotone hTT'.le
  have hABlt : A < B := e.strictMono hTT'
  have hP : ∀ ⦃V W : IrreducibleCloseds X⦄, V ≤ W →
      (f ⁻¹' (V : Set X)).Nonempty → (f ⁻¹' (W : Set X)).Nonempty := by
    intro V W hVW hV
    exact hV.mono (Set.preimage_mono hVW)
  have ha : e T =
      (⟨A, (e T).property⟩ : {V : IrreducibleCloseds X // (f ⁻¹' V).Nonempty}) := by
    apply Subtype.ext
    rfl
  have hb : e T' =
      (⟨B, (e T').property⟩ : {V : IrreducibleCloseds X // (f ⁻¹' V).Nonempty}) := by
    apply Subtype.ext
    rfl
  let E : Set.Ici (⟨T, le_of_lt hTT'⟩ : Set.Iic T') ≃o
      Set.Ici (⟨A, hAB⟩ : Set.Iic B) :=
    (upperIntervalOrderIsoNormalized e hP hAB (e T).property (e T').property
      (le_of_lt hTT') ha hb).symm
  have hcodim : relativeCodimension (le_of_lt hTT') =
      Order.coheight (⟨A, hAB⟩ : Set.Iic B) := by
    simpa [relativeCodimension] using coheight_eq_of_upperIntervalOrderIso E
  refine ⟨?_, ?_⟩
  · rw [hcodim]
    exact (hX hABlt).1
  · intro p hp
    let lp := liftSeriesToIci p hp.1
    have hpgen : IsMaximalSeriesBetween
        (⟨T, le_of_lt hTT'⟩ : Set.Iic T')
        (⟨T', (by simp : T' ∈ Set.Iic T')⟩ : Set.Iic T') p := hp
    have hlp := isMaximalSeriesBetween_lift
      (α := Set.Iic T') (a := (⟨T, le_of_lt hTT'⟩ : Set.Iic T'))
      (b := (⟨T', (by simp : T' ∈ Set.Iic T')⟩ : Set.Iic T'))
      (hab := le_of_lt hTT') hpgen.1 hpgen.2.1 hpgen
    let mp := lp.map E E.strictMono
    have hmp := isMaximalSeriesBetween_map_orderIso (e := E) hlp
    let q := mp.map (fun x : Set.Ici (⟨A, hAB⟩ : Set.Iic B) =>
      (x : Set.Iic B)) (by
        intro x y hxy
        exact hxy)
    have hqgen : IsMaximalSeriesBetween
        (⟨A, hAB⟩ : Set.Iic B)
        (⟨B, (by simp : B ∈ Set.Iic B)⟩ : Set.Iic B) q := by
      exact isMaximalSeriesBetween_lower hmp
    have hq : IsMaximalChainBetween A B hAB q := hqgen
    have hqeq : q.length = Order.coheight (⟨A, hAB⟩ : Set.Iic B) :=
      (hX hABlt).2 q hq
    calc
      (p.length : ℕ∞) = (q.length : ℕ∞) := by
        change (p.length : ℕ∞) = (p.length : ℕ∞)
        rfl
      _ = relativeCodimension (le_of_lt hTT') := by
        rw [hcodim]
        exact hqeq

theorem isCatenary_iff_openCover :
    IsCatenary X ↔
      ∃ (ι : Type v) (U : ι → Opens X),
        TopologicalSpace.IsOpenCover U ∧ ∀ i, IsCatenary (U i) := by
  constructor
  · intro hX
    refine ⟨PUnit, (fun _ => ⟨Set.univ, isOpen_univ⟩), ?_, ?_⟩
    · simp [TopologicalSpace.IsOpenCover]
    · intro i
      exact isCatenary_of_isOpen isOpen_univ hX
  · rintro ⟨ι, U, hU, hUi⟩
    intro T T' hTT'
    obtain ⟨x, hxT⟩ := T.2.nonempty
    obtain ⟨i, hxi⟩ := hU.exists_mem x
    let f : (U i) → X := (↑)
    have hf : _root_.Topology.IsOpenEmbedding f := (U i).2.isOpenEmbedding_subtypeVal
    let e := orderIsoOfIsOpenEmbedding f hf
    have hPA : (f ⁻¹' (T : Set X)).Nonempty := ⟨⟨x, hxi⟩, hxT⟩
    have hPB : (f ⁻¹' (T' : Set X)).Nonempty :=
      hPA.mono (Set.preimage_mono hTT'.le)
    have hP : ∀ ⦃V W : IrreducibleCloseds X⦄, V ≤ W →
        (f ⁻¹' (V : Set X)).Nonempty → (f ⁻¹' (W : Set X)).Nonempty := by
      intro V W hVW hV
      exact hV.mono (Set.preimage_mono hVW)
    let a : IrreducibleCloseds (U i) := e.symm ⟨T, hPA⟩
    let b : IrreducibleCloseds (U i) := e.symm ⟨T', hPB⟩
    have hab : a ≤ b := by
      exact e.symm.monotone hTT'.le
    have hablt : a < b := by
      exact e.symm.strictMono hTT'
    have ha : e a = ⟨T, hPA⟩ := by
      exact e.apply_symm_apply _
    have hb : e b = ⟨T', hPB⟩ := by
      exact e.apply_symm_apply _
    let E := upperIntervalOrderIsoNormalized e hP hTT'.le hPA hPB hab ha hb
    have hcodim :
        Order.coheight (⟨T, hTT'.le⟩ : Set.Iic T') =
          Order.coheight (⟨a, hab⟩ : Set.Iic b) :=
      coheight_eq_of_upperIntervalOrderIso E
    have hcodim' :
        relativeCodimension hTT'.le = relativeCodimension hab := by
      simpa [relativeCodimension] using hcodim
    refine ⟨?_, ?_⟩
    · rw [hcodim']
      exact (hUi i hablt).1
    · intro p hp
      let lp := liftSeriesToIci p hp.1
      have hpgen : IsMaximalSeriesBetween
          (⟨T, hTT'.le⟩ : Set.Iic T')
          (⟨T', (by simp : T' ∈ Set.Iic T')⟩ : Set.Iic T') p := hp
      have hlp := isMaximalSeriesBetween_lift (α := Set.Iic T')
        (a := (⟨T, hTT'.le⟩ : Set.Iic T'))
        (b := (⟨T', (by simp : T' ∈ Set.Iic T')⟩ : Set.Iic T'))
        (hab := hTT'.le) hpgen.1 hpgen.2.1 hpgen
      let mp := lp.map E E.strictMono
      have hmp := isMaximalSeriesBetween_map_orderIso (e := E) hlp
      let q := mp.map (fun x : Set.Ici (⟨a, hab⟩ : Set.Iic b) =>
        (x : Set.Iic b)) (by
          intro x y hxy
          exact hxy)
      have hqgen : IsMaximalSeriesBetween
          (⟨a, hab⟩ : Set.Iic b)
          (⟨b, (by simp : b ∈ Set.Iic b)⟩ : Set.Iic b) q := by
        exact isMaximalSeriesBetween_lower hmp
      have hq : IsMaximalChainBetween a b hab q := hqgen
      have hqeq : q.length = Order.coheight (⟨a, hab⟩ : Set.Iic b) :=
        (hUi i hablt).2 q hq
      calc
        (p.length : ℕ∞) = (q.length : ℕ∞) := by
          change (p.length : ℕ∞) = (p.length : ℕ∞)
          rfl
        _ = relativeCodimension (le_of_lt hTT') := by
          rw [hcodim']
          simpa [relativeCodimension] using hqeq

theorem isCatenary_subtype_of_isLocallyClosed
    (hX : IsCatenary X) {Y : Set X} (hY : IsLocallyClosed Y) :
    IsCatenary Y := by
  rcases hY with ⟨U, Z, hU, hZ, rfl⟩
  have hZcat : IsCatenary Z := isCatenary_of_isClosed hZ hX
  let V : Set Z := (Subtype.val : Z → X) ⁻¹' U
  have hV : IsOpen V := by
    dsimp [V]
    exact hU.preimage continuous_subtype_val
  have hVcat : IsCatenary V := isCatenary_of_isOpen hV hZcat
  let h : ↥(U ∩ Z) ≃ₜ ↥V := by
    exact locallyClosedSubtypeHomeomorph (U := U) (Z := Z)
  let e := irreducibleClosedOrderIsoOfHomeomorph h
  exact isCatenary_of_irreducibleClosedOrderIso e.symm hVcat

theorem isCatenary_iff_finite_and_additive_relativeCodimension :
    IsCatenary X ↔
      (∀ ⦃Y Y' : IrreducibleCloseds X⦄ (hYY' : Y < Y'),
        relativeCodimension (le_of_lt hYY') < ⊤) ∧
        (∀ ⦃Y Y' Y'' : IrreducibleCloseds X⦄
          (hYY' : Y < Y') (hY'Y'' : Y' < Y''),
          relativeCodimension (le_of_lt (lt_trans hYY' hY'Y'')) =
              relativeCodimension (le_of_lt hYY') +
              relativeCodimension (le_of_lt hY'Y'')) := by
  constructor
  · intro h
    constructor
    · intro Y Y' hYY'
      exact (h hYY').1
    · intro Y Y' Y'' hYY' hY'Y''
      have hfinYY' : relativeCodimension (le_of_lt hYY') < ⊤ :=
        (h hYY').1
      have hfinY'Y'' : relativeCodimension (le_of_lt hY'Y'') < ⊤ :=
        (h hY'Y'').1
      obtain ⟨p, hp, hplen⟩ :=
        exists_maximal_chain_between hYY' hfinYY'
      obtain ⟨q, hq, hqlen⟩ :=
        exists_maximal_chain_between hY'Y'' hfinY'Y''
      obtain ⟨r, hr, hrlen⟩ :=
        exists_maximal_chain_smash hp hq
      have hp_eq : p.length = relativeCodimension (le_of_lt hYY') :=
        (h hYY').2 p hp
      have hq_eq : q.length = relativeCodimension (le_of_lt hY'Y'') :=
        (h hY'Y'').2 q hq
      calc
        relativeCodimension (le_of_lt (lt_trans hYY' hY'Y'')) = r.length :=
          ((h (lt_trans hYY' hY'Y'')).2 r hr).symm
        _ = p.length + q.length := by exact_mod_cast hrlen
        _ = relativeCodimension (le_of_lt hYY') +
              relativeCodimension (le_of_lt hY'Y'') := by rw [hp_eq, hq_eq]
  · rintro ⟨hfin, hadd⟩
    have aux : ∀ n : ℕ, ∀ {A B : IrreducibleCloseds X}
        (hAB : A < B) (p : LTSeries (Set.Iic B)),
        IsMaximalChainBetween A B (le_of_lt hAB) p →
        p.length = n →
        p.length = relativeCodimension (le_of_lt hAB) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro A B hAB p hp hpn
          cases n with
          | zero =>
              have hheadlast : p.head = p.last := by
                apply congrArg p
                apply Fin.ext
                simp [hpn]
              have hhead : (p.head : IrreducibleCloseds X) = A :=
                congrArg Subtype.val hp.1
              have hlast : (p.last : IrreducibleCloseds X) = B :=
                congrArg Subtype.val hp.2.1
              have hEq : A = B := by
                calc
                  A = (p.head : IrreducibleCloseds X) := hhead.symm
                  _ = (p.last : IrreducibleCloseds X) :=
                    congrArg (fun s : Set.Iic B => (s : IrreducibleCloseds X)) hheadlast
                  _ = B := hlast
              exact (hAB.ne hEq).elim
          | succ k =>
              by_cases hk : k = 0
              · subst k
                have hp0 : p.length ≠ 0 := by simp [hpn]
                have hno : ∀ Z : IrreducibleCloseds X, A < Z → Z < B → False := by
                  intro Z hAZ hZB
                  let z : Set.Iic B := ⟨Z, le_of_lt hZB⟩
                  let a : Set.Iic B := ⟨A, le_of_lt hAB⟩
                  let b : Set.Iic B := ⟨B, by simp⟩
                  let q₀ : LTSeries (Set.Iic B) :=
                    (RelSeries.singleton _ z).cons a (by
                      change A < Z
                      exact hAZ)
                  let q : LTSeries (Set.Iic B) := q₀.snoc b (by
                    change Z < B
                    exact hZB)
                  have hpq : Set.range p ⊆ Set.range q := by
                    rintro _ ⟨j, rfl⟩
                    have hjlt : j.val < p.length + 1 := j.isLt
                    have hjlt' : j.val < 2 := by omega
                    have hjval : j.val = 0 ∨ j.val = 1 := by omega
                    have hqhead : q.head = p.head := by
                      calc
                        q.head = a := by simp [q, q₀]
                        _ = p.head := by simpa [a] using hp.1.symm
                    have hqlast : q.last = p.last := by
                      calc
                        q.last = b := by simp [q]
                        _ = p.last := by
                          simpa [b] using hp.2.1.symm
                    rcases hjval with hjval | hjval
                    · have hjzero : j = 0 := Fin.ext hjval
                      subst j
                      rw [show p 0 = p.head by rfl, ← hqhead]
                      exact RelSeries.head_mem q
                    · have hjlast : j = Fin.last p.length := by
                        apply Fin.ext
                        simpa [hpn] using hjval
                      rw [hjlast]
                      change p.last ∈ Set.range q
                      rw [← hqlast]
                      exact RelSeries.last_mem q
                  have hqp : Set.range q ⊆ Set.range p := by
                    apply hp.2.2 q
                    · simp [q, q₀, a]
                    · simp [q, q₀, b]
                    · exact hpq
                  have hlen : q.length ≤ p.length := length_le_of_range_subset hqp
                  have : 2 ≤ 1 := by
                    simp [q, q₀, hpn] at hlen
                  omega
                have hco := coheight_Iic_eq_one_of_no_between hAB hno
                calc
                  (p.length : ℕ∞) = (1 : ℕ∞) := by simp [hpn]
                  _ = relativeCodimension (le_of_lt hAB) := by
                    simpa [relativeCodimension] using hco.symm
              · have hp0 : p.length ≠ 0 := by simp [hpn]
                let i : Fin (p.length + 1) := ⟨1, by omega⟩
                have hi0 : (0 : Fin (p.length + 1)) < i := by
                  change (0 : Nat) < 1
                  omega
                have hABi : A < (p i : IrreducibleCloseds X) := by
                  have h := p.strictMono hi0
                  have h' : (p.head : IrreducibleCloseds X) < (p i : IrreducibleCloseds X) := h
                  have hhead : (p.head : IrreducibleCloseds X) = A :=
                    congrArg Subtype.val hp.1
                  rw [hhead] at h'
                  exact h'
                have hiLast : i < (Fin.last p.length) := by
                  change 1 < p.length
                  omega
                have hBi : (p i : IrreducibleCloseds X) < B := by
                  have h := p.strictMono hiLast
                  have h' : (p i : IrreducibleCloseds X) < (p.last : IrreducibleCloseds X) := h
                  have hlast : (p.last : IrreducibleCloseds X) = B :=
                    congrArg Subtype.val hp.2.1
                  rw [hlast] at h'
                  exact h'
                have hno : ∀ Z : IrreducibleCloseds X,
                    A < Z → Z < (p i : IrreducibleCloseds X) → False := by
                  intro Z hAZ hZi
                  let t := p.tail hp0
                  let z : Set.Iic B := ⟨Z, by simpa using (hZi.trans hBi).le⟩
                  have hpos : 0 < p.length := Nat.pos_of_ne_zero hp0
                  have hzt : z < t.head := by
                    rw [RelSeries.head_tail]
                    have hi_one : p (⟨1, by omega⟩ : Fin (p.length + 1)) = p i := by
                      apply congrArg p
                      apply Fin.ext
                      simp [i]
                    have hi_one' := congrArg Subtype.val hi_one
                    have hZi' : (z : IrreducibleCloseds X) <
                        (p (⟨1, by omega⟩ : Fin (p.length + 1)) : IrreducibleCloseds X) := by
                      rw [hi_one']
                      simpa [z] using hZi
                    have hp_one_eq :
                        (p (⟨1, by omega⟩ : Fin (p.length + 1)) : IrreducibleCloseds X) =
                          (p 1 : IrreducibleCloseds X) := by
                      apply congrArg Subtype.val
                      apply congrArg p
                      apply Fin.ext
                      have hone_lt : (1 : Nat) < p.length + 1 := by omega
                      simp [Nat.mod_eq_of_lt hone_lt]
                    rw [hp_one_eq] at hZi'
                    change (z : IrreducibleCloseds X) < (p 1 : IrreducibleCloseds X)
                    exact hZi'
                  let q₀ : LTSeries (Set.Iic B) := t.cons z hzt
                  have hpheadz : p.head < z := by
                    change (p.head : IrreducibleCloseds X) < Z
                    have hhead : (p.head : IrreducibleCloseds X) = A :=
                      congrArg Subtype.val hp.1
                    rw [hhead]
                    exact hAZ
                  let q : LTSeries (Set.Iic B) := q₀.cons p.head (by
                    rw [show q₀.head = z by simp [q₀]]
                    exact hpheadz)
                  have htq₀ : Set.range t ⊆ Set.range q₀ := by
                    change Set.range t ⊆ Set.range (t.cons z hzt)
                    rw [range_cons_eq_insert (p := t) (a := z) hzt]
                    intro x hx
                    exact Set.mem_insert_iff.mpr (Or.inr hx)
                  have hq₀q : Set.range q₀ ⊆ Set.range q := by
                    change Set.range q₀ ⊆ Set.range (q₀.cons p.head hpheadz)
                    rw [range_cons_eq_insert (p := q₀) (a := p.head) hpheadz]
                    intro x hx
                    exact Set.mem_insert_iff.mpr (Or.inr hx)
                  have hpq : Set.range p ⊆ Set.range q := by
                    rw [range_eq_insert_head_tail hp0]
                    intro x hx
                    rcases Set.mem_insert_iff.mp hx with rfl | hx
                    · exact RelSeries.head_mem q
                    · exact hq₀q (htq₀ hx)
                  have hqp : Set.range q ⊆ Set.range p := by
                    have hqhead : q.head = p.head := by
                      dsimp [q]
                    have hqlast : q.last = p.last := by
                      dsimp [q, q₀, t]
                      simp
                    apply hp.2.2 q
                    · exact hqhead.trans hp.1
                    · exact hqlast.trans hp.2.1
                    · exact hpq
                  have hwq₀ : z ∈ Set.range q₀ := RelSeries.head_mem q₀
                  have hwp : z ∈ Set.range p := hqp (hq₀q hwq₀)
                  rcases hwp with ⟨j, hj⟩
                  have hj0 : (0 : Fin (p.length + 1)) < j := by
                    by_contra hjnot
                    have hjval : j.val = 0 := by
                      change ¬ 0 < j.val at hjnot
                      omega
                    have hjzero : j = 0 := Fin.ext hjval
                    subst j
                    have hp0z : (p.head : IrreducibleCloseds X) = Z := by
                      have h := congrArg Subtype.val hj
                      calc
                        (p.head : IrreducibleCloseds X) = (p 0 : IrreducibleCloseds X) := rfl
                        _ = Z := by simpa [z] using h
                    have hhead : (p.head : IrreducibleCloseds X) = A :=
                      congrArg Subtype.val hp.1
                    have : A = Z := hhead.symm.trans hp0z
                    exact (ne_of_lt hAZ) this
                  have hij : i ≤ j := by
                    change 1 ≤ j.val
                    omega
                  have hle := p.monotone hij
                  have hle' : (p i : IrreducibleCloseds X) ≤ (p j : IrreducibleCloseds X) := hle
                  have hpjZ : (p j : IrreducibleCloseds X) = Z := by
                    have h := congrArg Subtype.val hj
                    simpa [z] using h
                  rw [hpjZ] at hle'
                  exact (not_lt_of_ge hle') hZi
                have hco1 : relativeCodimension (le_of_lt hABi) = 1 := by
                  simpa [relativeCodimension] using
                    (coheight_Iic_eq_one_of_no_between hABi hno)
                have htail : IsMaximalChainBetween (p i : IrreducibleCloseds X) B
                    (le_of_lt hBi) (p.tail hp0) := by
                  simpa [i] using (maximal_tail hp hp0)
                have htail_len : (p.tail hp0).length = k := by
                  simp [hpn]
                have htail_eq : (p.tail hp0).length =
                    relativeCodimension (le_of_lt hBi) := by
                  exact ih k (Nat.lt_succ_self k) hBi (p.tail hp0) htail htail_len
                have hadd' := hadd hABi hBi
                calc
                  (p.length : ℕ∞) = ((1 + (p.tail hp0).length : ℕ) : ℕ∞) := by
                    exact_mod_cast (show p.length = 1 + (p.tail hp0).length by omega)
                  _ = (1 : ℕ∞) + relativeCodimension (le_of_lt hBi) := by
                    change (1 : ℕ∞) + (p.tail hp0).length =
                      (1 : ℕ∞) + relativeCodimension (le_of_lt hBi)
                    rw [htail_eq]
                  _ = relativeCodimension (le_of_lt hABi) +
                      relativeCodimension (le_of_lt hBi) := by rw [hco1]
                  _ = relativeCodimension (le_of_lt hAB) := hadd'.symm
    intro A B hAB
    refine ⟨hfin hAB, ?_⟩
    intro p hp
    exact aux p.length hAB p hp rfl

/-! ## Noetherian space of infinite codimension -/

/-
  The example is put on a type synonym so that the generated topology does
  not conflict with the ordinary topology on the real unit interval.
-/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def unitIntervalTail (n : ℕ+) : Set UnitInterval :=
  (fun x : UnitInterval => (x : ℝ)) ⁻¹' Set.Ioi (1 - ((n : ℕ) : ℝ)⁻¹)

def unitIntervalOpenGenerators : Set (Set UnitInterval) :=
  ({∅, Set.univ} : Set (Set UnitInterval)) ∪ Set.range unitIntervalTail

@[instance_reducible]
def unitIntervalTopology : TopologicalSpace UnitInterval :=
  TopologicalSpace.generateFrom unitIntervalOpenGenerators

abbrev NoetherianInfiniteCodimensionSpace :=
  WithTopology UnitInterval unitIntervalTopology

def noetherianExampleTail (n : ℕ+) : Set NoetherianInfiniteCodimensionSpace :=
  (WithTopology.equiv UnitInterval unitIntervalTopology) ⁻¹' unitIntervalTail n

def noetherianExampleInitialSegment (n : ℕ+) :
    Set NoetherianInfiniteCodimensionSpace :=
  (noetherianExampleTail n)ᶜ

def noetherianExampleZero : NoetherianInfiniteCodimensionSpace :=
  (WithTopology.equiv UnitInterval unitIntervalTopology).symm
    ⟨0, ⟨le_rfl, zero_le_one⟩⟩

theorem noetherianExample_isOpen_iff {U : Set NoetherianInfiniteCodimensionSpace} :
    IsOpen U ↔
      U = ∅ ∨ U = Set.univ ∨ ∃ n : ℕ+, U = noetherianExampleTail n := by
  have htail : ∀ {m n : ℕ+}, m ≤ n → unitIntervalTail n ⊆ unitIntervalTail m := by
    intro m n h x hx
    change 1 - ((n : ℕ) : ℝ)⁻¹ < (x : ℝ) at hx
    change 1 - ((m : ℕ) : ℝ)⁻¹ < (x : ℝ)
    have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.2
    have hinv : ((n : ℕ) : ℝ)⁻¹ ≤ ((m : ℕ) : ℝ)⁻¹ := by
      exact inv_anti₀ hm (by exact_mod_cast h)
    exact (sub_le_sub_left hinv 1).trans_lt hx
  have hinter : ∀ m n : ℕ+, unitIntervalTail m ∩ unitIntervalTail n =
      unitIntervalTail (max m n) := by
    intro m n
    rcases le_total m n with h | h
    · rw [max_eq_right h]
      exact Set.Subset.antisymm (fun _ hx => hx.2) (fun x hx => ⟨htail h hx, hx⟩)
    · rw [max_eq_left h]
      exact Set.Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx, htail h hx⟩)
  have hshape : ∀ {V : Set UnitInterval},
      TopologicalSpace.GenerateOpen unitIntervalOpenGenerators V →
        V = ∅ ∨ V = Set.univ ∨ ∃ n : ℕ+, V = unitIntervalTail n := by
    intro V hV
    induction hV with
    | basic s hs =>
        rcases hs with hs | ⟨n, rfl⟩
        · rcases hs with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨n, rfl⟩)
    | univ =>
        exact Or.inr (Or.inl rfl)
    | inter s t hs ht ihs iht =>
        rcases ihs with rfl | rfl | ⟨m, rfl⟩
        · exact Or.inl (by simp)
        · simpa only [Set.univ_inter] using iht
        · rcases iht with rfl | rfl | ⟨n, rfl⟩
          · exact Or.inl (by simp)
          · exact Or.inr (Or.inr ⟨m, by simp⟩)
          · exact Or.inr (Or.inr ⟨max m n, hinter m n⟩)
    | sUnion S hS ih =>
        by_cases huniv : ∃ s ∈ S, s = Set.univ
        · rcases huniv with ⟨s, hs, rfl⟩
          exact Or.inr (Or.inl (Set.Subset.antisymm
            (Set.subset_univ _) (Set.subset_sUnion_of_mem hs)))
        by_cases htailmem : ∃ n : ℕ+, unitIntervalTail n ∈ S
        · let N : Set ℕ+ := {n | unitIntervalTail n ∈ S}
          have hN : N.Nonempty := by
            rcases htailmem with ⟨n, hn⟩
            exact ⟨n, hn⟩
          obtain ⟨m, hmN⟩ :=
            WellFoundedLT.exists_minimal (α := ℕ+) inferInstance N hN
          have hmS : unitIntervalTail m ∈ S := hmN.prop
          refine Or.inr (Or.inr ⟨m, Set.Subset.antisymm ?_ (Set.subset_sUnion_of_mem hmS)⟩)
          apply Set.sUnion_subset
          intro s hs
          rcases ih s hs with hs0 | hsu | ⟨n, hn⟩
          · exact hs0 ▸ Set.empty_subset _
          · exact (huniv ⟨s, hs, hsu⟩).elim
          · rw [hn]
            apply htail
            have hnN : n ∈ N := by
              change unitIntervalTail n ∈ S
              rw [← hn]
              exact hs
            exact le_of_not_gt (hmN.not_lt hnN)
        · apply Or.inl
          apply Set.sUnion_eq_empty.mpr
          intro s hs
          rcases ih s hs with hs0 | hsu | ⟨n, hn⟩
          · exact hs0
          · exact (huniv ⟨s, hs, hsu⟩).elim
          · have hnS : unitIntervalTail n ∈ S := by
              rw [← hn]
              exact hs
            exact (htailmem ⟨n, hnS⟩).elim
  let e := WithTopology.equiv UnitInterval unitIntervalTopology
  constructor
  · intro hU
    have hV : @IsOpen UnitInterval unitIntervalTopology (e.symm ⁻¹' U) :=
      (WithTopology.isOpen_iff unitIntervalTopology).1 hU
    rcases hshape hV with hVempty | hVuniv | ⟨n, hVtail⟩
    · left
      apply (Set.preimage_eq_preimage e.symm.surjective).mp
      simp [hVempty]
    · right; left
      apply (Set.preimage_eq_preimage e.symm.surjective).mp
      simp [hVuniv]
    · right; right
      apply Exists.intro n
      apply (Set.preimage_eq_preimage e.symm.surjective).mp
      simp [noetherianExampleTail, e, hVtail]
  · rintro (rfl | rfl | ⟨n, rfl⟩)
    · exact isOpen_empty
    · exact isOpen_univ
    · apply (WithTopology.isOpen_iff unitIntervalTopology).2
      change @IsOpen UnitInterval unitIntervalTopology
        (e.symm ⁻¹' (e ⁻¹' unitIntervalTail n))
      rw [e.symm_preimage_preimage]
      change @IsOpen UnitInterval (TopologicalSpace.generateFrom unitIntervalOpenGenerators)
        (unitIntervalTail n)
      exact isOpen_generateFrom_of_mem
        (show unitIntervalTail n ∈ unitIntervalOpenGenerators from
          Or.inr ⟨n, rfl⟩)

theorem noetherianExample_isClosed_iff {F : Set NoetherianInfiniteCodimensionSpace} :
    IsClosed F ↔
      F = ∅ ∨ F = {noetherianExampleZero} ∨
        (∃ n : ℕ+, 1 < n ∧ F = noetherianExampleInitialSegment n) ∨
          F = Set.univ := by
  let e := WithTopology.equiv UnitInterval unitIntervalTopology
  have hzero : noetherianExampleInitialSegment 1 = {noetherianExampleZero} := by
    ext x
    constructor
    · intro hx
      change ¬ (1 - ((1 : ℕ) : ℝ)⁻¹ < ((e x : UnitInterval) : ℝ)) at hx
      have hxle : ((e x : UnitInterval) : ℝ) ≤ 0 := by
        simpa using (le_of_not_gt hx)
      have heq : (e x : UnitInterval) = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ := by
        apply Subtype.ext
        exact le_antisymm hxle (e x).2.1
      apply Set.mem_singleton_iff.mpr
      apply e.injective
      simpa [noetherianExampleZero, e] using heq
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change ¬ (1 - ((1 : ℕ) : ℝ)⁻¹ < ((e (noetherianExampleZero) : UnitInterval) : ℝ))
      simp [noetherianExampleZero, e]
  constructor
  · intro hF
    have hopen : IsOpen Fᶜ := hF.isOpen_compl
    rcases noetherianExample_isOpen_iff.mp hopen with hempty | huniv | ⟨n, htail⟩
    · right; right; right
      calc
        F = (Fᶜ)ᶜ := by simp
        _ = ∅ᶜ := by rw [hempty]
        _ = Set.univ := by simp
    · left
      calc
        F = (Fᶜ)ᶜ := by simp
        _ = Set.univᶜ := by rw [huniv]
        _ = ∅ := by simp
    · rcases eq_or_lt_of_le (show (1 : ℕ+) ≤ n from bot_le) with hn | hn
      · subst n
        right; left
        calc
          F = (Fᶜ)ᶜ := by simp
          _ = (noetherianExampleTail 1)ᶜ := by rw [htail]
          _ = noetherianExampleInitialSegment 1 := rfl
          _ = {noetherianExampleZero} := hzero
      · right; right; left
        refine ⟨n, hn, ?_⟩
        calc
          F = (Fᶜ)ᶜ := by simp
          _ = (noetherianExampleTail n)ᶜ := by rw [htail]
          _ = noetherianExampleInitialSegment n := rfl
  · rintro (rfl | rfl | ⟨n, hn, rfl⟩ | rfl)
    · exact isClosed_empty
    · rw [← hzero]
      change IsClosed (noetherianExampleTail 1)ᶜ
      exact isClosed_compl_iff.mpr
        (noetherianExample_isOpen_iff.mpr (Or.inr (Or.inr ⟨1, rfl⟩)))
    · change IsClosed (noetherianExampleTail n)ᶜ
      exact isClosed_compl_iff.mpr
        (noetherianExample_isOpen_iff.mpr (Or.inr (Or.inr ⟨n, rfl⟩)))
    · exact isClosed_univ

theorem noetherianExample_isNoetherian :
    NoetherianSpace NoetherianInfiniteCodimensionSpace := by
  let e := WithTopology.equiv UnitInterval unitIntervalTopology
  have htailUnit : ∀ {m n : ℕ+}, m ≤ n → unitIntervalTail n ⊆ unitIntervalTail m := by
    intro m n h x hx
    change 1 - ((n : ℕ) : ℝ)⁻¹ < (x : ℝ) at hx
    change 1 - ((m : ℕ) : ℝ)⁻¹ < (x : ℝ)
    have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.2
    have hinv : ((n : ℕ) : ℝ)⁻¹ ≤ ((m : ℕ) : ℝ)⁻¹ := by
      exact inv_anti₀ hm (by exact_mod_cast h)
    exact (sub_le_sub_left hinv 1).trans_lt hx
  have htailNo : ∀ {m n : ℕ+}, m ≤ n →
      noetherianExampleTail n ⊆ noetherianExampleTail m := by
    intro m n h x hx
    change e x ∈ unitIntervalTail n at hx
    change e x ∈ unitIntervalTail m
    exact htailUnit h hx
  have hzero_not_tail : ∀ n : ℕ+, noetherianExampleZero ∉ noetherianExampleTail n := by
    intro n
    change ¬ (1 - ((n : ℕ) : ℝ)⁻¹ < (0 : ℝ))
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast n.2
    exact not_lt_of_ge (sub_nonneg.mpr (inv_le_one_of_one_le₀ hn1))
  have hwitness : ∀ m : ℕ+, ∃ z : UnitInterval,
      z ∈ unitIntervalTail m ∧ z ∉ unitIntervalTail (m + 1) := by
    intro m
    let k : ℕ := (m : ℕ) + 1
    have hk : (1 : ℝ) ≤ (k : ℝ) := by
      dsimp [k]
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (m : ℕ)))
    have hkp : (0 : ℝ) < (k : ℝ) := zero_lt_one.trans_le hk
    have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.2
    have hmk : (m : ℝ) < (k : ℝ) := by
      dsimp [k]
      exact_mod_cast (Nat.lt_succ_self (m : ℕ))
    have hkinv : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk
    let z : UnitInterval := ⟨1 - (k : ℝ)⁻¹,
      sub_nonneg.mpr hkinv, sub_le_self 1 (inv_pos.mpr hkp).le⟩
    have hinv : (k : ℝ)⁻¹ < (m : ℝ)⁻¹ := (inv_lt_inv₀ hkp hm).2 hmk
    refine ⟨z, ?_, ?_⟩
    · change 1 - ((m : ℕ) : ℝ)⁻¹ < (z : ℝ)
      change 1 - (m : ℝ)⁻¹ < 1 - (k : ℝ)⁻¹
      exact (sub_lt_sub_left hinv 1)
    · change ¬ (1 - (((m + 1 : ℕ+) : ℕ) : ℝ)⁻¹ < (z : ℝ))
      change ¬ (1 - (k : ℝ)⁻¹ < 1 - (k : ℝ)⁻¹)
      exact lt_irrefl _
  have hcompact : ∀ {s : Set NoetherianInfiniteCodimensionSpace},
      IsOpen s → IsCompact s := by
    intro s hs
    rcases noetherianExample_isOpen_iff.mp hs with hs0 | hsu | ⟨m, rfl⟩
    · rw [hs0]
      exact isCompact_empty
    · rw [hsu]
      apply isCompact_of_finite_subcover
      intro ι U hUo hcover
      by_cases hUniv : ∃ i, U i = Set.univ
      · rcases hUniv with ⟨i, hi⟩
        refine ⟨{i}, ?_⟩
        intro x hx
        simp only [Set.mem_iUnion, Finset.mem_singleton]
        exact ⟨i, ⟨rfl, hi ▸ Set.mem_univ x⟩⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ _))
        rcases noetherianExample_isOpen_iff.mp (hUo i) with hi0 | hi1 | ⟨n, hin⟩
        · rw [hi0] at hi
          exfalso
          simp at hi
        · exact (hUniv ⟨i, hi1⟩).elim
        · rw [hin] at hi
          exfalso
          exact (hzero_not_tail n hi).elim
    · apply isCompact_of_finite_subcover
      intro ι U hUo hcover
      obtain ⟨z, hzm, hzn⟩ := hwitness m
      let x : NoetherianInfiniteCodimensionSpace := e.symm z
      have hxm : x ∈ noetherianExampleTail m := by
        change z ∈ unitIntervalTail m
        exact hzm
      have hxn : x ∉ noetherianExampleTail (m + 1) := by
        change z ∉ unitIntervalTail (m + 1)
        exact hzn
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxm)
      rcases noetherianExample_isOpen_iff.mp (hUo i) with hi0 | hi1 | ⟨n, hin⟩
      · rw [hi0] at hi
        exfalso
        simp at hi
      · refine ⟨{i}, ?_⟩
        intro y hy
        simp only [Set.mem_iUnion, Finset.mem_singleton]
        exact ⟨i, ⟨rfl, hi1 ▸ Set.mem_univ y⟩⟩
      · have hnm : n ≤ m := by
          by_contra hnot
          have hmn : m < n := lt_of_not_ge hnot
          have hsucc : m + 1 ≤ n := PNat.add_one_le_iff.mpr hmn
          have hiTail : x ∈ noetherianExampleTail n := by
            rw [hin] at hi
            exact hi
          exact hxn (htailNo hsucc hiTail)
        refine ⟨{i}, ?_⟩
        intro y hy
        simp only [Set.mem_iUnion, Finset.mem_singleton]
        refine ⟨i, ⟨rfl, ?_⟩⟩
        rw [hin]
        exact htailNo hnm hy
  apply (noetherianSpace_iff_opens NoetherianInfiniteCodimensionSpace).mpr
  intro s
  exact hcompact s.2

theorem noetherianExample_zero_isClosed :
    IsClosed ({noetherianExampleZero} : Set NoetherianInfiniteCodimensionSpace) := by
  exact noetherianExample_isClosed_iff.mpr (Or.inr (Or.inl rfl))

theorem noetherianExample_initialSegment_isIrreducible
    (n : ℕ+) (_hn : 1 < n) :
    IsIrreducible (noetherianExampleInitialSegment n) := by
  let e := WithTopology.equiv UnitInterval unitIntervalTopology
  have htailUnit : ∀ {m k : ℕ+}, m ≤ k → unitIntervalTail k ⊆ unitIntervalTail m := by
    intro m k h x hx
    change 1 - ((k : ℕ) : ℝ)⁻¹ < (x : ℝ) at hx
    change 1 - ((m : ℕ) : ℝ)⁻¹ < (x : ℝ)
    have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.2
    have hinv : ((k : ℕ) : ℝ)⁻¹ ≤ ((m : ℕ) : ℝ)⁻¹ := by
      exact inv_anti₀ hm (by exact_mod_cast h)
    exact (sub_le_sub_left hinv 1).trans_lt hx
  have htail : ∀ {m k : ℕ+}, m ≤ k →
      noetherianExampleTail k ⊆ noetherianExampleTail m := by
    intro m k h x hx
    change e x ∈ unitIntervalTail k at hx
    change e x ∈ unitIntervalTail m
    exact htailUnit h hx
  refine ⟨?_, ?_⟩
  · refine ⟨noetherianExampleZero, ?_⟩
    change ¬ (1 - ((n : ℕ) : ℝ)⁻¹ < (0 : ℝ))
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast n.2
    exact not_lt_of_ge (sub_nonneg.mpr (inv_le_one_of_one_le₀ hn1))
  · intro u v hu hv hsu hsv
    rcases noetherianExample_isOpen_iff.mp hu with hu0 | huu | ⟨a, hua⟩
    · rw [hu0] at hsu
      simp at hsu
    · rw [huu, Set.univ_inter]
      exact hsv
    · rcases noetherianExample_isOpen_iff.mp hv with hv0 | hvu | ⟨b, hvb⟩
      · rw [hv0] at hsv
        simp at hsv
      · rw [hvu, Set.inter_univ]
        exact hsu
      · rcases le_total a b with hab | hba
        · rw [hvb] at hsv
          rw [hua, hvb]
          rcases hsv with ⟨x, hxs, hxv⟩
          exact ⟨x, hxs, ⟨htail hab hxv, hxv⟩⟩
        · rw [hua] at hsu
          rw [hvb] at hsv
          rw [hua, hvb]
          rcases hsu with ⟨x, hxs, hxu⟩
          exact ⟨x, hxs, ⟨hxu, htail hba hxu⟩⟩

theorem noetherianExample_zero_isIrreducible :
    IsIrreducible ({noetherianExampleZero} : Set NoetherianInfiniteCodimensionSpace) :=
  isIrreducible_singleton

theorem noetherianExample_zero_codimension_eq_top :
    codimension
        (⟨{noetherianExampleZero}, noetherianExample_zero_isIrreducible,
          noetherianExample_zero_isClosed⟩ :
          IrreducibleCloseds NoetherianInfiniteCodimensionSpace) = ⊤ := by
  let e := WithTopology.equiv UnitInterval unitIntervalTopology
  have htailUnit : ∀ {m k : ℕ+}, m ≤ k → unitIntervalTail k ⊆ unitIntervalTail m := by
    intro m k h x hx
    change 1 - ((k : ℕ) : ℝ)⁻¹ < (x : ℝ) at hx
    change 1 - ((m : ℕ) : ℝ)⁻¹ < (x : ℝ)
    have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.2
    have hinv : ((k : ℕ) : ℝ)⁻¹ ≤ ((m : ℕ) : ℝ)⁻¹ := by
      exact inv_anti₀ hm (by exact_mod_cast h)
    exact (sub_le_sub_left hinv 1).trans_lt hx
  have htail : ∀ {m k : ℕ+}, m ≤ k →
      noetherianExampleTail k ⊆ noetherianExampleTail m := by
    intro m k h x hx
    change e x ∈ unitIntervalTail k at hx
    change e x ∈ unitIntervalTail m
    exact htailUnit h hx
  let zeroClosed : IrreducibleCloseds NoetherianInfiniteCodimensionSpace :=
    ⟨{noetherianExampleZero}, noetherianExample_zero_isIrreducible,
      noetherianExample_zero_isClosed⟩
  let segment : ∀ k : ℕ+, 1 < k → IrreducibleCloseds NoetherianInfiniteCodimensionSpace :=
    fun k hk => ⟨noetherianExampleInitialSegment k,
      noetherianExample_initialSegment_isIrreducible k hk,
      noetherianExample_isClosed_iff.mpr
        (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))⟩
  have hzero_lt_segment : ∀ {b : ℕ+} (hb : 1 < b),
      zeroClosed < segment b hb := by
    intro b hb
    apply lt_of_le_of_ne
    · intro x hx
      change x ∈ ({noetherianExampleZero} :
        Set NoetherianInfiniteCodimensionSpace) at hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change ¬ (1 - ((b : ℕ) : ℝ)⁻¹ < (0 : ℝ))
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
      exact not_lt_of_ge (sub_nonneg.mpr (inv_le_one_of_one_le₀ hb1))
    · intro heq
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
      have hbp : (0 : ℝ) < (b : ℝ) := zero_lt_one.trans_le hb1
      have hbinv : (b : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
      have hbinvlt : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hb)
      let z : UnitInterval := ⟨1 - (b : ℝ)⁻¹,
        sub_nonneg.mpr hbinv, sub_le_self 1 (inv_pos.mpr hbp).le⟩
      let x : NoetherianInfiniteCodimensionSpace := e.symm z
      have hxb : x ∈ noetherianExampleInitialSegment b := by
        change ¬ (1 - (b : ℝ)⁻¹ < (z : ℝ))
        change ¬ (1 - (b : ℝ)⁻¹ < 1 - (b : ℝ)⁻¹)
        exact lt_irrefl _
      have hxnot : x ∉ ({noetherianExampleZero} :
          Set NoetherianInfiniteCodimensionSpace) := by
        rw [Set.mem_singleton_iff]
        intro hxzero
        have hz : z = (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : UnitInterval) := by
          simpa [x, noetherianExampleZero, e] using congrArg e hxzero
        have hzval : (z : ℝ) = 0 := congrArg Subtype.val hz
        exact (sub_ne_zero.mpr (by exact ne_of_gt hbinvlt)) hzval
      apply hxnot
      apply heq.symm.le
      exact hxb
  have hsegment_strict :
      ∀ {a b : ℕ+} (ha : 1 < a) (hb : 1 < b), a < b →
        segment a ha < segment b hb := by
    intro a b ha hb hab
    apply lt_of_le_of_ne
    · intro x hx
      change x ∈ noetherianExampleInitialSegment a at hx
      change x ∈ noetherianExampleInitialSegment b
      change x ∉ noetherianExampleTail b
      intro hxb
      apply hx
      exact htail hab.le hxb
    · intro heq
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
        exact_mod_cast hb.le
      have hbp : (0 : ℝ) < (b : ℝ) := zero_lt_one.trans_le hb1
      have hap : (0 : ℝ) < (a : ℝ) := by exact_mod_cast a.2
      have habinv : (b : ℝ)⁻¹ < (a : ℝ)⁻¹ :=
        (inv_lt_inv₀ hbp hap).2 (by exact_mod_cast hab)
      have hbinv : (b : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
      let z : UnitInterval := ⟨1 - (b : ℝ)⁻¹,
        sub_nonneg.mpr hbinv, sub_le_self 1 (inv_pos.mpr hbp).le⟩
      let x : NoetherianInfiniteCodimensionSpace := e.symm z
      have hxb : x ∈ noetherianExampleInitialSegment b := by
        change ¬ (1 - (b : ℝ)⁻¹ < (z : ℝ))
        change ¬ (1 - (b : ℝ)⁻¹ < 1 - (b : ℝ)⁻¹)
        exact lt_irrefl _
      have hxaTail : x ∈ noetherianExampleTail a := by
        change 1 - (a : ℝ)⁻¹ < (z : ℝ)
        change 1 - (a : ℝ)⁻¹ < 1 - (b : ℝ)⁻¹
        exact sub_lt_sub_left habinv 1
      have hxa : x ∉ noetherianExampleInitialSegment a := by
        simpa [noetherianExampleInitialSegment] using hxaTail
      apply hxa
      apply heq.symm.le
      exact hxb
  unfold codimension
  change Order.coheight zeroClosed = ⊤
  apply Order.coheight_eq_top_iff.mpr
  intro N
  let k : Fin N → ℕ+ := fun i => ⟨i.val + 2, by exact Nat.succ_pos _⟩
  have hk : ∀ i : Fin N, 1 < k i := by
    intro i
    change 1 < i.val + 2
    exact Nat.lt_succ_iff.mpr (Nat.succ_le_succ (Nat.zero_le i.val))
  let q : Fin (N + 1) → IrreducibleCloseds NoetherianInfiniteCodimensionSpace :=
    Fin.cases zeroClosed (fun i => segment (k i) (hk i))
  have hq : StrictMono q := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero =>
            exact (lt_irrefl _ hij).elim
        | succ j =>
            change zeroClosed < segment (k j) (hk j)
            exact hzero_lt_segment (hk j)
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            exact (not_lt_of_ge (Fin.zero_le _) hij).elim
        | succ j =>
            change segment (k i) (hk i) < segment (k j) (hk j)
            apply hsegment_strict (hk i) (hk j)
            have hij' : i < j := Fin.succ_lt_succ_iff.mp hij
            change i.val + 2 < j.val + 2
            exact Nat.add_lt_add_right (Fin.lt_def.mp hij') 2
  refine ⟨LTSeries.mk N q hq, ?_, ?_⟩
  · rfl
  · rfl

end CodimensionAndCatenary

end Formalization.Books.Topology.Unit11
