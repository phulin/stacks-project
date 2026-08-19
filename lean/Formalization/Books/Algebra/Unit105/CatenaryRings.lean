import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit54.EssentiallyFiniteType
import Formalization.Books.Topology.Unit20.DimensionFunctions
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.MvPolynomial

/-!
# Commutative Algebra, Chapter 105: Catenary rings

The ring-theoretic catenary predicate uses finite strict chains in the prime
spectrum.  The maximal-chain interface is the canonical one from Topology,
Chapter 11, while universal catenarity and essential finite type use the
established algebra predicates.
-/

namespace Formalization.Books.Algebra.Unit105

universe u v

noncomputable section

/-! ## Prime chains and catenary rings -/

/- A finite strict chain in `Spec R` with prescribed endpoints. -/
def IsPrimeChainBetween
    {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) (hpq : p ≤ q)
    (c : LTSeries (Set.Iic q)) : Prop :=
    c.head = (⟨p, hpq⟩ : Set.Iic q) ∧
    c.last = (⟨q, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic q)

private def IsGlobalChainBetween {α : Type*} [Preorder α]
    (p q : α) (c : LTSeries α) : Prop :=
  c.head = p ∧ c.last = q

private def IsGlobalMaximalChainBetween {α : Type*} [Preorder α]
    (p q : α) (c : LTSeries α) : Prop :=
  c.head = p ∧ c.last = q ∧
    ∀ d : LTSeries α,
      d.head = p → d.last = q →
        Set.range c ⊆ Set.range d → Set.range d ⊆ Set.range c

private def IsGlobalCatenary (α : Type*) [Preorder α] : Prop :=
  ∀ ⦃p q : α⦄ (hpq : p < q),
    ∃ n : ℕ,
      (∀ c : LTSeries α,
        IsGlobalChainBetween p q c → c.length ≤ n) ∧
        ∀ c d : LTSeries α,
          IsGlobalMaximalChainBetween p q c →
          IsGlobalMaximalChainBetween p q d → c.length = d.length

private def forgetChain {α : Type*} [Preorder α]
    {q : α} (c : LTSeries (Set.Iic q)) : LTSeries α :=
  { length := c.length
    toFun := fun i => (c i : α)
    step := fun i => by
      exact c.strictMono (by
        change i.val < i.val + 1
        omega) }

private def liftChain {α : Type*} [Preorder α]
    {p q : α} (c : LTSeries α) (hhead : c.head = p) (hlast : c.last = q) :
    LTSeries (Set.Iic q) :=
  { length := c.length
    toFun := fun i => ⟨c i, by
      rw [← hlast]
      exact c.monotone (Fin.le_last i)⟩
    step := fun i => by
      apply c.strictMono
      change i.val < i.val + 1
      omega }

private lemma forgetChain_isGlobalChainBetween
    {α : Type*} [Preorder α] {p q : α} {c : LTSeries (Set.Iic q)}
    (hpq : p < q)
    (hc : c.head = (⟨p, le_of_lt hpq⟩ : Set.Iic q) ∧
      c.last = (⟨q, le_rfl⟩ : Set.Iic q)) :
    IsGlobalChainBetween p q (forgetChain c) := by
  exact ⟨congrArg Subtype.val hc.1, congrArg Subtype.val hc.2⟩

private lemma forgetChain_head_last
    {α : Type*} [Preorder α] {p q : α} {c : LTSeries (Set.Iic q)}
    (hpq : p ≤ q)
    (hc : c.head = (⟨p, hpq⟩ : Set.Iic q) ∧
      c.last = (⟨q, le_rfl⟩ : Set.Iic q)) :
    (forgetChain c).head = p ∧ (forgetChain c).last = q := by
  exact ⟨congrArg Subtype.val hc.1, congrArg Subtype.val hc.2⟩

private lemma forgetChain_liftChain
    {α : Type*} [Preorder α] {p q : α} {c : LTSeries α}
    (hhead : c.head = p) (hlast : c.last = q) :
    forgetChain (liftChain c hhead hlast) = c := by
  ext i <;> rfl

private lemma liftChain_head_last
    {α : Type*} [Preorder α] {p q : α} {c : LTSeries α}
    (hpq : p < q)
    (hhead : c.head = p) (hlast : c.last = q) :
    (liftChain c hhead hlast).head = (⟨p, le_of_lt hpq⟩ : Set.Iic q) ∧
      (liftChain c hhead hlast).last = (⟨q, le_rfl⟩ : Set.Iic q) := by
  constructor
  · apply Subtype.ext
    exact hhead
  · apply Subtype.ext
    exact hlast

private lemma globalMax_forget_iff
    {α : Type*} [PartialOrder α] {p q : α} (hpq : p < q)
    {c : LTSeries (Set.Iic q)}
    (hc : c.head = (⟨p, le_of_lt hpq⟩ : Set.Iic q) ∧
      c.last = (⟨q, le_rfl⟩ : Set.Iic q)) :
    IsGlobalMaximalChainBetween p q (forgetChain c) ↔
      Formalization.Books.Topology.Unit11.IsMaximalChainBetween p q
        (le_of_lt hpq) c := by
  constructor
  · intro h
    refine ⟨hc.1, hc.2, ?_⟩
    intro d hdhead hdlast hcd
    have hglobal : IsGlobalChainBetween p q (forgetChain d) :=
      forgetChain_isGlobalChainBetween hpq ⟨hdhead, hdlast⟩
    have hcd' : Set.range (forgetChain c) ⊆ Set.range (forgetChain d) := by
      intro x hx
      rcases hx with ⟨i, rfl⟩
      rcases hcd ⟨i, rfl⟩ with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      change d j = c i at hj
      exact congrArg Subtype.val hj
    have hdc := h.2.2 (forgetChain d) hglobal.1 hglobal.2 hcd'
    intro x hx
    rcases hx with ⟨i, rfl⟩
    rcases hdc ⟨i, rfl⟩ with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    simpa only [forgetChain] using hj
  · intro h
    have hc_headlast := forgetChain_head_last (le_of_lt hpq) hc
    refine ⟨hc_headlast.1, hc_headlast.2, ?_⟩
    intro d hdhead hdlast hcd
    let hd' := liftChain d hdhead hdlast
    have hd'headlast := liftChain_head_last hpq hdhead hdlast
    have hcd' : Set.range c ⊆ Set.range hd' := by
      intro x hx
      rcases hx with ⟨i, rfl⟩
      have hx' : (forgetChain c) i ∈ Set.range d := hcd ⟨i, rfl⟩
      rcases hx' with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      apply Subtype.ext
      simpa only [forgetChain, hd', liftChain] using hj
    have hdc' := h.2.2 hd' hd'headlast.1 hd'headlast.2 hcd'
    intro x hx
    rcases hx with ⟨i, rfl⟩
    rcases hdc' ⟨i, rfl⟩ with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simpa only [forgetChain, hd', liftChain] using congrArg Subtype.val hj

/- The source's bounded-chain/equal-maximal-chain definition. -/
def IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  ∀ ⦃p q : PrimeSpectrum R⦄ (hpq : p < q),
    ∃ n : ℕ,
      (∀ c : LTSeries (Set.Iic q),
        IsPrimeChainBetween p q (le_of_lt hpq) c → c.length ≤ n) ∧
        ∀ c d : LTSeries (Set.Iic q),
          Formalization.Books.Topology.Unit11.IsMaximalChainBetween
            p q (le_of_lt hpq) c →
          Formalization.Books.Topology.Unit11.IsMaximalChainBetween
            p q (le_of_lt hpq) d →
          c.length = d.length

private lemma isGlobalCatenary_iff_isCatenaryRing
    (R : Type u) [CommRing R] :
    IsGlobalCatenary (PrimeSpectrum R) ↔ IsCatenaryRing R := by
  constructor
  · intro h p q hpq
    obtain ⟨n, hn, hmax⟩ := h hpq
    refine ⟨n, ?_, ?_⟩
    · intro c hc
      exact hn (forgetChain c)
        (forgetChain_isGlobalChainBetween hpq hc)
    · intro c d hc hd
      apply hmax (forgetChain c) (forgetChain d)
      · exact (globalMax_forget_iff hpq ⟨hc.1, hc.2.1⟩).mpr hc
      · exact (globalMax_forget_iff hpq ⟨hd.1, hd.2.1⟩).mpr hd
  · intro h p q hpq
    obtain ⟨n, hn, hmax⟩ := h hpq
    refine ⟨n, ?_, ?_⟩
    · intro c hc
      have hc' := liftChain_head_last hpq hc.1 hc.2
      exact hn (liftChain c hc.1 hc.2) hc'
    · intro c d hc hd
      have hc' := liftChain_head_last hpq hc.1 hc.2.1
      have hd' := liftChain_head_last hpq hd.1 hd.2.1
      apply hmax (liftChain c hc.1 hc.2.1) (liftChain d hd.1 hd.2.1)
      · exact (globalMax_forget_iff hpq hc').mp (by
          rw [forgetChain_liftChain hc.1 hc.2.1]
          exact hc)
      · exact (globalMax_forget_iff hpq hd').mp (by
          rw [forgetChain_liftChain hd.1 hd.2.1]
          exact hd)

private def IsIntervalCatenary (α : Type*) [PartialOrder α] : Prop :=
  ∀ ⦃p q : α⦄ (hpq : p < q),
    Order.coheight (⟨p, le_of_lt hpq⟩ : Set.Iic q) < ⊤ ∧
      ∀ c : LTSeries (Set.Iic q),
        Formalization.Books.Topology.Unit11.IsMaximalChainBetween
          p q (le_of_lt hpq) c →
          (c.length : ℕ∞) = Order.coheight (⟨p, le_of_lt hpq⟩ : Set.Iic q)

private lemma length_le_of_range_subset'
    {α : Type*} [Preorder α] {p q : LTSeries α}
    (hpq : Set.range p ⊆ Set.range q) : p.length ≤ q.length := by
  have hcard := Set.ncard_le_ncard hpq
  rw [Set.ncard_range_of_injective p.strictMono.injective,
    Set.ncard_range_of_injective q.strictMono.injective] at hcard
  simpa using hcard

private lemma range_subset_of_range_subset_of_length_le'
    {α : Type*} [Preorder α] {p q : LTSeries α}
    (hpq : Set.range p ⊆ Set.range q) (hqlen : q.length ≤ p.length) :
    Set.range q ⊆ Set.range p := by
  have hcard : (Set.range q).ncard ≤ (Set.range p).ncard := by
    rw [Set.ncard_range_of_injective p.strictMono.injective,
      Set.ncard_range_of_injective q.strictMono.injective]
    simpa using hqlen
  have hfinq : (Set.range q).Finite := Set.finite_range q
  have heq : Set.range p = Set.range q := Set.eq_of_subset_of_ncard_le hpq hcard hfinq
  rw [heq]

private lemma exists_maximal_interval_chain
    {α : Type*} [PartialOrder α] {p q : α} (hpq : p < q)
    (hfin : Order.coheight (⟨p, le_of_lt hpq⟩ : Set.Iic q) < ⊤) :
    ∃ c : LTSeries (Set.Iic q),
      Formalization.Books.Topology.Unit11.IsMaximalChainBetween
        p q (le_of_lt hpq) c ∧
      (c.length : ℕ∞) = Order.coheight (⟨p, le_of_lt hpq⟩ : Set.Iic q) := by
  let x : Set.Iic q := ⟨p, le_of_lt hpq⟩
  let z : Set.Iic q := ⟨q, le_rfl⟩
  cases hc : Order.coheight x with
  | top => exact (hfin.ne hc).elim
  | coe n =>
      obtain ⟨c, hc_head, hc_len⟩ := Order.exists_series_of_coheight_eq_coe x hc
      have hc_last : c.last = z := by
        apply Subtype.ext
        apply le_antisymm
        · exact c.last.property
        · by_contra hle
          have hne' : c.last ≠ z := by
            intro heq
            apply hle
            simpa [heq]
          have hlt : c.last < z := lt_of_le_of_ne c.last.property hne'
          let d := c.snoc z hlt
          have hle := Order.length_le_coheight_head (p := d)
          rw [RelSeries.head_snoc, hc_head, hc] at hle
          have hcontra : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
            simpa [d, hc_len] using hle
          exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self n)) hcontra
      have hc_max :
          Formalization.Books.Topology.Unit11.IsMaximalChainBetween
            p q (le_of_lt hpq) c := by
        refine ⟨?_, hc_last, ?_⟩
        · simpa [x] using hc_head
        · intro d hd_head hd_last hcd
          have hle := Order.length_le_coheight_head (p := d)
          rw [hd_head, hc] at hle
          have hlen : d.length ≤ c.length := by
            exact_mod_cast (show (d.length : ℕ∞) ≤ (c.length : ℕ∞) by
              simpa [hc_len] using hle)
          exact range_subset_of_range_subset_of_length_le' hcd hlen
      exact ⟨c, hc_max, by simpa [hc] using hc_len⟩

private lemma isGlobalCatenary_iff_isIntervalCatenary
    {α : Type*} [PartialOrder α] :
    IsGlobalCatenary α ↔ IsIntervalCatenary α := by
  constructor
  · intro h p q hpq
    obtain ⟨n, hn, hmax⟩ := h hpq
    let x : Set.Iic q := ⟨p, le_of_lt hpq⟩
    let z : Set.Iic q := ⟨q, le_rfl⟩
    have hco : Order.coheight x ≤ (n : ℕ∞) := by
      apply Order.coheight_le_iff'.mpr
      intro c hc_head
      by_cases hc_last : c.last = z
      · have hhead : (forgetChain c).head = p := by
          change (c.head : α) = p
          simpa [x] using congrArg Subtype.val hc_head
        have hlast : (forgetChain c).last = q := by
          change (c.last : α) = q
          simpa [z] using congrArg Subtype.val hc_last
        have hg : IsGlobalChainBetween p q (forgetChain c) := ⟨hhead, hlast⟩
        have hlen := hn (forgetChain c) hg
        exact_mod_cast hlen
      · have hlt : c.last < z := lt_of_le_of_ne c.last.property hc_last
        let d := c.snoc z hlt
        have hd_head : d.head = x := by simpa [d, hc_head, x]
        have hd_last : d.last = z := by simp [d]
        have hhead' : (forgetChain d).head = p := by
          change (d.head : α) = p
          simpa [x] using congrArg Subtype.val hd_head
        have hlast' : (forgetChain d).last = q := by
          change (d.last : α) = q
          simpa [z] using congrArg Subtype.val hd_last
        have hg : IsGlobalChainBetween p q (forgetChain d) := ⟨hhead', hlast'⟩
        have hlen := hn (forgetChain d) hg
        have hlen' : c.length + 1 ≤ n := by
          change c.length + 1 ≤ n
          simpa [d, forgetChain] using hlen
        have hlen'' : c.length ≤ n := by omega
        exact_mod_cast hlen''
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_lt hco (WithTop.coe_lt_top n)
    · intro c hc
      obtain ⟨d, hd, hdl⟩ := exists_maximal_interval_chain hpq
        (lt_of_le_of_lt hco (WithTop.coe_lt_top n))
      have hc_global := (globalMax_forget_iff hpq ⟨hc.1, hc.2.1⟩).mpr hc
      have hd_global := (globalMax_forget_iff hpq ⟨hd.1, hd.2.1⟩).mpr hd
      have heq := hmax (forgetChain c) (forgetChain d) hc_global hd_global
      calc
        (c.length : ℕ∞) = (d.length : ℕ∞) := by exact_mod_cast heq
        _ = Order.coheight x := hdl
  · intro h p q hpq
    obtain ⟨hfin, hmax⟩ := h hpq
    cases hc : Order.coheight (⟨p, le_of_lt hpq⟩ : Set.Iic q) with
    | top => exact (hfin.ne hc).elim
    | coe n =>
        refine ⟨n, ?_, ?_⟩
        · intro c hc_global
          let d := liftChain c hc_global.1 hc_global.2
          have hd_headlast := liftChain_head_last hpq hc_global.1 hc_global.2
          have hle := Order.length_le_coheight_head (p := d)
          rw [hd_headlast.1, hc] at hle
          exact_mod_cast hle
        · intro c d hc hd
          let c' := liftChain c hc.1 hc.2.1
          let d' := liftChain d hd.1 hd.2.1
          have hc'headlast := liftChain_head_last hpq hc.1 hc.2.1
          have hd'headlast := liftChain_head_last hpq hd.1 hd.2.1
          have hc'max := (globalMax_forget_iff hpq hc'headlast).mp (by
            rw [forgetChain_liftChain hc.1 hc.2.1]
            exact hc)
          have hd'max := (globalMax_forget_iff hpq hd'headlast).mp (by
            rw [forgetChain_liftChain hd.1 hd.2.1]
            exact hd)
          have hc_len := hmax c' hc'max
          have hd_len := hmax d' hd'max
          exact_mod_cast (hc_len.trans hd_len.symm)

private lemma globalMax_map_forward
    {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    {p q : α} (c : LTSeries α) (hpq : p < q) :
    IsGlobalMaximalChainBetween p q c →
      IsGlobalMaximalChainBetween (e p) (e q) (c.map e e.strictMono) := by
  rintro ⟨hc_head, hc_last, hcmax⟩
  refine ⟨by simp [hc_head], by simp [hc_last], ?_⟩
  intro d hd_head hd_last hcd
  let d' := d.map e.symm e.symm.strictMono
  have hd'_head : d'.head = p := by
    simpa [d'] using congrArg e.symm hd_head
  have hd'_last : d'.last = q := by
    simpa [d'] using congrArg e.symm hd_last
  have hcd' : Set.range c ⊆ Set.range d' := by
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hcd ⟨i, rfl⟩
    refine ⟨j, ?_⟩
    simpa [d'] using congrArg e.symm hj
  have hdc' := hcmax d' hd'_head hd'_last hcd'
  intro y hy
  obtain ⟨i, rfl⟩ := hy
  obtain ⟨j, hj⟩ := hdc' ⟨i, rfl⟩
  refine ⟨j, ?_⟩
  simpa [d'] using congrArg e hj

private lemma globalMax_map_iff
    {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    {p q : α} (c : LTSeries α) (hpq : p < q) :
    IsGlobalMaximalChainBetween p q c ↔
      IsGlobalMaximalChainBetween (e p) (e q) (c.map e e.strictMono) := by
  constructor
  · exact globalMax_map_forward e c hpq
  · rintro ⟨hc_head, hc_last, hcmax⟩
    refine ⟨by simpa using congrArg e.symm hc_head,
      by simpa using congrArg e.symm hc_last, ?_⟩
    intro d hd_head hd_last hcd
    let d' := d.map e e.strictMono
    have hd'_head : d'.head = e p := by
      simpa [d'] using congrArg e hd_head
    have hd'_last : d'.last = e q := by
      simpa [d'] using congrArg e hd_last
    have hcd' : Set.range (c.map e e.strictMono) ⊆ Set.range d' := by
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, hj⟩ := hcd ⟨i, rfl⟩
      refine ⟨j, ?_⟩
      change e (d j) = e (c i)
      exact congrArg e hj
    have hdc' := hcmax d' hd'_head hd'_last hcd'
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨j, hj⟩ := hdc' ⟨i, rfl⟩
    refine ⟨j, ?_⟩
    apply e.injective
    change e (c j) = e (d i)
    change e (c j) = e (d i) at hj
    exact hj

private lemma isGlobalCatenary_of_orderIso
    {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    (h : IsGlobalCatenary α) : IsGlobalCatenary β := by
  intro p q hpq
  obtain ⟨n, hn, hmax⟩ := h (e.symm.lt_iff_lt.mpr hpq)
  refine ⟨n, ?_, ?_⟩
  · intro c hc
    let c' := c.map e.symm e.symm.strictMono
    have hc'_head : c'.head = e.symm p := by
      simpa [c'] using congrArg e.symm hc.1
    have hc'_last : c'.last = e.symm q := by
      simpa [c'] using congrArg e.symm hc.2
    simpa [c'] using hn c' ⟨hc'_head, hc'_last⟩
  · intro c d hc hd
    let c' := c.map e.symm e.symm.strictMono
    let d' := d.map e.symm e.symm.strictMono
    have hc'max := (globalMax_map_iff e.symm c hpq).mp hc
    have hd'max := (globalMax_map_iff e.symm d hpq).mp hd
    simpa [c', d'] using hmax c' d' hc'max hd'max

private def antiPullChain {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o βᵒᵈ) (c : LTSeries β) : LTSeries α :=
  { length := c.length
    toFun := fun i => e.symm (c i.rev)
    step := by
      intro i
      apply e.symm.strictMono
      apply c.strictMono
      exact Fin.rev_strictAnti Fin.castSucc_lt_succ
    }

private def antiPushChain {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o βᵒᵈ) (c : LTSeries α) : LTSeries β :=
  { length := c.length
    toFun := fun i => e (c i.rev)
    step := by
      intro i
      change (e (c (Fin.rev i.succ)) : βᵒᵈ) < e (c (Fin.rev i.castSucc))
      exact e.strictMono (c.strictMono (Fin.rev_strictAnti Fin.castSucc_lt_succ))
    }

private lemma antiPullChain_head {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o βᵒᵈ) (c : LTSeries β) :
    (antiPullChain e c).head = e.symm c.last := by
  unfold antiPullChain
  change e.symm (c (Fin.rev 0)) = e.symm c.last
  rw [Fin.rev_zero]
  exact congrArg e.symm c.apply_last

private lemma antiPullChain_last {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o βᵒᵈ) (c : LTSeries β) :
    (antiPullChain e c).last = e.symm c.head := by
  unfold antiPullChain
  change e.symm (c (Fin.rev (Fin.last c.length))) = e.symm c.head
  rw [Fin.rev_last]
  exact congrArg e.symm c.apply_zero

private lemma antiPushChain_head {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o βᵒᵈ) (c : LTSeries α) :
    (antiPushChain e c).head = e c.last := by
  unfold antiPushChain
  change e (c (Fin.rev 0)) = e c.last
  rw [Fin.rev_zero]
  exact congrArg e c.apply_last

private lemma antiPushChain_last {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o βᵒᵈ) (c : LTSeries α) :
    (antiPushChain e c).last = e c.head := by
  unfold antiPushChain
  change e (c (Fin.rev (Fin.last c.length))) = e c.head
  rw [Fin.rev_last]
  exact congrArg e c.apply_zero

private lemma globalMax_anti_pull_iff
    {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o βᵒᵈ)
    {p q : β} (c : LTSeries β) (hpq : p < q) :
    IsGlobalMaximalChainBetween p q c ↔
      IsGlobalMaximalChainBetween (e.symm q) (e.symm p) (antiPullChain e c) := by
  constructor
  · rintro ⟨hc_head, hc_last, hcmax⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [antiPullChain_head] using congrArg e.symm hc_last
    · simpa [antiPullChain_last] using congrArg e.symm hc_head
    · intro d hd_head hd_last hcd
      let d' := antiPushChain e d
      have hd'_head : d'.head = p := by
        rw [show d'.head = e d.last by
          change (antiPushChain e d).head = e d.last
          exact antiPushChain_head e d]
        rw [hd_last]
        change (e (e.symm p) : βᵒᵈ) = p
        exact e.apply_symm_apply p
      have hd'_last : d'.last = q := by
        rw [show d'.last = e d.head by
          change (antiPushChain e d).last = e d.head
          exact antiPushChain_last e d]
        rw [hd_head]
        change (e (e.symm q) : βᵒᵈ) = q
        exact e.apply_symm_apply q
      have hcd' : Set.range c ⊆ Set.range d' := by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hcd ⟨i.rev, rfl⟩
        · refine ⟨j.rev, ?_⟩
          change e (d (Fin.rev j.rev)) = c i
          rw [Fin.rev_rev]
          change (e (d j) : βᵒᵈ) = (c i : βᵒᵈ)
          unfold antiPullChain at hj
          change d j = e.symm (c (Fin.rev i.rev)) at hj
          rw [Fin.rev_rev] at hj
          have hj' := congrArg e hj
          change (e (d j) : βᵒᵈ) = e (e.symm (c i : βᵒᵈ)) at hj'
          have hcancel : e (e.symm (c i : βᵒᵈ)) = (c i : βᵒᵈ) :=
            e.apply_symm_apply _
          exact hj'.trans hcancel
      have hdc' := hcmax d' hd'_head hd'_last hcd'
      intro y hy
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨j, hj⟩ := hdc' ⟨i.rev, rfl⟩
      refine ⟨j.rev, ?_⟩
      have hj' : (c j : βᵒᵈ) = (d' i.rev : βᵒᵈ) := by simpa using hj
      unfold antiPullChain
      change e.symm (c (Fin.rev j.rev)) = d i
      rw [Fin.rev_rev]
      simpa [d', antiPushChain, antiPullChain, Fin.rev_rev] using congrArg e.symm hj'
  · rintro ⟨hc_head, hc_last, hcmax⟩
    refine ⟨?_, ?_, ?_⟩
    · apply e.symm.injective
      simpa [antiPullChain_last] using hc_last
    · apply e.symm.injective
      simpa [antiPullChain_head] using hc_head
    · intro d hd_head hd_last hcd
      let d' := antiPullChain e d
      have hd'_head : d'.head = e.symm q := by
        calc
          d'.head = e.symm d.last := by simpa [d', antiPullChain_head]
          _ = e.symm q := congrArg e.symm hd_last
      have hd'_last : d'.last = e.symm p := by
        calc
          d'.last = e.symm d.head := by simpa [d', antiPullChain_last]
          _ = e.symm p := congrArg e.symm hd_head
      have hcd' : Set.range (antiPullChain e c) ⊆ Set.range d' := by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hcd ⟨i.rev, rfl⟩
        · refine ⟨j.rev, ?_⟩
          simpa [d', antiPullChain, Fin.rev_rev] using congrArg e.symm hj
      have hdc' := hcmax d' hd'_head hd'_last hcd'
      intro y hy
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨j, hj⟩ := hdc' ⟨i.rev, rfl⟩
      let j' : Fin (c.length + 1) := Fin.cast (by simp [antiPullChain]) j
      refine ⟨j'.rev, ?_⟩
      apply e.symm.injective
      have hh : e.symm (c j'.rev) = e.symm (d i) := by
        simpa [d', antiPullChain, Fin.rev_rev, j', Fin.cast_rev, Function.id_def] using hj
      exact hh

private lemma isGlobalCatenary_of_orderAntiIso
    {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o βᵒᵈ)
    (h : IsGlobalCatenary α) : IsGlobalCatenary β := by
  intro p q hpq
  have hpq' : e.symm (q : βᵒᵈ) < e.symm (p : βᵒᵈ) :=
    e.symm.strictMono hpq
  obtain ⟨n, hn, hmax⟩ := h hpq'
  refine ⟨n, ?_, ?_⟩
  · intro c hc
    let c' := antiPullChain e c
    have hc_head : c'.head = e.symm (q : βᵒᵈ) := by
      simpa [c', antiPullChain_head] using congrArg e.symm hc.2
    have hc_last : c'.last = e.symm (p : βᵒᵈ) := by
      simpa [c', antiPullChain_last] using congrArg e.symm hc.1
    have hlen := hn c' ⟨hc_head, hc_last⟩
    simpa [c', antiPullChain] using hlen
  · intro c d hc hd
    let c' := antiPullChain e c
    let d' := antiPullChain e d
    have hc'max := (globalMax_anti_pull_iff e c hpq).mp hc
    have hd'max := (globalMax_anti_pull_iff e d hpq).mp hd
    have heq := hmax c' d' hc'max hd'max
    simpa [c', d', antiPullChain] using heq

/- The direct comparison with the topological catenary predicate on `Spec R`. -/
theorem isCatenaryRing_iff_isCatenary_primeSpectrum
    (R : Type u) [CommRing R] :
    IsCatenaryRing R ↔
      Formalization.Books.Topology.Unit11.IsCatenary (PrimeSpectrum R) := by
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds R
  constructor
  · intro hR
    have hglobal : IsGlobalCatenary (PrimeSpectrum R) :=
      (isGlobalCatenary_iff_isCatenaryRing R).mpr hR
    have hclosed : IsGlobalCatenary
        (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) :=
      isGlobalCatenary_of_orderAntiIso e hglobal
    have hinterval := (isGlobalCatenary_iff_isIntervalCatenary).mp hclosed
    simpa [IsIntervalCatenary,
      Formalization.Books.Topology.Unit11.IsCatenary,
      Formalization.Books.Topology.Unit11.relativeCodimension] using hinterval
  · intro htop
    have hinterval : IsIntervalCatenary
        (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) := by
      simpa [IsIntervalCatenary,
        Formalization.Books.Topology.Unit11.IsCatenary,
        Formalization.Books.Topology.Unit11.relativeCodimension] using htop
    have hclosed : IsGlobalCatenary
        (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) :=
      (isGlobalCatenary_iff_isIntervalCatenary).mpr hinterval
    let e' : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) ≃o
        (PrimeSpectrum R)ᵒᵈ :=
      (e.dual.trans (OrderIso.dualDual
        (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))).symm).symm
    have hglobal : IsGlobalCatenary (PrimeSpectrum R) :=
      isGlobalCatenary_of_orderAntiIso e' hclosed
    exact (isGlobalCatenary_iff_isCatenaryRing R).mp hglobal

private def forgetSubtype {α : Type*} [Preorder α] {P : Set α}
    (c : LTSeries P) : LTSeries α :=
  { length := c.length
    toFun := fun i => (c i : α)
    step := fun i => c.strictMono (by
      change i.val < i.val + 1
      omega) }

private def liftChain_lower {α : Type*} [Preorder α] {P : Set α}
    (hP : ∀ ⦃p q : α⦄, q ∈ P → p ≤ q → p ∈ P)
    {p q : α} (hq : q ∈ P) (c : LTSeries α)
    (hhead : c.head = p) (hlast : c.last = q) : LTSeries P :=
  { length := c.length
    toFun := fun i => ⟨c i, by
      apply hP hq
      rw [← hlast]
      exact c.monotone (Fin.le_last i)⟩
    step := fun i => by
      apply c.strictMono
      change i.val < i.val + 1
      omega }

private lemma isGlobalCatenary_of_lowerSet
    {α : Type*} [PartialOrder α] (P : Set α)
    (hP : ∀ ⦃p q : α⦄, q ∈ P → p ≤ q → p ∈ P)
    (h : IsGlobalCatenary α) : IsGlobalCatenary P := by
  intro p q hpq
  obtain ⟨n, hn, hmax⟩ := h (show (p : α) < q from hpq)
  refine ⟨n, ?_, ?_⟩
  · intro c hc
    have hc' : IsGlobalChainBetween (p : α) q (forgetSubtype c) :=
      ⟨congrArg Subtype.val hc.1, congrArg Subtype.val hc.2⟩
    exact hn _ hc'
  · intro c d hc hd
    have hc_global : IsGlobalMaximalChainBetween (p : α) q (forgetSubtype c) := by
      refine ⟨congrArg Subtype.val hc.1, congrArg Subtype.val hc.2.1, ?_⟩
      intro e he_head he_last hce
      let e' := liftChain_lower hP (show (q : α) ∈ P from q.property)
        e he_head he_last
      have he'_head : e'.head = p := by
        change ⟨e.head, ?_⟩ = p
        apply Subtype.ext
        exact he_head
      have he'_last : e'.last = q := by
        change ⟨e.last, ?_⟩ = q
        apply Subtype.ext
        exact he_last
      have hce' : Set.range c ⊆ Set.range e' := by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hce ⟨i, rfl⟩
        refine ⟨j, ?_⟩
        apply Subtype.ext
        exact hj
      have hsub := hc.2.2 e' he'_head he'_last hce'
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
      refine ⟨j, ?_⟩
      exact congrArg Subtype.val hj
    have hd_global : IsGlobalMaximalChainBetween (p : α) q (forgetSubtype d) := by
      refine ⟨congrArg Subtype.val hd.1, congrArg Subtype.val hd.2.1, ?_⟩
      intro e he_head he_last hde
      let e' := liftChain_lower hP (show (q : α) ∈ P from q.property)
        e he_head he_last
      have he'_head : e'.head = p := by
        change ⟨e.head, ?_⟩ = p
        apply Subtype.ext
        exact he_head
      have he'_last : e'.last = q := by
        change ⟨e.last, ?_⟩ = q
        apply Subtype.ext
        exact he_last
      have hde' : Set.range d ⊆ Set.range e' := by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hde ⟨i, rfl⟩
        refine ⟨j, ?_⟩
        apply Subtype.ext
        exact hj
      have hsub := hd.2.2 e' he'_head he'_last hde'
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
      refine ⟨j, ?_⟩
      exact congrArg Subtype.val hj
    exact hmax _ _ hc_global hd_global

/-! ## Universal catenarity -/

/- An algebra of finite type is represented by the canonical algebra class. -/
def IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
      IsCatenaryRing S

/- The source warns that catenarity is not preserved by arbitrary finite-type
   algebras over a catenary ring.  Since the warning supplies no quantified
   counterexample, it is retained here as documentation rather than promoted
   to an unsupported standalone existence theorem. -/

/- The polynomial-algebra test stated immediately after the definition. -/
theorem isUniversallyCatenary_iff_mPolynomial
    (R : Type u) [CommRing R] :
    IsUniversallyCatenary R ↔
        IsNoetherianRing R ∧
        ∀ n : ℕ, IsCatenaryRing (MvPolynomial (Fin n) R) := by
  sorry

/-! ## Localization, essential finite type, and local checking -/

theorem isCatenaryRing_localization
    (R : Type u) [CommRing R] (S : Submonoid R)
    (hR : IsCatenaryRing R) :
    IsCatenaryRing (Localization S) := by
  let e := IsLocalization.primeSpectrumOrderIso S (Localization S)
  have hlower : ∀ ⦃p q : PrimeSpectrum R⦄,
      Disjoint (S : Set R) q.asIdeal → p ≤ q →
        Disjoint (S : Set R) p.asIdeal := by
    intro p q hq hpq
    rw [Set.disjoint_left] at hq ⊢
    intro x hxS hxp
    exact hq hxS (hpq hxp)
  have hglobalR : IsGlobalCatenary (PrimeSpectrum R) :=
    (isGlobalCatenary_iff_isCatenaryRing R).mpr hR
  have hglobalSub : IsGlobalCatenary
      {p : PrimeSpectrum R // Disjoint (S : Set R) p.asIdeal} :=
    isGlobalCatenary_of_lowerSet _ hlower hglobalR
  have hglobalLoc : IsGlobalCatenary (PrimeSpectrum (Localization S)) :=
    isGlobalCatenary_of_orderIso e.symm hglobalSub
  exact (isGlobalCatenary_iff_isCatenaryRing _).mp hglobalLoc

theorem isUniversallyCatenary_localization
    (R : Type u) [CommRing R] (S : Submonoid R)
    (hR : IsUniversallyCatenary R) :
    IsUniversallyCatenary (Localization S) := by
  sorry

theorem isUniversallyCatenary_of_essFiniteType
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (hA : IsUniversallyCatenary A)
    (hB : Algebra.EssFiniteType A B) :
    IsUniversallyCatenary B := by
  sorry

theorem isCatenaryRing_localization_iff
    (R : Type u) [CommRing R] :
    List.TFAE
      [ IsCatenaryRing R
      , ∀ p : PrimeSpectrum R,
          IsCatenaryRing (Localization.AtPrime p.asIdeal)
      , ∀ m : MaximalSpectrum R,
          IsCatenaryRing (Localization.AtPrime m.asIdeal) ] := by
  sorry

theorem isUniversallyCatenary_localization_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    List.TFAE
      [ IsUniversallyCatenary R
      , ∀ p : PrimeSpectrum R,
          IsUniversallyCatenary (Localization.AtPrime p.asIdeal)
      , ∀ m : MaximalSpectrum R,
          IsUniversallyCatenary (Localization.AtPrime m.asIdeal) ] := by
  sorry

/-! ## Quotients and minimal components -/

theorem isCatenaryRing_quotient
    (R : Type u) [CommRing R] (I : Ideal R)
    (hR : IsCatenaryRing R) :
    IsCatenaryRing (R ⧸ I) := by
  sorry

theorem isUniversallyCatenary_quotient
    (R : Type u) [CommRing R] (I : Ideal R)
    (hR : IsUniversallyCatenary R) :
    IsUniversallyCatenary (R ⧸ I) := by
  sorry

theorem isCatenaryRing_iff_quotient_minimalPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsCatenaryRing R ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
        IsCatenaryRing (R ⧸ p.asIdeal) := by
  sorry

theorem isUniversallyCatenary_iff_quotient_minimalPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsUniversallyCatenary R ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
        IsUniversallyCatenary (R ⧸ p.asIdeal) := by
  sorry

/-! ## Cohen--Macaulay rings and modules -/

theorem isUniversallyCatenary_of_isCohenMacaulayRing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing R) :
    IsUniversallyCatenary R := by
  sorry

theorem isUniversallyCatenary_of_isCohenMacaulayModule
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Formalization.Books.Algebra.Unit103.IsCohenMacaulayModule R M)
    (hsupp : Module.support R M = Set.univ) :
    IsUniversallyCatenary R := by
  sorry

/-! ## Dimension functions on a Noetherian local ring -/

/-
The topological dimension function has integer values, whereas Mathlib's
Krull dimension has values in `WithBot ℕ∞`.  This predicate records the source
map `p ↦ dim(A / p)` by requiring a nonnegative integer-valued function whose
canonical `toNat` value is that quotient dimension.
-/
def IsPrimeQuotientDimensionFunction
    (A : Type u) [CommRing A]
    (δ : PrimeSpectrum A → ℤ) : Prop :=
  Formalization.Books.Topology.Unit20.IsDimensionFunction δ ∧
    ∀ p : PrimeSpectrum A,
      0 ≤ δ p ∧
        (((δ p).toNat : ℕ∞) : WithBot ℕ∞) =
          ringKrullDim (A ⧸ p.asIdeal)

theorem isCatenaryRing_iff_primeQuotientDimensionFunction
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    IsCatenaryRing A ↔
      ∃ δ : PrimeSpectrum A → ℤ,
        IsPrimeQuotientDimensionFunction A δ := by
  sorry

end

end Formalization.Books.Algebra.Unit105
