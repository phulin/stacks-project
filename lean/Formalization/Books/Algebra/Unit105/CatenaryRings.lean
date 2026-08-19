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
    ∀ ⦃p q : α⦄ (_hpq : p < q),
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
    {p q : α} (c : LTSeries α) (_hhead : c.head = p) (hlast : c.last = q) :
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
            simp [heq]
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
        have hd_head : d.head = x := by simp [d, hc_head, x]
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
    {p q : α} (c : LTSeries α) (_hpq : p < q) :
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
    {p q : β} (c : LTSeries β) (_hpq : p < q) :
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
          unfold antiPullChain at hj
          change d j = e.symm (c (Fin.rev i.rev)) at hj
          rw [Fin.rev_rev] at hj
          have hj' := congrArg e hj
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
          d'.head = e.symm d.last := by simp [d', antiPullChain_head]
          _ = e.symm q := congrArg e.symm hd_last
      have hd'_last : d'.last = e.symm p := by
        calc
          d'.last = e.symm d.head := by simp [d', antiPullChain_last]
          _ = e.symm p := congrArg e.symm hd_head
      have hcd' : Set.range (antiPullChain e c) ⊆ Set.range d' := by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hcd ⟨i.rev, rfl⟩
        · refine ⟨j.rev, ?_⟩
          change e.symm (d (Fin.rev j.rev)) = e.symm (c i.rev)
          rw [Fin.rev_rev]
          exact congrArg e.symm hj
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
    (_hhead : c.head = p) (hlast : c.last = q) : LTSeries P :=
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

private def liftChain_upper {α : Type*} [Preorder α] {P : Set α}
    (hP : ∀ ⦃p q : α⦄, p ∈ P → p ≤ q → q ∈ P)
    {p q : α} (hp : p ∈ P) (c : LTSeries α)
    (_hhead : c.head = p) (hlast : c.last = q) : LTSeries P :=
  { length := c.length
    toFun := fun i => ⟨c i, by
      apply hP hp
      rw [← _hhead]
      exact c.monotone (Fin.zero_le i)⟩
    step := fun i => by
      apply c.strictMono
      change i.val < i.val + 1
      omega }

private lemma isGlobalCatenary_of_upperSet
    {α : Type*} [PartialOrder α] (P : Set α)
    (hP : ∀ ⦃p q : α⦄, p ∈ P → p ≤ q → q ∈ P)
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
      let e' := liftChain_upper hP (show (p : α) ∈ P from p.property)
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
      let e' := liftChain_upper hP (show (p : α) ∈ P from p.property)
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

private lemma isGlobalCatenary_of_upperSet_at
    {α : Type*} [PartialOrder α] (P : Set α)
    (hP : ∀ ⦃p q : α⦄, p ∈ P → p ≤ q → q ∈ P)
    {p q : α} (hp : p ∈ P) (hpq : p < q)
    (h : IsGlobalCatenary P) :
    ∃ n : ℕ,
      (∀ c : LTSeries α,
        IsGlobalChainBetween p q c → c.length ≤ n) ∧
        ∀ c d : LTSeries α,
          IsGlobalMaximalChainBetween p q c →
          IsGlobalMaximalChainBetween p q d → c.length = d.length := by
  let p' : P := ⟨p, hp⟩
  let q' : P := ⟨q, hP hp (le_of_lt hpq)⟩
  obtain ⟨n, hn, hmax⟩ := h (show p' < q' from hpq)
  refine ⟨n, ?_, ?_⟩
  · intro c hc
    let c' := liftChain_upper hP hp c hc.1 hc.2
    have hc'_head : c'.head = p' := by
      apply Subtype.ext
      exact hc.1
    have hc'_last : c'.last = q' := by
      apply Subtype.ext
      exact hc.2
    exact hn c' ⟨hc'_head, hc'_last⟩
  · intro c d hc hd
    let c' := liftChain_upper hP hp c hc.1 hc.2.1
    let d' := liftChain_upper hP hp d hd.1 hd.2.1
    have hc'_max : IsGlobalMaximalChainBetween p' q' c' := by
      refine ⟨?_, ?_, ?_⟩
      · apply Subtype.ext
        exact hc.1
      · apply Subtype.ext
        exact hc.2.1
      · intro e he_head he_last hce
        let e' := forgetSubtype e
        have he'_head : e'.head = p := by
          change (e.head : α) = p
          exact congrArg Subtype.val he_head
        have he'_last : e'.last = q := by
          change (e.last : α) = q
          exact congrArg Subtype.val he_last
        have hce' : Set.range c ⊆ Set.range e' := by
          intro x hx
          obtain ⟨i, rfl⟩ := hx
          obtain ⟨j, hj⟩ := hce ⟨i, rfl⟩
          refine ⟨j, ?_⟩
          exact congrArg Subtype.val hj
        have hsub := hc.2.2 e' he'_head he'_last hce'
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
        refine ⟨j, ?_⟩
        apply Subtype.ext
        simpa [c', liftChain_upper, e', forgetSubtype] using hj
    have hd'_max : IsGlobalMaximalChainBetween p' q' d' := by
      refine ⟨?_, ?_, ?_⟩
      · apply Subtype.ext
        exact hd.1
      · apply Subtype.ext
        exact hd.2.1
      · intro e he_head he_last hde
        let e' := forgetSubtype e
        have he'_head : e'.head = p := by
          change (e.head : α) = p
          exact congrArg Subtype.val he_head
        have he'_last : e'.last = q := by
          change (e.last : α) = q
          exact congrArg Subtype.val he_last
        have hde' : Set.range d ⊆ Set.range e' := by
          intro x hx
          obtain ⟨i, rfl⟩ := hx
          obtain ⟨j, hj⟩ := hde ⟨i, rfl⟩
          refine ⟨j, ?_⟩
          exact congrArg Subtype.val hj
        have hsub := hd.2.2 e' he'_head he'_last hde'
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
        refine ⟨j, ?_⟩
        apply Subtype.ext
        simpa [d', liftChain_upper, e', forgetSubtype] using hj
    simpa [c', d', liftChain_upper] using hmax c' d' hc'_max hd'_max

private lemma isCatenaryRing_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hR : IsCatenaryRing R) : IsCatenaryRing S := by
  let e := Ideal.primeSpectrumOrderIsoZeroLocusOfSurj f hf
    (I := RingHom.ker f) rfl
  have hglobalR : IsGlobalCatenary (PrimeSpectrum R) :=
    (isGlobalCatenary_iff_isCatenaryRing R).mpr hR
  have hglobalZ : IsGlobalCatenary (PrimeSpectrum.zeroLocus (R := R) (RingHom.ker f)) :=
    isGlobalCatenary_of_upperSet (PrimeSpectrum.zeroLocus (R := R) (RingHom.ker f))
      (fun {p q} hp hpq => by
        rw [PrimeSpectrum.mem_zeroLocus] at hp ⊢
        exact hp.trans hpq) hglobalR
  have hglobalS : IsGlobalCatenary (PrimeSpectrum S) :=
    isGlobalCatenary_of_orderIso e.symm hglobalZ
  exact (isGlobalCatenary_iff_isCatenaryRing S).mp hglobalS

/-! ## Universal catenarity -/

/- An algebra of finite type is represented by the canonical algebra class. -/
def IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
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

private lemma isCatenaryRing_of_finiteType
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    [Algebra A T] [Algebra.FiniteType A T]
    (hA : IsUniversallyCatenary A) : IsCatenaryRing T := by
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
      (inferInstance : Algebra.FiniteType A T)
  have hpoly : IsCatenaryRing (MvPolynomial (Fin n) A) :=
    ((isUniversallyCatenary_iff_mPolynomial A).mp hA).2 n
  exact isCatenaryRing_of_surjective f.toRingHom hf hpoly

private def liftChain_iic {α : Type*} [Preorder α] {q m : α}
    (hqm : q ≤ m) (c : LTSeries (Set.Iic q)) : LTSeries (Set.Iic m) :=
  { length := c.length
    toFun := fun i => ⟨(c i : α), (c i).property.trans hqm⟩
    step := fun i => by
      apply c.strictMono
      change i.val < i.val + 1
      omega }

private def restrictChain_iic {α : Type*} [Preorder α] {q m : α}
    (hqm : q ≤ m) (c : LTSeries (Set.Iic m)) (hlast : c.last = ⟨q, hqm⟩) :
    LTSeries (Set.Iic q) :=
  { length := c.length
    toFun := fun i => ⟨(c i : α), by
      change (c i : α) ≤ q
      have hi : (c i : α) ≤ (c.last : α) := c.monotone (Fin.le_last i)
      have hlast' := congrArg Subtype.val hlast
      rw [hlast'] at hi
      exact hi⟩
    step := fun i => by
      apply c.strictMono
      change i.val < i.val + 1
      omega }

private lemma isCatenaryRing_of_globalCatenary_iic
    {R : Type u} [CommRing R] {p q m : PrimeSpectrum R}
    (h : IsGlobalCatenary (Set.Iic m)) (hpq : p < q) (hqm : q ≤ m) :
    ∃ n : ℕ,
      (∀ c : LTSeries (Set.Iic q),
        IsPrimeChainBetween p q (le_of_lt hpq) c → c.length ≤ n) ∧
        ∀ c d : LTSeries (Set.Iic q),
          Formalization.Books.Topology.Unit11.IsMaximalChainBetween
            p q (le_of_lt hpq) c →
          Formalization.Books.Topology.Unit11.IsMaximalChainBetween
            p q (le_of_lt hpq) d → c.length = d.length := by
  let p' : Set.Iic m := ⟨p, (le_of_lt hpq).trans hqm⟩
  let q' : Set.Iic m := ⟨q, hqm⟩
  have hpq' : p' < q' := hpq
  obtain ⟨n, hn, hmax⟩ := h hpq'
  refine ⟨n, ?_, ?_⟩
  · intro c hc
    let c' := liftChain_iic hqm c
    have hc_head : c'.head = p' := by
      apply Subtype.ext
      change (c.head : PrimeSpectrum R) = p
      exact congrArg Subtype.val hc.1
    have hc_last : c'.last = q' := by
      apply Subtype.ext
      change (c.last : PrimeSpectrum R) = q
      exact congrArg Subtype.val hc.2
    exact hn c' ⟨hc_head, hc_last⟩
  · intro c d hc hd
    let c' := liftChain_iic hqm c
    let d' := liftChain_iic hqm d
    have hc'_head : c'.head = p' := by
      apply Subtype.ext
      change (c.head : PrimeSpectrum R) = p
      exact congrArg Subtype.val hc.1
    have hc'_last : c'.last = q' := by
      apply Subtype.ext
      change (c.last : PrimeSpectrum R) = q
      exact congrArg Subtype.val hc.2.1
    have hd'_head : d'.head = p' := by
      apply Subtype.ext
      change (d.head : PrimeSpectrum R) = p
      exact congrArg Subtype.val hd.1
    have hd'_last : d'.last = q' := by
      apply Subtype.ext
      change (d.last : PrimeSpectrum R) = q
      exact congrArg Subtype.val hd.2.1
    have hc'_max : IsGlobalMaximalChainBetween p' q' c' := by
      refine ⟨hc'_head, hc'_last, ?_⟩
      intro e he_head he_last hce
      let e' := restrictChain_iic hqm e he_last
      have he'_head : e'.head = (⟨p, le_of_lt hpq⟩ : Set.Iic q) := by
        apply Subtype.ext
        change (e.head : PrimeSpectrum R) = p
        exact congrArg Subtype.val he_head
      have he'_last : e'.last = (⟨q, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic q) := by
        apply Subtype.ext
        change (e.last : PrimeSpectrum R) = q
        exact congrArg Subtype.val he_last
      have hce' : Set.range c ⊆ Set.range e' := by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hce ⟨i, rfl⟩
        refine ⟨j, ?_⟩
        apply Subtype.ext
        simpa [e', restrictChain_iic, c', liftChain_iic] using
          congrArg Subtype.val hj
      have hsub := hc.2.2 e' he'_head he'_last hce'
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
      refine ⟨j, ?_⟩
      apply Subtype.ext
      simpa [e', restrictChain_iic, c', liftChain_iic] using
        congrArg Subtype.val hj
    have hd'_max : IsGlobalMaximalChainBetween p' q' d' := by
      refine ⟨hd'_head, hd'_last, ?_⟩
      intro e he_head he_last hde
      let e' := restrictChain_iic hqm e he_last
      have he'_head : e'.head = (⟨p, le_of_lt hpq⟩ : Set.Iic q) := by
        apply Subtype.ext
        change (e.head : PrimeSpectrum R) = p
        exact congrArg Subtype.val he_head
      have he'_last : e'.last = (⟨q, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic q) := by
        apply Subtype.ext
        change (e.last : PrimeSpectrum R) = q
        exact congrArg Subtype.val he_last
      have hde' : Set.range d ⊆ Set.range e' := by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hde ⟨i, rfl⟩
        refine ⟨j, ?_⟩
        apply Subtype.ext
        simpa [e', restrictChain_iic, d', liftChain_iic] using
          congrArg Subtype.val hj
      have hsub := hd.2.2 e' he'_head he'_last hde'
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
      refine ⟨j, ?_⟩
      apply Subtype.ext
      simpa [e', restrictChain_iic, d', liftChain_iic] using
        congrArg Subtype.val hj
    exact hmax c' d' hc'_max hd'_max

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
  rw [IsUniversallyCatenary] at hR ⊢
  refine ⟨IsLocalization.isNoetherianRing S (Localization S) hR.1, ?_⟩
  intro T _ _ _
  let _ : Algebra R T :=
    ((algebraMap (Localization S) T).comp (algebraMap R (Localization S))).toAlgebra
  have hTower : IsScalarTower R (Localization S) T :=
    IsScalarTower.of_algebraMap_eq' (by
      change ((algebraMap (Localization S) T).comp (algebraMap R (Localization S))) =
        ((algebraMap (Localization S) T).comp (algebraMap R (Localization S)))
      rfl)
  have hEssLoc : Algebra.EssFiniteType R (Localization S) :=
    Algebra.EssFiniteType.of_isLocalization (R := R) (S := Localization S) S
  have hEssT : Algebra.EssFiniteType (Localization S) T :=
    Algebra.EssFiniteType.of_finiteType (R := Localization S) (S := T)
  have hEss : Algebra.EssFiniteType R T :=
    @Algebra.EssFiniteType.comp R (Localization S) T _ _ _ _ _ _ hTower hEssLoc hEssT
  rw [Algebra.essFiniteType_iff_exists_subalgebra] at hEss
  obtain ⟨T₀, M, hT₀, hloc⟩ := hEss
  let _ : Algebra.FiniteType R T₀ := hT₀
  have hcat₀ : IsCatenaryRing T₀ := hR.2 T₀
  have hcatloc : IsCatenaryRing (Localization M) :=
    isCatenaryRing_localization T₀ M hcat₀
  let _ : IsLocalization M T := hloc
  let e : Localization M ≃+* T :=
    (IsLocalization.algEquiv M (Localization M) T).toRingEquiv
  have hglobalLoc : IsGlobalCatenary (PrimeSpectrum (Localization M)) :=
    (isGlobalCatenary_iff_isCatenaryRing _).mpr hcatloc
  have hglobalT : IsGlobalCatenary (PrimeSpectrum T) :=
    isGlobalCatenary_of_orderIso (PrimeSpectrum.comapEquiv e) hglobalLoc
  exact (isGlobalCatenary_iff_isCatenaryRing _).mp hglobalT

theorem isUniversallyCatenary_of_essFiniteType
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] (hA : IsUniversallyCatenary A)
    (hB : Algebra.EssFiniteType A B) :
    IsUniversallyCatenary B := by
  rw [IsUniversallyCatenary]
  let _ : IsNoetherianRing A := hA.1
  have hB' := hB
  rw [Algebra.essFiniteType_iff_exists_subalgebra] at hB'
  obtain ⟨B₀, M, hB₀, hloc⟩ := hB'
  let _ : Algebra.FiniteType A B₀ := hB₀
  have hnoeth : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing A B₀
  let _ : IsNoetherianRing B₀ := hnoeth
  let _ : IsLocalization M B := hloc
  refine ⟨IsLocalization.isNoetherianRing M B hnoeth, ?_⟩
  intro T _ _ _
  let _ : Algebra A T :=
    ((algebraMap B T).comp (algebraMap A B)).toAlgebra
  have hTower : IsScalarTower A B T :=
    IsScalarTower.of_algebraMap_eq' (by
      change ((algebraMap B T).comp (algebraMap A B)) =
        ((algebraMap B T).comp (algebraMap A B))
      rfl)
  have hEssT : Algebra.EssFiniteType B T :=
    Algebra.EssFiniteType.of_finiteType (R := B) (S := T)
  have hEss : Algebra.EssFiniteType A T :=
    @Algebra.EssFiniteType.comp A B T _ _ _ _ _ _ hTower hB hEssT
  rw [Algebra.essFiniteType_iff_exists_subalgebra] at hEss
  obtain ⟨T₀, N, hT₀, hlocT⟩ := hEss
  let _ : Algebra.FiniteType A T₀ := hT₀
  have hcat₀ : IsCatenaryRing T₀ := isCatenaryRing_of_finiteType hA
  have hcatloc : IsCatenaryRing (Localization N) :=
    isCatenaryRing_localization T₀ N hcat₀
  let _ : IsLocalization N T := hlocT
  let e : Localization N ≃+* T :=
    (IsLocalization.algEquiv N (Localization N) T).toRingEquiv
  have hglobalLoc : IsGlobalCatenary (PrimeSpectrum (Localization N)) :=
    (isGlobalCatenary_iff_isCatenaryRing _).mpr hcatloc
  have hglobalT : IsGlobalCatenary (PrimeSpectrum T) :=
    isGlobalCatenary_of_orderIso (PrimeSpectrum.comapEquiv e) hglobalLoc
  exact (isGlobalCatenary_iff_isCatenaryRing _).mp hglobalT

theorem isCatenaryRing_localization_iff
    (R : Type u) [CommRing R] :
    List.TFAE
      [ IsCatenaryRing R
      , ∀ p : PrimeSpectrum R,
          IsCatenaryRing (Localization.AtPrime p.asIdeal)
      , ∀ m : MaximalSpectrum R,
          IsCatenaryRing (Localization.AtPrime m.asIdeal) ] := by
  tfae_have 1 → 2 := fun h p => by
    exact isCatenaryRing_localization R p.asIdeal.primeCompl h
  tfae_have 2 → 3 := fun h m => by
    exact h (MaximalSpectrum.toPrimeSpectrum m)
  tfae_have 3 → 1 := fun h => by
    intro p q hpq
    obtain ⟨J, hJ, hqJ⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
    let m : MaximalSpectrum R := ⟨J, hJ⟩
    have hglobalLoc :
        IsGlobalCatenary (PrimeSpectrum (Localization.AtPrime m.asIdeal)) :=
      (isGlobalCatenary_iff_isCatenaryRing _).mpr (h m)
    let e := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime m.asIdeal) m.asIdeal
    have hglobalIic : IsGlobalCatenary
        (Set.Iic (MaximalSpectrum.toPrimeSpectrum m)) :=
      isGlobalCatenary_of_orderIso e hglobalLoc
    exact isCatenaryRing_of_globalCatenary_iic hglobalIic hpq hqJ
  tfae_finish

theorem isUniversallyCatenary_localization_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    List.TFAE
      [ IsUniversallyCatenary R
      , ∀ p : PrimeSpectrum R,
          IsUniversallyCatenary (Localization.AtPrime p.asIdeal)
      , ∀ m : MaximalSpectrum R,
          IsUniversallyCatenary (Localization.AtPrime m.asIdeal) ] := by
  tfae_have 1 → 2 := fun h p => by
    exact isUniversallyCatenary_localization R p.asIdeal.primeCompl h
  tfae_have 2 → 3 := fun h m => by
    exact h (MaximalSpectrum.toPrimeSpectrum m)
  tfae_have 3 → 1 := fun h => by
    rw [IsUniversallyCatenary]
    refine ⟨inferInstance, ?_⟩
    intro S _ _ _
    have hiff := (isCatenaryRing_localization_iff S).out 0 2
      (a := IsCatenaryRing S)
      (b := ∀ m : MaximalSpectrum S,
        IsCatenaryRing (Localization.AtPrime m.asIdeal))
      (h₁ := rfl) (h₂ := rfl)
    apply hiff.mpr
    intro n
    let p : Ideal R := n.asIdeal.comap (algebraMap R S)
    let pSpec : PrimeSpectrum R := ⟨p, inferInstance⟩
    obtain ⟨J, hJ, hpJ⟩ := Ideal.exists_le_maximal p pSpec.2.ne_top
    let m : MaximalSpectrum R := ⟨J, hJ⟩
    have hmp : p ≤ m.asIdeal := hpJ
    have hMN : m.asIdeal.primeCompl ≤ p.primeCompl := by
      intro x hx hxp
      exact hx (hmp hxp)
    let _ : Algebra (Localization.AtPrime m.asIdeal)
        (Localization.AtPrime p) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe
        (Localization.AtPrime m.asIdeal) (Localization.AtPrime p)
        m.asIdeal.primeCompl p.primeCompl hMN
    let _ : IsScalarTower R (Localization.AtPrime m.asIdeal)
        (Localization.AtPrime p) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le
        (Localization.AtPrime m.asIdeal) (Localization.AtPrime p)
        m.asIdeal.primeCompl p.primeCompl hMN
    have hlocP : IsLocalization
        (p.primeCompl.map (algebraMap R (Localization.AtPrime m.asIdeal)))
        (Localization.AtPrime p) :=
      IsLocalization.isLocalization_of_submonoid_le
        (Localization.AtPrime m.asIdeal) (Localization.AtPrime p)
        m.asIdeal.primeCompl p.primeCompl hMN
    let _ : IsLocalization
        (p.primeCompl.map (algebraMap R (Localization.AtPrime m.asIdeal)))
        (Localization.AtPrime p) := hlocP
    have hEssP : Algebra.EssFiniteType (Localization.AtPrime m.asIdeal)
        (Localization.AtPrime p) :=
      Algebra.EssFiniteType.of_isLocalization
        (R := Localization.AtPrime m.asIdeal) (S := Localization.AtPrime p)
        (p.primeCompl.map (algebraMap R (Localization.AtPrime m.asIdeal)))
    have hUCp : IsUniversallyCatenary (Localization.AtPrime p) :=
      isUniversallyCatenary_of_essFiniteType _ _ (h m) hEssP
    let _ : n.asIdeal.LiesOver p := ⟨rfl⟩
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime n.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver p n.asIdeal
    have hEssSnR : Algebra.EssFiniteType R
        (Localization.AtPrime n.asIdeal) := inferInstance
    let _ : Algebra.EssFiniteType R
        (Localization.AtPrime n.asIdeal) := hEssSnR
    have hEssSnP : Algebra.EssFiniteType (Localization.AtPrime p)
        (Localization.AtPrime n.asIdeal) :=
      Algebra.EssFiniteType.of_comp R (Localization.AtPrime p)
        (Localization.AtPrime n.asIdeal)
    have hUCn : IsUniversallyCatenary (Localization.AtPrime n.asIdeal) :=
      isUniversallyCatenary_of_essFiniteType _ _ hUCp hEssSnP
    exact hUCn.2 (Localization.AtPrime n.asIdeal)
  tfae_finish

/-! ## Quotients and minimal components -/

theorem isCatenaryRing_quotient
    (R : Type u) [CommRing R] (I : Ideal R)
    (hR : IsCatenaryRing R) :
    IsCatenaryRing (R ⧸ I) := by
  exact isCatenaryRing_of_surjective (Ideal.Quotient.mk I) Quotient.mk_surjective hR

theorem isUniversallyCatenary_quotient
    (R : Type u) [CommRing R] (I : Ideal R)
    (hR : IsUniversallyCatenary R) :
    IsUniversallyCatenary (R ⧸ I) := by
  exact isUniversallyCatenary_of_essFiniteType R (R ⧸ I) hR inferInstance

theorem isCatenaryRing_iff_quotient_minimalPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsCatenaryRing R ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
        IsCatenaryRing (R ⧸ p.asIdeal) := by
  constructor
  · intro hR p hp
    exact isCatenaryRing_quotient R p.asIdeal hR
  · intro hR
    apply (isGlobalCatenary_iff_isCatenaryRing R).mp
    intro p q hpq
    obtain ⟨r, hr, hrp⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := p.asIdeal) bot_le
    let p' : PrimeSpectrum R := ⟨r, hr.1.1⟩
    let P : Set (PrimeSpectrum R) :=
      PrimeSpectrum.zeroLocus (R := R) r
    have hpP : p ∈ P := by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact hrp
    have hP : ∀ ⦃a b : PrimeSpectrum R⦄, a ∈ P → a ≤ b → b ∈ P := by
      intro a b ha hab
      rw [PrimeSpectrum.mem_zeroLocus] at ha ⊢
      exact ha.trans hab
    have hglobalP : IsGlobalCatenary P := by
      let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus r
      exact isGlobalCatenary_of_orderIso e
        ((isGlobalCatenary_iff_isCatenaryRing (R ⧸ r)).mpr
          (hR p' hr))
    exact isGlobalCatenary_of_upperSet_at P hP hpP hpq hglobalP

theorem isUniversallyCatenary_iff_quotient_minimalPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsUniversallyCatenary R ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
        IsUniversallyCatenary (R ⧸ p.asIdeal) := by
  constructor
  · intro hR p hp
    exact isUniversallyCatenary_quotient R p.asIdeal hR
  · intro hR
    rw [IsUniversallyCatenary]
    refine ⟨inferInstance, ?_⟩
    intro S _ _ _
    let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
    apply (isCatenaryRing_iff_quotient_minimalPrime S).mpr
    intro q hq
    let p : Ideal R := q.asIdeal.comap (algebraMap R S)
    obtain ⟨r, hr, hrp⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := p) bot_le
    let f : (R ⧸ r) →+* (R ⧸ p) := Ideal.Quotient.factor hrp
    let _ : Algebra (R ⧸ r) (R ⧸ p) := f.toAlgebra
    let _ : Algebra.FiniteType (R ⧸ r) (R ⧸ p) :=
      Algebra.FiniteType.of_surjective (Algebra.ofId (R ⧸ r) (R ⧸ p))
        (by
          intro x
          exact Ideal.Quotient.factor_surjective hrp x)
    have hUCp : IsUniversallyCatenary (R ⧸ p) :=
      isUniversallyCatenary_of_essFiniteType (R ⧸ r) (R ⧸ p)
        (hR ⟨r, hr.1.1⟩ hr) inferInstance
    let _ : Algebra (R ⧸ p) (S ⧸ q.asIdeal) :=
      Ideal.Quotient.algebraQuotientOfLEComap (p := p) (P := q.asIdeal) le_rfl
    let _ : IsScalarTower R (R ⧸ p) (S ⧸ q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' (by
        change (algebraMap (R ⧸ p) (S ⧸ q.asIdeal)).comp
            (algebraMap R (R ⧸ p)) = algebraMap R (S ⧸ q.asIdeal)
        rfl)
    let _ : Algebra.FiniteType R (S ⧸ q.asIdeal) := inferInstance
    let _ : Algebra.FiniteType (R ⧸ p) (S ⧸ q.asIdeal) :=
      Algebra.FiniteType.of_restrictScalars_finiteType
        (R := R) (S := R ⧸ p) (A := S ⧸ q.asIdeal)
    exact isCatenaryRing_of_finiteType hUCp

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
