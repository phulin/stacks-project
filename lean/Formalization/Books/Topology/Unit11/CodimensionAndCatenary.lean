import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
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

/- The source's definition of a catenary space. -/
def IsCatenary (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ ⦃T T' : IrreducibleCloseds X⦄ (hTT' : T < T'),
    relativeCodimension (le_of_lt hTT') < ⊤ ∧
      ∀ p : LTSeries (Set.Iic T'),
        IsMaximalChainBetween T T' (le_of_lt hTT') p →
          p.length = relativeCodimension (le_of_lt hTT')

theorem isCatenary_iff_openCover :
    IsCatenary X ↔
      ∃ (ι : Type v) (U : ι → Opens X),
        TopologicalSpace.IsOpenCover U ∧ ∀ i, IsCatenary (U i) := by
  sorry

theorem isCatenary_subtype_of_isLocallyClosed
    (hX : IsCatenary X) {Y : Set X} (hY : IsLocallyClosed Y) :
    IsCatenary Y := by
  sorry

theorem isCatenary_iff_finite_and_additive_relativeCodimension :
    IsCatenary X ↔
      (∀ ⦃Y Y' : IrreducibleCloseds X⦄ (hYY' : Y < Y'),
        relativeCodimension (le_of_lt hYY') < ⊤) ∧
        (∀ ⦃Y Y' Y'' : IrreducibleCloseds X⦄
          (hYY' : Y < Y') (hY'Y'' : Y' < Y''),
          relativeCodimension (le_of_lt (lt_trans hYY' hY'Y'')) =
              relativeCodimension (le_of_lt hYY') +
              relativeCodimension (le_of_lt hY'Y'')) := by
  sorry

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
