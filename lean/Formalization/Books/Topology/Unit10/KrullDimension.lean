import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.WithTopology

/-!
# Topology, Chapter 10: Krull dimension

The source's chains of irreducible closed subsets are represented by
Mathlib's `IrreducibleCloseds` and `LTSeries` types.  The global dimension is
Mathlib's canonical `topologicalKrullDim`; the local dimension is the
infimum of the dimensions of the open neighbourhood subspaces.
-/

namespace Formalization.Books.Topology.Unit10

open Set Function _root_.Topology TopologicalSpace

universe u v

section KrullDimension

variable {X : Type u} [TopologicalSpace X]

/-! ### Chains and global dimension -/

theorem irreducibleClosedChain_term_isClosed_isIrreducible
    (C : LTSeries (IrreducibleCloseds X)) (i : Fin (C.length + 1)) :
    IsClosed (C i : Set X) ∧ IsIrreducible (C i : Set X) := by
  exact ⟨(C i).isClosed, (C i).isIrreducible⟩

theorem irreducibleClosedChain_adjacent_strict
    (C : LTSeries (IrreducibleCloseds X)) (i : Fin C.length) :
    C (Fin.castSucc i) < C i.succ := by
  exact C.step i

theorem krullDimension_eq_iSup_chainLength :
    topologicalKrullDim X =
      ⨆ C : LTSeries (IrreducibleCloseds X), (C.length : WithBot ℕ∞) := by
  rfl

theorem krullDimension_eq_bot_iff :
    topologicalKrullDim X = ⊥ ↔ IsEmpty X := by
  rw [topologicalKrullDim, Order.krullDim_eq_bot_iff]
  constructor
  · intro h
    refine ⟨?_⟩
    intro x
    exact h.false
      (⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds X)
  · intro h
    refine ⟨?_⟩
    intro C
    rcases C.isIrreducible.nonempty with ⟨x, hx⟩
    exact h.false x

/-! ### Dimension at a point -/

/-- The Krull dimension of `X` at `x`, as the infimum over open neighbourhoods. -/
noncomputable def krullDimensionAt (x : X) : WithBot ℕ∞ :=
  ⨅ U : OpenNhdsOf x, topologicalKrullDim (U : Set X)

theorem krullDimensionAt_le (x : X) {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    krullDimensionAt x ≤ topologicalKrullDim U := by
  change (⨅ V : OpenNhdsOf x, topologicalKrullDim (V : Set X)) ≤
    topologicalKrullDim U
  exact iInf_le (fun V : OpenNhdsOf x => topologicalKrullDim (V : Set X))
    (⟨⟨U, hU⟩, hx⟩ : OpenNhdsOf x)

theorem krullDimension_mono_of_open_subset
    {U' U : Set X} (hU' : IsOpen U') (hU : IsOpen U) (hsub : U' ⊆ U) :
    topologicalKrullDim U' ≤ topologicalKrullDim U := by
  let f : U' → U := fun x => ⟨x, hsub x.2⟩
  have hf : IsOpenEmbedding f := by
    apply IsOpenEmbedding.of_comp f hU.isOpenEmbedding_subtypeVal
    simpa [f, Function.comp_def] using hU'.isOpenEmbedding_subtypeVal
  exact hf.isInducing.topologicalKrullDim_le

theorem krullDimensionAt_isLeast (x : X) :
    IsLeast
      {d : WithBot ℕ∞ |
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ topologicalKrullDim U = d}
      (krullDimensionAt x) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU⟩ :=
      ciInf_mem (fun U : OpenNhdsOf x => topologicalKrullDim (U : Set X))
    exact ⟨U, U.isOpen, U.mem, hU⟩
  · intro d hd
    rcases hd with ⟨U, hU, hxU, hEq⟩
    rw [← hEq]
    exact krullDimensionAt_le x hU hxU

theorem krullDimensionAt_hasBasis (x : X) :
    (𝓝 x).HasBasis
      (fun U : Set X =>
        IsOpen U ∧ x ∈ U ∧ topologicalKrullDim U = krullDimensionAt x)
      (fun U => U) := by
  apply (OpenNhdsOf.basis_nhds (x := x)).to_hasBasis
  · intro V _
    obtain ⟨W, hWopen, hxW, hWdim⟩ := (krullDimensionAt_isLeast x).1
    refine ⟨W ∩ (V : Set X), ?_, inter_subset_right⟩
    refine ⟨hWopen.inter V.isOpen, ⟨hxW, V.mem⟩, ?_⟩
    apply le_antisymm
    · exact
        (krullDimension_mono_of_open_subset (hWopen.inter V.isOpen) hWopen
          inter_subset_left).trans_eq hWdim
    · exact krullDimensionAt_le x (hWopen.inter V.isOpen) ⟨hxW, V.mem⟩
  · intro U hU
    exact ⟨⟨⟨U, hU.1⟩, hU.2.1⟩, trivial, Subset.rfl⟩

/-! ### Local and global dimensions -/

theorem krullDimension_eq_iSup_krullDimensionAt :
    topologicalKrullDim X = ⨆ x : X, krullDimensionAt x := by
  apply le_antisymm
  · rw [krullDimension_eq_iSup_chainLength]
    refine iSup_le fun C => ?_
    obtain ⟨x, hx⟩ := C.head.isIrreducible.nonempty
    refine le_iSup_of_le x ?_
    rw [krullDimensionAt]
    refine le_iInf fun U => ?_
    let f : U → X := (↑)
    have hf : IsOpenEmbedding f := U.isOpen.isOpenEmbedding_subtypeVal
    let e : IrreducibleCloseds U ≃o
        {V : IrreducibleCloseds X | (f ⁻¹' V).Nonempty} :=
      TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf
    have hmeet (i : Fin (C.length + 1)) :
        (f ⁻¹' (C i : Set X)).Nonempty := by
      refine ⟨⟨x, U.mem⟩, ?_⟩
      change x ∈ (C i : Set X)
      exact C.head_le i hx
    let D : LTSeries (IrreducibleCloseds U) :=
      { length := C.length
        toFun := fun i => e.symm ⟨C i, hmeet i⟩
        step := fun i => e.symm.strictMono (by
          change C (Fin.castSucc i) < C i.succ
          exact C.step i) }
    simpa [topologicalKrullDim, D] using (Order.LTSeries.length_le_krullDim D)
  · refine iSup_le fun x => ?_
    exact (krullDimensionAt_le x isOpen_univ (mem_univ x)).trans
      (topologicalKrullDim_subspace_le X (Set.univ : Set X))

/-! ### Examples -/

/-- `Fin n → ℝ` is the usual coordinate model of Euclidean `n`-space. -/
theorem krullDimension_euclideanSpace (n : ℕ) :
    topologicalKrullDim (Fin n → ℝ) = 0 := by
  apply le_antisymm
  · rw [topologicalKrullDim]
    refine Order.krullDim_nonpos_iff_forall_isMax.mpr ?_
    intro C D hCD
    obtain ⟨x, hxC⟩ := isIrreducible_iff_singleton.mp C.isIrreducible
    obtain ⟨y, hyD⟩ := isIrreducible_iff_singleton.mp D.isIrreducible
    have hCD' : (C : Set (Fin n → ℝ)) ⊆ (D : Set (Fin n → ℝ)) := hCD
    rw [hxC, hyD] at hCD'
    have hxy : x = y := Set.singleton_subset_singleton.mp hCD'
    apply SetLike.coe_subset_coe.mp
    rw [hyD, hxC]
    simp [hxy]
  · rw [topologicalKrullDim]
    exact Order.krullDim_nonneg_iff.mpr
      ⟨⟨{(0 : Fin n → ℝ)}, isIrreducible_singleton, isClosed_singleton⟩⟩

/- The following topology has open sets `∅`, `{generic}`, and the whole
   space.  The constructors correspond to the source's `s` and `η`. -/
inductive KrullTwoPointSpace where
  | special
  | generic

def krullTwoPointOpenGenerators : Set (Set KrullTwoPointSpace) :=
  {({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace)}

@[instance_reducible]
def krullTwoPointTopology : TopologicalSpace KrullTwoPointSpace :=
  TopologicalSpace.generateFrom krullTwoPointOpenGenerators

instance krullTwoPointSpace_topologicalSpace :
    TopologicalSpace KrullTwoPointSpace :=
  krullTwoPointTopology

theorem krullTwoPointSpace_isOpen_iff {U : Set KrullTwoPointSpace} :
    IsOpen U ↔
      U = ∅ ∨ U = {KrullTwoPointSpace.generic} ∨ U = Set.univ := by
  constructor
  · intro h
    induction h with
    | basic s hs =>
        simp [krullTwoPointOpenGenerators] at hs
        exact Or.inr (Or.inl hs)
    | univ => exact Or.inr (Or.inr rfl)
    | inter s t hs ht ihs iht =>
        rcases ihs with rfl | rfl | rfl <;>
          rcases iht with rfl | rfl | rfl <;> simp
    | sUnion S hS ih =>
        by_cases hu : Set.univ ∈ S
        · exact Or.inr (Or.inr (by
            apply Set.Subset.antisymm
            · exact subset_univ _
            · exact subset_sUnion_of_mem hu))
        · by_cases hg : ({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace) ∈ S
          · apply Or.inr (Or.inl (by
              apply Set.Subset.antisymm
              · apply sUnion_subset
                intro s hs
                rcases ih s hs with hs0 | hs1 | hsu
                · rw [hs0]
                  exact empty_subset _
                · rw [hs1]
                · exact (hu (hsu ▸ hs)).elim
              · exact subset_sUnion_of_mem hg))
          · apply Or.inl (by
              rw [eq_empty_iff_forall_notMem]
              intro x hx
              rcases mem_sUnion.mp hx with ⟨s, hsS, hxs⟩
              rcases ih s hsS with hs0 | hs1 | hsu
              · simp [hs0] at hxs
              · exact hg (hs1 ▸ hsS)
              · exact hu (hsu ▸ hsS))
  · rintro (rfl | rfl | rfl)
    · exact isOpen_empty
    · exact isOpen_generateFrom_of_mem (by simp [krullTwoPointOpenGenerators])
    · exact isOpen_univ

theorem krullDimension_twoPointSpace_maximal_chain :
    ∃ C : LTSeries (IrreducibleCloseds KrullTwoPointSpace),
      C.length = 1 ∧
        (C.head : Set KrullTwoPointSpace) = {KrullTwoPointSpace.special} ∧
        (C.last : Set KrullTwoPointSpace) = Set.univ ∧
        (C.length : WithBot ℕ∞) = topologicalKrullDim KrullTwoPointSpace := by
  have hgenericOpen : IsOpen ({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace) :=
    krullTwoPointSpace_isOpen_iff.mpr (Or.inr (Or.inl rfl))
  have hspecialClosed : IsClosed ({KrullTwoPointSpace.special} : Set KrullTwoPointSpace) := by
    apply isOpen_compl_iff.mp
    rw [show ({KrullTwoPointSpace.special} : Set KrullTwoPointSpace)ᶜ =
        {KrullTwoPointSpace.generic} by
      ext z
      cases z <;> simp]
    exact hgenericOpen
  have hunivIrred : IsIrreducible (Set.univ : Set KrullTwoPointSpace) := by
    refine ⟨⟨KrullTwoPointSpace.special, Set.mem_univ _⟩, ?_⟩
    intro u v hu hv hu' hv'
    rw [krullTwoPointSpace_isOpen_iff] at hu hv
    rcases hu with hu | hu | hu <;>
      rcases hv with hv | hv | hv <;>
      rcases hu with rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl <;>
      simp_all
  let A : IrreducibleCloseds KrullTwoPointSpace :=
    ⟨{KrullTwoPointSpace.special}, isIrreducible_singleton, hspecialClosed⟩
  let B : IrreducibleCloseds KrullTwoPointSpace :=
    ⟨Set.univ, hunivIrred, isClosed_univ⟩
  let C : LTSeries (IrreducibleCloseds KrullTwoPointSpace) :=
    { length := 1
      toFun := ![A, B]
      step := by
        intro i
        fin_cases i
        change A < B
        apply SetLike.coe_ssubset_coe.mp
        refine ⟨subset_univ _, ?_⟩
        intro h
        have hg : KrullTwoPointSpace.generic ∈
            (A : Set KrullTwoPointSpace) :=
          h (by simp [B])
        simp [A] at hg }
  have hdim_le : topologicalKrullDim KrullTwoPointSpace ≤ 1 := by
    rw [topologicalKrullDim, Order.krullDim_le_one_iff]
    intro D
    have hcomp : IsOpen (D : Set KrullTwoPointSpace)ᶜ :=
      isOpen_compl_iff.mpr D.isClosed
    rcases krullTwoPointSpace_isOpen_iff.mp hcomp with h0 | hg | hu
    · have hD : (D : Set KrullTwoPointSpace) = Set.univ := by
        ext z
        cases z <;> simp_all
      right
      intro E hDE
      apply SetLike.coe_subset_coe.mp
      rw [hD]
      exact subset_univ _
    · have hspecial : KrullTwoPointSpace.special ∈ D := by
        by_contra h
        have hs : KrullTwoPointSpace.special ∈ (D : Set KrullTwoPointSpace)ᶜ := h
        rw [hg] at hs
        simp at hs
      have hgeneric : KrullTwoPointSpace.generic ∉ D := by
        intro hD
        have hs : KrullTwoPointSpace.generic ∈ (D : Set KrullTwoPointSpace)ᶜ := by
          rw [hg]
          simp
        exact hs hD
      have hD : (D : Set KrullTwoPointSpace) =
          {KrullTwoPointSpace.special} := by
        ext z
        cases z <;> simp [hspecial, hgeneric]
      left
      intro E hED
      apply SetLike.coe_subset_coe.mp
      rw [hD]
      rcases E.isIrreducible.nonempty with ⟨z, hz⟩
      have hzD : z ∈ (D : Set KrullTwoPointSpace) := hED hz
      have hzS : z ∈ ({KrullTwoPointSpace.special} : Set KrullTwoPointSpace) := by
        simpa [hD] using hzD
      have hzs : z = KrullTwoPointSpace.special := by
        simpa using hzS
      rw [← hzs]
      exact Set.singleton_subset_iff.mpr hz
    · have hD : (D : Set KrullTwoPointSpace) = ∅ := by
        ext z
        cases z <;> simp_all
      obtain ⟨z, hz⟩ := D.isIrreducible.nonempty
      rw [hD] at hz
      exact hz.elim
  have hdim_ge : (1 : WithBot ℕ∞) ≤ topologicalKrullDim KrullTwoPointSpace := by
    simpa [topologicalKrullDim, C] using
      (Order.LTSeries.length_le_krullDim C)
  have hdim_eq : topologicalKrullDim KrullTwoPointSpace = 1 :=
    le_antisymm hdim_le hdim_ge
  refine ⟨C, rfl, ?_, ?_, ?_⟩
  · change (A : Set KrullTwoPointSpace) = {KrullTwoPointSpace.special}
    rfl
  · change (B : Set KrullTwoPointSpace) = Set.univ
    rfl
  · simpa [C] using hdim_eq.symm

theorem krullDimension_twoPointSpace :
    topologicalKrullDim KrullTwoPointSpace = 1 := by
  obtain ⟨C, hlen, hhead, hlast, heq⟩ :=
    krullDimension_twoPointSpace_maximal_chain
  simpa [hlen] using heq.symm

/-- The finite-chain generalization of the two-point example. -/
@[instance_reducible]
def krullFiniteChainTopology (n : ℕ) : TopologicalSpace (Fin (n + 1)) :=
  TopologicalSpace.generateFrom
    (Set.range (fun i : Fin (n + 1) => Set.Ici i))

abbrev KrullFiniteChainSpace (n : ℕ) :=
  WithTopology (Fin (n + 1)) (krullFiniteChainTopology n)

theorem krullDimension_finiteChain (n : ℕ) :
    topologicalKrullDim (KrullFiniteChainSpace n) = n := by
  classical
  let _ : TopologicalSpace (Fin (n + 1)) := krullFiniteChainTopology n
  have hupper :
      ∀ (s : Set (Fin (n + 1))), IsOpen s →
        ∀ ⦃i j : Fin (n + 1)⦄, i ∈ s → i ≤ j → j ∈ s := by
    intro s hs
    induction hs with
    | basic s hs =>
        rcases hs with ⟨i, rfl⟩
        intro x y hxy hle
        exact hxy.trans hle
    | univ =>
        intro x y hxy hle
        exact Set.mem_univ _
    | inter s t hs ht ihs iht =>
        intro x y hxy hle
        exact ⟨ihs hxy.1 hle, iht hxy.2 hle⟩
    | sUnion S hS ih =>
        intro x y hxy hle
        rcases Set.mem_sUnion.mp hxy with ⟨s, hsS, hxs⟩
        exact Set.mem_sUnion.mpr ⟨s, hsS, ih s hsS hxs hle⟩
  have hlower :
      ∀ (D : IrreducibleCloseds (Fin (n + 1))),
        ∀ ⦃i j : Fin (n + 1)⦄,
          i ∈ (D : Set (Fin (n + 1))) → j ≤ i → j ∈ (D : Set (Fin (n + 1))) := by
    intro D i j hi hji
    by_contra hj
    have hjc : j ∈ ((D : Set (Fin (n + 1)))ᶜ) := hj
    have hopen : IsOpen ((D : Set (Fin (n + 1)))ᶜ) :=
      isOpen_compl_iff.mpr D.isClosed
    exact (hupper _ hopen hjc hji) hi
  let relevant : IrreducibleCloseds (Fin (n + 1)) → Finset (Fin (n + 1)) :=
    fun D => Finset.univ.filter (fun i => i ∈ (D : Set (Fin (n + 1))))
  have hfilter_nonempty (D : IrreducibleCloseds (Fin (n + 1))) :
      (relevant D).Nonempty := by
    obtain ⟨i, hi⟩ := D.isIrreducible.nonempty
    refine ⟨i, ?_⟩
    change i ∈ Finset.univ.filter
      (fun i : Fin (n + 1) => i ∈ (D : Set (Fin (n + 1))))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  let maxIndex : IrreducibleCloseds (Fin (n + 1)) → Fin (n + 1) :=
    fun D => (relevant D).max' (hfilter_nonempty D)
  have hmaxmem (D : IrreducibleCloseds (Fin (n + 1))) :
      maxIndex D ∈ (D : Set (Fin (n + 1))) := by
    have hm : maxIndex D ∈ relevant D := by
      exact Finset.max'_mem _ _
    have hm' : maxIndex D ∈ Finset.univ.filter
        (fun i : Fin (n + 1) => i ∈ (D : Set (Fin (n + 1)))) := by
      simpa only [relevant] using hm
    exact (Finset.mem_filter.mp hm').2
  have hlemax (D : IrreducibleCloseds (Fin (n + 1)))
      {i : Fin (n + 1)} (hi : i ∈ (D : Set (Fin (n + 1)))) :
      i ≤ maxIndex D := by
    have hi' : i ∈ relevant D := by
      change i ∈ Finset.univ.filter
        (fun i : Fin (n + 1) => i ∈ (D : Set (Fin (n + 1))))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    simpa [maxIndex] using (Finset.le_max' (relevant D) i hi')
  have hD_eq (D : IrreducibleCloseds (Fin (n + 1))) :
      (D : Set (Fin (n + 1))) = Set.Iic (maxIndex D) := by
    ext i
    constructor
    · intro hi
      exact hlemax D hi
    · intro hi
      exact hlower D (hmaxmem D) hi
  have hmax_strict : StrictMono maxIndex := by
    intro D E hDE
    have hDEsub : (D : Set (Fin (n + 1))) ⊆ (E : Set (Fin (n + 1))) := hDE.le
    have hle : maxIndex D ≤ maxIndex E :=
      hlemax E (hDEsub (hmaxmem D))
    have hne : maxIndex D ≠ maxIndex E := by
      intro heq
      apply hDE.ne
      apply SetLike.coe_injective
      rw [hD_eq D, hD_eq E, heq]
    exact lt_of_le_of_ne hle hne
  have hmap :
      Order.krullDim (IrreducibleCloseds (Fin (n + 1))) ≤
        Order.krullDim (Fin (n + 1)) :=
    Order.krullDim_le_of_strictMono maxIndex hmax_strict
  have hfin : Order.krullDim (Fin (n + 1)) ≤ n := by
    rw [Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    refine iSup_le fun C => ?_
    apply Nat.cast_le.mpr
    apply Nat.le_of_lt_succ
    simpa using C.length_lt_card
  have hIoi (i : Fin (n + 1)) : IsOpen (Set.Ioi i) := by
    have heq : Set.Ioi i =
        ⋃ j : {j : Fin (n + 1) // i < j}, Set.Ici (j : Fin (n + 1)) := by
      ext x
      constructor
      · intro hxi
        refine Set.mem_iUnion.mpr
          ⟨(⟨x, hxi⟩ : {j : Fin (n + 1) // i < j}), ?_⟩
        change (↑(⟨x, hxi⟩ : {j : Fin (n + 1) // i < j}) : Fin (n + 1)) ≤ x
        exact le_rfl
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
        exact lt_of_lt_of_le j.property hj
    rw [heq]
    exact isOpen_iUnion fun j =>
      isOpen_generateFrom_of_mem (Set.mem_range.mpr ⟨(j : Fin (n + 1)), rfl⟩)
  have hIic_closed (i : Fin (n + 1)) : IsClosed (Set.Iic i) := by
    apply isOpen_compl_iff.mp
    rw [compl_Iic]
    exact hIoi i
  have hIic_irred (i : Fin (n + 1)) : IsIrreducible (Set.Iic i) := by
    refine ⟨⟨i, ?_⟩, ?_⟩
    · change i ≤ i
      exact le_rfl
    intro u v hu hv hu' hv'
    rcases hu' with ⟨x, hxi, hxu⟩
    rcases hv' with ⟨y, hyi, hyv⟩
    have hxi' : x ≤ i := hxi
    have hyi' : y ≤ i := hyi
    let z := max x y
    refine ⟨z, ?_, ?_, ?_⟩
    · exact max_le hxi' hyi'
    · exact hupper u hu hxu (le_max_left _ _)
    · exact hupper v hv hyv (le_max_right _ _)
  let I : Fin (n + 1) → IrreducibleCloseds (Fin (n + 1)) :=
    fun i => ⟨Set.Iic i, hIic_irred i, hIic_closed i⟩
  have hI_strict : StrictMono I := by
    intro i j hij
    apply SetLike.coe_ssubset_coe.mp
    change Set.Iic i ⊂ Set.Iic j
    refine ⟨?_, ?_⟩
    · intro x hx
      exact le_trans hx hij.le
    · intro h
      have hj : j ∈ Set.Iic j := by
        change j ≤ j
        exact le_rfl
      have hji : j ∈ Set.Iic i := h hj
      exact (not_le_of_gt hij) hji
  let C : LTSeries (IrreducibleCloseds (Fin (n + 1))) :=
    { length := n
      toFun := I
      step := by
        intro i
        change I i.castSucc < I i.succ
        exact hI_strict i.castSucc_lt_succ }
  have hge : (n : WithBot ℕ∞) ≤
      topologicalKrullDim (Fin (n + 1)) := by
    simpa [topologicalKrullDim, C] using
      (Order.LTSeries.length_le_krullDim C)
  have hfin_dim : topologicalKrullDim (Fin (n + 1)) = n :=
    le_antisymm (by simpa [topologicalKrullDim] using hmap.trans hfin) hge
  let f : Fin (n + 1) → KrullFiniteChainSpace n :=
    WithTopology.toTopology (krullFiniteChainTopology n)
  have hf : IsHomeomorph f := by
    refine ⟨WithTopology.continuous_toTopology _, ?_, ?_⟩
    · intro s hs
      rw [WithTopology.isOpen_iff]
      simpa [f, Set.preimage_image_eq _ (WithTopology.toTopology_injective _)] using hs
    · simpa [f] using (WithTopology.toTopology_bijective (krullFiniteChainTopology n))
  have hdim_homeo :
      topologicalKrullDim (Fin (n + 1)) =
        topologicalKrullDim (KrullFiniteChainSpace n) :=
    IsHomeomorph.topologicalKrullDim_eq f hf
  exact hdim_homeo.symm.trans hfin_dim

/-! ### Equidimensional spaces -/

/-- Every irreducible component of `X` has the same Krull dimension. -/
def Equidimensional : Prop :=
  ∃ d : WithBot ℕ∞,
    ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = d

end KrullDimension

end Formalization.Books.Topology.Unit10
