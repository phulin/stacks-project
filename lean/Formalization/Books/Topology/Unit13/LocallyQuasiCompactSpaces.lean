import Formalization.Books.Topology.Unit12.QuasiCompactSpacesAndMaps
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.ShrinkingLemma

/-!
# Topology, Chapter 13: Locally quasi-compact spaces

The source's locally quasi-compact condition is Mathlib's
`LocallyCompactSpace`: its `local_compact_nhds` field says that every
neighbourhood of a point contains a compact neighbourhood of that point.
The weaker condition that every point merely has one compact neighbourhood is
Mathlib's `WeaklyLocallyCompactSpace`.  Neighbourhoods below are expressed by
membership in `𝓝`, so they are not required to be open.

The source uses `p + 1`-tuples of indices.  We represent such a tuple by a
function `Fin (p + 1) → I`, which also handles repetitions without adding
extra cases to the interfaces.
-/

namespace Formalization.Books.Topology.Unit13

open Set Function Filter _root_.Topology TopologicalSpace

universe u v w

section LocallyQuasiCompactSpaces

variable {X : Type u} [TopologicalSpace X]

/-! ### Locally quasi-compact spaces -/

theorem locallyCompactSpace_iff_weaklyLocallyCompactSpace [T2Space X] :
    LocallyCompactSpace X ↔ WeaklyLocallyCompactSpace X := by
  constructor
  · intro h
    let : LocallyCompactSpace X := h
    infer_instance
  · intro h
    let : WeaklyLocallyCompactSpace X := h
    infer_instance

/-! ### Baire category -/

theorem dense_iInter_of_isOpen_of_locallyCompactSpace
    [T2Space X] [LocallyCompactSpace X]
    (U : ℕ → Set X)
    (hUopen : ∀ n, 1 ≤ n → IsOpen (U n))
    (hUdense : ∀ n, 1 ≤ n → Dense (U n)) :
    Dense (⋂ (n : ℕ) (_h : 1 ≤ n), U n) := by
  exact dense_biInter_of_isOpen (S := {n : ℕ | 1 ≤ n}) hUopen (Set.to_countable _) hUdense

/-! ### Relatively compact refinements -/

theorem exists_closure_subset_of_compactSpace
    [CompactSpace X] [T2Space X] {I : Type v}
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (⋃ i, U i) = (Set.univ : Set X)) :
    ∃ V : I → Set X,
      (⋃ i, V i) = (Set.univ : Set X) ∧
        (∀ i, IsOpen (V i)) ∧
          ∀ i, closure (V i) ⊆ U i := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen (by
    simp [hUcover])
  let U' : I → Set X := fun i => if i ∈ s then U i else ∅
  have hU'open : ∀ i, IsOpen (U' i) := by
    intro i
    by_cases hi : i ∈ s <;> simp [U', hi, hUopen]
  have hU'finite : ∀ x : X, {i | x ∈ U' i}.Finite := by
    intro x
    apply s.finite_toSet.subset
    intro i hi
    by_contra hi'
    simp [U'] at hi
    exact hi' hi.1
  have hU'cover : (Set.univ : Set X) ⊆ ⋃ i, U' i := by
    intro x hx
    rcases mem_iUnion₂.1 (hs hx) with ⟨i, hi, hxi⟩
    refine mem_iUnion.2 ⟨i, ?_⟩
    simp [U', hi, hxi]
  obtain ⟨V, hVcover, hVopen, hVsubset, _⟩ :=
    exists_subset_iUnion_closure_subset_t2space (s := (Set.univ : Set X))
      isCompact_univ hU'open (fun x _ => hU'finite x) hU'cover
  refine ⟨V, univ_subset_iff.1 hVcover, hVopen, ?_⟩
  intro i
  refine (hVsubset i).trans ?_
  intro x hx
  by_cases hi : i ∈ s
  · have hxi : x ∈ U i := by
      simpa [U', hi] using hx
    exact hxi
  · exfalso
    simp [U', hi] at hx

/-! ### Refinements controlling multiple intersections -/

private theorem finite_refinement
    [CompactSpace X] [T2Space X] (p : ℕ) (I : Type) [Fintype I]
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (⋃ i, U i) = (Set.univ : Set X))
    {κ : (Fin (p + 1) → I) → Type w}
    (W : ∀ a : Fin (p + 1) → I, κ a → Set X)
    (hWopen : ∀ (a : Fin (p + 1) → I) (k : κ a), IsOpen (W a k))
    (hWcover : ∀ a : Fin (p + 1) → I,
      (⋂ j, U (a j)) = ⋃ k, W a k) :
    ∃ (J : Type w) (V : J → Set X) (α : J → I),
      (⋃ j, V j) = (Set.univ : Set X) ∧
          (∀ j, IsOpen (V j)) ∧
            (∀ j, closure (V j) ⊆ U (α j)) ∧
              ∀ a : Fin (p + 1) → J,
                (⋂ j, V (a j)).Nonempty →
                  ∃ k : κ (fun j => α (a j)),
                    (⋂ j, V (a j)) ⊆ W (fun j => α (a j)) k := by
  classical
  obtain ⟨V, hVcover, hVopen, hVclosure⟩ :=
    exists_closure_subset_of_compactSpace U hUopen hUcover
  let C := (Fin (p + 1) → I) × Fin (p + 1)
  let κC : C → Type w := fun c => κ c.1
  let Kset : C → Set X := fun c => ⋂ j, closure (V (c.1 j))
  let Kother : C → Set X := fun c =>
    ⋂ j, if j = c.2 then (Set.univ : Set X) else closure (V (c.1 j))
  have hKcompact : ∀ c, IsCompact (Kset c) := by
    intro c
    apply IsCompact.of_isClosed_subset isCompact_univ
      (isClosed_iInter fun j => isClosed_closure) (subset_univ _)
  have hKcover : ∀ c, Kset c ⊆ ⋃ k : κC c, W c.1 k := by
    intro c x hx
    rw [← hWcover c.1]
    refine mem_iInter.2 fun j => hVclosure (c.1 j) (mem_iInter.1 hx j)
  choose sK hsK using fun c =>
    (hKcompact c).elim_finite_subcover (fun k : κC c => W c.1 k)
      (fun k => hWopen c.1 k) (hKcover c)
  let Choice : C → Type w := fun c => Option (κC c)
  let E : I → (c : C) → Choice c → Set X := fun i c z =>
    if c.1 c.2 = i then
      match z with
      | none => V i \ Kother c
      | some k => V i ∩ W c.1 k
    else Set.univ
  have hKother_closed : ∀ c, IsClosed (Kother c) := by
    intro c
    exact isClosed_iInter fun j => by
      split_ifs <;> simp
  have hEopen : ∀ (i : I) (c : C) (z : Choice c), IsOpen (E i c z) := by
    intro i c z
    dsimp [E]
    split_ifs with hi
    · cases z with
      | none => exact hVopen i |>.sdiff (hKother_closed c)
      | some k => exact (hVopen i).inter (hWopen _ k)
    · exact isOpen_univ
  let J : Type w := Σ i : I, ∀ c : C, Choice c
  let V' : J → Set X := fun z => V z.1 ∩ ⋂ c, E z.1 c (z.2 c)
  let α' : J → I := fun z => z.1
  have hV'cover : (⋃ z, V' z) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm (subset_univ _)
    intro x hx
    rcases mem_iUnion.1 (hVcover ▸ hx) with ⟨i, hxi⟩
    have hchoice : ∀ c : C, ∃ z : Choice c, x ∈ E i c z := by
      intro c
      by_cases hi : c.1 c.2 = i
      · by_cases hxother : x ∈ Kother c
        · have hxfull : x ∈ Kset c := by
            refine mem_iInter.2 fun l => ?_
            by_cases hl : l = c.2
            · simpa [hl, hi] using (subset_closure hxi)
            · simpa [hl] using (mem_iInter.1 hxother l)
          rcases mem_iUnion₂.1 (hsK c hxfull) with ⟨k, hk, hxk⟩
          exact ⟨some k, by
            dsimp [E]
            rw [if_pos hi]
            exact ⟨hxi, hxk⟩⟩
        · exact ⟨none, by
            dsimp [E]
            rw [if_pos hi]
            exact ⟨hxi, hxother⟩⟩
      · exact ⟨none, by
          dsimp [E]
          rw [if_neg hi]
          exact mem_univ x⟩
    choose q hq using hchoice
    exact mem_iUnion.2 ⟨⟨i, q⟩, ⟨hxi, mem_iInter.2 hq⟩⟩
  have hV'open : ∀ z, IsOpen (V' z) := by
    intro z
    exact (hVopen z.1).inter (isOpen_iInter_of_finite fun c => hEopen z.1 c (z.2 c))
  have hV'closure : ∀ z, closure (V' z) ⊆ U (α' z) := by
    intro z
    exact (closure_mono inter_subset_left).trans (hVclosure z.1)
  refine ⟨J, V', α', hV'cover, hV'open, hV'closure, ?_⟩
  intro a ha
  let c₀ : C := (fun j => (a j).1, 0)
  cases hz : (a 0).2 c₀ with
  | none =>
      exfalso
      rcases ha with ⟨x, hx⟩
      have hx₀ : x ∈ V' (a 0) := mem_iInter.1 hx 0
      have hE₀ : x ∈ E (a 0).1 c₀ ((a 0).2 c₀) := mem_iInter.1 hx₀.2 c₀
      have hxnot : x ∉ Kother c₀ := by
        rw [hz] at hE₀
        have hE₀' : x ∈ V (a 0).1 \ Kother c₀ := by
          simpa [E, c₀] using hE₀
        exact hE₀'.2
      have hxother : x ∈ Kother c₀ := by
        dsimp [Kother, c₀]
        refine mem_iInter.2 fun l => ?_
        by_cases hl : l = 0
        · simp [hl]
        · have hxl : x ∈ V ((a l).1) := (mem_iInter.1 hx l).1
          simpa [hl] using (subset_closure hxl)
      exact hxnot hxother
  | some k =>
      refine ⟨k, ?_⟩
      intro x hx
      have hx₀ : x ∈ V' (a 0) := mem_iInter.1 hx 0
      have hE₀ : x ∈ E (a 0).1 c₀ ((a 0).2 c₀) := mem_iInter.1 hx₀.2 c₀
      rw [hz] at hE₀
      have hE₀' : x ∈ V (a 0).1 ∩ W c₀.1 k := by
        simpa [E, c₀] using hE₀
      exact hE₀'.2

theorem exists_refinement_of_compactSpace
    [CompactSpace X] [T2Space X] (p : ℕ) {I : Type v}
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (⋃ i, U i) = (Set.univ : Set X))
    {κ : (Fin (p + 1) → I) → Type w}
    (W : ∀ a : Fin (p + 1) → I, κ a → Set X)
    (hWopen : ∀ (a : Fin (p + 1) → I) (k : κ a), IsOpen (W a k))
    (hWcover : ∀ a : Fin (p + 1) → I,
      (⋂ j, U (a j)) = ⋃ k, W a k) :
    ∃ (J : Type w) (V : J → Set X) (α : J → I),
      (⋃ j, V j) = (Set.univ : Set X) ∧
          (∀ j, IsOpen (V j)) ∧
          (∀ j, closure (V j) ⊆ U (α j)) ∧
    ∀ a : Fin (p + 1) → J,
              (⋂ j, V (a j)).Nonempty →
                ∃ k : κ (fun j => α (a j)),
                  (⋂ j, V (a j)) ⊆ W (fun j => α (a j)) k := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen (by
    simp [hUcover])
  let e : Fin s.card → I := fun j => (s.equivFin.symm j : I)
  have hUcover' : (⋃ j, U (e j)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm (subset_univ _)
    intro x hx
    rcases mem_iUnion₂.1 (hs (Set.mem_univ x)) with ⟨i, hi, hxi⟩
    let j : Fin s.card := s.equivFin ⟨i, hi⟩
    refine mem_iUnion.2 ⟨j, ?_⟩
    simpa [e, j] using hxi
  let κ' : (Fin (p + 1) → Fin s.card) → Type w := fun a =>
    κ (fun j => e (a j))
  let W' : ∀ a : Fin (p + 1) → Fin s.card, κ' a → Set X := fun a k =>
    W (fun j => e (a j)) k
  have hW'open : ∀ (a : Fin (p + 1) → Fin s.card) (k : κ' a), IsOpen (W' a k) := by
    intro a k
    exact hWopen _ _
  have hW'cover : ∀ a : Fin (p + 1) → Fin s.card,
      (⋂ j, U (e (a j))) = ⋃ k, W' a k := by
    intro a
    exact hWcover (fun j => e (a j))
  obtain ⟨J, V, α, hVcover, hVopen, hVclosure, hVinter⟩ :=
    finite_refinement p (Fin s.card) (fun j => U (e j))
      (fun j => hUopen _) hUcover' W' hW'open hW'cover
  refine ⟨J, V, fun j => e (α j), hVcover, hVopen, ?_, ?_⟩
  · intro j
    exact hVclosure j
  · intro a ha
    obtain ⟨k, hk⟩ := hVinter a ha
    exact ⟨k, hk⟩

/-! ### Lifting a cover from a compact closed subset -/

theorem exists_lift_covering_of_isCompact
    [T2Space X] [LocallyCompactSpace X] {Z : Set X}
    (hZ : IsCompact Z) (p : ℕ) {I : Type v}
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (W : (Fin (p + 1) → I) → Set X)
    (hWopen : ∀ a, IsOpen (W a))
    (hWsubset : ∀ a, W a ⊆ ⋂ j, U (a j))
    (hZcover : Z ⊆ ⋃ i, U i)
    (hWZ : ∀ a, W a ∩ Z = (⋂ j, U (a j)) ∩ Z) :
    ∃ V : I → Set X,
      Z ⊆ ⋃ i, V i ∧
        (∀ i, IsOpen (V i)) ∧
          (∀ i, closure (V i) ⊆ U i) ∧
            ∀ a, (⋂ j, V (a j)) ⊆ W a := by
  classical
  obtain ⟨s, hs⟩ := hZ.elim_finite_subcover U hUopen hZcover
  let U' : I → Set X := fun i => if i ∈ s then U i else ∅
  have hU'open : ∀ i, IsOpen (U' i) := by
    intro i
    by_cases hi : i ∈ s <;> simp [U', hi, hUopen]
  have hU'finite : ∀ x : X, {i | x ∈ U' i}.Finite := by
    intro x
    apply s.finite_toSet.subset
    intro i hi
    by_contra hi'
    simp [U'] at hi
    exact hi' hi.1
  have hU'cover : Z ⊆ ⋃ i, U' i := by
    intro x hx
    rcases mem_iUnion₂.1 (hs hx) with ⟨i, hi, hxi⟩
    refine mem_iUnion.2 ⟨i, ?_⟩
    simp [U', hi, hxi]
  obtain ⟨V, hVcover, hVopen, hVsubset, _⟩ :=
    exists_subset_iUnion_closure_subset_t2space hZ hU'open
      (fun x _ => hU'finite x) hU'cover
  have hVclosure : ∀ i, closure (V i) ⊆ U i := by
    intro i
    by_cases hi : i ∈ s
    · exact (hVsubset i).trans (by simp [U', hi])
    · intro x hx
      exfalso
      have hx' := hVsubset i hx
      simp [U', hi] at hx'
  let A := {i : I // i ∈ s}
  let C := Fin (p + 1) → A
  let T : C → Set X := fun a =>
    closure ((⋂ j, V (a j).1) \ W (fun j => (a j).1))
  let Tall : Set X := ⋃ a : C, T a
  have hTsubset : ∀ a : C, T a ⊆ ⋂ j, U (a j).1 := by
    intro a x hx
    refine mem_iInter.2 fun j => ?_
    by_cases hxW : x ∈ W (fun l => (a l).1)
    · exact mem_iInter.1 (hWsubset (fun l => (a l).1) hxW) j
    · exact hVclosure (a j).1 (closure_mono
        (sdiff_subset.trans (iInter_subset _ j)) hx)
  have hTdisjoint : ∀ a : C, Disjoint (T a) Z := by
    intro a
    rw [disjoint_left]
    intro x hxT hxZ
    have hxnot : x ∉ W (fun j => (a j).1) := by
      intro hxW
      have hTcomp : T a ⊆ (W (fun j => (a j).1))ᶜ := by
        apply closure_minimal
        · intro y hy
          exact hy.2
        · exact isClosed_compl_iff.2 (hWopen (fun j => (a j).1))
      exact hTcomp hxT hxW
    have hxU : x ∈ (⋂ j, U (a j).1) := hTsubset a hxT
    have hxW : x ∈ W (fun j => (a j).1) := by
      have : x ∈ W (fun j => (a j).1) ∩ Z := by
        rw [hWZ]
        exact ⟨hxU, hxZ⟩
      exact this.1
    exact hxnot hxW
  have hTallclosed : IsClosed Tall := by
    exact isClosed_iUnion_of_finite fun a => isClosed_closure
  have hTallZ : Disjoint Tall Z := by
    rw [disjoint_left]
    intro x hxT hxZ
    rcases mem_iUnion.1 hxT with ⟨a, hxa⟩
    exact (disjoint_left.1 (hTdisjoint a)) hxa hxZ
  let V' : I → Set X := fun i => V i \ Tall
  have hV'cover : Z ⊆ ⋃ i, V' i := by
    intro x hx
    rcases mem_iUnion.1 (hVcover hx) with ⟨i, hxi⟩
    refine mem_iUnion.2 ⟨i, ⟨hxi, ?_⟩⟩
    intro hxT
    exact (disjoint_left.1 hTallZ) hxT hx
  have hV'open : ∀ i, IsOpen (V' i) := by
    intro i
    exact hVopen i |>.sdiff hTallclosed
  have hV'closure : ∀ i, closure (V' i) ⊆ U i := by
    intro i
    exact (closure_mono sdiff_subset).trans (hVclosure i)
  refine ⟨V', hV'cover, hV'open, hV'closure, ?_⟩
  intro a x hx
  by_cases ha : ∀ j, a j ∈ s
  · let b : C := fun j => ⟨a j, ha j⟩
    by_contra hxW
    have hxT : x ∈ T b := by
      apply subset_closure
      refine ⟨mem_iInter.2 fun j => (mem_iInter.1 hx j).1, hxW⟩
    have hxTall : x ∈ Tall := mem_iUnion.2 ⟨b, hxT⟩
    exact (mem_iInter.1 hx 0).2 hxTall
  · rcases not_forall.1 ha with ⟨j, hj⟩
    exfalso
    have hxU' := hVsubset (a j) (subset_closure ((mem_iInter.1 hx j).1))
    simp [U', hj] at hxU'

/-! ### Lifting a cover from a quasi-compact Hausdorff subset -/

theorem exists_lift_covering_of_isCompact_of_pairwise_separated
    {Z : Set X} (hZ : IsCompact Z)
    (hZsep : ∀ ⦃x y : X⦄, x ∈ Z → y ∈ Z → x ≠ y →
      ∃ A B : Set X,
        IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) {I : Type v}
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (W : (Fin (p + 1) → I) → Set X)
    (hWopen : ∀ a, IsOpen (W a))
    (hWsubset : ∀ a, W a ⊆ ⋂ j, U (a j))
    (hZcover : Z ⊆ ⋃ i, U i)
    (hWZ : ∀ a, W a ∩ Z = (⋂ j, U (a j)) ∩ Z) :
    ∃ V : I → Set X,
      Z ⊆ ⋃ i, V i ∧
        (∀ i, IsOpen (V i)) ∧
          (∀ i, V i ⊆ U i) ∧
            (∀ i, closure (V i) ∩ Z ⊆ U i) ∧
              ∀ a, (⋂ j, V (a j)) ⊆ W a := by
  classical
  obtain ⟨s, hs⟩ := hZ.elim_finite_subcover U hUopen hZcover
  have hchoose : ∀ z : Z, ∃ i, i ∈ s ∧ (z : X) ∈ U i := by
    intro z
    rcases mem_iUnion₂.1 (hs z.property) with ⟨i, hi, hzi⟩
    exact ⟨i, hi, hzi⟩
  choose i hi hzi using hchoose
  let Bad : Z → Set X := fun z => Z \ U (i z)
  have hsep : ∀ (z : Z) (y : {y : X // y ∈ Bad z}),
      ∃ A B : Set X,
        IsOpen A ∧ IsOpen B ∧ (z : X) ∈ A ∧ (y : X) ∈ B ∧ Disjoint A B := by
    intro z y
    have hne : (z : X) ≠ (y : X) := by
      intro h
      exact y.property.2 (h ▸ hzi z)
    exact hZsep z.property y.property.1 hne
  choose A B hAo hBo hzA hyB hAB using hsep
  have hBadcompact : ∀ z : Z, IsCompact (Bad z) := by
    intro z
    exact hZ.diff (hUopen (i z))
  have hBadcover : ∀ z : Z,
      Bad z ⊆ ⋃ y : {y : X // y ∈ Bad z}, B z y := by
    intro z x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, hyB z ⟨x, hx⟩⟩
  choose t ht using fun z =>
    (hBadcompact z).elim_finite_subcover (fun y : {y : X // y ∈ Bad z} => B z y)
      (fun y => hBo z y) (hBadcover z)
  let N : Z → Set X := fun z => U (i z) ∩ ⋂ y ∈ t z, A z y
  have hNopen : ∀ z : Z, IsOpen (N z) := by
    intro z
    exact (hUopen (i z)).inter (isOpen_biInter_finset fun y hy => hAo z y)
  have hzN : ∀ z : Z, (z : X) ∈ N z := by
    intro z
    refine ⟨hzi z, ?_⟩
    exact mem_iInter₂.2 fun y hy => hzA z y
  have hNsubsetU : ∀ z : Z, N z ⊆ U (i z) := fun z => inter_subset_left
  have hNclosureZ : ∀ z : Z, closure (N z) ∩ Z ⊆ U (i z) := by
    intro z x hx
    by_contra hxU
    have hxBad : x ∈ Bad z := ⟨hx.2, hxU⟩
    rcases mem_iUnion₂.1 (ht z hxBad) with ⟨y, hy, hxyB⟩
    have hNA : N z ⊆ A z y := by
      intro w hw
      exact mem_iInter₂.1 hw.2 y hy
    have hxyA : x ∈ closure (A z y) := closure_mono hNA hx.1
    have hABcomp : closure (A z y) ⊆ (B z y)ᶜ := by
      apply closure_minimal
      · intro w hwA hwB
        exact (disjoint_left.1 (hAB z y)) hwA hwB
      · exact isClosed_compl_iff.2 (hBo z y)
    exact hABcomp hxyA hxyB
  obtain ⟨r, hr⟩ := hZ.elim_finite_subcover N hNopen (by
    intro z hz
    exact mem_iUnion.2 ⟨⟨z, hz⟩, hzN ⟨z, hz⟩⟩)
  let R := {z : Z // z ∈ r}
  let V₀ : I → Set X := fun k =>
    ⋃ z : R, if k = i z.1 then N z.1 else ∅
  have hV₀open : ∀ k, IsOpen (V₀ k) := by
    intro k
    apply isOpen_iUnion
    intro z
    by_cases hk : k = i z.1
    · rw [if_pos hk]
      exact hNopen z.1
    · rw [if_neg hk]
      exact isOpen_empty
  have hV₀subset : ∀ k, V₀ k ⊆ U k := by
    intro k x hx
    rcases mem_iUnion.1 hx with ⟨z, hxz⟩
    by_cases hk : k = i z.1
    · rw [hk]
      exact hNsubsetU z.1 (by simpa [hk] using hxz)
    · simp [hk] at hxz
  have hV₀cover : Z ⊆ ⋃ k, V₀ k := by
    intro z hz
    rcases mem_iUnion₂.1 (hr hz) with ⟨z', hz'r, hzz'⟩
    refine mem_iUnion.2 ⟨i z', ?_⟩
    refine mem_iUnion.2 ⟨⟨z', hz'r⟩, ?_⟩
    simp [hzz']
  have hV₀closureZ : ∀ k, closure (V₀ k) ∩ Z ⊆ U k := by
    intro k x hx
    have hx' : x ∈ ⋃ z : R, closure (if k = i z.1 then N z.1 else ∅) := by
      rw [← closure_iUnion_of_finite]
      exact hx.1
    rcases mem_iUnion.1 hx' with ⟨z, hzx⟩
    by_cases hk : k = i z.1
    · rw [hk]
      exact hNclosureZ z.1 ⟨by simpa [hk] using hzx, hx.2⟩
    · simp [hk] at hzx
  let K := {i : I // i ∈ s}
  let C := Fin (p + 1) → K
  let T : C → Set X := fun a =>
    closure ((⋂ j, V₀ (a j).1) \ W (fun j => (a j).1))
  let Tall : Set X := ⋃ a : C, T a
  have hTsubset : ∀ a : C, T a ∩ Z ⊆ ⋂ j, U (a j).1 := by
    intro a x hx
    refine mem_iInter.2 fun j => ?_
    by_cases hxW : x ∈ W (fun l => (a l).1)
    · exact mem_iInter.1 (hWsubset (fun l => (a l).1) hxW) j
    · apply hV₀closureZ (a j).1
      refine ⟨?_, hx.2⟩
      exact closure_mono (sdiff_subset.trans (iInter_subset _ j)) hx.1
  have hTdisjoint : ∀ a : C, Disjoint (T a) Z := by
    intro a
    rw [disjoint_left]
    intro x hxT hxZ
    have hxnot : x ∉ W (fun j => (a j).1) := by
      intro hxW
      have hTcomp : T a ⊆ (W (fun j => (a j).1))ᶜ := by
        apply closure_minimal
        · intro y hy
          exact hy.2
        · exact isClosed_compl_iff.2 (hWopen (fun j => (a j).1))
      exact hTcomp hxT hxW
    have hxU : x ∈ (⋂ j, U (a j).1) := hTsubset a ⟨hxT, hxZ⟩
    have hxW : x ∈ W (fun j => (a j).1) := by
      have : x ∈ W (fun j => (a j).1) ∩ Z := by
        rw [hWZ]
        exact ⟨hxU, hxZ⟩
      exact this.1
    exact hxnot hxW
  have hTallclosed : IsClosed Tall := by
    exact isClosed_iUnion_of_finite fun a => isClosed_closure
  have hTallZ : Disjoint Tall Z := by
    rw [disjoint_left]
    intro x hxT hxZ
    rcases mem_iUnion.1 hxT with ⟨a, hxa⟩
    exact (disjoint_left.1 (hTdisjoint a)) hxa hxZ
  let V' : I → Set X := fun k => V₀ k \ Tall
  have hV'cover : Z ⊆ ⋃ k, V' k := by
    intro x hx
    rcases mem_iUnion.1 (hV₀cover hx) with ⟨k, hxk⟩
    refine mem_iUnion.2 ⟨k, ⟨hxk, ?_⟩⟩
    intro hxT
    exact (disjoint_left.1 hTallZ) hxT hx
  have hV'open : ∀ k, IsOpen (V' k) := by
    intro k
    exact hV₀open k |>.sdiff hTallclosed
  have hV'subset : ∀ k, V' k ⊆ U k := by
    intro k
    exact sdiff_subset.trans (hV₀subset k)
  have hV'closureZ : ∀ k, closure (V' k) ∩ Z ⊆ U k := by
    intro k x hx
    apply hV₀closureZ k
    exact ⟨closure_mono sdiff_subset hx.1, hx.2⟩
  refine ⟨V', hV'cover, hV'open, hV'subset, hV'closureZ, ?_⟩
  intro a x hx
  by_cases ha : ∀ j, a j ∈ s
  · let b : C := fun j => ⟨a j, ha j⟩
    by_contra hxW
    have hxT : x ∈ T b := by
      apply subset_closure
      refine ⟨mem_iInter.2 fun j => (mem_iInter.1 hx j).1, hxW⟩
    have hxTall : x ∈ Tall := mem_iUnion.2 ⟨b, hxT⟩
    exact (mem_iInter.1 hx 0).2 hxTall
  · rcases not_forall.1 ha with ⟨j, hj⟩
    have hV₀empty : V₀ (a j) = ∅ := by
      ext y
      constructor
      · intro hy
        rcases mem_iUnion.1 hy with ⟨z, hzy⟩
        by_cases heq : a j = i z.1
        · exact hj (heq ▸ hi z.1)
        · simp [heq] at hzy
      · simp
    exfalso
    have hxj : x ∈ V₀ (a j) := (mem_iInter.1 hx j).1
    rw [hV₀empty] at hxj
    exact hxj.elim

end LocallyQuasiCompactSpaces

end Formalization.Books.Topology.Unit13
