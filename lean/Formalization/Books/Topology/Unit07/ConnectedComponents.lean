import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.CardComponents
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.RatLemmas

/-!
# Topology, Chapter 7: Connected components

The source's connected spaces, connected subsets, connected components, and
the quotient by connected components are represented by Mathlib's canonical
`ConnectedSpace`, `IsConnected`, `connectedComponent`, and
`ConnectedComponents` declarations.  The source's total and local
connectedness notions are likewise recorded through Mathlib's
`TotallyDisconnectedSpace` and `LocallyConnectedSpace` APIs.
-/

namespace Formalization.Books.Topology.Unit07

open Set Function _root_.Topology TopologicalSpace

universe u v

section ConnectedComponents

variable {X : Type u} [TopologicalSpace X]

/-! ## Connected spaces and connected components -/

/- The source's definition of a connected space is Mathlib's canonical class.
   The clopen characterization is the source-facing form of that class. -/
theorem connectedSpace_iff_clopen_partition :
    ConnectedSpace X ↔
      Nonempty X ∧ ∀ T : Set X, IsClopen T → T = ∅ ∨ T = Set.univ :=
  connectedSpace_iff_clopen

/- `connectedComponent` is Mathlib's canonical maximal connected subset. -/
theorem connectedComponent_is_connected (x : X) :
    IsConnected (connectedComponent x) := by
  exact isConnected_connectedComponent

theorem connectedComponent_is_maximal_connected {T : Set X} {x : X}
    (hT : IsConnected T) (hx : x ∈ T) : T ⊆ connectedComponent x := by
  exact hT.subset_connectedComponent hx

theorem connectedComponent_eq_of_mem {x y : X}
    (hy : y ∈ connectedComponent x) :
    connectedComponent x = connectedComponent y := by
  exact connectedComponent_eq hy

theorem connectedComponent_is_closed (x : X) :
    IsClosed (connectedComponent x) := by
  exact isClosed_connectedComponent

theorem not_connectedSpace_of_isEmpty [IsEmpty X] : ¬ ConnectedSpace X := by
  rintro ⟨⟨x⟩⟩
  exact isEmptyElim x

theorem image_of_connected {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    {E : Set X} (hE : IsConnected E) (hf : Continuous f) :
    IsConnected (f '' E) := by
  exact hE.image f hf.continuousOn

theorem closure_of_connected {T : Set X} (hT : IsConnected T) :
    IsConnected (closure T) := by
  exact hT.closure

/- The unique component containing a connected subset, expressed using the
   canonical component sets rather than a parallel component predicate. -/
theorem existsUnique_connectedComponent_containing {T : Set X}
    (hT : IsConnected T) :
    ∃! C : Set X, (∃ x : X, C = connectedComponent x) ∧ T ⊆ C := by
  rcases hT.nonempty with ⟨x, hx⟩
  refine ExistsUnique.intro (connectedComponent x) ?_ ?_
  · exact ⟨⟨x, rfl⟩, hT.subset_connectedComponent hx⟩
  · intro C hC
    rcases hC with ⟨⟨y, rfl⟩, hTC⟩
    exact connectedComponent_eq (hTC hx)

theorem existsUnique_connectedComponent_containing_point (x : X) :
    ∃! C : Set X, (∃ y : X, C = connectedComponent y) ∧ x ∈ C := by
  refine ExistsUnique.intro (connectedComponent x) ?_ ?_
  · exact ⟨⟨x, rfl⟩, mem_connectedComponent⟩
  · intro C hC
    rcases hC with ⟨⟨y, rfl⟩, hx⟩
    exact connectedComponent_eq hx

theorem connectedComponent_cover :
    (⋃ x : X, connectedComponent x) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro x _
    exact mem_iUnion_of_mem x mem_connectedComponent

theorem connectedComponent_disjoint_of_ne {x y : X}
    (h : connectedComponent x ≠ connectedComponent y) :
    Disjoint (connectedComponent x) (connectedComponent y) := by
  exact connectedComponent_disjoint h

/- This records the source's warning that components need not be open. -/
theorem infinite_binary_product_has_singleton_components :
    ∀ x : ℕ → Bool,
      connectedComponent x = {x} ∧
        ¬ IsOpen ({x} : Set (ℕ → Bool)) := by
  intro x
  refine ⟨connectedComponent_eq_singleton x, ?_⟩
  intro hopen
  rcases (isOpen_pi_iff.mp hopen x (mem_singleton x)) with ⟨I, u, hu, hI⟩
  obtain ⟨n, hn⟩ := I.exists_notMem
  let y : ℕ → Bool := Function.update x n (Bool.not (x n))
  have hy : y ∈ (I : Set ℕ).pi u := by
    intro i hi
    have hin : i ≠ n := fun h => hn (h ▸ hi)
    simpa [y, hin] using (hu i hi).2
  have hyeq : y = x := Set.mem_singleton_iff.mp (hI hy)
  have hn_eq := congrFun hyeq n
  simp [y] at hn_eq

/-! ## Quasi-components -/

theorem connectedComponent_subset_quasiComponent (x : X) :
    connectedComponent x ⊆
      ⋂ Z : {Z : Set X // IsClopen Z ∧ x ∈ Z}, (Z : Set X) := by
  exact connectedComponent_subset_iInter_isClopen

/- The following concrete carrier and basis encode the example in the
   source.  The named constructors play the roles of `x`, `y`, and `z_n`.
   A separate carrier is used so this example's topology does not replace the
   canonical topology on `Bool ⊕ ℕ`. -/
inductive QuasiComponentExample where
  | x
  | y
  | z (n : ℕ)

def quasiComponentExampleX : QuasiComponentExample := .x

def quasiComponentExampleY : QuasiComponentExample := .y

def quasiComponentExampleTail (n : ℕ) : Set QuasiComponentExample :=
  Set.range (fun k : ℕ => QuasiComponentExample.z (n + k))

def quasiComponentExampleBasis : Set (Set QuasiComponentExample) :=
  Set.range (fun n : ℕ =>
    ({QuasiComponentExample.z n} : Set QuasiComponentExample)) ∪
    Set.range (fun n : ℕ => insert quasiComponentExampleX (quasiComponentExampleTail n)) ∪
    Set.range (fun n : ℕ => insert quasiComponentExampleY (quasiComponentExampleTail n))

instance quasiComponentExample_topologicalSpace :
    TopologicalSpace QuasiComponentExample :=
  TopologicalSpace.generateFrom quasiComponentExampleBasis

theorem quasiComponentExample_basis_is_basis :
    TopologicalSpace.IsTopologicalBasis quasiComponentExampleBasis := by
  classical
  have hsingle_mem (n : ℕ) :
      ({QuasiComponentExample.z n} : Set QuasiComponentExample) ∈
        quasiComponentExampleBasis := by
    simp only [quasiComponentExampleBasis, mem_union, mem_range]
    exact Or.inl (Or.inl ⟨n, rfl⟩)
  have hX_mem (n : ℕ) :
      insert quasiComponentExampleX (quasiComponentExampleTail n) ∈
        quasiComponentExampleBasis := by
    simp only [quasiComponentExampleBasis, mem_union, mem_range]
    exact Or.inl (Or.inr ⟨n, rfl⟩)
  have hY_mem (n : ℕ) :
      insert quasiComponentExampleY (quasiComponentExampleTail n) ∈
        quasiComponentExampleBasis := by
    simp only [quasiComponentExampleBasis, mem_union, mem_range]
    exact Or.inr ⟨n, rfl⟩
  have htail_subset (n m : ℕ) :
      quasiComponentExampleTail (n + m) ⊆
        quasiComponentExampleTail n ∩ quasiComponentExampleTail m := by
    intro a ha
    rcases ha with ⟨k, hk⟩
    constructor
    · refine ⟨m + k, ?_⟩
      rw [← hk]
      simp [Nat.add_comm, Nat.add_left_comm]
    · refine ⟨n + k, ?_⟩
      rw [← hk]
      simp [Nat.add_comm, Nat.add_left_comm]
  refine { exists_subset_inter := ?_, sUnion_eq := ?_, eq_generateFrom := rfl }
  · intro t₁ ht₁ t₂ ht₂ a ha
    simp only [quasiComponentExampleBasis, mem_union, mem_range] at ht₁ ht₂
    rcases ht₁ with (⟨n, rfl⟩ | ⟨n, rfl⟩) | ⟨n, rfl⟩
    · rcases ht₂ with (⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩
      · have ha_eq : a = QuasiComponentExample.z n := mem_singleton_iff.mp ha.1
        subst a
        refine ⟨{QuasiComponentExample.z n}, hsingle_mem n, mem_singleton _,
          subset_inter (singleton_subset_iff.mpr (mem_singleton _))
            (singleton_subset_iff.mpr ha.2)⟩
      · have ha_eq : a = QuasiComponentExample.z n := mem_singleton_iff.mp ha.1
        subst a
        refine ⟨{QuasiComponentExample.z n}, hsingle_mem n, mem_singleton _,
          subset_inter (singleton_subset_iff.mpr (mem_singleton _))
            (singleton_subset_iff.mpr ha.2)⟩
      · have ha_eq : a = QuasiComponentExample.z n := mem_singleton_iff.mp ha.1
        subst a
        refine ⟨{QuasiComponentExample.z n}, hsingle_mem n, mem_singleton _,
          subset_inter (singleton_subset_iff.mpr (mem_singleton _))
            (singleton_subset_iff.mpr ha.2)⟩
    · rcases ht₂ with (⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩
      · have ha_eq : a = QuasiComponentExample.z m := mem_singleton_iff.mp ha.2
        subst a
        refine ⟨{QuasiComponentExample.z m}, hsingle_mem m, mem_singleton _,
          subset_inter (singleton_subset_iff.mpr ha.1)
            (singleton_subset_iff.mpr (mem_singleton _))⟩
      · have ha₁ := ha.1
        have ha₂ := ha.2
        simp only [mem_insert_iff] at ha₁ ha₂
        by_cases hax : a = quasiComponentExampleX
        · subst a
          refine ⟨insert quasiComponentExampleX (quasiComponentExampleTail (n + m)),
            hX_mem (n + m), Or.inl rfl, ?_⟩
          intro b hb
          simp only [mem_insert_iff] at hb ⊢
          rcases hb with rfl | hb
          · exact ⟨Or.inl rfl, Or.inl rfl⟩
          · exact ⟨Or.inr ((htail_subset n m) hb).1,
              Or.inr ((htail_subset n m) hb).2⟩
        · have han := ha₁.resolve_left hax
          rcases han with ⟨k, rfl⟩
          refine ⟨{QuasiComponentExample.z (n + k)}, hsingle_mem _, mem_singleton _,
            subset_inter (singleton_subset_iff.mpr ha₁)
              (singleton_subset_iff.mpr ha₂)⟩
      · have ha₁ := ha.1
        have ha₂ := ha.2
        simp only [mem_insert_iff] at ha₁ ha₂
        by_cases hax : a = quasiComponentExampleX
        · rcases ha₂ with hay | ham
          · cases hax
            cases hay
          · rcases ham with ⟨k, hk⟩
            cases hax
            cases hk
        · have han := ha₁.resolve_left hax
          rcases ha₂ with hay | ham
          · rcases han with ⟨k, hk⟩
            cases hay
            cases hk
          · rcases han with ⟨k, rfl⟩
            refine ⟨{QuasiComponentExample.z (n + k)}, hsingle_mem _, mem_singleton _,
              subset_inter (singleton_subset_iff.mpr ha₁)
                (singleton_subset_iff.mpr (Or.inr ham))⟩
    · rcases ht₂ with (⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩
      · have ha_eq : a = QuasiComponentExample.z m := mem_singleton_iff.mp ha.2
        subst a
        refine ⟨{QuasiComponentExample.z m}, hsingle_mem m, mem_singleton _,
          subset_inter (singleton_subset_iff.mpr ha.1)
            (singleton_subset_iff.mpr (mem_singleton _))⟩
      · have ha₁ := ha.1
        have ha₂ := ha.2
        simp only [mem_insert_iff] at ha₁ ha₂
        by_cases hay : a = quasiComponentExampleY
        · rcases ha₂ with hax | ham
          · cases hay
            cases hax
          · rcases ham with ⟨k, hk⟩
            cases hay
            cases hk
        · have han := ha₁.resolve_left hay
          rcases ha₂ with hax | ham
          · rcases han with ⟨k, hk⟩
            cases hax
            cases hk
          · rcases han with ⟨k, rfl⟩
            refine ⟨{QuasiComponentExample.z (n + k)}, hsingle_mem _, mem_singleton _,
              subset_inter (singleton_subset_iff.mpr ha₁)
                (singleton_subset_iff.mpr (Or.inr ham))⟩
      · have ha₁ := ha.1
        have ha₂ := ha.2
        simp only [mem_insert_iff] at ha₁ ha₂
        by_cases hay : a = quasiComponentExampleY
        · subst a
          refine ⟨insert quasiComponentExampleY (quasiComponentExampleTail (n + m)),
            hY_mem (n + m), Or.inl rfl, ?_⟩
          intro b hb
          simp only [mem_insert_iff] at hb ⊢
          rcases hb with rfl | hb
          · exact ⟨Or.inl rfl, Or.inl rfl⟩
          · exact ⟨Or.inr ((htail_subset n m) hb).1,
              Or.inr ((htail_subset n m) hb).2⟩
        · have han := ha₁.resolve_left hay
          rcases han with ⟨k, rfl⟩
          refine ⟨{QuasiComponentExample.z (n + k)}, hsingle_mem _, mem_singleton _,
            subset_inter (singleton_subset_iff.mpr ha₁)
              (singleton_subset_iff.mpr ha₂)⟩
  · simp only [quasiComponentExampleBasis, sUnion_union, sUnion_range]
    ext a
    cases a <;> simp [quasiComponentExampleX, quasiComponentExampleY,
      quasiComponentExampleTail]

theorem quasiComponentExample_components :
    connectedComponent quasiComponentExampleX = {quasiComponentExampleX} ∧
      (⋂ Z :
          {Z : Set QuasiComponentExample //
            IsClopen Z ∧ quasiComponentExampleX ∈ Z},
          (Z : Set QuasiComponentExample)) =
        {quasiComponentExampleX, quasiComponentExampleY} := by
  classical
  have hb := quasiComponentExample_basis_is_basis
  have hsingle_mem (n : ℕ) :
      ({QuasiComponentExample.z n} : Set QuasiComponentExample) ∈
        quasiComponentExampleBasis := by
    simp only [quasiComponentExampleBasis, mem_union, mem_range]
    exact Or.inl (Or.inl ⟨n, rfl⟩)
  have hX_mem (n : ℕ) :
      insert quasiComponentExampleX (quasiComponentExampleTail n) ∈
        quasiComponentExampleBasis := by
    simp only [quasiComponentExampleBasis, mem_union, mem_range]
    exact Or.inl (Or.inr ⟨n, rfl⟩)
  have hY_mem (n : ℕ) :
      insert quasiComponentExampleY (quasiComponentExampleTail n) ∈
        quasiComponentExampleBasis := by
    simp only [quasiComponentExampleBasis, mem_union, mem_range]
    exact Or.inr ⟨n, rfl⟩
  have hclopen_z (n : ℕ) :
      IsClopen ({QuasiComponentExample.z n} : Set QuasiComponentExample) := by
    have hopen : IsOpen ({QuasiComponentExample.z n} : Set QuasiComponentExample) :=
      hb.isOpen (hsingle_mem n)
    have hcomp : IsOpen ({QuasiComponentExample.z n} : Set QuasiComponentExample)ᶜ := by
      apply hb.isOpen_iff.mpr
      intro a ha
      cases a with
      | x =>
          refine ⟨insert quasiComponentExampleX (quasiComponentExampleTail (n + 1)),
            hX_mem (n + 1), ?_, ?_⟩
          · simp [quasiComponentExampleX, quasiComponentExampleTail]
          · intro b hb
            simp only [mem_insert_iff] at hb
            rcases hb with rfl | ⟨k, rfl⟩
            · simp [quasiComponentExampleX]
            · simp
              omega
      | y =>
          refine ⟨insert quasiComponentExampleY (quasiComponentExampleTail (n + 1)),
            hY_mem (n + 1), ?_, ?_⟩
          · simp [quasiComponentExampleY, quasiComponentExampleTail]
          · intro b hb
            simp only [mem_insert_iff] at hb
            rcases hb with rfl | ⟨k, rfl⟩
            · simp [quasiComponentExampleY]
            · simp
              omega
      | z m =>
          by_cases hmn : m = n
          · subst m
            simp at ha
          · refine ⟨{QuasiComponentExample.z m}, hsingle_mem m, mem_singleton _,
              singleton_subset_iff.mpr ha⟩
    exact ⟨by simpa using hcomp.isClosed_compl, hopen⟩
  have hnotz {S : Set QuasiComponentExample} (hS : IsPreconnected S)
      (hXS : quasiComponentExampleX ∈ S) (n : ℕ) :
      S ⊆ ({QuasiComponentExample.z n} : Set QuasiComponentExample)ᶜ := by
    exact hS.subset_isClopen (hclopen_z n).compl
      ⟨quasiComponentExampleX, hXS, by simp [quasiComponentExampleX]⟩
  have hnotxy {S : Set QuasiComponentExample} (hS : IsPreconnected S)
      (hXS : quasiComponentExampleX ∈ S) (hYS : quasiComponentExampleY ∈ S) :
      False := by
    have hcover : S ⊆
        insert quasiComponentExampleX (quasiComponentExampleTail 0) ∪
          insert quasiComponentExampleY (quasiComponentExampleTail 0) := by
      intro a ha
      cases a with
      | x =>
          exact Or.inl (by simp [quasiComponentExampleX, quasiComponentExampleTail])
      | y =>
          exact Or.inr (by simp [quasiComponentExampleY, quasiComponentExampleTail])
      | z n =>
          exact Or.inl (Or.inr ⟨n, by simp⟩)
    have hB :
        (S ∩ insert quasiComponentExampleX (quasiComponentExampleTail 0)).Nonempty :=
      ⟨quasiComponentExampleX, hXS,
        by simp [quasiComponentExampleX, quasiComponentExampleTail]⟩
    have hC :
        (S ∩ insert quasiComponentExampleY (quasiComponentExampleTail 0)).Nonempty :=
      ⟨quasiComponentExampleY, hYS,
        by simp [quasiComponentExampleY, quasiComponentExampleTail]⟩
    rcases hS _ _ (hb.isOpen (hX_mem 0)) (hb.isOpen (hY_mem 0)) hcover hB hC with
      ⟨a, haS, haB, haC⟩
    cases a with
    | x => simp [quasiComponentExampleY, quasiComponentExampleTail] at haC
    | y => simp [quasiComponentExampleX, quasiComponentExampleTail] at haB
    | z n => simpa using (hnotz hS hXS n) haS
  have hconn_subset {S : Set QuasiComponentExample} (hS : IsConnected S)
      (hXS : quasiComponentExampleX ∈ S) :
      S ⊆ ({quasiComponentExampleX} : Set QuasiComponentExample) := by
    intro a ha
    cases a with
    | x => simp [quasiComponentExampleX]
    | y => exact False.elim (hnotxy hS.isPreconnected hXS ha)
    | z n => simpa using (hnotz hS.isPreconnected hXS n) ha
  have hcomponent :
      connectedComponent quasiComponentExampleX = {quasiComponentExampleX} := by
    apply Set.Subset.antisymm
    · exact hconn_subset isConnected_connectedComponent mem_connectedComponent
    · exact singleton_subset_iff.mpr mem_connectedComponent
  have hclopen_contains_y {U : Set QuasiComponentExample} (hU : IsClopen U)
      (hXU : quasiComponentExampleX ∈ U) : quasiComponentExampleY ∈ U := by
    by_contra hYU
    have hBX : ∃ n : ℕ,
        insert quasiComponentExampleX (quasiComponentExampleTail n) ⊆ U := by
      rcases hb.exists_subset_of_mem_open hXU hU.isOpen with ⟨V, hV, hXV, hVU⟩
      simp only [quasiComponentExampleBasis, mem_union, mem_range] at hV
      rcases hV with (⟨n, rfl⟩ | ⟨n, rfl⟩) | ⟨n, rfl⟩
      · simp [quasiComponentExampleX] at hXV
      · exact ⟨n, hVU⟩
      · simp [quasiComponentExampleX, quasiComponentExampleTail] at hXV
        cases hXV
    have hCY : ∃ m : ℕ,
        insert quasiComponentExampleY (quasiComponentExampleTail m) ⊆ Uᶜ := by
      have hYU' : quasiComponentExampleY ∈ Uᶜ := by simpa using hYU
      rcases hb.exists_subset_of_mem_open hYU' hU.1.isOpen_compl with ⟨V, hV, hYV, hVU⟩
      simp only [quasiComponentExampleBasis, mem_union, mem_range] at hV
      rcases hV with (⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩
      · simp [quasiComponentExampleY] at hYV
      · simp [quasiComponentExampleY, quasiComponentExampleTail] at hYV
        cases hYV
      · exact ⟨m, hVU⟩
    rcases hBX with ⟨n, hn⟩
    rcases hCY with ⟨m, hm⟩
    have htailU : QuasiComponentExample.z (n + m) ∈ U :=
      hn (by
        simp only [mem_insert_iff]
        right
        refine ⟨m, ?_⟩
        simp)
    have htailUc : QuasiComponentExample.z (n + m) ∈ Uᶜ :=
      hm (by
        simp only [mem_insert_iff]
        right
        refine ⟨n, ?_⟩
        simp [Nat.add_comm])
    exact htailUc htailU
  have hXq : quasiComponentExampleX ∈
      (⋂ Z : {Z : Set QuasiComponentExample //
        IsClopen Z ∧ quasiComponentExampleX ∈ Z}, (Z : Set QuasiComponentExample)) := by
    rw [mem_iInter]
    exact fun Z => Z.property.2
  have hYq : quasiComponentExampleY ∈
      (⋂ Z : {Z : Set QuasiComponentExample //
        IsClopen Z ∧ quasiComponentExampleX ∈ Z}, (Z : Set QuasiComponentExample)) := by
    rw [mem_iInter]
    exact fun Z => hclopen_contains_y Z.property.1 Z.property.2
  have hq_subset :
      (⋂ Z : {Z : Set QuasiComponentExample //
        IsClopen Z ∧ quasiComponentExampleX ∈ Z}, (Z : Set QuasiComponentExample)) ⊆
        {quasiComponentExampleX, quasiComponentExampleY} := by
    intro a ha
    cases a with
    | x => simp [quasiComponentExampleX, quasiComponentExampleY]
    | y => simp [quasiComponentExampleX, quasiComponentExampleY]
    | z n =>
        have hz := (mem_iInter.mp ha)
          ⟨({QuasiComponentExample.z n} : Set QuasiComponentExample)ᶜ,
            ⟨(hclopen_z n).compl, by simp [quasiComponentExampleX]⟩⟩
        simp at hz
  have hpair_subset :
      {quasiComponentExampleX, quasiComponentExampleY} ⊆
        (⋂ Z : {Z : Set QuasiComponentExample //
          IsClopen Z ∧ quasiComponentExampleX ∈ Z}, (Z : Set QuasiComponentExample)) := by
    intro a ha
    simp only [mem_insert_iff, mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hXq
    · exact hYq
  exact ⟨hcomponent, Set.Subset.antisymm hq_subset hpair_subset⟩

/-! ## Quotienting by connected components -/

theorem connected_fibres_quotient_connectedComponents_bijective
    {Y : Type v} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hfib : ∀ y : Y, IsConnected (f ⁻¹' ({y} : Set Y)))
    (hclosed : ∀ T : Set Y,
      IsClosed T ↔ IsClosed (f ⁻¹' T)) :
    Function.Bijective hf.connectedComponentsMap := by
  apply Topology.IsCoinducing.connectedComponentsMap_bijective
    (isQuotientMap_iff_isClosed.mpr ?_).isCoinducing hfib
  exact ⟨fun y => (hfib y).nonempty, hclosed⟩

theorem open_connected_fibres_connectedComponents_bijective
    {Y : Type v} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hopen : IsOpenMap f)
    (hfib : ∀ y : Y, IsConnected (f ⁻¹' ({y} : Set Y))) :
    Function.Bijective hf.connectedComponentsMap := by
  rcases (show Function.Surjective f from fun y => by
    rcases (hfib y).nonempty with ⟨x, hx⟩
    exact ⟨x, hx⟩) with hsurj
  exact (hopen.isQuotientMap hf hsurj).isCoinducing.connectedComponentsMap_bijective hfib

/-! ## A finite-fibre consequence -/

theorem finite_fibre_connectedComponents_at_most
    {Y : Type v} [TopologicalSpace Y] [Nonempty X] [ConnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (hopen : IsOpenMap f)
    (hclosed : IsClosedMap f) {y : Y}
    (hy : (f ⁻¹' ({y} : Set Y)).Finite) :
    ENat.card (ConnectedComponents X) ≤ (f ⁻¹' ({y} : Set Y)).encard := by
  have hfc : Continuous f := hf
  have hfinite : (f ⁻¹' ({y} : Set Y)).Finite := hy
  exact hopen.enatCard_connectedComponents_le_encard_preimage_singleton hclosed y

theorem finite_fibre_connectedComponent_properties
    {Y : Type v} [TopologicalSpace Y] [Nonempty X] [ConnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (hopen : IsOpenMap f)
    (hclosed : IsClosedMap f) {y : Y}
    (hy : (f ⁻¹' ({y} : Set Y)).Finite) (x : X) :
    IsOpen (connectedComponent x) ∧
      IsClosed (connectedComponent x) ∧
      (f '' connectedComponent x).Nonempty ∧
      IsOpen (f '' connectedComponent x) ∧
      IsClosed (f '' connectedComponent x) ∧
      f '' connectedComponent x = (Set.univ : Set Y) := by
  have hfc : Continuous f := hf
  have hfinite : Finite (ConnectedComponents X) :=
    hopen.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace hclosed hy
  have hdisc : DiscreteTopology (ConnectedComponents X) :=
    @Finite.instDiscreteTopology (ConnectedComponents X) _ inferInstance hfinite
  have hcomp_open : IsOpen (connectedComponent x) :=
    (ConnectedComponents.discreteTopology_iff.mp hdisc) x
  refine ⟨hcomp_open, isClosed_connectedComponent,
    ⟨f x, ⟨x, mem_connectedComponent, rfl⟩⟩, hopen _ hcomp_open,
    hclosed _ isClosed_connectedComponent, ?_⟩
  exact IsClopen.eq_univ
    ⟨hclosed _ isClosed_connectedComponent, hopen _ hcomp_open⟩
    ⟨f x, ⟨x, mem_connectedComponent, rfl⟩⟩

/-! ## Totally disconnected spaces -/

theorem totallyDisconnectedSpace_iff_components_singletons :
    TotallyDisconnectedSpace X ↔
      ∀ x : X, connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton

theorem discreteSpace_totallyDisconnected [DiscreteTopology X] :
    TotallyDisconnectedSpace X := by
  infer_instance

theorem rational_subset_real_totallyDisconnected_not_discrete :
    IsTotallyDisconnected (Set.range ((↑) : ℚ → ℝ)) ∧
      ¬ DiscreteTopology (Set.range ((↑) : ℚ → ℝ)) := by
  refine ⟨Rat.isEmbedding_coe_real.isTotallyDisconnected_range.mpr inferInstance, ?_⟩
  intro hdisc
  have hqdisc : DiscreteTopology ℚ :=
    Rat.isEmbedding_coe_real.toHomeomorph.discreteTopology_iff.mpr hdisc
  have hopen : IsOpen ({0} : Set ℚ) := @isOpen_discrete ℚ _ hqdisc _
  have hzero : (0 : ℚ) ∈ interior ({0} : Set ℚ) :=
    mem_interior_iff_mem_nhds.mpr (hopen.mem_nhds (mem_singleton _))
  rw [Rat.interior_compact_eq_empty (isCompact_singleton (x := (0 : ℚ)))] at hzero
  exact hzero

/-! ## The quotient space of connected components -/

theorem connectedComponents_quotientMap :
    IsQuotientMap (ConnectedComponents.mk : X → ConnectedComponents X) := by
  exact ConnectedComponents.isQuotientMap_coe

theorem connectedComponents_map_continuous :
    Continuous (ConnectedComponents.mk : X → ConnectedComponents X) := by
  exact ConnectedComponents.continuous_coe

theorem connectedComponents_totallyDisconnected :
    TotallyDisconnectedSpace (ConnectedComponents X) := by
  infer_instance

theorem continuous_map_factors_through_connectedComponents
    {Y : Type v} [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) :
    ∃ g : ConnectedComponents X → Y,
      Continuous g ∧
        g ∘ ((↑) : X → ConnectedComponents X) = f := by
  exact ⟨hf.connectedComponentsLift, hf.connectedComponentsLift_continuous,
    hf.connectedComponentsLift_comp_coe⟩

/-! ## Locally connected spaces -/

theorem locallyConnectedSpace_iff_connected_neighborhood_basis :
    LocallyConnectedSpace X ↔
      ∀ x : X,
        (𝓝 x).HasBasis
          (fun s : Set X => s ∈ 𝓝 x ∧ IsConnected s) (fun s => s) := by
  rw [locallyConnectedSpace_iff_connected_basis]
  constructor
  · intro h x
    exact (h x).congr
      (fun s => by
        constructor
        · rintro ⟨hs, hp⟩
          exact ⟨hs, ⟨⟨x, mem_of_mem_nhds hs⟩, hp⟩⟩
        · rintro ⟨hs, hc⟩
          exact ⟨hs, hc.2⟩)
      (fun _ _ => rfl)
  · intro h x
    exact (h x).congr
      (fun s => by
        constructor
        · rintro ⟨hs, hc⟩
          exact ⟨hs, hc.2⟩
        · rintro ⟨hs, hp⟩
          exact ⟨hs, ⟨⟨x, mem_of_mem_nhds hs⟩, hp⟩⟩)
      (fun _ _ => rfl)

theorem isLocallyConnected_open [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) : LocallyConnectedSpace U := by
  exact hU.locallyConnectedSpace

theorem isOpen_connectedComponent_of_locallyConnected
    [LocallyConnectedSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  exact isOpen_connectedComponent

theorem isClopen_connectedComponent_of_locallyConnected
    [LocallyConnectedSpace X] (x : X) :
    IsClopen (connectedComponent x) := by
  exact isClopen_connectedComponent

theorem isOpen_connectedComponent_of_open_subset
    [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) (x : X) :
    IsOpen (connectedComponentIn U x) := by
  exact hU.connectedComponentIn

theorem locallyConnected_open_connected_neighborhood_basis
    [LocallyConnectedSpace X] (x : X) :
    (𝓝 x).HasBasis
      (fun s : Set X => IsOpen s ∧ x ∈ s ∧ IsConnected s) (fun s => s) :=
  LocallyConnectedSpace.open_connected_basis x

end ConnectedComponents

end Formalization.Books.Topology.Unit07
