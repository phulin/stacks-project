import Formalization.Books.Topology.Unit08.IrreducibleComponents
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Data.PNat.Basic
import Mathlib.Data.PNat.Interval
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.WithTopology

/-!
# Topology, Chapter 9: Noetherian topological spaces

The source's Noetherian spaces use Mathlib's canonical `NoetherianSpace`
predicate.  Mathlib defines it using the ascending chain condition on opens;
the equivalent well-foundedness statement for closed sets is recorded below
in the source's convention.  Local Noetherianity is not present in Mathlib's
topology API, so it is defined here using neighborhoods and the induced
topology on a subset.
-/

namespace Formalization.Books.Topology.Unit09

open Set Function _root_.Topology TopologicalSpace

universe u v

section NoetherianTopologicalSpaces

variable {X : Type u} [TopologicalSpace X]

/-! ## Definition -/

/- The source's definition of a Noetherian space is Mathlib's canonical
   `TopologicalSpace.NoetherianSpace`; this equivalence exposes its closed-set
   descending-chain formulation. -/
theorem noetherianSpace_iff_descending_closed :
    NoetherianSpace X ↔ WellFoundedLT (Closeds X) :=
  (noetherianSpace_TFAE X).out 0 1

/- A neighborhood in the source is represented by membership in `𝓝 x`, and
   `NoetherianSpace U` uses the subtype topology induced from `X`. -/
class LocallyNoetherianSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_mem_nhds_noetherian :
    ∀ x : X, ∃ U : Set X, U ∈ 𝓝 x ∧ NoetherianSpace U

export LocallyNoetherianSpace (exists_mem_nhds_noetherian)

/-! ## Basic properties of Noetherian spaces -/

/- The first part of the source's lemma is already the canonical Mathlib
   subtype instance. -/
theorem noetherianSpace_subtype [NoetherianSpace X] (U : Set X) :
    NoetherianSpace U := by
  infer_instance

/- The second and third parts are the corresponding Mathlib theorems. -/
theorem noetherianSpace_finite_irreducibleComponents [NoetherianSpace X] :
    (irreducibleComponents X).Finite := by
  exact NoetherianSpace.finite_irreducibleComponents

theorem noetherianSpace_exists_isOpen_nonempty_subset_irreducibleComponent
    [NoetherianSpace X] (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ Z := by
  exact NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ

/-! ## Images and finite unions -/

theorem noetherianSpace_image {Y : Type v} [TopologicalSpace Y]
    [NoetherianSpace X] {f : X → Y} (hf : Continuous f) :
    NoetherianSpace (Set.range f) := by
  exact NoetherianSpace.range f hf

theorem locallyNoetherianSpace_image {Y : Type v} [TopologicalSpace Y]
    [LocallyNoetherianSpace X] {f : X → Y} (hf : Continuous f)
    (hopen : IsOpenMap f) :
    LocallyNoetherianSpace (Set.range f) := by
  constructor
  intro y
  obtain ⟨x, hxy⟩ := y.property
  obtain ⟨U, hU, hUN⟩ := exists_mem_nhds_noetherian x
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hxV⟩
  let g : V → Set.range f := fun z =>
    ⟨f z, ⟨(z : X), rfl⟩⟩
  let _ : NoetherianSpace U := hUN
  let _ : NoetherianSpace V := NoetherianSpace.of_subset hVU
  have hg : Continuous g := by
    dsimp [g]
    exact (hf.comp continuous_subtype_val).subtype_mk _
  have heq : Set.range g = (Subtype.val ⁻¹' (f '' V) : Set (Set.range f)) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(w : X), w.property, rfl⟩
    · intro hz
      rcases hz with ⟨x', hx'V, hxf'⟩
      refine ⟨⟨x', hx'V⟩, ?_⟩
      apply Subtype.ext
      exact hxf'
  refine ⟨Set.range g, ?_, NoetherianSpace.range g hg⟩
  rw [heq]
  apply (hopen V hVopen).preimage continuous_subtype_val |>.mem_nhds
  exact ⟨x, hxV, hxy⟩

theorem noetherianSpace_iUnion_of_finite {ι : Type v} [Finite ι]
    (U : ι → Set X) (hU : ∀ i, NoetherianSpace (U i)) :
    NoetherianSpace (⋃ i, U i) := by
  let _ : ∀ i, NoetherianSpace (U i) := hU
  exact NoetherianSpace.iUnion U

/-! ## Closed points and the source's example -/

theorem exists_closed_point_of_noetherian_t0
    [NoetherianSpace X] [T0Space X] [Nonempty X] :
    ∃ x : X, IsClosed ({x} : Set X) := by
  obtain ⟨x, _, hx⟩ :=
    IsClosed.exists_closed_singleton (S := (Set.univ : Set X)) isClosed_univ univ_nonempty
  exact ⟨x, hx⟩

/- The source uses the positive natural numbers.  `ℕ+` is the canonical
   positive-natural carrier, and `WithTopology` lets this example carry the
   source topology without changing the usual topology on `ℕ+` elsewhere. -/
def initialSegmentOpenSets : Set (Set ℕ+) :=
  ({∅, Set.univ} : Set (Set ℕ+)) ∪
    Set.range (fun n : ℕ+ => Set.Iic n)

@[instance_reducible]
def initialSegmentTopology : TopologicalSpace ℕ+ :=
  TopologicalSpace.generateFrom initialSegmentOpenSets

abbrev InitialSegmentSpace := WithTopology ℕ+ initialSegmentTopology

theorem initialSegmentSpace_isOpen_iff {U : Set InitialSegmentSpace} :
    IsOpen U ↔
      U = ∅ ∨ U = Set.univ ∨
        ∃ n : ℕ+, U =
          ((WithTopology.equiv ℕ+ initialSegmentTopology) ⁻¹' (Set.Iic n)) := by
  classical
  let e : InitialSegmentSpace ≃ ℕ+ :=
    WithTopology.equiv ℕ+ initialSegmentTopology
  rw [WithTopology.isOpen_iff]
  change TopologicalSpace.GenerateOpen initialSegmentOpenSets (e.symm ⁻¹' U) ↔
    U = ∅ ∨ U = Set.univ ∨ ∃ n : ℕ+, U = e ⁻¹' Set.Iic n
  have hunion :
      ∀ (S : Set (Set ℕ+)),
        (∀ s ∈ S, s = ∅ ∨ s = Set.univ ∨ ∃ n : ℕ+, s = Set.Iic n) →
          ⋃₀ S = ∅ ∨ ⋃₀ S = Set.univ ∨ ∃ n : ℕ+, ⋃₀ S = Set.Iic n := by
    intro S hS
    by_cases hUniv : Set.univ ∈ S
    · exact Or.inr (Or.inl (Set.sUnion_eq_univ_iff.mpr
        (fun x => ⟨Set.univ, hUniv, Set.mem_univ x⟩)))
    by_cases hUnbounded : ∀ n : ℕ+, ∃ x ∈ ⋃₀ S, n < x
    · right
      left
      apply Set.eq_univ_iff_forall.mpr
      intro x
      obtain ⟨y, hy, hxy⟩ := hUnbounded x
      rcases Set.mem_sUnion.mp hy with ⟨s, hs, hys⟩
      rcases hS s hs with hs0 | hsu | ⟨n, hn⟩
      · exact (hs0 ▸ hys).elim
      · have : Set.univ ∈ S := hsu ▸ hs
        exact (hUniv this).elim
      · have hs' : Set.Iic n ∈ S := hn ▸ hs
        have hys' : y ∈ Set.Iic n := hn ▸ hys
        exact Set.mem_sUnion.mpr ⟨Set.Iic n, hs', le_trans hxy.le hys'⟩
    · push Not at hUnbounded
      obtain ⟨n0, hn0⟩ := hUnbounded
      by_cases hne : (⋃₀ S).Nonempty
      · let A : Set ℕ+ := {n | Set.Iic n ∈ S}
        have hAfin : A.Finite := by
          apply (Set.finite_Iic n0).subset
          intro n hn
          exact hn0 n (Set.mem_sUnion.mpr
            ⟨Set.Iic n, hn, by simp⟩)
        have hAnon : A.Nonempty := by
          rcases hne with ⟨x, hx⟩
          rcases Set.mem_sUnion.mp hx with ⟨s, hs, hxs⟩
          rcases hS s hs with hs0 | hsu | ⟨n, hn⟩
          · exact (hs0 ▸ hxs).elim
          · have : Set.univ ∈ S := hsu ▸ hs
            exact (hUniv this).elim
          · have hs' : Set.Iic n ∈ S := hn ▸ hs
            exact ⟨n, hs'⟩
        obtain ⟨m, hmA, hmax⟩ := Set.exists_max_image A id hAfin hAnon
        right
        right
        refine ⟨m, ?_⟩
        apply Set.Subset.antisymm
        · intro x hx
          rcases Set.mem_sUnion.mp hx with ⟨s, hs, hxs⟩
          rcases hS s hs with hs0 | hsu | ⟨n, hn⟩
          · exact (hs0 ▸ hxs).elim
          · have : Set.univ ∈ S := hsu ▸ hs
            exact (hUniv this).elim
          · subst s
            have hnm : n ≤ m := by
              simpa using hmax n (show n ∈ A from hs)
            exact le_trans hxs hnm
        · intro x hx
          exact Set.mem_sUnion.mpr ⟨Set.Iic m, hmA, hx⟩
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)
  have hclass :
      ∀ {V : Set ℕ+}, TopologicalSpace.GenerateOpen initialSegmentOpenSets V →
        V = ∅ ∨ V = Set.univ ∨ ∃ n : ℕ+, V = Set.Iic n := by
    intro V hV
    induction hV with
    | basic s hs =>
        simp [initialSegmentOpenSets] at hs
        rcases hs with hs | ⟨n, rfl⟩
        · rcases hs with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨n, rfl⟩)
    | univ => exact Or.inr (Or.inl rfl)
    | inter s t hs ht ihs iht =>
        rcases ihs with rfl | rfl | ⟨n, rfl⟩
        · exact Or.inl (by simp)
        · simpa using iht
        · rcases iht with rfl | rfl | ⟨m, rfl⟩
          · exact Or.inl (by simp)
          · exact Or.inr (Or.inr ⟨n, by simp⟩)
          · refine Or.inr (Or.inr ⟨min n m, ?_⟩)
            ext x
            simp
    | sUnion S hS ih =>
        exact hunion S (fun s hs => ih s hs)
  constructor
  · intro h
    have hUeq : U = e ⁻¹' (e.symm ⁻¹' U) := by
      ext x
      simp
    rcases hclass h with h0 | hu | ⟨n, hn⟩
    · left
      calc
        U = e ⁻¹' (e.symm ⁻¹' U) := hUeq
        _ = ∅ := by rw [h0]; simp
    · right
      left
      calc
        U = e ⁻¹' (e.symm ⁻¹' U) := hUeq
        _ = Set.univ := by rw [hu]; simp
    · right
      right
      refine ⟨n, ?_⟩
      calc
        U = e ⁻¹' (e.symm ⁻¹' U) := hUeq
        _ = e ⁻¹' Set.Iic n := by rw [hn]
  · rintro (rfl | rfl | ⟨n, rfl⟩)
    · exact TopologicalSpace.GenerateOpen.basic _ (by simp [initialSegmentOpenSets])
    · exact TopologicalSpace.GenerateOpen.univ
    · have he : e.symm ⁻¹' (e ⁻¹' Set.Iic n) = Set.Iic n := by
        ext x
        simp
      rw [he]
      exact TopologicalSpace.GenerateOpen.basic _ (by simp [initialSegmentOpenSets])

theorem initialSegmentSpace_locallyNoetherian :
    LocallyNoetherianSpace InitialSegmentSpace := by
  let e : InitialSegmentSpace ≃ ℕ+ :=
    WithTopology.equiv ℕ+ initialSegmentTopology
  constructor
  intro x
  refine ⟨e ⁻¹' Set.Iic (e x), ?_, ?_⟩
  · have hopen : IsOpen (e ⁻¹' Set.Iic (e x)) :=
      initialSegmentSpace_isOpen_iff.mpr (Or.inr (Or.inr ⟨e x, rfl⟩))
    exact hopen.mem_nhds (by simp)
  · have hfin : (Set.Iic (e x)).Finite := Set.finite_Iic _
    have hpre : (e ⁻¹' Set.Iic (e x)).Finite :=
      hfin.preimage e.injective.injOn
    let _ : Finite (e ⁻¹' Set.Iic (e x) : Set InitialSegmentSpace) :=
      Set.finite_coe_iff.mpr hpre
    exact (inferInstance : NoetherianSpace (e ⁻¹' Set.Iic (e x)))

theorem initialSegmentSpace_has_no_closed_points :
    ∀ x : InitialSegmentSpace, ¬ IsClosed ({x} : Set InitialSegmentSpace) := by
  intro x hx
  let e : InitialSegmentSpace ≃ ℕ+ :=
    WithTopology.equiv ℕ+ initialSegmentTopology
  have hcomp : IsOpen ({x}ᶜ : Set InitialSegmentSpace) := hx.isOpen_compl
  rcases initialSegmentSpace_isOpen_iff.mp hcomp with h0 | hu | ⟨n, hn⟩
  · have hne : e.symm (e x + 1) ≠ x := by
      intro h
      have hh := congrArg e h
      have heq : e x + 1 = e x := by simpa using hh
      have hlt : e x < e x + 1 := by
        simpa [PNat.add_one] using PNat.lt_succ_self (e x)
      exact (ne_of_gt hlt) heq
    have hy : e.symm (e x + 1) ∈ ({x}ᶜ : Set InitialSegmentSpace) := by
      simp [hne]
    rw [h0] at hy
    exact hy
  · have hxnot : x ∉ ({x}ᶜ : Set InitialSegmentSpace) := by simp
    rw [hu] at hxnot
    exact hxnot (Set.mem_univ x)
  · have hlt1 : n < n + 1 := by
      simpa [PNat.add_one] using PNat.lt_succ_self n
    have hlt2 : n + 1 < (n + 1) + 1 := by
      exact PNat.lt_succ_self (n + 1)
    have hnot1 : e.symm (n + 1) ∉ ({x}ᶜ : Set InitialSegmentSpace) := by
      rw [hn]
      simpa [e] using (not_le_of_gt hlt1)
    have hnot2 :
        e.symm ((n + 1) + 1) ∉ ({x}ᶜ : Set InitialSegmentSpace) := by
      rw [hn]
      simpa [e] using (not_le_of_gt (lt_trans hlt1 hlt2))
    have h1 : e.symm (n + 1) = x := by simpa using hnot1
    have h2 : e.symm ((n + 1) + 1) = x := by simpa using hnot2
    have heq1 : n + 1 = e x := by
      simpa using congrArg e h1
    have heq2 : (n + 1) + 1 = e x := by
      simpa using congrArg e h2
    exact (ne_of_lt hlt2) (heq1.trans heq2.symm)

/- The last sentence of the source refers to the later scheme-theoretic
   closed-point lemma.  Mathlib's canonical interface for that source notion
   is used here to state the cross-reference without importing a later project
   chapter. -/
theorem initialSegmentSpace_not_underlying_locallyNoetherian_scheme :
    ¬ ∃ S : AlgebraicGeometry.Scheme,
      AlgebraicGeometry.IsLocallyNoetherian S ∧
        Nonempty (S ≃ₜ InitialSegmentSpace) := by
  sorry

/-! ## Local connectedness -/

theorem locallyConnectedSpace_of_locallyNoetherian
    [LocallyNoetherianSpace X] : LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x E hE
  obtain ⟨U, hUx, hUN⟩ := exists_mem_nhds_noetherian x
  let V : Set X := E ∩ U
  have hVx : V ∈ 𝓝 x := by
    dsimp [V]
    exact Filter.inter_mem hE hUx
  have hVN : NoetherianSpace V := by
    let _ : NoetherianSpace U := hUN
    apply NoetherianSpace.of_subset (W := U) (V := V)
    intro y hy
    exact hy.2
  let _ : NoetherianSpace V := hVN
  let xV : V := ⟨x, ⟨mem_of_mem_nhds hE, mem_of_mem_nhds hUx⟩⟩
  let I : Set (Set V) :=
    {C | C ∈ irreducibleComponents V ∧ xV ∈ C}
  let J : Set (Set V) :=
    irreducibleComponents V \ {C | xV ∈ C}
  let C0 : Set V := ⋃₀ I
  have hcomponents : (irreducibleComponents V).Finite :=
    noetherianSpace_finite_irreducibleComponents
  have hIpre : ∀ C ∈ I, IsPreconnected C := by
    intro C hC
    exact (hC.1.1.isConnected.isPreconnected)
  have hIcommon : ∀ C ∈ I, xV ∈ C := by
    intro C hC
    exact hC.2
  have hC0pre : IsPreconnected C0 := by
    dsimp [C0]
    exact isPreconnected_sUnion xV I hIcommon hIpre
  have hxI : xV ∈ C0 := by
    apply Set.mem_sUnion.mpr
    refine ⟨irreducibleComponent xV, ?_, mem_irreducibleComponent⟩
    exact ⟨irreducibleComponent_mem_irreducibleComponents xV, mem_irreducibleComponent⟩
  have hJclosed : IsClosed (⋃₀ J) := by
    change IsClosed (⋃₀ (irreducibleComponents V \ {C | xV ∈ C}))
    rw [Set.sUnion_eq_biUnion]
    apply hcomponents.sdiff.isClosed_biUnion
    intro C hC
    exact isClosed_of_mem_irreducibleComponents C hC.1
  let O0 : Set V := (⋃₀ J)ᶜ
  have hO0open : IsOpen O0 := by
    dsimp [O0]
    exact hJclosed.isOpen_compl
  have hxO0 : xV ∈ O0 := by
    dsimp [O0]
    intro hxJ
    rcases Set.mem_sUnion.mp hxJ with ⟨C, hCJ, hxC⟩
    exact hCJ.2 hxC
  have hO0sub : O0 ⊆ C0 := by
    intro z hz
    have hzcover : z ∈ ⋃₀ (irreducibleComponents V) := by
      rw [sUnion_irreducibleComponents]
      trivial
    rcases Set.mem_sUnion.mp hzcover with ⟨C, hC, hzC⟩
    by_cases hxC : xV ∈ C
    · exact Set.mem_sUnion.mpr ⟨C, ⟨hC, hxC⟩, hzC⟩
    · exfalso
      exact hz (Set.mem_sUnion.mpr ⟨C, ⟨hC, hxC⟩, hzC⟩)
  let C : Set X := (Subtype.val : V → X) '' C0
  have hCpre : IsPreconnected C := by
    dsimp [C]
    exact hC0pre.image _ continuous_subtype_val.continuousOn
  have hCsub : C ⊆ E := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (show (z : X) ∈ E ∩ U from z.property).1
  have hCnhds : C ∈ 𝓝 x := by
    have hO0nh : O0 ∈ 𝓝 xV := hO0open.mem_nhds hxO0
    rcases (mem_nhds_subtype V xV O0).mp hO0nh with ⟨W, hW, hWO⟩
    apply Filter.mem_of_superset (Filter.inter_mem hW hVx)
    intro y hy
    exact ⟨⟨y, hy.2⟩, hO0sub (hWO hy.1), rfl⟩
  exact ⟨C, hCnhds, hCpre, hCsub⟩

end NoetherianTopologicalSpaces

end Formalization.Books.Topology.Unit09
