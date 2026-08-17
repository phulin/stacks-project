import Formalization.Books.Topology.Unit05.Bases
import Formalization.Books.Topology.Unit09.NoetherianSpaces
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructible
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Spectral.Prespectral

/-!
# Topology, Chapter 12: Quasi-compact spaces and maps

The source's quasi-compact spaces are represented by Mathlib's `CompactSpace`
class and `IsCompact` predicate, which do not include a Hausdorff assumption.
The source's quasi-compact maps are Mathlib's `IsSpectralMap`, and its
retrocompact subsets are Mathlib's `IsRetrocompact`.  The compact-open basis
and finite-intersection hypotheses are likewise represented by the canonical
`PrespectralSpace` and `QuasiSeparatedSpace` interfaces.
-/

namespace Formalization.Books.Topology.Unit12

open Set Function _root_.Topology TopologicalSpace

universe u v w

section QuasiCompactSpacesAndMaps

variable {X : Type u} [TopologicalSpace X]

/-!
The first source definition is Mathlib's `CompactSpace X`, equivalently
`IsCompact (Set.univ : Set X)`.  The source's map definition is exactly
`IsSpectralMap`: continuity together with compactness of inverse images of
compact opens.  The source's subset definition is Mathlib's `IsRetrocompact`,
whose canonical API also records the equivalent subtype-map formulation.
-/

theorem compactSpace_iff_isCompact_univ :
    CompactSpace X ↔ IsCompact (Set.univ : Set X) := by
  exact isCompact_univ_iff.symm

theorem isSpectralMap_iff {Y : Type v} [TopologicalSpace Y] {f : X → Y} :
    IsSpectralMap f ↔
      Continuous f ∧
        ∀ ⦃V : Set Y⦄, IsOpen V → IsCompact V → IsCompact (f ⁻¹' V) := by
  exact ⟨fun h => ⟨h.continuous, h.isCompact_preimage_of_isOpen⟩,
    fun h => ⟨h.1, h.2⟩⟩

theorem compactSpace_iff_finite_subcover :
    CompactSpace X ↔
      ∀ {ι : Type u} (U : ι → Set X),
        (∀ i, IsOpen (U i)) →
          (⋃ i, U i) = (Set.univ : Set X) →
            ∃ s : Finset ι, (⋃ i ∈ s, U i) = (Set.univ : Set X) := by
  sorry

/-! ### Composition and closed subsets -/

theorem isSpectralMap_comp {Y : Type v} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : IsSpectralMap f) (hg : IsSpectralMap g) :
    IsSpectralMap (g ∘ f) := by
  exact hg.comp hf

theorem isCompact_of_isClosed [CompactSpace X] {E : Set X} (hE : IsClosed E) :
    IsCompact E := by
  exact hE.isCompact

/-! ### Compact subsets of Hausdorff spaces -/

theorem isClosed_of_isCompact [T2Space X] {E : Set X} (hE : IsCompact E) :
    IsClosed E := by
  exact hE.isClosed

theorem separatedNhds_of_disjoint_isCompact [T2Space X]
    {E₁ E₂ : Set X} (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂)
    (hdisj : Disjoint E₁ E₂) :
    SeparatedNhds E₁ E₂ := by
  exact SeparatedNhds.of_isCompact_isCompact hE₁ hE₂ hdisj

theorem isClosed_iff_isCompact_of_compactSpace [CompactSpace X] [T2Space X]
    {E : Set X} :
    IsClosed E ↔ IsCompact E := by
  exact ⟨fun h => h.isCompact, fun h => h.isClosed⟩

/-! ### The finite-intersection characterization -/

theorem nonempty_iInter_of_finite_iInter_nonempty [CompactSpace X]
    {ι : Type v} {Z : ι → Set X}
    (hclosed : ∀ i, IsClosed (Z i))
    (hfinite : ∀ s : Finset ι, (⋂ i ∈ s, Z i).Nonempty) :
    (⋂ i, Z i).Nonempty := by
  exact CompactSpace.iInter_nonempty hclosed hfinite

/-! ### Images and closed points -/

theorem isCompact_range_of_compactSpace {Y : Type v} [TopologicalSpace Y]
    [CompactSpace X] {f : X → Y} (hf : Continuous f) :
    IsCompact (Set.range f) := by
  exact isCompact_range hf

theorem isRetrocompact_range_of_isSpectralMap {Y : Type v} [TopologicalSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) :
    IsRetrocompact (Set.range f) := by
  intro U hUcomp hUopen
  rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  exact (hf.isCompact_preimage_of_isOpen hUopen hUcomp).image hf.continuous

theorem exists_closed_point [CompactSpace X] [T0Space X] [Nonempty X] :
    ∃ x : X, IsClosed ({x} : Set X) := by
  obtain ⟨x, _, hxc⟩ :=
    IsClosed.exists_closed_singleton (S := (Set.univ : Set X)) isClosed_univ
      Set.univ_nonempty
  exact ⟨x, hxc⟩

theorem isCompact_closedPoints [CompactSpace X] [T0Space X] :
    IsCompact (closedPoints X) := by
  apply isCompact_of_finite_subcover
  intro ι U hU hcover
  have hcover_univ : (⋃ i, U i) = (Set.univ : Set X) := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hne : ((⋃ i, U i)ᶜ : Set X).Nonempty :=
      ⟨x, by simpa only [mem_compl_iff] using hx⟩
    obtain ⟨z, hz, hzc⟩ := IsClosed.exists_closed_singleton
      (S := ((⋃ i, U i)ᶜ : Set X)) (isOpen_iUnion hU).isClosed_compl hne
    have hzU : z ∈ ⋃ i, U i := hcover (mem_closedPoints_iff.mpr hzc)
    exact hz hzU
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (by rw [hcover_univ])
  exact ⟨s, fun x hx => hs (Set.mem_univ x)⟩

/-! ### Connected components -/

theorem connectedComponent_eq_iInter_isClopen_of_compact_prespectral
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] (x : X) :
    connectedComponent x =
      ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X) := by
  let S : Set X :=
    ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X)
  change connectedComponent x = S
  have hSclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_iInter fun s => s.2.1.1
  have hSx : x ∈ S := by
    dsimp [S]
    exact mem_iInter.2 fun s => s.2.2
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  refine IsPreconnected.subset_connectedComponent ?_ hSx
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hSclosed]
  intro a b ha hb hSab hab
  have hAcompact : IsCompact (S ∩ a) := (hSclosed.inter ha).isCompact
  have hBcompact : IsCompact (S ∩ b) := (hSclosed.inter hb).isCompact
  have hAcomplement : S ∩ a ⊆ bᶜ := by
    intro y hy hby
    exact (Set.disjoint_left.1 hab hy.2) hby
  have hBcomplement : S ∩ b ⊆ aᶜ := by
    intro y hy hay
    exact (Set.disjoint_left.1 hab hay) hy.2
  obtain ⟨U, hUcompact, hUopen, hAU, hUb⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hAcompact hb.isOpen_compl
      hAcomplement
  obtain ⟨V, hVcompact, hVopen, hBV, hVa⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hBcompact ha.isOpen_compl
      hBcomplement
  have hSUV : S ∩ U ∩ V = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases hSab hy.1.1 with hya | hyb
    · exact hVa hy.2 hya
    · exact hUb hy.1.2 hyb
  have hK1empty : (U ∩ V) ∩ S = ∅ := by
    simpa [inter_assoc, inter_left_comm, inter_comm] using hSUV
  have hK2empty : (U ∪ V)ᶜ ∩ S = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases hSab hy.2 with hya | hyb
    · exact hy.1 (Or.inl (hAU ⟨hy.2, hya⟩))
    · exact hy.1 (Or.inr (hBV ⟨hy.2, hyb⟩))
  have hK1 : IsCompact (U ∩ V) :=
    QuasiSeparatedSpace.inter_isCompact U V hUopen hUcompact hVopen hVcompact
  have hK2 : IsCompact (U ∪ V)ᶜ :=
    (hUopen.union hVopen).isClosed_compl.isCompact
  obtain ⟨F₁, hF₁⟩ := hK1.elim_finite_subfamily_closed
    (fun s : {s : Set X // IsClopen s ∧ x ∈ s} => (s : Set X))
    (fun s => s.2.1.1) (by simpa [S] using hK1empty)
  obtain ⟨F₂, hF₂⟩ := hK2.elim_finite_subfamily_closed
    (fun s : {s : Set X // IsClopen s ∧ x ∈ s} => (s : Set X))
    (fun s => s.2.1.1) (by simpa [S] using hK2empty)
  let W₁ : Set X := ⋂ s ∈ F₁, (s : Set X)
  let W₂ : Set X := ⋂ s ∈ F₂, (s : Set X)
  have hW₁ : IsClopen W₁ := by
    dsimp [W₁]
    exact isClopen_biInter_finset fun s hs => s.2.1
  have hW₂ : IsClopen W₂ := by
    dsimp [W₂]
    exact isClopen_biInter_finset fun s hs => s.2.1
  have hxW₁ : x ∈ W₁ := by
    dsimp [W₁]
    exact mem_iInter₂.2 fun s hs => s.2.2
  have hxW₂ : x ∈ W₂ := by
    dsimp [W₂]
    exact mem_iInter₂.2 fun s hs => s.2.2
  have hW₁disj : W₁ ∩ U ∩ V = ∅ := by
    dsimp [W₁]
    simpa [inter_assoc, inter_left_comm, inter_comm] using hF₁
  have hW₂subset : W₂ ⊆ U ∪ V := by
    intro y hy
    by_contra hyUV
    have hy' : y ∈ (U ∪ V)ᶜ ∩ W₂ :=
      ⟨by simpa only [mem_compl_iff] using hyUV, hy⟩
    rw [hF₂] at hy'
    exact hy'.elim
  let W : Set X := W₁ ∩ W₂
  have hW : IsClopen W := hW₁.inter hW₂
  have hxW : x ∈ W := ⟨hxW₁, hxW₂⟩
  have hWsubset : W ⊆ U ∪ V := fun y hy => hW₂subset hy.2
  have hWdisj : W ∩ U ∩ V = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hy' : y ∈ W₁ ∩ U ∩ V :=
      ⟨⟨hy.1.1.1, hy.1.2⟩, hy.2⟩
    rw [hW₁disj] at hy'
    exact hy'.elim
  have hWU : IsClopen (W ∩ U) :=
    isClopen_inter_of_disjoint_cover_clopen' hW hWsubset hUopen hVopen hWdisj
  have hWV : IsClopen (W ∩ V) := by
    apply isClopen_inter_of_disjoint_cover_clopen' (a := V) (b := U) hW
      (by simpa [union_comm] using hWsubset)
      hVopen hUopen
    simpa [inter_assoc, inter_left_comm, inter_comm] using hWdisj
  rcases hSab hSx with hxa | hxb
  · have hxU : x ∈ U := hAU ⟨hSx, hxa⟩
    have hSsubsetWU : S ⊆ W ∩ U := by
      intro y hy
      exact mem_iInter.1 hy ⟨W ∩ U, hWU, ⟨hxW, hxU⟩⟩
    refine Or.inl ?_
    intro y hy
    by_contra hya
    exact hUb (hSsubsetWU hy).2 ((hSab hy).resolve_left hya)
  · have hxV : x ∈ V := hBV ⟨hSx, hxb⟩
    have hSsubsetWV : S ⊆ W ∩ V := by
      intro y hy
      exact mem_iInter.1 hy ⟨W ∩ V, hWV, ⟨hxW, hxV⟩⟩
    refine Or.inr ?_
    intro y hy
    by_contra hyb
    exact hVa (hSsubsetWV hy).2 ((hSab hy).resolve_right hyb)

theorem connectedComponent_eq_iInter_isClopen_of_compact_Hausdorff
    [CompactSpace X] [T2Space X] (x : X) :
    connectedComponent x =
      ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X) := by
  exact connectedComponent_eq_iInter_isClopen x

/-! ### Closed unions of connected components -/

/-- A subset which is an intersection of open-and-closed subsets. -/
def IsIntersectionOfClopens (T : Set X) : Prop :=
  ∃ S : Set (Set X), T = ⋂₀ S ∧ ∀ U ∈ S, IsClopen U

/-- A subset which is a union of connected components. -/
def IsUnionOfConnectedComponents (T : Set X) : Prop :=
  ∃ S : Set X, T = ⋃ x ∈ S, connectedComponent x

theorem isIntersectionOfClopens_iff_isClosed_isUnionOfConnectedComponents
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] {T : Set X} :
    IsIntersectionOfClopens T ↔
    IsClosed T ∧ IsUnionOfConnectedComponents T := by
  constructor
  · rintro ⟨S, hTS, hS⟩
    refine ⟨?_, ?_⟩
    · rw [hTS]
      exact isClosed_sInter fun U hU => (hS U hU).isClosed
    · refine ⟨⋂₀ S, ?_⟩
      rw [hTS]
      ext y
      constructor
      · intro hy
        exact mem_iUnion₂_of_mem hy mem_connectedComponent
      · intro hy
        rcases mem_iUnion₂.1 hy with ⟨z, hz, hyz⟩
        exact subset_sInter (fun U hU =>
          (hS U hU).connectedComponent_subset (mem_sInter.1 hz U hU)) hyz
  · rintro ⟨hTclosed, hTunion⟩
    classical
    let R : Set (Set X) := {U | IsClopen U ∧ T ⊆ U}
    have hTcompact : IsCompact T := hTclosed.isCompact
    obtain ⟨A, hTA⟩ := hTunion
    have hcomponent_disjoint : ∀ x, x ∉ T →
        Disjoint (connectedComponent x) T := by
      intro x hx
      apply Set.disjoint_left.2
      intro y hycomp hyT
      rw [hTA] at hyT
      rcases mem_iUnion₂.1 hyT with ⟨z, hz, hyz⟩
      have hcomp : connectedComponent x = connectedComponent z :=
        (connectedComponent_eq hycomp).trans (connectedComponent_eq hyz).symm
      apply hx
      rw [hTA]
      have hxz : x ∈ connectedComponent z := by
        rw [← hcomp]
        exact mem_connectedComponent
      exact mem_iUnion₂_of_mem hz hxz
    have hseparate : ∀ x, x ∉ T →
        ∃ U, IsClopen U ∧ T ⊆ U ∧ x ∉ U := by
      intro x hx
      have hcomponent :=
        connectedComponent_eq_iInter_isClopen_of_compact_prespectral x
      have hempty : T ∩
          (⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X)) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hycomp : y ∈ connectedComponent x := by
          rw [hcomponent]
          exact hy.2
        exact Set.disjoint_left.1 (hcomponent_disjoint x hx) hycomp hy.1
      obtain ⟨F, hF⟩ := hTcompact.elim_finite_subfamily_closed
        (fun s : {s : Set X // IsClopen s ∧ x ∈ s} => (s : Set X))
        (fun s => s.2.1.1) hempty
      let W : Set X := ⋂ s ∈ F, (s : Set X)
      have hW : IsClopen W := by
        dsimp [W]
        exact isClopen_biInter_finset fun s hs => s.2.1
      have hxW : x ∈ W := by
        dsimp [W]
        exact mem_iInter₂.2 fun s hs => s.2.2
      have hTdisj : T ∩ W = ∅ := by
        dsimp [W]
        exact hF
      refine ⟨Wᶜ, hW.compl, ?_, ?_⟩
      · intro y hyT hyW
        have hyempty : y ∈ T ∩ W := ⟨hyT, hyW⟩
        rw [hTdisj] at hyempty
        exact hyempty.elim
      · intro hxWc
        exact hxWc hxW
    have hT_sInter : T = ⋂₀ R := by
      apply Subset.antisymm
      · exact subset_sInter fun U hU => hU.2
      · intro x hxR
        by_contra hxT
        obtain ⟨U, hUclopen, hTU, hxU⟩ := hseparate x hxT
        exact hxU (mem_sInter.1 hxR U ⟨hUclopen, hTU⟩)
    refine ⟨R, hT_sInter, ?_⟩
    intro U hU
    exact hU.1

/-! ### Noetherian spaces -/

theorem noetherianSpace_isCompactSpace [NoetherianSpace X] : CompactSpace X := by
  infer_instance

theorem isRetrocompact_of_noetherianSpace [NoetherianSpace X] (Z : Set X) :
    IsRetrocompact Z := by
  exact fun _ _ _ => NoetherianSpace.isCompact _

theorem noetherianSpace_of_compactSpace_of_locallyNoetherianSpace
    [CompactSpace X]
    [Formalization.Books.Topology.Unit09.LocallyNoetherianSpace X] :
    NoetherianSpace X := by
  choose U hU hUN using fun x : X =>
    Formalization.Books.Topology.Unit09.exists_mem_nhds_noetherian x
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  let _ : ∀ x : X, NoetherianSpace (U x) := hUN
  have hNoeth : NoetherianSpace (⋃ x : s, U x) :=
    NoetherianSpace.iUnion (fun x : s => U x)
  have hs' : (⋃ x ∈ s, U x) = (Set.univ : Set X) := by
    simpa using hs
  have hunion : (⋃ x : s, U x) = ⋃ x ∈ s, U x := by
    ext y
    constructor
    · intro hy
      rcases mem_iUnion.1 hy with ⟨x, hy⟩
      exact mem_iUnion₂_of_mem x.property hy
    · intro hy
      rcases mem_iUnion₂.1 hy with ⟨x, hxs, hy⟩
      exact mem_iUnion.2 ⟨⟨x, hxs⟩, hy⟩
  apply TopologicalSpace.noetherian_univ_iff.mp
  rw [← hs']
  rw [← hunion]
  exact hNoeth

/-! ### Alexander subbase theorem -/

theorem compactSpace_of_isSubbasis
    {𝔅 : Set (Set X)}
    (h𝔅 : Formalization.Books.Topology.Unit05.IsSubbasis 𝔅)
    (hcover : ∀ P : Set (Set X), P ⊆ 𝔅 →
      ⋃₀ P = (Set.univ : Set X) →
        ∃ Q : Set (Set X), Q ⊆ P ∧ Q.Finite ∧ ⋃₀ Q = (Set.univ : Set X)) :
    CompactSpace X := by
  change @TopologicalSpace.IsTopologicalBasis X _
    (Formalization.Books.Topology.Unit05.finiteIntersections 𝔅) at h𝔅
  have hgen : @TopologicalSpace.IsTopologicalBasis X
      (TopologicalSpace.generateFrom 𝔅)
      (Formalization.Books.Topology.Unit05.finiteIntersections 𝔅) := by
    exact TopologicalSpace.isTopologicalBasis_of_subbasis
      (t := TopologicalSpace.generateFrom 𝔅) (s := 𝔅) rfl
  have hT : (inferInstance : TopologicalSpace X) =
      TopologicalSpace.generateFrom 𝔅 :=
    (TopologicalSpace.IsTopologicalBasis.eq_generateFrom (t := inferInstance) h𝔅).trans
      (TopologicalSpace.IsTopologicalBasis.eq_generateFrom
        (t := TopologicalSpace.generateFrom 𝔅) hgen).symm
  exact compactSpace_generateFrom hT hcover

end QuasiCompactSpacesAndMaps

end Formalization.Books.Topology.Unit12
