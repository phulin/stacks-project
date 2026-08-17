import Formalization.Books.Topology.Unit15.ConstructibleSets
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Maps.Basic

/-!
# Topology, Chapter 21: Nowhere dense sets

The source's interior and nowhere-dense predicates are Mathlib's canonical
`interior` and `IsNowhereDense`.  Relative statements are expressed in the
subtype topology, and a map that is a homeomorphism onto a closed subspace is
represented by `IsClosedEmbedding`.
-/

namespace Formalization.Books.Topology.Unit21

open Set Function _root_.Topology TopologicalSpace

universe u v

section NowhereDenseSets

variable {X : Type u} [TopologicalSpace X]

/-!
The first item of the source definition is already the canonical `interior`.
Its largest-open-subset property is provided by Mathlib's
`interior_maximal`.  The second item is exactly Mathlib's `IsNowhereDense`,
defined by `interior (closure T) = ∅`; no parallel local definitions are
introduced.
-/

/-! ### Finite unions -/

theorem isNowhereDense_sUnion {S : Set (Set X)} (hS : S.Finite)
    (hT : ∀ T ∈ S, IsNowhereDense T) :
    IsNowhereDense (⋃₀ S) := by
  revert hT
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      intro hT
      simp
  | insert T S ih =>
      intro hT
      simp only [forall_mem_insert, sUnion_insert] at *
      rw [IsNowhereDense, closure_union,
        interior_union_isClosed_of_interior_empty isClosed_closure (ih hT.2)]
      exact hT.1

/-! ### Open subspaces and open coverings -/

theorem isNowhereDense_of_isOpen_subspace
    {U : Set X} (hU : IsOpen U) {T : Set X} (hTU : T ⊆ U)
    (hT : IsNowhereDense ((Subtype.val : U → X) ⁻¹' T)) :
    IsNowhereDense T := by
  have himage : (Subtype.val : U → X) '' ((Subtype.val : U → X) ⁻¹' T) = T :=
    Set.image_preimage_eq_of_subset (by
      intro x hx
      exact ⟨⟨x, hTU hx⟩, rfl⟩)
  exact himage ▸
    (Topology.IsInducing.isNowhereDense_image hU.isOpenEmbedding_subtypeVal.isInducing hT)

theorem isNowhereDense_of_isOpen_cover
    {ι : Type v} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : ⋃ i, U i = (univ : Set X))
    {T : Set X}
    (hT : ∀ i, IsNowhereDense
      ((Subtype.val : U i → X) ⁻¹' (T ∩ U i))) :
    IsNowhereDense T := by
  rw [isNowhereDense_iff_forall_notMem_nhds]
  intro x hx hcl
  have hxcover : x ∈ ⋃ i, U i := by
    rw [hUcover]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxcover
  let xi : U i := ⟨x, hi⟩
  have hxi : xi ∈ ((Subtype.val : U i → X) ⁻¹' (T ∩ U i)) := by
    change x ∈ T ∩ U i
    exact ⟨hx, hi⟩
  apply (isNowhereDense_iff_forall_notMem_nhds.mp (hT i) xi hxi)
  have hpre : (Subtype.val : U i → X) ⁻¹' closure T =
      closure ((Subtype.val : U i → X) ⁻¹' (T ∩ U i)) := by
    simpa only [Subtype.preimage_coe_inter_self] using
      (hUopen i).isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val T
  rw [← hpre, nhds_subtype_eq_comap]
  exact Filter.preimage_mem_comap hcl

/-! ### Images under closed embeddings -/

theorem isNowhereDense_image_of_isClosedEmbedding
    {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (hclosed : IsClosedEmbedding f) {T : Set X}
    (hT : IsNowhereDense T) :
    IsNowhereDense (f '' T) := by
  exact Topology.IsInducing.isNowhereDense_image
    (IsClosedEmbedding.of_continuous_injective_isClosedMap hf hclosed.injective
      hclosed.isClosedMap).isInducing hT

/-! ### Preimages under open maps -/

theorem isClosed_isNowhereDense_preimage_of_isOpenMap
    {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (hopen : IsOpenMap f) {T : Set Y}
    (hTclosed : IsClosed T) (hT : IsNowhereDense T) :
    IsClosed (f ⁻¹' T) ∧ IsNowhereDense (f ⁻¹' T) := by
  refine ⟨hTclosed.preimage hf, ?_⟩
  rw [IsNowhereDense] at hT ⊢
  rw [← hopen.preimage_closure_eq_closure_preimage hf T,
    ← hopen.preimage_interior_eq_interior_preimage hf (closure T), hT]
  simp

theorem isClosed_isNowhereDense_iff_preimage_of_surjective_isOpenMap
    {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (hsurjective : Surjective f) (hopen : IsOpenMap f) {T : Set Y} :
    (IsClosed T ∧ IsNowhereDense T) ↔
      (IsClosed (f ⁻¹' T) ∧ IsNowhereDense (f ⁻¹' T)) := by
  constructor
  · rintro ⟨hTc, hT⟩
    exact isClosed_isNowhereDense_preimage_of_isOpenMap f hf hopen hTc hT
  · rintro ⟨hpreclosed, hpreND⟩
    have hq : IsQuotientMap f := hopen.isQuotientMap hf hsurjective
    have hTclosed : IsClosed T :=
      ((isQuotientMap_iff_isClosed.mp hq).2 T).mpr hpreclosed
    refine ⟨hTclosed, ?_⟩
    rw [IsNowhereDense]
    have hpreempty : f ⁻¹' interior (closure T) = ∅ := by
      calc
        f ⁻¹' interior (closure T) = interior (f ⁻¹' closure T) :=
          hopen.preimage_interior_eq_interior_preimage hf (closure T)
        _ = interior (closure (f ⁻¹' T)) := by
          rw [hopen.preimage_closure_eq_closure_preimage hf T]
        _ = ∅ := by simpa [IsNowhereDense] using hpreND
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨x, rfl⟩ := hsurjective y
    have hx : x ∈ f ⁻¹' interior (closure T) := hy
    rw [hpreempty] at hx
    exact hx

private theorem exists_finite_sUnion_isLocallyClosed_compl
    {S : Set (Set X)} (hS : S.Finite)
    (hLocallyClosed : ∀ T ∈ S, IsLocallyClosed T) :
    ∃ R : Set (Set X), R.Finite ∧
      (∀ T ∈ R, IsLocallyClosed T) ∧ (⋃₀ S)ᶜ = ⋃₀ R := by
  revert hLocallyClosed
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      intro hLocallyClosed
      refine ⟨{univ}, Set.finite_singleton _, ?_, ?_⟩
      · intro T hT
        simpa only [Set.mem_singleton_iff] using hT ▸ isOpen_univ.isLocallyClosed
      · simp
  | insert T S ih =>
      intro hLocallyClosed
      simp only [forall_mem_insert] at hLocallyClosed
      obtain ⟨R, hRfinite, hRlocallyClosed, hR⟩ := ih hLocallyClosed.2
      rcases hLocallyClosed.1 with ⟨U, Z, hU, hZ, hT⟩
      let R' := (Set.image (fun A : Set X => A ∩ Uᶜ) R) ∪
        Set.image (fun A : Set X => A ∩ Zᶜ) R
      refine ⟨R', hRfinite.image _ |>.union (hRfinite.image _), ?_, ?_⟩
      · intro A hA
        simp only [R', Set.mem_union, Set.mem_image] at hA
        rcases hA with (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
        · exact (hRlocallyClosed B hB).inter hU.isClosed_compl.isLocallyClosed
        · exact (hRlocallyClosed B hB).inter hZ.isOpen_compl.isLocallyClosed
      · rw [sUnion_insert, hT, compl_union, compl_inter, hR]
        simp only [R', sUnion_union, sUnion_image]
        rw [union_inter_distrib_right]
        simp only [sUnion_eq_biUnion, inter_iUnion, inter_comm]

private theorem isNowhereDense_of_isLocallyClosed_of_subset_compl_of_dense
    {Y : Type*} [TopologicalSpace Y] {D A : Set Y}
    (hD : Dense D) (hA : IsLocallyClosed A) (hAD : A ⊆ Dᶜ) :
    IsNowhereDense A := by
  rw [isNowhereDense_iff_forall_notMem_nhds]
  intro x hx hcl
  obtain ⟨U, Z, hU, hZ, hAeq⟩ := hA
  rw [hAeq] at hx
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hcl
  obtain ⟨y, hyUV, hyD⟩ :=
    hD.inter_open_nonempty (U ∩ V) (hU.inter hVopen)
      ⟨x, ⟨hx.1, hxV⟩⟩
  have hyA : y ∈ A := by
    rw [hAeq]
    refine ⟨hyUV.1, ?_⟩
    apply hZ.closure_subset
    apply closure_mono inter_subset_right
    rw [← hAeq]
    exact hVsub hyUV.2
  exact (hAD hyA) hyD

/-! ### Dense open subsets of closures -/

theorem exists_dense_open_subset_of_closure_of_finite_union_isLocallyClosed
    {E : Set X}
    (hE : ∃ S : Set (Set X), S.Finite ∧
      (∀ T ∈ S, IsLocallyClosed T) ∧ E = ⋃₀ S) :
    ∃ U : Set (closure E), IsOpen U ∧ Dense U ∧ (U : Set X) ⊆ E := by
  obtain ⟨S, hS, hLocallyClosed, hE⟩ := hE
  obtain ⟨R, hRfinite, hRlocallyClosed, hR⟩ :=
    exists_finite_sUnion_isLocallyClosed_compl hS hLocallyClosed
  let D : Set (closure E) := (Subtype.val : closure E → X) ⁻¹' E
  have hDdense : Dense D := by
    apply Subtype.dense_iff.mpr
    intro x hx
    have himage : (Subtype.val : closure E → X) '' D = E := by
      apply Set.image_preimage_eq_of_subset
      intro y hy
      exact ⟨⟨y, subset_closure hy⟩, rfl⟩
    rw [himage]
    exact hx
  let Q : Set (Set (closure E)) :=
    Set.image (fun A : Set X => (Subtype.val : closure E → X) ⁻¹' A) R
  have hQfinite : Q.Finite := hRfinite.image _
  have hQnowhereDense : ∀ A ∈ Q, IsNowhereDense A := by
    intro A hA
    rcases hA with ⟨B, hB, rfl⟩
    have hBsubset : B ⊆ Eᶜ := by
      intro x hx
      have hxR : x ∈ ⋃₀ R := subset_sUnion_of_mem hB hx
      have hxS : x ∈ (⋃₀ S)ᶜ := by
        rw [hR]
        exact hxR
      simpa [hE] using hxS
    apply isNowhereDense_of_isLocallyClosed_of_subset_compl_of_dense hDdense
    · exact (hRlocallyClosed B hB).preimage continuous_subtype_val
    · intro x hxB hxD
      exact (hBsubset hxB) hxD
  have hDcompl : Dᶜ = ⋃₀ Q := by
    dsimp [D, Q]
    rw [← preimage_compl, hE, hR, preimage_sUnion, sUnion_image]
  have hDcomplNowhereDense : IsNowhereDense Dᶜ := by
    rw [hDcompl]
    exact isNowhereDense_sUnion hQfinite hQnowhereDense
  let V : Set (closure E) := (closure (Dᶜ))ᶜ
  have hV : IsOpen V ∧ Dense V := by
    dsimp [V]
    exact isClosed_isNowhereDense_iff_compl.mp
      ⟨isClosed_closure, hDcomplNowhereDense.closure⟩
  refine ⟨V, hV.1, hV.2, ?_⟩
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  dsimp [V] at hz
  by_contra hzE
  apply hz
  apply subset_closure
  change (z : X) ∉ E
  exact hzE

/- The source's parenthetical example follows from the earlier chapter's
   finite-locally-closed description of constructible sets. -/
theorem exists_dense_open_subset_of_closure_of_isConstructible
    {E : Set X} (hE : IsConstructible E) :
    ∃ U : Set (closure E), IsOpen U ∧ Dense U ∧ (U : Set X) ⊆ E := by
  apply exists_dense_open_subset_of_closure_of_finite_union_isLocallyClosed
  exact Formalization.Books.Topology.Unit15.isConstructible_isFiniteUnion_isLocallyClosed hE

end NowhereDenseSets

end Formalization.Books.Topology.Unit21
