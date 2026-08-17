import Formalization.Books.Topology.Unit08.IrreducibleComponents
import Formalization.Books.Topology.Unit10.KrullDimension
import Formalization.Books.Topology.Unit12.QuasiCompactSpacesAndMaps
import Formalization.Books.Topology.Unit14.LimitsOfSpaces
import Formalization.Books.Topology.Unit15.ConstructibleSets
import Formalization.Books.Topology.Unit19.Specialization
import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Topology, Chapter 23: Spectral spaces

Mathlib's `SpectralSpace`, `IsSpectralMap`, and `constructibleTopology` are
the canonical interfaces for the definitions in the source.  The earlier
chapters supply the source-facing profinite predicate, specialization maps,
connected-components space, soberification, and the two-point example.
-/

namespace Formalization.Books.Topology.Unit23

open Set Function CategoryTheory CategoryTheory.Limits _root_.Topology TopologicalSpace
open Formalization.Books.Topology.Unit08
open Formalization.Books.Topology.Unit10
open Formalization.Books.Topology.Unit22

universe u v

variable {X : Type u} [TopologicalSpace X]

section SpectralSpaces

/-! ### The definition and the constructible topology -/

/-- Mathlib's bundled definition expands to the source's sobriety,
quasi-compactness, quasi-separatedness, and compact-open basis conditions.
Sobriety is represented by `QuasiSober` together with `T0Space`. -/
theorem spectralSpace_iff_source_conditions :
    SpectralSpace X ↔
      T0Space X ∧ CompactSpace X ∧ QuasiSober X ∧
        QuasiSeparatedSpace X ∧ PrespectralSpace X := by
  constructor
  · intro h
    exact ⟨h.toT0Space, h.toCompactSpace, h.toQuasiSober, h.toQuasiSeparatedSpace,
      h.toPrespectralSpace⟩
  · rintro ⟨hT0, hCompact, hSober, hQS, hPrespectral⟩
    exact { __ := hT0, __ := hCompact, __ := hSober, __ := hQS, __ := hPrespectral }

/- The source's spectral-map definition is Mathlib's `IsSpectralMap`, whose
   structure already contains continuity and compact-open preimages.  The
   earlier chapter API supplies the corresponding source-facing expansion. -/

/-- A source open is open for the constructible topology on a spectral space. -/
theorem isOpen_constructibleTopology_of_isOpen [SpectralSpace X]
    {U : Set X} (hU : IsOpen U) :
    IsOpen[constructibleTopology X] U := by
  obtain ⟨ι, V, hV, hVmem⟩ := PrespectralSpace.isTopologicalBasis.open_eq_iUnion hU
  rw [hV]
  apply @isOpen_iUnion X ι (constructibleTopology X) V
  intro i
  exact (hVmem i).2.isOpen_constructibleTopology_of_isOpen (hVmem i).1

/-- A constructible subset is clopen for the constructible topology. -/
theorem isConstructible_isOpen_isClosed_constructibleTopology [SpectralSpace X]
    {E : Set X} (hE : IsConstructible E) :
    IsOpen[constructibleTopology X] E ∧ IsClosed[constructibleTopology X] E := by
  induction hE using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
      have hUcompact : IsCompact U := hUcomp.isCompact
      have hUcompact' : IsCompact (Uᶜ)ᶜ := by
        simpa only [compl_compl] using hUcompact
      have hUcompopen : IsOpen[constructibleTopology X] Uᶜ :=
        IsCompact.isOpen_constructibleTopology_of_isClosed (s := Uᶜ) hUcompact'
          hUopen.isClosed_compl
      have hUclosed : IsClosed[constructibleTopology X] U := by
        simpa only [compl_compl] using
          (@IsOpen.isClosed_compl X (constructibleTopology X) Uᶜ hUcompopen)
      have hUconstructible : IsOpen[constructibleTopology X] U :=
        hUcompact.isOpen_constructibleTopology_of_isOpen hUopen
      exact ⟨hUconstructible, hUclosed⟩
  | union s hs t ht hs' ht' =>
      exact ⟨@IsOpen.union X s t (constructibleTopology X) hs'.1 ht'.1,
        @IsClosed.union X s t (constructibleTopology X) hs'.2 ht'.2⟩
  | compl s hs hs' =>
      exact ⟨(@isOpen_compl_iff X s (constructibleTopology X)).mpr hs'.2,
        (@isClosed_compl_iff X (constructibleTopology X) s).mpr hs'.1⟩

/-- A subset closed in the source topology is closed for the constructible
topology. -/
theorem isClosed_constructibleTopology_of_isClosed [SpectralSpace X]
    {E : Set X} (hE : IsClosed E) :
    IsClosed[constructibleTopology X] E := by
  have hEc : IsOpen[constructibleTopology X] Eᶜ :=
    isOpen_constructibleTopology_of_isOpen hE.isOpen_compl
  simpa only [compl_compl] using
    (@IsOpen.isClosed_compl X (constructibleTopology X) Eᶜ hEc)

/-- The constructible topology is the coarsest topology making every
constructible subset clopen. -/
theorem constructibleTopology_is_coarsest_for_constructible_clopen
    [SpectralSpace X] :
    (∀ E : Set X, IsConstructible E →
      IsOpen[constructibleTopology X] E ∧ IsClosed[constructibleTopology X] E) ∧
      ∀ t : TopologicalSpace X,
    (∀ E : Set X, IsConstructible E → IsOpen[t] E ∧ IsClosed[t] E) →
          constructibleTopology X ≤ t := by
  sorry

/-- Open subsets of the constructible topology are unions of constructible
subsets, as in the source. -/
theorem isOpen_constructibleTopology_iff_iUnion_isConstructible [SpectralSpace X]
    {E : Set X} :
    IsOpen[constructibleTopology X] E ↔
      ∃ S : Set (Set X), (∀ U ∈ S, IsConstructible U) ∧ ⋃₀ S = E := by
  constructor
  · intro hE
    change TopologicalSpace.GenerateOpen (constructibleTopologySubbasis X) E at hE
    induction hE with
    | basic U hU =>
        change (IsOpen U ∧ IsCompact U) ∨ (IsClosed U ∧ IsCompact Uᶜ) at hU
        rcases hU with ⟨hUopen, hUcomp⟩ | ⟨hUclosed, hUcomp⟩
        · refine ⟨{U}, ?_, by simp⟩
          intro V hV
          have hVU : V = U := by simpa using hV
          subst V
          exact hUcomp.isConstructible hUopen
        · refine ⟨{U}, ?_, by simp⟩
          intro V hV
          have hVU : V = U := by simpa using hV
          subst V
          exact (hUcomp.isConstructible hUclosed.isOpen_compl).of_compl
    | univ =>
        exact ⟨{univ}, by simp, by simp⟩
    | inter s t hs ht ihs iht =>
        rcases ihs with ⟨S, hS, hSE⟩
        rcases iht with ⟨T, hT, hTE⟩
        let R : Set (Set X) :=
          (fun p : Set X × Set X => p.1 ∩ p.2) '' (S ×ˢ T)
        refine ⟨R, ?_, ?_⟩
        · rintro _ ⟨⟨U, V⟩, ⟨hUS, hVT⟩, rfl⟩
          exact (hS U hUS).inter (hT V hVT)
        · ext x
          rw [← hSE, ← hTE]
          constructor
          · intro hx
            rcases mem_sUnion.mp hx with ⟨W, ⟨⟨U, V⟩, ⟨hUS, hVT⟩, rfl⟩, hxW⟩
            exact ⟨mem_sUnion.mpr ⟨U, hUS, hxW.1⟩,
              mem_sUnion.mpr ⟨V, hVT, hxW.2⟩⟩
          · intro hx
            rcases hx with ⟨hxS, hxT⟩
            rcases mem_sUnion.mp hxS with ⟨U, hUS, hxU⟩
            rcases mem_sUnion.mp hxT with ⟨V, hVT, hxV⟩
            exact mem_sUnion.mpr ⟨U ∩ V, ⟨⟨U, V⟩, ⟨hUS, hVT⟩, rfl⟩, ⟨hxU, hxV⟩⟩
    | sUnion S hS ih =>
        let R : Set (Set X) :=
          {U | ∃ s ∈ S, ∃ T : Set (Set X),
            (∀ V ∈ T, IsConstructible V) ∧ ⋃₀ T = s ∧ U ∈ T}
        refine ⟨R, ?_, ?_⟩
        · rintro U ⟨s, hsS, T, hT, hTE, hUT⟩
          exact hT U hUT
        · ext x
          constructor
          · intro hx
            rcases mem_sUnion.mp hx with ⟨U, ⟨s, hsS, T, hT, hTE, hUT⟩, hxU⟩
            exact mem_sUnion.mpr ⟨s, hsS, hTE ▸ mem_sUnion.mpr ⟨U, hUT, hxU⟩⟩
          · intro hx
            rcases mem_sUnion.mp hx with ⟨s, hsS, hxs⟩
            rcases ih s hsS with ⟨T, hT, hTE⟩
            rw [← hTE] at hxs
            rcases mem_sUnion.mp hxs with ⟨U, hUT, hxU⟩
            exact mem_sUnion.mpr ⟨U, ⟨s, hsS, T, hT, hTE, hUT⟩, hxU⟩
  · rintro ⟨S, hS, rfl⟩
    exact @isOpen_sUnion X (constructibleTopology X) S
      (fun U hU => (isConstructible_isOpen_isClosed_constructibleTopology (hS U hU)).1)

/-- Closed subsets of the constructible topology are intersections of
constructible subsets, as in the source. -/
theorem isClosed_constructibleTopology_iff_iInter_isConstructible [SpectralSpace X]
    {E : Set X} :
    IsClosed[constructibleTopology X] E ↔
      ∃ S : Set (Set X), (∀ U ∈ S, IsConstructible U) ∧ ⋂₀ S = E := by
  constructor
  · intro hE
    have hEc : IsOpen[constructibleTopology X] Eᶜ :=
      (@isOpen_compl_iff X E (constructibleTopology X)).mpr hE
    obtain ⟨S, hS, hSE⟩ :=
      isOpen_constructibleTopology_iff_iUnion_isConstructible.mp hEc
    refine ⟨compl '' S, ?_, ?_⟩
    · rintro U ⟨V, hV, rfl⟩
      exact (hS V hV).compl
    · rw [← Set.compl_sUnion S, hSE, compl_compl]
  · rintro ⟨S, hS, hSE⟩
    apply (@isOpen_compl_iff X E (constructibleTopology X)).mp
    rw [← hSE, Set.compl_sInter]
    exact @isOpen_sUnion X (constructibleTopology X) (compl '' S)
      (fun U hU =>
        (isConstructible_isOpen_isClosed_constructibleTopology (E := U) (by
          rcases hU with ⟨V, hV, rfl⟩
          exact (hS V hV).compl)).1)

/-! ### Constructible topology on spectral spaces -/

/-- The constructible topology of a spectral space is quasi-compact,
Hausdorff, and totally disconnected. -/
theorem constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact
    [SpectralSpace X] :
    @T2Space X (constructibleTopology X) ∧
      @TotallyDisconnectedSpace X (constructibleTopology X) ∧
        @CompactSpace X (constructibleTopology X) := by
  have hsep : ∀ {x y : X}, x ≠ y →
      ∃ U : Set X, IsOpen[constructibleTopology X] U ∧
        IsClosed[constructibleTopology X] U ∧ x ∈ U ∧ y ∉ U := by
    intro x y hxy
    obtain ⟨U, hU, hxor⟩ := exists_isOpen_xor_mem hxy
    rcases hxor with hxy | hyx
    · obtain ⟨V, hV, hxV, hVU⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxy.1 hU
      have hVopen : IsOpen[constructibleTopology X] V :=
        hV.2.isOpen_constructibleTopology_of_isOpen hV.1
      have hVcompopen : IsOpen[constructibleTopology X] Vᶜ :=
        IsCompact.isOpen_constructibleTopology_of_isClosed (s := Vᶜ)
          (by simpa only [compl_compl] using hV.2) hV.1.isClosed_compl
      have hVclosed : IsClosed[constructibleTopology X] V := by
        simpa only [compl_compl] using
          (@IsOpen.isClosed_compl X (constructibleTopology X) Vᶜ hVcompopen)
      exact ⟨V, hVopen, hVclosed, hxV, fun hyV => hxy.2 (hVU hyV)⟩
    · obtain ⟨V, hV, hyV, hVU⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyx.1 hU
      have hVopen : IsOpen[constructibleTopology X] V :=
        hV.2.isOpen_constructibleTopology_of_isOpen hV.1
      have hVcompopen : IsOpen[constructibleTopology X] Vᶜ :=
        IsCompact.isOpen_constructibleTopology_of_isClosed (s := Vᶜ)
          (by simpa only [compl_compl] using hV.2) hV.1.isClosed_compl
      exact ⟨Vᶜ, hVcompopen, @IsOpen.isClosed_compl X (constructibleTopology X) V hVopen,
        fun hxV => hyx.2 (hVU hxV), by simpa using hyV⟩
  have hT2 : @T2Space X (constructibleTopology X) := by
    exact @T2Space.mk X (constructibleTopology X) (by
      intro x y hxy
      obtain ⟨U, hUopen, hUclosed, hxU, hyU⟩ := hsep hxy
      exact ⟨U, Uᶜ, hUopen,
        (@isOpen_compl_iff X U (constructibleTopology X)).mpr hUclosed,
        hxU, hyU, disjoint_compl_right⟩)
  have hTD : @TotallyDisconnectedSpace X (constructibleTopology X) := by
    exact @TotallyDisconnectedSpace.mk X (constructibleTopology X) (by
      intro s hs hpre x hx y hy
      by_contra hxy
      obtain ⟨U, hUopen, hUclosed, hxU, hyU⟩ := hsep hxy
      rcases @disjoint_or_subset_of_isClopen X (constructibleTopology X) s U hpre
          ⟨hUclosed, hUopen⟩ with hdis | hsub
      · exact (Set.disjoint_left.1 hdis) hx hxU
      · exact hyU (hsub hy))
  have hCompact : @CompactSpace X (constructibleTopology X) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology X) X _
      (constructibleTopology X) (WithTopology.ofTopology)
      (WithTopology.continuous_ofTopology _) _ (WithTopology.ofTopology_surjective _)
  exact ⟨hT2, hTD, hCompact⟩

/-- A spectral map is continuous for the constructible topologies, has
quasi-compact fibres, and has constructibly closed image. -/
theorem spectralMap_constructibleTopology_properties
    {Y : Type v} [TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y]
    (f : X → Y) (hf : IsSpectralMap f) :
      Continuous[constructibleTopology X, constructibleTopology Y] f ∧
      (∀ y : Y, IsCompact (f ⁻¹' ({y} : Set Y))) ∧
        IsClosed[constructibleTopology Y] (Set.range f) := by
  have hcont : Continuous[constructibleTopology X, constructibleTopology Y] f := by
    rw [continuous_generateFrom_iff]
    intro U hU
    change (IsOpen U ∧ IsCompact U) ∨ (IsClosed U ∧ IsCompact Uᶜ) at hU
    rcases hU with ⟨hUopen, hUcomp⟩ | ⟨hUclosed, hUcomp⟩
    · exact (hf.isCompact_preimage_of_isOpen hUopen hUcomp).isOpen_constructibleTopology_of_isOpen
        (hUopen.preimage hf.continuous)
    · apply IsCompact.isOpen_constructibleTopology_of_isClosed (s := f ⁻¹' U)
      · simpa only [preimage_compl] using
          hf.isCompact_preimage_of_isOpen hUclosed.isOpen_compl hUcomp
      · exact hUclosed.preimage hf.continuous
  have hXprops := constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)
  have hYprops := constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := Y)
  have hXcompact : @CompactSpace X (constructibleTopology X) := hXprops.2.2
  have hYt2 : @T2Space Y (constructibleTopology Y) := hYprops.1
  have hfibers : ∀ y : Y, IsCompact (f ⁻¹' ({y} : Set Y)) := by
    intro y
    have hsingleton : @IsClosed Y (constructibleTopology Y) ({y} : Set Y) :=
      @isClosed_singleton Y (constructibleTopology Y)
        (@T2Space.t1Space Y (constructibleTopology Y) hYt2) y
    have hfiber_ct : @IsCompact X (constructibleTopology X) (f ⁻¹' ({y} : Set Y)) :=
      @IsClosed.isCompact X (constructibleTopology X) (f ⁻¹' ({y} : Set Y)) hXcompact
        (@IsClosed.preimage X Y (constructibleTopology X) (constructibleTopology Y) f hcont
          ({y} : Set Y) hsingleton)
    apply isCompact_of_finite_subcover
    intro ι U hUopen hUcover
    obtain ⟨s, hs⟩ := @IsCompact.elim_finite_subcover X (constructibleTopology X)
      (f ⁻¹' ({y} : Set Y)) ι hfiber_ct U
      (fun i => isOpen_constructibleTopology_of_isOpen (hUopen i)) hUcover
    exact ⟨s, hs⟩
  have hrange : @IsClosed Y (constructibleTopology Y) (Set.range f) :=
    @IsCompact.isClosed Y (constructibleTopology Y) hYt2 (Set.range f)
      (@isCompact_range X Y (constructibleTopology X) (constructibleTopology Y)
        hXcompact f hcont)
  exact ⟨hcont, hfibers, hrange⟩

/-- For maps between spectral spaces, continuity for the constructible
topologies is equivalent to being a spectral map. -/
theorem isSpectralMap_iff_continuous_constructibleTopology
    {Y : Type v} [TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y]
    {f : X → Y} (hf : Continuous f) :
    IsSpectralMap f ↔
      Continuous[constructibleTopology X, constructibleTopology Y] f := by
  constructor
  · intro hsf
    exact (spectralMap_constructibleTopology_properties f hsf).1
  · intro hct
    refine ⟨hf, ?_⟩
    intro V hVopen hVcomp
    have hVclopen :=
      isConstructible_isOpen_isClosed_constructibleTopology
        (X := Y) (hVcomp.isConstructible hVopen)
    have hpreclosed : @IsClosed X (constructibleTopology X) (f ⁻¹' V) :=
      @IsClosed.preimage X Y (constructibleTopology X) (constructibleTopology Y) f hct V
        hVclopen.2
    have hprecompact : @IsCompact X (constructibleTopology X) (f ⁻¹' V) :=
      @IsClosed.isCompact X (constructibleTopology X) (f ⁻¹' V)
        (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)).2.2
        hpreclosed
    apply isCompact_of_finite_subcover
    intro ι U hUopen hUcover
    obtain ⟨s, hs⟩ := @IsCompact.elim_finite_subcover X (constructibleTopology X)
      (f ⁻¹' V) ι hprecompact U
      (fun i => isOpen_constructibleTopology_of_isOpen (hUopen i)) hUcover
    exact ⟨s, hs⟩

/-- A subspace closed in the constructible topology of a spectral space is
spectral for its induced topology. -/
theorem spectralSpace_subtype_of_constructible_closed [SpectralSpace X]
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) :
    SpectralSpace E := by
  classical
  have hctcompact : @CompactSpace X (constructibleTopology X) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)).2.2
  have hEctcompact : @IsCompact X (constructibleTopology X) E :=
    @IsClosed.isCompact X (constructibleTopology X) E hctcompact hE
  have hEcompact : IsCompact E := by
    apply isCompact_iff_finite_subcover.mpr
    intro ι U hUopen hEcover
    obtain ⟨s, hs⟩ :=
      (@isCompact_iff_finite_subcover X (constructibleTopology X) E).mp hEctcompact U
        (fun i => isOpen_constructibleTopology_of_isOpen (hUopen i)) hEcover
    exact ⟨s, hs⟩
  have hcompact : CompactSpace E := isCompact_iff_compactSpace.mp hEcompact
  have hval : IsSpectralMap (Subtype.val : E → X) := by
    refine ⟨continuous_subtype_val, ?_⟩
    intro U hUopen hUcomp
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    have hUctclosed : @IsClosed X (constructibleTopology X) U := by
      exact (isConstructible_isOpen_isClosed_constructibleTopology
        (X := X) (hUcomp.isConstructible hUopen)).2
    have hEUctclosed : @IsClosed X (constructibleTopology X) (E ∩ U) :=
      @IsClosed.inter X E U (constructibleTopology X) hE hUctclosed
    have hEUctcompact : @IsCompact X (constructibleTopology X) (E ∩ U) :=
      @IsClosed.isCompact X (constructibleTopology X) (E ∩ U) hctcompact hEUctclosed
    apply isCompact_iff_finite_subcover.mpr
    intro ι V hVopen hEUcover
    obtain ⟨s, hs⟩ :=
      (@isCompact_iff_finite_subcover X (constructibleTopology X) (E ∩ U)).mp hEUctcompact V
        (fun i => isOpen_constructibleTopology_of_isOpen (hVopen i))
        (by simpa only [inter_comm] using hEUcover)
    exact ⟨s, by simpa only [inter_comm] using hs⟩
  have hprespectral : PrespectralSpace E :=
    PrespectralSpace.of_isInducing (Subtype.val : E → X) IsInducing.subtypeVal hval
  let _ : PrespectralSpace E := hprespectral
  let b : {K : Set X // IsOpen K ∧ IsCompact K} → Set E :=
    fun i => (Subtype.val : E → X) ⁻¹' (i : Set X)
  have hbset : Set.range b =
      (preimage (Subtype.val : E → X)) '' {U : Set X | IsOpen U ∧ IsCompact U} := by
    ext V
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(i : Set X), i.property, rfl⟩
    · rintro ⟨U, hU, rfl⟩
      exact ⟨⟨U, hU⟩, rfl⟩
  have hb : IsTopologicalBasis (Set.range b) := by
    rw [hbset]
    exact (PrespectralSpace.isTopologicalBasis (X := X)).isInducing IsInducing.subtypeVal
  have hqsep : QuasiSeparatedSpace E :=
    QuasiSeparatedSpace.of_isTopologicalBasis hb
      (by
        intro i j
        have hKopen : IsOpen (i : Set X) := i.property.1
        have hKopen' : IsOpen (j : Set X) := j.property.1
        have hKcompact : IsCompact ((i : Set X) ∩ (j : Set X)) :=
          QuasiSeparatedSpace.inter_isCompact _ _ hKopen i.property.2 hKopen' j.property.2
        simpa only [b, preimage_inter] using
          hval.isCompact_preimage_of_isOpen (hKopen.inter hKopen') hKcompact)
  have hqsober : QuasiSober E := by
    refine { sober := ?_ }
    intro Z hZ hZclosed
    let Z' : Set X := (Subtype.val : E → X) '' Z
    let Z'' : Set X := closure Z'
    have hZ' : IsIrreducible Z' :=
      hZ.image (Subtype.val : E → X) continuous_subtype_val.continuousOn
    have hZ'' : IsIrreducible Z'' := by
      simpa only [Z''] using hZ'.closure
    have hZ''nonempty : Z''.Nonempty := hZ'.nonempty.mono subset_closure
    obtain ⟨η, hη⟩ := QuasiSober.sober hZ'' isClosed_closure
    have hηE : η ∈ E := by
      by_contra hηE
      have hEcopen : IsOpen[constructibleTopology X] Eᶜ :=
        (@isOpen_compl_iff X E (constructibleTopology X)).mpr hE
      obtain ⟨S, hS, hSE⟩ :=
        isOpen_constructibleTopology_iff_iUnion_isConstructible (X := X) |>.mp hEcopen
      have hηEc : η ∈ Eᶜ := by simpa only [mem_compl_iff] using hηE
      obtain ⟨F, hFS, hηF⟩ := mem_sUnion.mp (hSE.symm ▸ hηEc)
      have hFE : F ⊆ Eᶜ := by
        intro x hx
        rw [← hSE]
        exact mem_sUnion.mpr ⟨F, hFS, hx⟩
      have hFconstructible : IsConstructible F := hS F hFS
      have hFfinite :=
        Formalization.Books.Topology.Unit15.isConstructible_isFiniteUnion_isLocallyClosed
          hFconstructible
      have hηdense :=
        (Formalization.Books.Topology.Unit15.dense_preimage_of_finite_locallyClosed_union_iff_mem_genericPoint
          hZ'' hFfinite hη).mpr hηF
      obtain ⟨W, hWopen, hWdense, hWF⟩ :=
        (Formalization.Books.Topology.Unit15.dense_preimage_of_finite_locallyClosed_union_iff
          hZ'' hFfinite).mpr hηdense
      have hZdense : Dense ((Subtype.val : Z'' → X) ⁻¹' Z') := by
        apply Subtype.dense_iff.mpr
        intro x hx
        have himage :
            (Subtype.val : Z'' → X) '' ((Subtype.val : Z'' → X) ⁻¹' Z') = Z' := by
          ext y
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact hz
          · intro hy
            exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
        rw [himage]
        exact hx
      obtain ⟨z0, hz0⟩ := hZ''nonempty
      have hWnonempty : W.Nonempty :=
        hWdense.nonempty_iff.mpr ⟨⟨z0, hz0⟩⟩
      obtain ⟨z, hzZ, hzW⟩ := hZdense.exists_mem_open hWopen hWnonempty
      have hzF := hWF hzW
      change (z : X) ∈ Z' at hzZ
      obtain ⟨e, heZ, hez⟩ := hzZ
      have hzE : (z : X) ∈ E := by
        rw [← hez]
        exact e.property
      exact (hFE hzF) hzE
    refine ⟨⟨η, hηE⟩, ?_⟩
    rw [isGenericPoint_def]
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    rw [image_singleton, hη.def]
    rw [← hZclosed.closure_eq]
    exact (IsInducing.subtypeVal.closure_eq_preimage_closure_image Z).symm
  have ht0 : T0Space E := inferInstance
  exact { __ := ht0, __ := hcompact, __ := hqsober, __ := hqsep, __ := hprespectral }

theorem spectralSpace_subtype_of_isConstructible [SpectralSpace X]
    {E : Set X} (hE : IsConstructible E) :
    SpectralSpace E := by
  exact spectralSpace_subtype_of_constructible_closed
    (isConstructible_isOpen_isClosed_constructibleTopology hE).2

theorem spectralSpace_subtype_of_isClosed [SpectralSpace X]
    {E : Set X} (hE : IsClosed E) :
    SpectralSpace E := by
  exact spectralSpace_subtype_of_constructible_closed
    (isClosed_constructibleTopology_of_isClosed hE)

/-! ### Specialization and generalization -/

/-- A point in the closure of a constructibly closed subset is a specialization
of a point of that subset. -/
theorem exists_generalization_mem_of_mem_closure_of_constructibleClosed
    [SpectralSpace X] {E : Set X}
    (_hE : IsClosed[constructibleTopology X] E) {x : X}
    (hx : x ∈ closure E) :
    ∃ y ∈ E, y ⤳ x := by
  have hctcompact : @CompactSpace X (constructibleTopology X) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)).2.2
  let ι : Type u := {U : Set X // IsOpen U ∧ IsCompact U ∧ x ∈ U}
  let t : ι → Set X := fun U => E ∩ (U : Set X)
  have htc : ∀ i, @IsClosed X (constructibleTopology X) (t i) := by
    intro i
    exact @IsClosed.inter X E (i : Set X) (constructibleTopology X) _hE
      (isConstructible_isOpen_isClosed_constructibleTopology
        (i.2.2.1.isConstructible i.2.1)).2
  have hfinite : ∀ s : Finset ι,
      IsOpen (⋂ i : ι, ⋂ (_ : i ∈ (↑s : Set ι)), (i : Set X)) ∧
        IsCompact (⋂ i : ι, ⋂ (_ : i ∈ (↑s : Set ι)), (i : Set X)) ∧
          x ∈ ⋂ i : ι, ⋂ (_ : i ∈ (↑s : Set ι)), (i : Set X) := by
    intro s
    have hopen : IsOpen (⋂ i : ι, ⋂ (_ : i ∈ (↑s : Set ι)), (i : Set X)) :=
      s.finite_toSet.isOpen_biInter (fun i hi => i.2.1)
    have hcompact : IsCompact (⋂ i : ι, ⋂ (_ : i ∈ (↑s : Set ι)), (i : Set X)) := by
      rw [← Set.sInter_image]
      apply QuasiSeparatedSpace.isCompact_sInter
        (s.finite_toSet.image (fun i : ι => (i : Set X)))
      · rintro V ⟨i, hi, rfl⟩
        exact Or.inl i.2.1
      · rintro V ⟨i, hi, rfl⟩
        exact i.2.2.1
    exact ⟨hopen, hcompact, Set.mem_iInter₂.2 (fun i hi => i.2.2.2)⟩
  have hfinite_inter : ∀ s : Finset ι,
      (⋂ i : ι, ⋂ (_ : i ∈ (↑s : Set ι)), t i).Nonempty := by
    intro s
    rcases mem_closure_iff.mp hx _ (hfinite s).1 (hfinite s).2.2 with ⟨z, hzU, hzE⟩
    refine ⟨z, Set.mem_iInter₂.2 ?_⟩
    intro i hi
    exact ⟨hzE, Set.mem_iInter₂.1 hzU i hi⟩
  have hnonempty : (⋂ i, t i).Nonempty :=
    @CompactSpace.iInter_nonempty X (constructibleTopology X) ι hctcompact t htc
      (by
        intro s
        change (⋂ i : ι, ⋂ (_ : i ∈ (↑s : Set ι)), t i).Nonempty
        exact hfinite_inter s)
  obtain ⟨y, hy⟩ := hnonempty
  let i0 : ι := ⟨Set.univ, isOpen_univ, CompactSpace.isCompact_univ, mem_univ _⟩
  have hyE : y ∈ E := by
    have hyi0 := mem_iInter.1 hy i0
    change y ∈ E ∩ (i0 : Set X) at hyi0
    exact hyi0.1
  refine ⟨y, hyE, ?_⟩
  rw [specializes_iff_mem_closure]
  apply PrespectralSpace.isTopologicalBasis.mem_closure_iff.mpr
  intro U hU hxU
  let i : ι := ⟨U, hU.1, hU.2, hxU⟩
  have hyi := mem_iInter.1 hy i
  change y ∈ E ∩ (i : Set X) at hyi
  exact ⟨y, (by simpa only [i] using hyi.2), by simp⟩

/-- A constructibly closed subset stable under specialization is closed in the
source topology. -/
theorem isClosed_of_constructibleClosed_of_stableUnderSpecialization
    [SpectralSpace X] {E : Set X}
    (hE : IsClosed[constructibleTopology X] E)
    (hstable : StableUnderSpecialization E) :
    IsClosed E := by
  apply isClosed_of_closure_subset
  intro x hx
  obtain ⟨y, hyE, hyspecializes⟩ :=
    exists_generalization_mem_of_mem_closure_of_constructibleClosed hE hx
  exact hstable hyspecializes hyE

/-- A constructibly open subset stable under generalization is open in the
source topology. -/
theorem isOpen_of_constructibleOpen_of_stableUnderGeneralization
    [SpectralSpace X] {E : Set X}
    (hE : IsOpen[constructibleTopology X] E)
    (hstable : StableUnderGeneralization E) :
    IsOpen E := by
  apply (@isClosed_compl_iff X (inferInstance : TopologicalSpace X) E).mp
  apply isClosed_of_constructibleClosed_of_stableUnderSpecialization (E := Eᶜ)
    ((@isClosed_compl_iff X (constructibleTopology X) E).mpr hE) hstable.compl

/-- Two points of a spectral space either have a common generalization or have
disjoint open neighbourhoods. -/
theorem spectral_two_point_dichotomy [SpectralSpace X] (x y : X) :
    (∃ z : X, z ⤳ x ∧ z ⤳ y) ∨
      ∃ U V : Set X,
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  let ιx : Type u := {U : Set X // IsOpen U ∧ IsCompact U ∧ x ∈ U}
  let ιy : Type u := {V : Set X // IsOpen V ∧ IsCompact V ∧ y ∈ V}
  let t : ιx × ιy → Set X := fun p => (p.1 : Set X) ∩ (p.2 : Set X)
  have hctcompact : @CompactSpace X (constructibleTopology X) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)).2.2
  have hfinite_x : ∀ s : Finset ιx,
      IsOpen (⋂ i : ιx, ⋂ (_ : i ∈ (↑s : Set ιx)), (i : Set X)) ∧
        IsCompact (⋂ i : ιx, ⋂ (_ : i ∈ (↑s : Set ιx)), (i : Set X)) ∧
          x ∈ ⋂ i : ιx, ⋂ (_ : i ∈ (↑s : Set ιx)), (i : Set X) := by
    intro s
    have hopen : IsOpen (⋂ i : ιx, ⋂ (_ : i ∈ (↑s : Set ιx)), (i : Set X)) :=
      s.finite_toSet.isOpen_biInter (fun i hi => i.2.1)
    have hcompact : IsCompact (⋂ i : ιx, ⋂ (_ : i ∈ (↑s : Set ιx)), (i : Set X)) := by
      rw [← Set.sInter_image]
      apply QuasiSeparatedSpace.isCompact_sInter
        (s.finite_toSet.image (fun i : ιx => (i : Set X)))
      · rintro U ⟨i, hi, rfl⟩
        exact Or.inl i.2.1
      · rintro U ⟨i, hi, rfl⟩
        exact i.2.2.1
    exact ⟨hopen, hcompact, Set.mem_iInter₂.2 (fun i hi => i.2.2.2)⟩
  have hfinite_y : ∀ s : Finset ιy,
      IsOpen (⋂ i : ιy, ⋂ (_ : i ∈ (↑s : Set ιy)), (i : Set X)) ∧
        IsCompact (⋂ i : ιy, ⋂ (_ : i ∈ (↑s : Set ιy)), (i : Set X)) ∧
          y ∈ ⋂ i : ιy, ⋂ (_ : i ∈ (↑s : Set ιy)), (i : Set X) := by
    intro s
    have hopen : IsOpen (⋂ i : ιy, ⋂ (_ : i ∈ (↑s : Set ιy)), (i : Set X)) :=
      s.finite_toSet.isOpen_biInter (fun i hi => i.2.1)
    have hcompact : IsCompact (⋂ i : ιy, ⋂ (_ : i ∈ (↑s : Set ιy)), (i : Set X)) := by
      rw [← Set.sInter_image]
      apply QuasiSeparatedSpace.isCompact_sInter
        (s.finite_toSet.image (fun i : ιy => (i : Set X)))
      · rintro U ⟨i, hi, rfl⟩
        exact Or.inl i.2.1
      · rintro U ⟨i, hi, rfl⟩
        exact i.2.2.1
    exact ⟨hopen, hcompact, Set.mem_iInter₂.2 (fun i hi => i.2.2.2)⟩
  have htc : ∀ p, @IsClosed X (constructibleTopology X) (t p) := by
    intro p
    exact @IsClosed.inter X (p.1 : Set X) (p.2 : Set X) (constructibleTopology X)
      (isConstructible_isOpen_isClosed_constructibleTopology
        (p.1.2.2.1.isConstructible p.1.2.1)).2
      (isConstructible_isOpen_isClosed_constructibleTopology
        (p.2.2.2.1.isConstructible p.2.2.1)).2
  by_cases hdisj : ∃ i : ιx, ∃ j : ιy, Disjoint (i : Set X) (j : Set X)
  · obtain ⟨i, j, hij⟩ := hdisj
    exact Or.inr ⟨i, j, i.2.1, j.2.1, i.2.2.2, j.2.2.2, hij⟩
  · have hpair : ∀ i : ιx, ∀ j : ιy,
        ((i : Set X) ∩ (j : Set X)).Nonempty := by
      intro i j
      by_contra hne
      apply hdisj
      refine ⟨i, j, Set.disjoint_left.2 ?_⟩
      intro z hzi hzj
      exact hne ⟨z, hzi, hzj⟩
    have hfinite : ∀ s : Finset (ιx × ιy),
        (⋂ p : ιx × ιy, ⋂ (_ : p ∈ (↑s : Set (ιx × ιy))), t p).Nonempty := by
      intro s
      let sx : Finset ιx := s.image Prod.fst
      let sy : Finset ιy := s.image Prod.snd
      have hxs := hfinite_x sx
      have hys := hfinite_y sy
      let i : ιx :=
        ⟨⋂ i : ιx, ⋂ (_ : i ∈ (↑sx : Set ιx)), (i : Set X),
          hxs.1, hxs.2.1, hxs.2.2⟩
      let j : ιy :=
        ⟨⋂ i : ιy, ⋂ (_ : i ∈ (↑sy : Set ιy)), (i : Set X),
          hys.1, hys.2.1, hys.2.2⟩
      obtain ⟨z, hz⟩ := hpair i j
      refine ⟨z, Set.mem_iInter₂.2 ?_⟩
      intro p hp
      have hp1 : p.1 ∈ (↑sx : Set ιx) := by
        change p.1 ∈ sx
        exact Finset.mem_image.2 ⟨p, hp, rfl⟩
      have hp2 : p.2 ∈ (↑sy : Set ιy) := by
        change p.2 ∈ sy
        exact Finset.mem_image.2 ⟨p, hp, rfl⟩
      have hzi : z ∈ (i : Set X) := hz.1
      have hzj : z ∈ (j : Set X) := hz.2
      change z ∈ (i : Set X) at hzi
      change z ∈ ⋂ i : ιx, ⋂ (_ : i ∈ (↑sx : Set ιx)), (i : Set X) at hzi
      change z ∈ (j : Set X) at hzj
      change z ∈ ⋂ i : ιy, ⋂ (_ : i ∈ (↑sy : Set ιy)), (i : Set X) at hzj
      change z ∈ (p.1 : Set X) ∩ (p.2 : Set X)
      exact ⟨Set.mem_iInter₂.1 hzi p.1 hp1,
        Set.mem_iInter₂.1 hzj p.2 hp2⟩
    have hnonempty : (⋂ p, t p).Nonempty :=
      @CompactSpace.iInter_nonempty X (constructibleTopology X)
        (ιx × ιy) hctcompact t htc hfinite
    obtain ⟨z, hz⟩ := hnonempty
    have hzx : z ⤳ x := by
      rw [specializes_iff_mem_closure]
      apply PrespectralSpace.isTopologicalBasis.mem_closure_iff.mpr
      intro U hU hxU
      let i : ιx := ⟨U, hU.1, hU.2, hxU⟩
      let j : ιy := ⟨Set.univ, isOpen_univ, CompactSpace.isCompact_univ, mem_univ _⟩
      have hzij := Set.mem_iInter.1 hz (i, j)
      change z ∈ (i : Set X) ∩ (j : Set X) at hzij
      exact ⟨z, hzij.1, by simp⟩
    have hzy : z ⤳ y := by
      rw [specializes_iff_mem_closure]
      apply PrespectralSpace.isTopologicalBasis.mem_closure_iff.mpr
      intro V hV hyV
      let i : ιx := ⟨Set.univ, isOpen_univ, CompactSpace.isCompact_univ, mem_univ _⟩
      let j : ιy := ⟨V, hV.1, hV.2, hyV⟩
      have hzij := Set.mem_iInter.1 hz (i, j)
      change z ∈ (i : Set X) ∩ (j : Set X) at hzij
      exact ⟨z, hzij.2, by simp⟩
    exact Or.inl ⟨z, hzx, hzy⟩

/-! ### Profinite spectral spaces -/

/-- The eight stated conditions characterizing profinite spectral spaces.
The unfinished ninth item in the source is intentionally not included. -/
theorem isProfiniteSpace_TFAE_spectral_separation_conditions [SpectralSpace X] :
    List.TFAE
      [IsProfiniteSpace X,
        T2Space X,
        TotallyDisconnectedSpace X,
        (∀ U : Set X, IsOpen U → IsCompact U → IsClosed U),
        (∀ ⦃x y : X⦄, x ⤳ y → x = y),
        (∀ x : X, IsClosed ({x} : Set X)),
        (∀ x : X, ∃ C : irreducibleComponents X,
          IsGenericPoint x (C : Set X)),
        constructibleTopology X = (inferInstance : TopologicalSpace X)] := by
  tfae_have 1 → 3 := by
    intro h
    exact (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mp h).2.2
  tfae_have 3 → 6 := by
    intro h
    let _ : TotallyDisconnectedSpace X := h
    exact fun x => isClosed_singleton
  tfae_have 5 ↔ 6 := by
    constructor
    · intro h
      let _ : T1Space X := t1Space_iff_specializes_imp_eq.mpr h
      exact fun x => isClosed_singleton
    · intro h
      let _ : T1Space X := ⟨h⟩
      exact t1Space_iff_specializes_imp_eq.mp inferInstance
  tfae_have 6 → 7 := by
    intro h x
    let _ : T1Space X := ⟨h⟩
    let C : irreducibleComponents X :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    obtain ⟨g, hg⟩ := QuasiSober.sober C.2.1
      (isClosed_of_mem_irreducibleComponents (C : Set X) C.2)
    have hCeq : (C : Set X) = ({g} : Set X) := by
      rw [← hg.def, closure_singleton]
    have hxg : x = g := by
      have hxC : x ∈ (C : Set X) := mem_irreducibleComponent
      have hxg' : x ∈ ({g} : Set X) := hCeq ▸ hxC
      simpa using hxg'
    exact ⟨C, by simpa [hxg] using hg⟩
  tfae_have 7 → 6 := by
    intro h x
    apply isClosed_of_closure_subset
    intro y hy
    obtain ⟨C, hC⟩ := h x
    have hyC : y ∈ (C : Set X) := by
      rw [← hC.def]
      exact hy
    obtain ⟨D, hD⟩ := h y
    have hDsub : (D : Set X) ⊆ (C : Set X) := by
      rw [← hD.def]
      exact closure_minimal (singleton_subset_iff.mpr hyC)
        (isClosed_of_mem_irreducibleComponents (C : Set X) C.2)
    have hCD : (C : Set X) = (D : Set X) := by
      exact Set.Subset.antisymm (D.2.2 C.2.1 hDsub) hDsub
    have hD' : IsGenericPoint y (C : Set X) := by
      rw [hCD]
      exact hD
    simpa [eq_comm] using hC.eq hD'
  tfae_have 5 → 4 := by
    intro h U hUopen hUcompact
    have hUclopen :=
      isConstructible_isOpen_isClosed_constructibleTopology
        (hUcompact.isConstructible hUopen)
    apply isClosed_of_constructibleClosed_of_stableUnderSpecialization hUclopen.2
    intro x y hxy hxU
    have hxy' : x = y := h hxy
    simpa [hxy'] using hxU
  tfae_have 4 → 2 := by
    intro h
    apply @T2Space.mk X (inferInstance) (by
      intro x y hxy
      obtain ⟨U, hUopen, hxor⟩ := exists_isOpen_xor_mem hxy
      rcases hxor with hxy | hyx
      · obtain ⟨V, hV, hxV, hVU⟩ :=
          PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxy.1 hUopen
        exact ⟨V, Vᶜ, hV.1,
          (h V hV.1 hV.2).isOpen_compl, hxV,
          fun hyV => hxy.2 (hVU hyV), disjoint_compl_right⟩
      · obtain ⟨V, hV, hyV, hVU⟩ :=
          PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyx.1 hUopen
        exact ⟨Vᶜ, V, (h V hV.1 hV.2).isOpen_compl, hV.1,
          fun hxV => hyx.2 (hVU hxV), hyV, disjoint_compl_left⟩)
  tfae_have 2 → 1 := by
    intro h
    let _ : T2Space X := h
    have hTD : TotallyDisconnectedSpace X := inferInstance
    exact isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected.mpr
      ⟨h, inferInstance, hTD⟩
  tfae_have 4 ↔ 8 := by
    constructor
    · intro h
      have hclopen : ∀ E : Set X, IsConstructible E → IsOpen E ∧ IsClosed E := by
        intro E hE
        induction hE using IsConstructible.empty_union_induction with
        | open_retrocompact U hUopen hUcompact =>
            exact ⟨hUopen, h U hUopen hUcompact.isCompact⟩
        | union s hs t ht hs' ht' =>
            exact ⟨hs'.1.union ht'.1, hs'.2.union ht'.2⟩
        | compl s hs hs' =>
            exact ⟨hs'.2.isOpen_compl, hs'.1.isClosed_compl⟩
      apply le_antisymm
      · exact (isOpen_implies_isOpen_iff.mpr
          (fun U hU => isOpen_constructibleTopology_of_isOpen hU))
      · apply isOpen_implies_isOpen_iff.mpr
        intro E hE
        rcases isOpen_constructibleTopology_iff_iUnion_isConstructible.mp hE with
          ⟨S, hS, rfl⟩
        exact isOpen_sUnion fun U hU =>
          (hclopen U (hS U hU)).1
    · intro h E hEopen hEcompact
      have hEctclosed :=
        (isConstructible_isOpen_isClosed_constructibleTopology
          (hEcompact.isConstructible hEopen)).2
      rw [h] at hEctclosed
      exact hEctclosed
  tfae_finish

/-- The connected-components space of a spectral space is profinite. -/
theorem connectedComponents_isProfiniteSpace [SpectralSpace X] :
    IsProfiniteSpace (ConnectedComponents X) := by
  exact Formalization.Books.Topology.Unit22.connectedComponents_is_profinite
    (fun x =>
      Formalization.Books.Topology.Unit12.connectedComponent_eq_iInter_isClopen_of_compact_prespectral
        x)

/-- The product of two spectral spaces is spectral. -/
theorem spectralSpace_prod {Y : Type v} [TopologicalSpace Y]
    [SpectralSpace X] [SpectralSpace Y] :
    SpectralSpace (X × Y) := by
  classical
  have hquasi : QuasiSober (X × Y) := by
    refine { sober := ?_ }
    intro Z hZ hZclosed
    let pZ : Set X := Prod.fst '' Z
    let qZ : Set Y := Prod.snd '' Z
    have hpZ : IsIrreducible pZ := hZ.image Prod.fst continuous_fst.continuousOn
    have hqZ : IsIrreducible qZ := hZ.image Prod.snd continuous_snd.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hpZ.closure isClosed_closure
    obtain ⟨y, hy⟩ := QuasiSober.sober hqZ.closure isClosed_closure
    have hxyZ : (x, y) ∈ Z := by
      by_contra hnot
      obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hUV⟩ :=
        (@isOpen_prod_iff X Y (inferInstance : TopologicalSpace X)
          (inferInstance : TopologicalSpace Y)).mp hZclosed.isOpen_compl x y hnot
      have hxcl : x ∈ closure pZ := by
        rw [← hx.def]
        exact subset_closure (by simp)
      have hycl : y ∈ closure qZ := by
        rw [← hy.def]
        exact subset_closure (by simp)
      obtain ⟨z₁, hz₁U, hz₁p⟩ := mem_closure_iff.mp hxcl U hUopen hxU
      obtain ⟨z₂, hz₂V, hz₂q⟩ := mem_closure_iff.mp hycl V hVopen hyV
      rcases hz₁p with ⟨z₁, hz₁Z, rfl⟩
      rcases hz₂q with ⟨z₂, hz₂Z, rfl⟩
      have hZU : (Z ∩ (Prod.fst ⁻¹' U)).Nonempty := ⟨z₁, hz₁Z, hz₁U⟩
      have hZV : (Z ∩ (Prod.snd ⁻¹' V)).Nonempty := ⟨z₂, hz₂Z, hz₂V⟩
      obtain ⟨z, hzZ, hzUV⟩ :=
        hZ.isPreirreducible (Prod.fst ⁻¹' U) (Prod.snd ⁻¹' V)
          (hUopen.preimage continuous_fst) (hVopen.preimage continuous_snd) hZU hZV
      have hzUV' : z ∈ U ×ˢ V := hzUV
      exact (hUV hzUV') hzZ
    refine ⟨(x, y), ?_⟩
    rw [isGenericPoint_def]
    apply Set.Subset.antisymm
    · exact closure_minimal (singleton_subset_iff.mpr hxyZ) hZclosed
    · intro z hzZ
      have hzx : x ⤳ z.1 := by
        rw [specializes_iff_mem_closure, hx.def]
        exact subset_closure ⟨z, hzZ, rfl⟩
      have hzy : y ⤳ z.2 := by
        rw [specializes_iff_mem_closure, hy.def]
        exact subset_closure ⟨z, hzZ, rfl⟩
      exact specializes_iff_mem_closure.mp (specializes_prod.mpr ⟨hzx, hzy⟩)
  let b :
      ({U : Set X // IsOpen U ∧ IsCompact U} ×
        {V : Set Y // IsOpen V ∧ IsCompact V}) → Set (X × Y) :=
    fun p => (p.1 : Set X) ×ˢ (p.2 : Set Y)
  have hbset : Set.range b =
      image2 (· ×ˢ ·) {U : Set X | IsOpen U ∧ IsCompact U}
        {V : Set Y | IsOpen V ∧ IsCompact V} := by
    ext W
    constructor
    · rintro ⟨⟨U, V⟩, rfl⟩
      exact ⟨U, U.property, V, V.property, rfl⟩
    · rintro ⟨U, hU, V, hV, rfl⟩
      exact ⟨(⟨U, hU⟩, ⟨V, hV⟩), rfl⟩
  have hb : IsTopologicalBasis (Set.range b) := by
    rw [hbset]
    exact (PrespectralSpace.isTopologicalBasis (X := X)).prod
      (PrespectralSpace.isTopologicalBasis (X := Y))
  have hpres : PrespectralSpace (X × Y) :=
    PrespectralSpace.of_isTopologicalBasis' hb (fun p => p.1.2.2.prod p.2.2.2)
  have hqsep : QuasiSeparatedSpace (X × Y) :=
    QuasiSeparatedSpace.of_isTopologicalBasis hb (fun p q => by
      have hXcompact : IsCompact ((p.1 : Set X) ∩ (q.1 : Set X)) :=
        QuasiSeparatedSpace.inter_isCompact _ _ p.1.2.1 p.1.2.2 q.1.2.1 q.1.2.2
      have hYcompact : IsCompact ((p.2 : Set Y) ∩ (q.2 : Set Y)) :=
        QuasiSeparatedSpace.inter_isCompact _ _ p.2.2.1 p.2.2.2 q.2.2.1 q.2.2.2
      have heq : b p ∩ b q =
          ((p.1 : Set X) ∩ (q.1 : Set X)) ×ˢ
            ((p.2 : Set Y) ∩ (q.2 : Set Y)) := by
        ext z
        simp [b, and_assoc, and_left_comm]
      rw [heq]
      exact hXcompact.prod hYcompact)
  have hT0 : T0Space (X × Y) := inferInstance
  have hcompact : CompactSpace (X × Y) := inferInstance
  exact spectralSpace_iff_source_conditions.mpr
    ⟨hT0, hcompact, hquasi, hqsep, hpres⟩

/-- A bijective spectral map between spectral spaces is a homeomorphism when
specializations or generalizations lift along it. -/
theorem isHomeomorph_of_bijective_spectralMap_of_lift
    {Y : Type v} [TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y]
    (f : X → Y) (hf : IsSpectralMap f) (hbijective : Function.Bijective f)
    (hlift : GeneralizingMap f ∨ SpecializingMap f) :
    IsHomeomorph f := by
  have hcontct :
      Continuous[constructibleTopology X, constructibleTopology Y] f :=
    (spectralMap_constructibleTopology_properties f hf).1
  have hXct : @CompactSpace X (constructibleTopology X) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := X)).2.2
  have hYct : @T2Space Y (constructibleTopology Y) :=
    (constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact (X := Y)).1
  have hct :
      @IsHomeomorph X Y (constructibleTopology X) (constructibleTopology Y) f := by
    apply (@isHomeomorph_iff_continuous_bijective X Y
      (constructibleTopology X) (constructibleTopology Y) f hXct hYct).2
    exact ⟨hcontct, hbijective⟩
  have hopen_of_generalizing (hgeneralizing : GeneralizingMap f) :
      ∀ V : Set X, IsOpen V → IsCompact V → IsOpen (f '' V) := by
    intro V hVopen hVcompact
    have hVctopen : @IsOpen X (constructibleTopology X) V :=
      hVcompact.isOpen_constructibleTopology_of_isOpen hVopen
    have hfVctopen : @IsOpen Y (constructibleTopology Y) (f '' V) :=
      (@IsHomeomorph.isOpenMap X Y (constructibleTopology X) (constructibleTopology Y) f hct)
        _ hVctopen
    exact isOpen_of_constructibleOpen_of_stableUnderGeneralization hfVctopen
      (show StableUnderGeneralization (f '' V) from
        hgeneralizing.stableUnderGeneralization_image
          hVopen.stableUnderGeneralization)
  have hopen_of_specializing (hspecializing : SpecializingMap f) :
      ∀ V : Set X, IsOpen V → IsCompact V → IsOpen (f '' V) := by
    intro V hVopen hVcompact
    have hVctopen : @IsOpen X (constructibleTopology X) V :=
      hVcompact.isOpen_constructibleTopology_of_isOpen hVopen
    have hVctclosed : @IsClosed X (constructibleTopology X) Vᶜ :=
      (@isClosed_compl_iff X (constructibleTopology X) V).mpr hVctopen
    have hfVcomplctclosed :
        @IsClosed Y (constructibleTopology Y) (f '' Vᶜ) :=
      (@IsHomeomorph.isClosedMap X Y (constructibleTopology X) (constructibleTopology Y) f hct)
        _ hVctclosed
    have hfVcomplclosed : IsClosed (f '' Vᶜ) :=
      isClosed_of_constructibleClosed_of_stableUnderSpecialization
        hfVcomplctclosed
        (hspecializing.stableUnderSpecialization_image
          hVopen.isClosed_compl.stableUnderSpecialization)
    simpa only [Set.image_compl_eq hbijective, compl_compl] using hfVcomplclosed.isOpen_compl
  have hopenmap : IsOpenMap f := by
    rcases hlift with hgeneralizing | hspecializing
    · intro U hU
      refine (PrespectralSpace.isTopologicalBasis (X := Y)).isOpen_iff.mpr ?_
      intro y hy
      obtain ⟨x, rfl⟩ := hbijective.2 y
      have hxU : x ∈ U := by
        rcases hy with ⟨x', hx', hfx'⟩
        have hxeq : x' = x := hbijective.1 hfx'
        simpa [hxeq] using hx'
      obtain ⟨V, hV, hxV, hVU⟩ :=
        (PrespectralSpace.isTopologicalBasis (X := X)).isOpen_iff.mp hU x hxU
      refine ⟨f '' V, ?_, ⟨x, hxV, rfl⟩, Set.image_mono hVU⟩
      exact ⟨hopen_of_generalizing hgeneralizing V hV.1 hV.2,
        hV.2.image hf.continuous⟩
    · intro U hU
      refine (PrespectralSpace.isTopologicalBasis (X := Y)).isOpen_iff.mpr ?_
      intro y hy
      obtain ⟨x, rfl⟩ := hbijective.2 y
      have hxU : x ∈ U := by
        rcases hy with ⟨x', hx', hfx'⟩
        have hxeq : x' = x := hbijective.1 hfx'
        simpa [hxeq] using hx'
      obtain ⟨V, hV, hxV, hVU⟩ :=
        (PrespectralSpace.isTopologicalBasis (X := X)).isOpen_iff.mp hU x hxU
      refine ⟨f '' V, ?_, ⟨x, hxV, rfl⟩, Set.image_mono hVU⟩
      exact ⟨hopen_of_specializing hspecializing V hV.1 hV.2,
        hV.2.image hf.continuous⟩
  exact ⟨hf.continuous, hopenmap, hbijective.1, hbijective.2⟩

/-! ### Inverse limits -/

/-- The inverse limit of a directed inverse system of finite sober spaces is
spectral.  Sobriety is expressed canonically as `QuasiSober` plus `T0Space`. -/
theorem spectralSpace_of_directed_inverse_limit_finite_sober
    {J : Type v} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (F : Jᵒᵖ ⥤ TopCat.{max v u})
    (hfinite : ∀ j, Finite (F.obj j))
    (hsober : ∀ j, QuasiSober (F.obj j))
    (hT0 : ∀ j, T0Space (F.obj j)) :
    SpectralSpace ((limit F : TopCat.{max v u}) : Type (max v u)) := by
  sorry

/-- A bundled source-facing interface for a directed inverse system of finite
sober topological spaces. -/
structure DirectedFiniteSoberPresentation (X : Type u) [TopologicalSpace X] where
  index : Type u
  [preorder : Preorder index]
  [directed : IsDirectedOrder index]
  [nonempty : Nonempty index]
  diagram : indexᵒᵖ ⥤ TopCat.{u}
  finite : ∀ i, Finite (diagram.obj i)
  sober : ∀ i, QuasiSober (diagram.obj i)
  t0 : ∀ i, T0Space (diagram.obj i)
  homeomorph : X ≃ₜ ((limit diagram : TopCat.{u}) : Type u)

/-- A topological space is spectral exactly when it is homeomorphic to a
directed inverse limit of finite sober spaces. -/
theorem spectralSpace_iff_directed_inverse_limit_finite_sober :
    SpectralSpace X ↔
      Nonempty (DirectedFiniteSoberPresentation X) := by
  sorry

/-! ### The two-point product presentation -/

/-- The earlier chapter's `KrullTwoPointSpace` is the two-point space with one
generic point and one closed point used by the source. -/
theorem krullTwoPointSpace_is_finite_sober :
    Finite KrullTwoPointSpace ∧
      QuasiSober KrullTwoPointSpace ∧
        T0Space KrullTwoPointSpace := by
  have hfinite : Finite KrullTwoPointSpace := by
    apply Finite.of_injective (fun z : KrullTwoPointSpace =>
      match z with | .special => false | .generic => true)
    intro a b hab
    cases a <;> cases b <;> simp_all
  have hgenericOpen : IsOpen ({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace) :=
    krullTwoPointSpace_isOpen_iff.mpr (Or.inr (Or.inl rfl))
  have hspecialClosed : IsClosed ({KrullTwoPointSpace.special} : Set KrullTwoPointSpace) := by
    apply isOpen_compl_iff.mp
    rw [show ({KrullTwoPointSpace.special} : Set KrullTwoPointSpace)ᶜ =
      {KrullTwoPointSpace.generic} by ext z; cases z <;> simp]
    exact hgenericOpen
  have hspecial : IsGenericPoint KrullTwoPointSpace.special
      ({KrullTwoPointSpace.special} : Set KrullTwoPointSpace) := by
    rw [isGenericPoint_def]
    exact closure_eq_iff_isClosed.mpr hspecialClosed
  have hgeneric : IsGenericPoint KrullTwoPointSpace.generic
      (Set.univ : Set KrullTwoPointSpace) := by
    rw [isGenericPoint_def]
    apply Set.eq_univ_of_forall
    intro z
    cases z with
    | generic => exact subset_closure (by simp)
    | special =>
        apply mem_closure_iff.mpr
        intro U hUopen hUspecial
        rcases krullTwoPointSpace_isOpen_iff.mp hUopen with h0 | hg | hu
        · simp [h0] at hUspecial
        · simp [hg] at hUspecial
        · refine ⟨KrullTwoPointSpace.generic, ?_, by simp⟩
          simp [hu]
  have hquasi : QuasiSober KrullTwoPointSpace := by
    constructor
    intro S hS hSclosed
    have hSopen : IsOpen Sᶜ := hSclosed.isOpen_compl
    rcases krullTwoPointSpace_isOpen_iff.mp hSopen with h0 | hg | hu
    · have hSuniv : S = Set.univ := by
        simpa only [compl_compl, compl_empty] using congrArg compl h0
      exact ⟨KrullTwoPointSpace.generic, hSuniv ▸ hgeneric⟩
    · have hSspecial : S = ({KrullTwoPointSpace.special} : Set KrullTwoPointSpace) := by
        rw [← compl_compl S, hg]
        ext z
        cases z <;> simp
      exact ⟨KrullTwoPointSpace.special, hSspecial ▸ hspecial⟩
    · have hSempty : S = ∅ := by
        simpa only [compl_compl, compl_univ] using congrArg compl hu
      have hfalse : False := by
        simpa [hSempty] using hS.nonempty
      exact hfalse.elim
  have hT0 : T0Space KrullTwoPointSpace := by
    apply (t0Space_iff_exists_isOpen_xor_mem KrullTwoPointSpace).mpr
    intro a b hab
    cases a with
    | special =>
        cases b with
        | special => exact (hab rfl).elim
        | generic =>
            refine ⟨{KrullTwoPointSpace.generic}, hgenericOpen, ?_⟩
            exact Or.inr ⟨by simp, by simp⟩
    | generic =>
        cases b with
        | special =>
            refine ⟨{KrullTwoPointSpace.generic}, hgenericOpen, ?_⟩
            exact Or.inl ⟨by simp, by simp⟩
        | generic => exact (hab rfl).elim
  exact ⟨hfinite, hquasi, hT0⟩

/-- Spectral spaces are precisely the constructibly closed subspaces of
products of copies of the two-point space, up to homeomorphism. -/
theorem spectralSpace_iff_constructibleClosed_subspace_of_product_twoPoint :
    SpectralSpace X ↔
      ∃ (I : Type u) (E : Set (I → KrullTwoPointSpace)),
        IsClosed[constructibleTopology (I → KrullTwoPointSpace)] E ∧
          Nonempty (X ≃ₜ E) := by
  sorry

/-! ### Soberification and Noetherian spaces -/

private theorem soberification_isTopologicalBasis :
    IsTopologicalBasis (soberificationBasis (X := X)) := by
  apply isTopologicalBasis_of_subbasis_of_finiteInter
  · rfl
  · refine { univ_mem := ?_, inter_mem := ?_ }
    · refine ⟨⟨Set.univ, isOpen_univ⟩, ?_⟩
      ext Z
      change ((Z : Set X) ∩ (Set.univ : Set X)).Nonempty ↔
        Z ∈ (Set.univ : Set (Soberification X))
      simp only [inter_univ, mem_univ, iff_true]
      exact Z.isIrreducible.nonempty
    · rintro _ ⟨U, rfl⟩ _ ⟨V, rfl⟩
      refine ⟨⟨(U : Set X) ∩ V, U.isOpen.inter V.isOpen⟩, ?_⟩
      ext Z
      change ((Z : Set X) ∩ ((U : Set X) ∩ V)).Nonempty ↔
        ((Z : Set X) ∩ U).Nonempty ∧ ((Z : Set X) ∩ (V : Set X)).Nonempty
      constructor
      · rintro ⟨x, hxZ, hxUV⟩
        exact ⟨⟨x, hxZ, hxUV.1⟩, ⟨x, hxZ, hxUV.2⟩⟩
      · rintro ⟨⟨x, hxZ, hxU⟩, ⟨y, hyZ, hyV⟩⟩
        exact Z.isIrreducible.isPreirreducible (U : Set X) (V : Set X)
          U.isOpen V.isOpen ⟨x, hxZ, hxU⟩ ⟨y, hyZ, hyV⟩

/-- The soberification of a quasi-compact space is quasi-compact. -/
private theorem soberification_isCompact_of_isOpen_isCompact [CompactSpace X]
    {U : Set X} (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    IsCompact (soberificationOpen (X := X) U) := by
  classical
  refine isCompact_of_finite_subcover ?_
  intro ι V hVopen hVcover
  have hex : ∀ x : U, ∃ i : ι,
      soberificationMap (X := X) (x : X) ∈ V i := by
    intro x
    have hxS : soberificationMap (X := X) (x : X) ∈ soberificationOpen (X := X) U := by
      change ((closure ({(x : X)} : Set X) ∩ U).Nonempty)
      exact ⟨x, subset_closure (by simp), x.property⟩
    rcases mem_iUnion.mp (hVcover hxS) with ⟨i, hi⟩
    exact ⟨i, hi⟩
  choose i hi using hex
  have hexBasis : ∀ x : U, ∃ A : Opens X,
      soberificationMap (X := X) (x : X) ∈ soberificationOpen (A : Set X) ∧
        soberificationOpen (A : Set X) ⊆ V (i x) := by
    intro x
    obtain ⟨W, hW, hxW, hWV⟩ :=
      soberification_isTopologicalBasis.exists_subset_of_mem_open (hi x) (hVopen (i x))
    rcases hW with ⟨A, rfl⟩
    exact ⟨A, hxW, hWV⟩
  choose A hA hAsub using hexBasis
  have hAx : ∀ x : U, (x : X) ∈ (A x : Set X) := by
    intro x
    have hxA := hA x
    change ((closure ({(x : X)} : Set X) ∩ (A x : Set X)).Nonempty) at hxA
    exact (isGenericPoint_closure.mem_open_set_iff (A x).isOpen).mpr hxA
  let B : U → Set X := fun x => (A x : Set X) ∩ U
  have hBopen : ∀ x : U, IsOpen (B x) := by
    intro x
    exact (A x).isOpen.inter hUopen
  have hBcover : U ⊆ ⋃ x : U, B x := by
    intro x hx
    have hxB : x ∈ B ⟨x, hx⟩ := ⟨hAx ⟨x, hx⟩, hx⟩
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxB⟩
  obtain ⟨s, hs⟩ := hUcompact.elim_finite_subcover B hBopen hBcover
  refine ⟨s.image i, ?_⟩
  intro Z hZ
  change Z ∈ ⋃ j ∈ s.image i, V j
  rcases hZ with ⟨x, hxZ, hxU⟩
  rcases mem_iUnion.mp (hs hxU) with ⟨x', hx'⟩
  rcases mem_iUnion.mp hx' with ⟨hx's, hxB⟩
  have hxA : x ∈ (A x' : Set X) := hxB.1
  have hZA : Z ∈ soberificationOpen (A x' : Set X) := ⟨x, hxZ, hxA⟩
  have hZV : Z ∈ V (i x') := hAsub x' hZA
  exact mem_iUnion.mpr ⟨i x', mem_iUnion.mpr ⟨s.mem_image_of_mem i hx's, hZV⟩⟩

/-- The soberification of a quasi-compact space is quasi-compact. -/
theorem soberification_is_quasiCompact [CompactSpace X] :
    CompactSpace (Soberification X) := by
  have hcu : IsCompact (soberificationOpen (X := X) (Set.univ : Set X)) :=
    soberification_isCompact_of_isOpen_isCompact isOpen_univ isCompact_univ
  have heq : soberificationOpen (X := X) (Set.univ : Set X) =
      (Set.univ : Set (Soberification X)) := by
    ext Z
    change ((Z : Set X) ∩ (Set.univ : Set X)).Nonempty ↔ _
    simp [Z.isIrreducible.nonempty]
  exact ⟨heq ▸ hcu⟩

/-- The soberification of a quasi-compact prespectral quasi-separated space is
spectral. -/
theorem soberification_is_spectral [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] :
    SpectralSpace (Soberification X) := by
  let b : {U : Opens X // IsCompact (U : Set X)} → Set (Soberification X) :=
    fun U => soberificationOpen (U : Set X)
  have hb : IsTopologicalBasis (Set.range b) := by
    apply soberification_isTopologicalBasis.isTopologicalBasis_of_exists_subset
    · rintro _ ⟨U, rfl⟩
      exact soberification_isTopologicalBasis.isOpen ⟨U, rfl⟩
    · rintro W ⟨U, rfl⟩ Z hZ
      change ((Z : Set X) ∩ (U : Set X)).Nonempty at hZ
      rcases hZ with ⟨x, hxZ, hxU⟩
      obtain ⟨V, ⟨hVopen, hVcompact⟩, hxV, hVU⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU U.isOpen
      let V' : Opens X := ⟨V, hVopen⟩
      refine ⟨b ⟨V', hVcompact⟩, ⟨⟨V', hVcompact⟩, rfl⟩, ?_, ?_⟩
      · exact ⟨x, hxZ, hxV⟩
      · intro Q hQ
        rcases hQ with ⟨y, hyQ, hyV⟩
        exact ⟨y, hyQ, hVU hyV⟩
  have hPres : PrespectralSpace (Soberification X) :=
    PrespectralSpace.of_isTopologicalBasis' hb (fun U =>
      soberification_isCompact_of_isOpen_isCompact U.1.isOpen U.2)
  have hQS : QuasiSeparatedSpace (Soberification X) :=
    QuasiSeparatedSpace.of_isTopologicalBasis hb (fun U V => by
      have hUVcompact : IsCompact ((U.1 : Set X) ∩ (V.1 : Set X)) :=
        QuasiSeparatedSpace.inter_isCompact _ _ U.1.isOpen U.2 V.1.isOpen V.2
      have heq : b U ∩ b V =
          soberificationOpen (X := X) ((U.1 : Set X) ∩ (V.1 : Set X)) := by
        ext Z
        constructor
        · intro hZ
          rcases hZ.1 with ⟨x, hxZ, hxU⟩
          rcases hZ.2 with ⟨y, hyZ, hyV⟩
          exact Z.isIrreducible.isPreirreducible (U.1 : Set X) (V.1 : Set X)
            U.1.isOpen V.1.isOpen ⟨x, hxZ, hxU⟩ ⟨y, hyZ, hyV⟩
        · intro hZ
          rcases hZ with ⟨x, hxZ, hxUV⟩
          exact ⟨⟨x, hxZ, hxUV.1⟩, ⟨x, hxZ, hxUV.2⟩⟩
      rw [heq]
      exact soberification_isCompact_of_isOpen_isCompact
        (U.1.isOpen.inter V.1.isOpen) hUVcompact)
  let hsob := soberification_is_sober (X := X)
  let _ : T0Space (Soberification X) := hsob.2
  let _ : CompactSpace (Soberification X) := soberification_is_quasiCompact (X := X)
  let _ : QuasiSober (Soberification X) := hsob.1
  let _ : PrespectralSpace (Soberification X) := hPres
  let _ : QuasiSeparatedSpace (Soberification X) := hQS
  exact spectralSpace_iff_source_conditions.mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The soberification of a Noetherian space is Noetherian and spectral. -/
theorem soberification_is_noetherian_spectral [NoetherianSpace X] :
    NoetherianSpace (Soberification X) ∧ SpectralSpace (Soberification X) := by
  constructor
  · apply (noetherianSpace_iff_opens _).mpr
    intro O
    let U : Opens X := soberificationOpenComap (X := X) O
    let V : Opens (Soberification X) :=
      ⟨soberificationOpen (U : Set X),
        isOpen_generateFrom_of_mem ⟨U, rfl⟩⟩
    have hcomapV : soberificationOpenComap (X := X) V = U := by
      apply Opens.ext
      ext x
      change soberificationMap (X := X) x ∈ soberificationOpen (U : Set X) ↔ x ∈ U
      exact (isGenericPoint_closure.mem_open_set_iff U.isOpen).symm
    have hOV : O = V := by
      apply (soberificationOpenComap_bijective (X := X)).1
      simpa [U] using hcomapV.symm
    rw [hOV]
    exact soberification_isCompact_of_isOpen_isCompact U.isOpen
      (NoetherianSpace.isCompact (U : Set X))
  · exact soberification_is_spectral (X := X)

end SpectralSpaces

end Formalization.Books.Topology.Unit23
