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

variable {X : Type u} [topologyX : TopologicalSpace X]

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
    (∀ E : Set X, @IsConstructible X topologyX E →
      @IsOpen X (@constructibleTopology X topologyX) E ∧
        @IsClosed X (@constructibleTopology X topologyX) E) ∧
    ∀ t : TopologicalSpace X,
    (∀ E : Set X, @IsConstructible X topologyX E →
      @IsOpen X t E ∧ @IsClosed X t E) →
          t ≤ @constructibleTopology X topologyX := by
  constructor
  · intro E hE
    exact isConstructible_isOpen_isClosed_constructibleTopology hE
  · intro t ht
    change t ≤ @TopologicalSpace.generateFrom X (@constructibleTopologySubbasis X topologyX)
    apply le_generateFrom
    rintro s (hs | hs)
    · have hsc : @IsConstructible X topologyX s :=
        @IsCompact.isConstructible X topologyX s
          (inferInstance : @QuasiSeparatedSpace X topologyX) hs.2 hs.1
      exact show @IsOpen X t s from (ht s hsc).1
    · have hopen : @IsOpen X topologyX sᶜ :=
        @IsClosed.isOpen_compl X topologyX s hs.1
      have hsc : @IsConstructible X topologyX sᶜ :=
        @IsCompact.isConstructible X topologyX sᶜ
          (inferInstance : @QuasiSeparatedSpace X topologyX) hs.2 hopen
      exact show @IsOpen X t s from
        (ht s (@IsConstructible.of_compl X topologyX s hsc)).1

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
  classical
  let L := ((limit F : TopCat.{max v u}) : Type (max v u))
  let P := ∀ j : Jᵒᵖ, (F.obj j : Type (max v u))
  let tP : TopologicalSpace P :=
    @Pi.topologicalSpace (Jᵒᵖ) (fun j => (F.obj j : Type (max v u)))
      (fun j => (F.obj j).str)
  let _ : TopologicalSpace P := tP
  let g : L → P := fun x j => (limit.π F j) x
  have hgind : @Topology.IsInducing L P (inferInstance : TopologicalSpace L) tP g := by
    rw [TopCat.limit_topology F]
    exact inducing_iInf_to_pi (fun j => limit.π F j)
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Concrete.limit_ext F x y
    intro j
    exact congrFun hxy j
  let C : Set P :=
    ⋂ (i : Jᵒᵖ) (j : Jᵒᵖ) (f : i ⟶ j), {x | F.map f (x i) = x j}
  have hgrange : Set.range g = C := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      dsimp [C]
      simp only [mem_iInter]
      intro i j f
      exact ConcreteCategory.congr_hom (limit.w F f) x
    · intro y hy
      have hy' : ∀ (i j : Jᵒᵖ) (f : i ⟶ j), F.map f (y i) = y j := by
        simpa [C] using hy
      let S : Cone F :=
        { pt := TopCat.of PUnit
          π :=
            { app := fun j => TopCat.ofHom
                { toFun := fun _ : PUnit => y j
                  continuous_toFun := continuous_const }
              naturality := by
                intro i j f
                ext x
                simpa using (hy' i j f).symm } }
      refine ⟨(limit.isLimit F).lift S PUnit.unit, ?_⟩
      funext j
      exact ConcreteCategory.congr_hom ((limit.isLimit F).fac S j) PUnit.unit
  let tD : TopologicalSpace P :=
    @Pi.topologicalSpace (Jᵒᵖ) (fun j => (F.obj j : Type (max v u))) (fun _ => ⊥)
  let _ : TopologicalSpace P := tP
  have hDcompact : @CompactSpace P tD := by
    let _ : ∀ j : Jᵒᵖ, TopologicalSpace (F.obj j) := fun _ => ⊥
    let _ : ∀ j : Jᵒᵖ, DiscreteTopology (F.obj j) := fun j => discreteTopology_bot _
    let _ : ∀ j : Jᵒᵖ, Finite (F.obj j) := hfinite
    let _ : TopologicalSpace P := tD
    infer_instance
  have hCcompact : @IsCompact P tD C := by
    let _ : ∀ j : Jᵒᵖ, TopologicalSpace (F.obj j) := fun _ => ⊥
    let _ : ∀ j : Jᵒᵖ, DiscreteTopology (F.obj j) := fun j => discreteTopology_bot _
    let _ : TopologicalSpace P := tD
    have hCclosed : @IsClosed P tD C := by
      dsimp [C]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro f
      exact isClosed_eq
        ((continuous_of_discreteTopology : @Continuous (F.obj i) (F.obj j) ⊥ ⊥
          (F.map f)).comp (continuous_apply i))
        (continuous_apply j)
    exact @IsClosed.isCompact P tD C hDcompact hCclosed
  have hCcompact_cylinder (j : Jᵒᵖ) (V : Set (F.obj j)) :
      @IsCompact P tD (C ∩ {x | x j ∈ V}) := by
    let _ : ∀ j : Jᵒᵖ, TopologicalSpace (F.obj j) := fun _ => ⊥
    let _ : ∀ j : Jᵒᵖ, DiscreteTopology (F.obj j) := fun j => discreteTopology_bot _
    let _ : TopologicalSpace P := tD
    have hCclosed : @IsClosed P tD C := by
      dsimp [C]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j'
      apply isClosed_iInter
      intro f
      exact isClosed_eq
        ((continuous_of_discreteTopology : @Continuous (F.obj i) (F.obj j') ⊥ ⊥
          (F.map f)).comp (continuous_apply i))
        (continuous_apply j')
    have hVclosed : @IsClosed P tD {x | x j ∈ V} := by
      exact (isClosed_discrete V).preimage (continuous_apply j)
    exact @IsClosed.isCompact P tD (C ∩ {x | x j ∈ V}) hDcompact
      (hCclosed.inter hVclosed)
  have hId : @Continuous P P tD tP id := by
    apply continuous_iff_le_induced.mpr
    change
      @Pi.topologicalSpace (Jᵒᵖ) (fun j => (F.obj j : Type (max v u))) (fun _ => ⊥) ≤
        TopologicalSpace.induced id
          (@Pi.topologicalSpace (Jᵒᵖ) (fun j => (F.obj j : Type (max v u)))
            (fun j => (F.obj j).str))
    simp only [induced_id, Pi.topologicalSpace]
    exact iInf_mono fun j => induced_mono bot_le
  have hcompact_cylinder (j : Jᵒᵖ) (V : Set (F.obj j)) :
      IsCompact ((limit.π F j) ⁻¹' V) := by
    have himage : g '' ((limit.π F j) ⁻¹' V) = C ∩ {x | x j ∈ V} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨hgrange ▸ ⟨y, rfl⟩, ?_⟩
        change (limit.π F j) y ∈ V at hy
        simpa [g] using hy
      · rintro ⟨hxC, hxV⟩
        have hxrange : x ∈ Set.range g := by
          rw [hgrange]
          exact hxC
        rcases hxrange with ⟨y, rfl⟩
        refine ⟨y, ?_, rfl⟩
        change (limit.π F j) y ∈ V
        change (g y) j ∈ V at hxV
        simpa [g] using hxV
    apply (@Topology.IsInducing.isCompact_iff L P
      (inferInstance : TopologicalSpace L) tP ((limit.π F j) ⁻¹' V) g hgind).mpr
    rw [himage]
    have hcompactC' : @IsCompact P tP (C ∩ {x | x j ∈ V}) := by
      simpa only [image_id] using
        (@IsCompact.image P P tD tP (C ∩ {x | x j ∈ V}) id
          (hCcompact_cylinder j V) hId)
    simpa only [image_id] using hcompactC'
  have hcompactL : CompactSpace L := by
    have huniv : IsCompact (Set.univ : Set L) := by
      apply (@Topology.IsInducing.isCompact_iff L P
        (inferInstance : TopologicalSpace L) tP Set.univ g hgind).mpr
      rw [image_univ, hgrange]
      have hcompactC' : @IsCompact P tP C := by
        simpa only [image_id] using
          (@IsCompact.image P P tD tP C id hCcompact hId)
      simpa only [image_id] using hcompactC'
    exact ⟨huniv⟩
  let B : Set (Set L) :=
    {U | ∃ (j : Jᵒᵖ) (V : Set (F.obj j)), IsOpen V ∧ U = (limit.π F j) ⁻¹' V}
  have hB : IsTopologicalBasis B := by
    let T : ∀ j : Jᵒᵖ, Set (Set (F.obj j)) := fun _ => {V | IsOpen V}
    have hT : ∀ j, IsTopologicalBasis (T j) := by
      intro j
      simpa [T] using
        (isTopologicalBasis_opens : IsTopologicalBasis {V : Set (F.obj j) | IsOpen V})
    have huniv : ∀ i : Jᵒᵖ, Set.univ ∈ T i := by
      intro i
      exact isOpen_univ
    have hinter : ∀ (i : Jᵒᵖ) (U₁ U₂ : Set (F.obj i)), U₁ ∈ T i → U₂ ∈ T i →
        U₁ ∩ U₂ ∈ T i := by
      intro i U₁ U₂ hU₁ hU₂
      exact hU₁.inter hU₂
    have hcompat : ∀ (i j : Jᵒᵖ) (f : i ⟶ j) (V : Set (F.obj j)) (_hV : V ∈ T j),
        F.map f ⁻¹' V ∈ T i := by
      intro i j f V hV
      exact hV.preimage (F.map f).hom.2
    simpa [B, T] using
      (TopCat.isTopologicalBasis_cofiltered_limit.{u, v, v}
        (F := F) (C := limit.cone F) (limit.isLimit F) T hT huniv hinter hcompat)
  have hcompactB : ∀ U ∈ B, IsCompact U := by
    rintro U ⟨j, V, hV, rfl⟩
    exact hcompact_cylinder j V
  have hprespectral : PrespectralSpace L :=
    PrespectralSpace.of_isTopologicalBasis hB hcompactB
  let b : (Σ j : Jᵒᵖ, {V : Set (F.obj j) // IsOpen V}) → Set L :=
    fun p => (limit.π F p.1) ⁻¹' p.2.1
  have hbasis : IsTopologicalBasis (Set.range b) := by
    have hrange : Set.range b = B := by
      ext U
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.1, p.2.1, p.2.2, rfl⟩
      · rintro ⟨j, V, hV, rfl⟩
        exact ⟨⟨j, ⟨V, hV⟩⟩, rfl⟩
    rw [hrange]
    exact hB
  have hcompact_inter (p q : Σ j : Jᵒᵖ, {V : Set (F.obj j) // IsOpen V}) :
      IsCompact (b p ∩ b q) := by
    let G : Finset (Jᵒᵖ) := {p.1, q.1}
    obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists G
    have hpG : p.1 ∈ G := by
      change p.1 ∈ ({p.1, q.1} : Finset (Jᵒᵖ))
      exact Finset.mem_insert_self _ _
    have hqG : q.1 ∈ G := by
      change q.1 ∈ ({p.1, q.1} : Finset (Jᵒᵖ))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    let a : k ⟶ p.1 := (hk hpG).some
    let c : k ⟶ q.1 := (hk hqG).some
    let V : Set (F.obj k) := (F.map a) ⁻¹' p.2.1 ∩ (F.map c) ⁻¹' q.2.1
    have hV : IsOpen V := by
      dsimp [V]
      exact (p.2.2.preimage (F.map a).hom.2).inter (q.2.2.preimage (F.map c).hom.2)
    have heq : b p ∩ b q = (limit.π F k) ⁻¹' V := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · change F.map a ((limit.π F k) x) ∈ p.2.1
          rw [← ConcreteCategory.comp_apply, limit.w F a]
          exact hx.1
        · change F.map c ((limit.π F k) x) ∈ q.2.1
          rw [← ConcreteCategory.comp_apply, limit.w F c]
          exact hx.2
      · intro hx
        change (F.map a ((limit.π F k) x) ∈ p.2.1 ∧
          F.map c ((limit.π F k) x) ∈ q.2.1) at hx
        refine ⟨?_, ?_⟩
        · change (limit.π F p.1) x ∈ p.2.1
          have hxa := hx.1
          rw [← ConcreteCategory.comp_apply, limit.w F a] at hxa
          exact hxa
        · change (limit.π F q.1) x ∈ q.2.1
          have hxc := hx.2
          rw [← ConcreteCategory.comp_apply, limit.w F c] at hxc
          exact hxc
    rw [heq]
    exact hcompact_cylinder k V
  have hquasiSeparated : QuasiSeparatedSpace L :=
    QuasiSeparatedSpace.of_isTopologicalBasis hbasis hcompact_inter
  have hcont : @Continuous L P (inferInstance : TopologicalSpace L) tP g := by
    exact @Topology.IsInducing.continuous L P g
      tP (inferInstance : TopologicalSpace L) hgind
  have hT0L : T0Space L := by
    let _ : ∀ j : Jᵒᵖ, T0Space (F.obj j) := hT0
    have hT0P : @T0Space P
        tP := by
      exact @Pi.instT0Space (Jᵒᵖ) (fun j => (F.obj j : Type (max v u)))
        (fun j => (F.obj j).str) hT0
    exact @t0Space_of_injective_of_continuous L P (inferInstance : TopologicalSpace L)
      tP g hginj hcont hT0P
  have hquasiSober : QuasiSober L := by
    constructor
    intro Z hZ hZclosed
    let Zj : ∀ j : Jᵒᵖ, Set (F.obj j) := fun j => (limit.π F j) '' Z
    have hZj : ∀ j, IsIrreducible (Zj j) := by
      intro j
      exact hZ.image _ (limit.π F j).hom.2.continuousOn
    let xj : ∀ j : Jᵒᵖ, F.obj j := fun j =>
      Classical.choose ((hsober j).sober (hZj j).closure isClosed_closure)
    have hxj : ∀ j, IsGenericPoint (xj j) (closure (Zj j)) := by
      intro j
      exact Classical.choose_spec ((hsober j).sober (hZj j).closure isClosed_closure)
    have hxcompat : ∀ (i j : Jᵒᵖ) (f : i ⟶ j), F.map f (xj i) = xj j := by
      intro i j f
      let _ : T0Space (F.obj j) := hT0 j
      apply Inseparable.eq
      rw [inseparable_iff_forall_isOpen]
      intro V hV
      have hleft : F.map f (xj i) ∈ V ↔
          (Zj i ∩ (F.map f) ⁻¹' V).Nonempty := by
        change xj i ∈ (F.map f).hom ⁻¹' V ↔
          (Zj i ∩ (F.map f).hom ⁻¹' V).Nonempty
        exact (hxj i).mem_open_set_iff (hV.preimage (F.map f).hom.2) |>.trans
          (closure_inter_open_nonempty_iff (hV.preimage (F.map f).hom.2))
      have hright : xj j ∈ V ↔ (Zj j ∩ V).Nonempty := by
        rw [hxj j |>.mem_open_set_iff hV, closure_inter_open_nonempty_iff hV]
      have himage : (Zj i ∩ (F.map f) ⁻¹' V).Nonempty ↔ (Zj j ∩ V).Nonempty := by
        constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, hzV⟩
          refine ⟨(limit.π F j) z, ⟨z, hz, rfl⟩, ?_⟩
          change F.map f ((limit.π F i) z) ∈ V at hzV
          rw [← ConcreteCategory.comp_apply, limit.w F f] at hzV
          exact hzV
        · rintro ⟨_, ⟨z, hz, rfl⟩, hzV⟩
          refine ⟨(limit.π F i) z, ⟨z, hz, rfl⟩, ?_⟩
          change F.map f ((limit.π F i) z) ∈ V
          rw [← ConcreteCategory.comp_apply, limit.w F f]
          exact hzV
      exact hleft.trans (himage.trans hright.symm)
    let x : P := xj
    have hxC : x ∈ C := by
      dsimp [C, x]
      simp only [mem_iInter]
      intro i j f
      exact hxcompat i j f
    have hxrange : x ∈ Set.range g := by
      rw [hgrange]
      exact hxC
    obtain ⟨y, hy⟩ := hxrange
    have hbasic : ∀ (j : Jᵒᵖ) (V : Set (F.obj j)), IsOpen V →
        (y ∈ (limit.π F j) ⁻¹' V ↔ (Z ∩ (limit.π F j) ⁻¹' V).Nonempty) := by
      intro j V hV
      have hleft : xj j ∈ V ↔ (Zj j ∩ V).Nonempty := by
        rw [hxj j |>.mem_open_set_iff hV, closure_inter_open_nonempty_iff hV]
      have hright : (Zj j ∩ V).Nonempty ↔
          (Z ∩ (limit.π F j) ⁻¹' V).Nonempty := by
        constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, hzV⟩
          exact ⟨z, hz, hzV⟩
        · rintro ⟨z, hz, hzV⟩
          exact ⟨(limit.π F j) z, ⟨z, hz, rfl⟩, hzV⟩
      have hyj : (limit.π F j) y = xj j := by
        simpa [g, x] using congrFun hy j
      rw [show y ∈ (limit.π F j) ⁻¹' V ↔ xj j ∈ V by simp [hyj]]
      exact hleft.trans hright
    have hyZ : y ∈ Z := by
      by_contra hyZ
      obtain ⟨U, hU, hyU, hUZ⟩ := hB.isOpen_iff.mp hZclosed.isOpen_compl y hyZ
      change ∃ (j : Jᵒᵖ) (V : Set (F.obj j)), IsOpen V ∧
        U = (limit.π F j) ⁻¹' V at hU
      obtain ⟨j, V, hV, rfl⟩ := hU
      have hnonempty := (hbasic j V hV).mp hyU
      rcases hnonempty with ⟨z, hz, hzV⟩
      exact (hUZ hzV) hz
    refine ⟨y, ?_⟩
    rw [isGenericPoint_def]
    apply subset_antisymm
    · exact closure_minimal (singleton_subset_iff.mpr hyZ) hZclosed
    · intro z hz
      rw [mem_closure_iff]
      intro U hU hzU
      obtain ⟨B', hB', hzB', hB'U⟩ := hB.isOpen_iff.mp hU z hzU
      rcases hB' with ⟨j, V, hV, rfl⟩
      exact ⟨y, hB'U ((hbasic j V hV).mpr ⟨z, hz, hzB'⟩), rfl⟩
  exact { __ := hT0L, __ := hcompactL, __ := hquasiSober, __ := hquasiSeparated, __ := hprespectral }

private theorem quasiSober_of_finite {Y : Type u} [TopologicalSpace Y] [Finite Y] :
    QuasiSober Y := by
  classical
  constructor
  intro Z hZ hZclosed
  let t : Finset (Set Y) := (Set.toFinite Z).toFinset.image
    (fun z : Y => closure ({z} : Set Y))
  have htclosed : ∀ S ∈ t, IsClosed S := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨z, -, rfl⟩
    exact isClosed_closure
  have hZsub : Z ⊆ ⋃₀ (t : Set (Set Y)) := by
    intro z hz
    refine mem_sUnion.mpr ⟨closure ({z} : Set Y), ?_, subset_closure (by simp)⟩
    exact Finset.mem_image.mpr ⟨z, (Set.toFinite Z).mem_toFinset.mpr hz, rfl⟩
  obtain ⟨S, hSt, hZS⟩ :=
    (isIrreducible_iff_sUnion_isClosed.mp hZ) t htclosed hZsub
  rcases Finset.mem_image.mp hSt with ⟨z, hzZ, rfl⟩
  have hzZ' : z ∈ Z := (Set.toFinite Z).mem_toFinset.mp hzZ
  refine ⟨z, ?_⟩
  rw [isGenericPoint_def]
  apply subset_antisymm
  · exact closure_minimal (singleton_subset_iff.mpr hzZ') hZclosed
  · exact hZS

private theorem constructibleOpen_contains_finite_coordinate_cylinder
    {I : Type u} {U : Set (I → KrullTwoPointSpace)}
    (hU : IsOpen[constructibleTopology (I → KrullTwoPointSpace)] U) {x : I → KrullTwoPointSpace}
    (hx : x ∈ U) :
    ∃ F : Finset I,
      x ∈ (F : Set I).pi (fun i => ({x i} : Set KrullTwoPointSpace)) ∧
        (F : Set I).pi (fun i => ({x i} : Set KrullTwoPointSpace)) ⊆ U := by
  classical
  change TopologicalSpace.GenerateOpen
      (constructibleTopologySubbasis (I → KrullTwoPointSpace)) U at hU
  induction hU generalizing x with
  | basic S hS =>
      rcases hS with ⟨hSopen, hScompact⟩ | ⟨hSclosed, hScompact⟩
      · obtain ⟨T, hT, hxT, hTS⟩ :=
          (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens)).isOpen_iff.mp
            hSopen x hx
        rcases hT with ⟨W, F, hW, rfl⟩
        refine ⟨F, ?_, ?_⟩
        · intro i hi
          simp
        · intro y hy
          apply hTS
          intro i hi
          have hyx : y i = x i := by simpa using hy i hi
          rw [hyx]
          exact hxT i hi
      · have hScompl : IsOpen Sᶜ := hSclosed.isOpen_compl
        let ι : Type u := {p : (I → Set KrullTwoPointSpace) × Finset I //
          (∀ i, i ∈ p.2 → IsOpen (p.1 i)) ∧
            (p.2 : Set I).pi p.1 ⊆ Sᶜ}
        let b : ι → Set (I → KrullTwoPointSpace) :=
          fun p => (p.1.2 : Set I).pi p.1.1
        have hbopen : ∀ p : ι, IsOpen (b p) := by
          intro p
          rcases p with ⟨⟨W, F⟩, hW, hWF⟩
          change IsOpen ((F : Set I).pi W)
          exact isOpen_set_pi F.finite_toSet (fun i hi => hW i hi)
        have hcover : Sᶜ ⊆ ⋃ p : ι, b p := by
          intro y hy
          obtain ⟨T, hT, hyT, hTS⟩ :=
            (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens)).isOpen_iff.mp
              hScompl y hy
          rcases hT with ⟨W, F, hW, rfl⟩
          let p : ι := ⟨(W, F), ⟨by
            intro i hi
            simpa using hW i hi, hTS⟩⟩
          refine mem_iUnion.mpr ⟨p, ?_⟩
          change y ∈ (F : Set I).pi W
          exact hyT
        obtain ⟨s, hs⟩ := hScompact.elim_finite_subcover b hbopen hcover
        let F : Finset I := s.biUnion (fun p => p.1.2)
        have hcoord : ∀ p : ι, p ∈ s →
            ∃ i, i ∈ p.1.2 ∧ x i ∉ p.1.1 i := by
          intro p hp
          have hxp : x ∉ b p := by
            intro hxpS
            exact (p.2.2 hxpS) hx
          by_contra h
          push Not at h
          exact hxp (by
            intro i hi
            exact h i hi)
        choose ip hipF hipout using hcoord
        refine ⟨F, ?_, ?_⟩
        · intro i hi
          simp
        · intro y hy
          by_contra hyS
          have hySc : y ∈ Sᶜ := hyS
          obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hs hySc)
          have hip : ip p hp ∈ F := by
            exact Finset.mem_biUnion.mpr ⟨p, hp, hipF p hp⟩
          have hxy : y (ip p hp) = x (ip p hp) := by
            simpa using hy (ip p hp) hip
          have hyW : y (ip p hp) ∈ p.1.1 (ip p hp) := hyp (ip p hp) (hipF p hp)
          exact (hipout p hp) (by simpa [hxy] using hyW)
  | univ =>
      refine ⟨∅, by simp, ?_⟩
      intro y hy
      simp
  | inter s t hs ht ihs iht =>
      rcases ihs hx.1 with ⟨F, hxF, hFs⟩
      rcases iht hx.2 with ⟨G, hxG, hGt⟩
      refine ⟨F ∪ G, ?_, ?_⟩
      · intro i hi
        simp
      · intro y hy
        constructor
        · apply hFs
          intro i hi
          exact hy i (Finset.mem_union_left G hi)
        · apply hGt
          intro i hi
          exact hy i (Finset.mem_union_right F hi)
  | sUnion S hS ih =>
      rcases mem_sUnion.mp hx with ⟨T, hTS, hxT⟩
      rcases ih T hTS hxT with ⟨F, hxF, hFU⟩
      exact ⟨F, hxF, fun y hy => mem_sUnion.mpr ⟨T, hTS, hFU hy⟩⟩

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

private theorem spectralSpace_pi_krullTwoPoint {I : Type u} :
    SpectralSpace (I → KrullTwoPointSpace) := by
  classical
  have hK := krullTwoPointSpace_is_finite_sober
  let _ : Finite KrullTwoPointSpace := hK.1
  let _ : QuasiSober KrullTwoPointSpace := hK.2.1
  let _ : T0Space KrullTwoPointSpace := hK.2.2
  have hKcompact : ∀ S : Set KrullTwoPointSpace, IsCompact S := by
    intro S
    exact (Set.toFinite S).isCompact
  have hcompactCylinder : ∀ (U : I → Set KrullTwoPointSpace) (F : Finset I),
      IsCompact ((F : Set I).pi U) := by
    intro U F
    let W : I → Set KrullTwoPointSpace := fun i => if i ∈ F then U i else Set.univ
    have hW : ∀ i, IsCompact (W i) := by
      intro i
      dsimp [W]
      split_ifs <;> exact hKcompact _
    rw [← Set.pi_univ_ite (F : Set I) U]
    exact isCompact_univ_pi hW
  have hcompact : CompactSpace (I → KrullTwoPointSpace) := by
    refine ⟨?_⟩
    simpa only [Set.pi_univ] using
      (isCompact_univ_pi (fun _ => hKcompact Set.univ))
  have hquasiSober : QuasiSober (I → KrullTwoPointSpace) := by
    constructor
    intro Z hZ hZclosed
    let Zi : ∀ i : I, Set KrullTwoPointSpace := fun i => Function.eval i '' Z
    have hZi : ∀ i, IsIrreducible (Zi i) := by
      intro i
      exact hZ.image _ (continuous_apply i).continuousOn
    let xi : ∀ i : I, KrullTwoPointSpace := fun i =>
      Classical.choose ((inferInstance : QuasiSober KrullTwoPointSpace).sober
        (hZi i).closure isClosed_closure)
    have hxi : ∀ i, IsGenericPoint (xi i) (closure (Zi i)) := by
      intro i
      exact Classical.choose_spec ((inferInstance : QuasiSober KrullTwoPointSpace).sober
        (hZi i).closure isClosed_closure)
    let x : I → KrullTwoPointSpace := xi
    have hxZ : x ∈ Z := by
      by_contra hx
      obtain ⟨S, hS, hxS, hSZ⟩ :=
        (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens)).isOpen_iff.mp
          hZclosed.isOpen_compl x hx
      rcases hS with ⟨U, F, hU, rfl⟩
      have hZiU : ∀ i ∈ F, (Z ∩ (Function.eval i ⁻¹' U i)).Nonempty := by
        intro i hi
        have hUiopen : IsOpen (U i) := by simpa using hU i hi
        have hxiU : xi i ∈ U i := hxS i hi
        have hZU : (closure (Zi i) ∩ U i).Nonempty :=
          (hxi i).mem_open_set_iff hUiopen |>.mp hxiU
        rw [closure_inter_open_nonempty_iff hUiopen] at hZU
        rcases hZU with ⟨_, ⟨z, hz, rfl⟩, hzU⟩
        exact ⟨z, hz, hzU⟩
      have hfinite : ∀ s : Finset I, s ⊆ F →
          (Z ∩ (s : Set I).pi U).Nonempty := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            intro hsF
            simpa using hZ.nonempty
        | @insert i s hi ih =>
            intro hsF
            have hiF : i ∈ F := hsF (Finset.mem_insert_self _ _)
            have hsF' : s ⊆ F := fun j hj => hsF (Finset.mem_insert_of_mem hj)
            have hA := hZiU i hiF
            have hB := ih hsF'
            have hUiopen : IsOpen (U i) := by simpa using hU i hiF
            have hAopen : IsOpen
                ((Function.eval i : (I → KrullTwoPointSpace) → KrullTwoPointSpace) ⁻¹' U i) :=
              @IsOpen.preimage (I → KrullTwoPointSpace) KrullTwoPointSpace
                _ _ (Function.eval i) (continuous_apply i) (U i) hUiopen
            have hBopen : IsOpen ((s : Set I).pi U) :=
              isOpen_set_pi s.finite_toSet (fun j hj => by simpa using hU j (hsF' hj))
            obtain ⟨z, hzZ, hzAB⟩ :=
              hZ.isPreirreducible _ _ hAopen hBopen hA hB
            refine ⟨z, hzZ, ?_⟩
            change ∀ j, j ∈ (insert i s : Finset I) → z j ∈ U j
            intro j hj'
            simp only [Finset.mem_insert] at hj'
            rcases hj' with rfl | hj'
            · exact hzAB.1
            · exact hzAB.2 j hj'
      obtain ⟨z, hzZ, hzS⟩ := hfinite F subset_rfl
      exact (hSZ hzS) hzZ
    refine ⟨x, ?_⟩
    rw [isGenericPoint_def]
    apply subset_antisymm
    · exact closure_minimal (singleton_subset_iff.mpr hxZ) hZclosed
    · intro z hzZ
      rw [mem_closure_iff]
      intro U hUopen hzU
      obtain ⟨S, hS, hzS, hSU⟩ :=
        (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens)).isOpen_iff.mp
          hUopen z hzU
      rcases hS with ⟨V, F, hV, rfl⟩
      have hxS : x ∈ (F : Set I).pi V := by
        intro i hi
        have hViopen : IsOpen (V i) := by simpa using hV i hi
        apply (hxi i).mem_open_set_iff hViopen |>.mpr
        exact ⟨z i, subset_closure ⟨z, hzZ, rfl⟩, hzS i hi⟩
      exact ⟨x, hSU hxS, rfl⟩
  have hprespectral : PrespectralSpace (I → KrullTwoPointSpace) := by
    let B : Set (Set (I → KrullTwoPointSpace)) :=
      {S | ∃ (U : I → Set KrullTwoPointSpace) (F : Finset I),
        (∀ i, i ∈ F → IsOpen (U i)) ∧ S = (F : Set I).pi U}
    have hB : IsTopologicalBasis B := by
      simpa [B] using (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens))
    exact PrespectralSpace.of_isTopologicalBasis hB
      (by
        intro S hS
        rcases hS with ⟨U, F, hU, rfl⟩
        exact hcompactCylinder U F)
  have hquasiSeparated : QuasiSeparatedSpace (I → KrullTwoPointSpace) := by
    let B : Set (Set (I → KrullTwoPointSpace)) :=
      {S | ∃ (U : I → Set KrullTwoPointSpace) (F : Finset I),
        (∀ i, i ∈ F → IsOpen (U i)) ∧ S = (F : Set I).pi U}
    have hB : IsTopologicalBasis B := by
      simpa [B] using (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens))
    let ιB := {p : (I → Set KrullTwoPointSpace) × Finset I //
      ∀ i, i ∈ p.2 → IsOpen (p.1 i)}
    let b : ιB → Set (I → KrullTwoPointSpace) :=
      fun p => (p.1.2 : Set I).pi p.1.1
    have hbasis : IsTopologicalBasis (Set.range b) := by
      have hrange : Set.range b = B := by
        ext S
        constructor
        · rintro ⟨p, rfl⟩
          exact ⟨p.1.1, p.1.2, p.2, rfl⟩
        · rintro ⟨U, F, hU, rfl⟩
          exact ⟨⟨(U, F), hU⟩, rfl⟩
      rw [hrange]
      exact hB
    refine QuasiSeparatedSpace.of_isTopologicalBasis hbasis (by
      intro p q
      rcases p with ⟨⟨U, F⟩, hU⟩
      rcases q with ⟨⟨V, G⟩, hV⟩
      change IsCompact ((F : Set I).pi U ∩ (G : Set I).pi V)
      let H : I → Set KrullTwoPointSpace := fun i =>
        if i ∈ F then if i ∈ G then U i ∩ V i else U i
        else if i ∈ G then V i else Set.univ
      rw [show (F : Set I).pi U ∩ (G : Set I).pi V =
          ((F ∪ G : Finset I) : Set I).pi H by
        ext x
        constructor
        · intro hx
          change ∀ i, i ∈ F ∪ G → x i ∈ H i
          intro i hi
          change i ∈ F ∪ G at hi
          rcases Finset.mem_union.mp hi with hiF | hiG
          · by_cases hiG' : i ∈ G
            · simpa [H, hiF, hiG'] using
                (show x i ∈ U i ∩ V i from ⟨hx.1 i hiF, hx.2 i hiG'⟩)
            · simpa [H, hiF, hiG'] using hx.1 i hiF
          · by_cases hiF' : i ∈ F
            · simpa [H, hiF', hiG] using
                (show x i ∈ U i ∩ V i from ⟨hx.1 i hiF', hx.2 i hiG⟩)
            · simpa [H, hiF', hiG] using hx.2 i hiG
        · intro hx
          change ∀ i, i ∈ F ∪ G → x i ∈ H i at hx
          refine ⟨?_, ?_⟩
          · intro i hi
            change i ∈ F at hi
            have hxi := hx i (Finset.mem_union_left G hi)
            by_cases hiG : i ∈ G
            · have hxi' : x i ∈ U i ∩ V i := by simpa [H, hi, hiG] using hxi
              exact hxi'.1
            · have hxi' : x i ∈ U i := by simpa [H, hi, hiG] using hxi
              exact hxi'
          · intro i hi
            change i ∈ G at hi
            have hxi := hx i (Finset.mem_union_right F hi)
            by_cases hiF : i ∈ F
            · by_cases hiG : i ∈ G
              · have hxi' : x i ∈ U i ∩ V i := by simpa [H, hiF, hiG] using hxi
                exact hxi'.2
              · exact (hiG hi).elim
            · have hxi' : x i ∈ V i := by simpa [H, hiF, hi] using hxi
              exact hxi'
      ]
      exact hcompactCylinder H (F ∪ G))
  have hT0 : T0Space (I → KrullTwoPointSpace) := inferInstance
  exact { __ := hT0, __ := hcompact, __ := hquasiSober, __ := hquasiSeparated, __ := hprespectral }

/-- Spectral spaces are precisely the constructibly closed subspaces of
products of copies of the two-point space, up to homeomorphism. -/
theorem spectralSpace_iff_constructibleClosed_subspace_of_product_twoPoint :
    SpectralSpace X ↔
      ∃ (I : Type u) (E : Set (I → KrullTwoPointSpace)),
        IsClosed[constructibleTopology (I → KrullTwoPointSpace)] E ∧
          Nonempty (X ≃ₜ E) := by
  constructor
  · intro hX
    classical
    let _ : SpectralSpace X := hX
    have hK := krullTwoPointSpace_is_finite_sober
    let _ : Finite KrullTwoPointSpace := hK.1
    let I : Type u := {U : Set X // IsOpen U ∧ IsCompact U}
    let fU : ∀ i : I, X → KrullTwoPointSpace := fun i x =>
      if x ∈ (i : Set X) then KrullTwoPointSpace.generic else KrullTwoPointSpace.special
    have hfU : ∀ i : I, IsSpectralMap (fU i) := by
      intro i
      have hcont : Continuous (fU i) := by
        rw [continuous_generateFrom_iff]
        intro V hV
        have hV' : V = ({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace) := by
          simpa [krullTwoPointOpenGenerators] using hV
        rw [hV']
        rw [show fU i ⁻¹' ({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace) =
            (i : Set X) by
          ext x
          simp [fU]]
        exact i.property.1
      refine ⟨hcont, ?_⟩
      intro V hVopen hVcompact
      rcases krullTwoPointSpace_isOpen_iff.mp hVopen with hV0 | hVg | hVu
      · subst V
        simp
      · subst V
        rw [show fU i ⁻¹' ({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace) =
            (i : Set X) by
          ext x
          simp [fU]]
        exact i.property.2
      · subst V
        exact isCompact_univ
    let f : X → (I → KrullTwoPointSpace) := fun x i => fU i x
    have hfcont : Continuous f := by
      apply continuous_pi
      intro i
      exact (hfU i).continuous
    have hfSpectral : IsSpectralMap f := by
      refine ⟨hfcont, ?_⟩
      intro V hVopen hVcompact
      let ιB : Type u := {p : (I → Set KrullTwoPointSpace) × Finset I //
        ∀ i, i ∈ p.2 → IsOpen (p.1 i)}
      let b : ιB → Set (I → KrullTwoPointSpace) :=
        fun p => (p.1.2 : Set I).pi p.1.1
      have hbopen : ∀ p : ιB, IsOpen (b p) := by
        intro p
        rcases p with ⟨⟨W, F⟩, hW⟩
        change IsOpen ((F : Set I).pi W)
        exact isOpen_set_pi F.finite_toSet (fun i hi => hW i hi)
      let ιV : Type u := {p : ιB // b p ⊆ V}
      let bV : ιV → Set (I → KrullTwoPointSpace) := fun p => b p
      have hcover : V ⊆ ⋃ p : ιV, bV p := by
        intro y hy
        obtain ⟨S, hS, hyS, hSV⟩ :=
          (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens)).isOpen_iff.mp
            hVopen y hy
        rcases hS with ⟨W, F, hW, rfl⟩
        let p : ιB := ⟨(W, F), by
          intro i hi
          simpa using hW i hi⟩
        have hp : b p ⊆ V := hSV
        refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
        exact hyS
      obtain ⟨s, hs⟩ := hVcompact.elim_finite_subcover bV
        (fun p => hbopen p.1) hcover
      have hVe : V = ⋃ p ∈ s, bV p := by
        apply subset_antisymm
        · intro y hy
          exact hs hy
        · exact iUnion₂_subset (fun p hp => p.property)
      have hpre : ∀ p : ιB, IsCompact (f ⁻¹' b p) := by
        intro p
        rcases p with ⟨⟨W, F⟩, hW⟩
        change IsCompact ((fun x i => fU i x) ⁻¹' ((F : Set I).pi W))
        rw [show (fun x i => fU i x) ⁻¹' ((F : Set I).pi W) =
            ⋂ i : I, ⋂ (_ : i ∈ (F : Set I)), (fU i) ⁻¹' W i by
          ext x
          simp only [Set.mem_preimage, Set.mem_pi, Set.mem_iInter]]
        rw [← Set.sInter_image]
        apply QuasiSeparatedSpace.isCompact_sInter
          (F.finite_toSet.image (fun i : I => (fU i) ⁻¹' W i))
        · rintro S ⟨i, hi, rfl⟩
          exact Or.inl (IsOpen.preimage (hfU i).continuous (hW i hi))
        · rintro S ⟨i, hi, rfl⟩
          exact (hfU i).isCompact_preimage_of_isOpen (hW i hi)
            (Set.toFinite (W i)).isCompact
      rw [hVe]
      simp only [Set.preimage_iUnion]
      exact s.isCompact_biUnion (fun p hp => hpre p.1)
    have hinj : Function.Injective f := by
      intro x y hxy
      by_contra hne
      obtain ⟨U, hUopen, hxor⟩ := exists_isOpen_xor_mem hne
      rcases hxor with hxyU | hyxU
      · obtain ⟨K, hK, hxK, hKU⟩ :=
          PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxyU.1 hUopen
        let i : I := ⟨K, hK.1, hK.2⟩
        have hyK : y ∉ (i : Set X) := by
          intro hy
          exact hxyU.2 (hKU hy)
        have hcoord : f x i ≠ f y i := by
          simp [f, fU, i, hxK, hyK]
        exact hcoord (congrFun hxy i)
      · obtain ⟨K, hK, hyK, hKU⟩ :=
          PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyxU.1 hUopen
        let i : I := ⟨K, hK.1, hK.2⟩
        have hxK : x ∉ (i : Set X) := by
          intro hx
          exact hyxU.2 (hKU hx)
        have hcoord : f x i ≠ f y i := by
          simp [f, fU, i, hxK, hyK]
        exact hcoord (congrFun hxy i)
    let _ : SpectralSpace (I → KrullTwoPointSpace) := spectralSpace_pi_krullTwoPoint
    have hEclosed : IsClosed[constructibleTopology (I → KrullTwoPointSpace)] (Set.range f) :=
      (spectralMap_constructibleTopology_properties f hfSpectral).2.2
    have hebij : Function.Bijective (fun x : X =>
        (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)) := by
      constructor
      · intro x y hxy
        exact hinj (congrArg Subtype.val hxy)
      · intro y
        rcases y.property with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        apply Subtype.ext
        exact hx
    let e : X ≃ Set.range f := Equiv.ofBijective _ hebij
    have hecont : Continuous e := by
      change Continuous (fun x : X => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f))
      exact hfcont.subtype_mk (fun x => ⟨x, rfl⟩)
    have heopen : IsOpenMap e := by
      intro U hU
      obtain ⟨ι, V, hV, hVmem⟩ :=
        PrespectralSpace.isTopologicalBasis.open_eq_iUnion hU
      let i : ι → I := fun j => ⟨V j, (hVmem j).1, (hVmem j).2⟩
      let C : ι → Set (I → KrullTwoPointSpace) := fun j =>
        (Function.eval (i j) ⁻¹' ({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace))
      have hCopen : ∀ j, IsOpen (C j) := by
        intro j
        exact IsOpen.preimage (continuous_apply (i j))
          (krullTwoPointSpace_isOpen_iff.mpr (Or.inr (Or.inl rfl)))
      apply isOpen_induced_iff.mpr
      refine ⟨⋃ j, C j, isOpen_iUnion hCopen, ?_⟩
      ext y
      constructor
      · intro hy
        change y.1 ∈ ⋃ j, C j at hy
        obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
        rcases y.property with ⟨x, hx⟩
        have hy_eq : y = e x := by
          apply Subtype.ext
          exact hx.symm
        rw [← hx] at hyj
        have hxV : x ∈ V j := by
          simpa [C, i, f, fU] using hyj
        exact ⟨x, hV ▸ mem_iUnion.mpr ⟨j, hxV⟩, hy_eq.symm⟩
      · rintro ⟨x, hxU, rfl⟩
        rw [hV] at hxU
        obtain ⟨j, hxj⟩ := mem_iUnion.mp hxU
        change (e x).1 ∈ ⋃ j, C j
        refine mem_iUnion.mpr ⟨j, ?_⟩
        change f x (i j) ∈ ({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace)
        simp [i, f, fU, hxj]
    refine ⟨I, Set.range f, hEclosed, ?_⟩
    exact ⟨e.toHomeomorphOfContinuousOpen hecont heopen⟩
  · rintro ⟨I, E, hE, ⟨e⟩⟩
    let _ : SpectralSpace (I → KrullTwoPointSpace) := spectralSpace_pi_krullTwoPoint
    have hEspace : SpectralSpace E :=
      spectralSpace_subtype_of_constructible_closed hE
    let _ : SpectralSpace E := hEspace
    have hT0 : T0Space X := e.isEmbedding.t0Space
    have hcompact : CompactSpace X := e.symm.compactSpace
    have hquasiSober : QuasiSober X := e.isOpenEmbedding.quasiSober
    have hquasiSeparated : QuasiSeparatedSpace X :=
      (quasiSeparatedSpace_congr e).mpr inferInstance
    have hprespectral : PrespectralSpace X :=
      PrespectralSpace.of_isInducing e e.isInducing e.isProperMap.isSpectralMap
    exact spectralSpace_iff_source_conditions.mpr
      ⟨hT0, hcompact, hquasiSober, hquasiSeparated, hprespectral⟩

/-! ### Directed finite inverse-limit presentation -/

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
  constructor
  · intro hX
    classical
    obtain ⟨I, E, hE, ⟨e⟩⟩ :=
      (spectralSpace_iff_constructibleClosed_subspace_of_product_twoPoint (X := X)).mp hX
    have hK := krullTwoPointSpace_is_finite_sober
    let _ : Finite KrullTwoPointSpace := hK.1
    let _ : T0Space KrullTwoPointSpace := hK.2.2
    let p : ∀ J : Finset I, (I → KrullTwoPointSpace) → (J → KrullTwoPointSpace) :=
      fun J x j => x j.1
    let A : ∀ J : Finset I, Set (J → KrullTwoPointSpace) :=
      fun J => p J '' E
    let restrict : ∀ {J K : Finset I}, K ⊆ J →
        (J → KrullTwoPointSpace) → (K → KrullTwoPointSpace) :=
      fun {J K} h x k => x ⟨k.1, h k.2⟩
    let mapObj : ∀ {J K : Finset I}, K ⊆ J →
        TopCat.Hom (TopCat.of (A J)) (TopCat.of (A K)) := fun {J K} (h : K ⊆ J) =>
      TopCat.ofHom
        { toFun := fun y : A J =>
            (⟨restrict h y.1, by
              rcases y.property with ⟨x, hx, hxy⟩
              exact ⟨x, hx, by
                ext k
                change x k.1 = y.1 ⟨k.1, h k.2⟩
                exact congrFun hxy ⟨k.1, h k.2⟩⟩⟩ : A K)
          continuous_toFun := by
            apply Continuous.subtype_mk
            · apply continuous_pi
              intro k
              let j : J := ⟨k.1, h k.2⟩
              change Continuous (fun y : A J => y.1 j)
              exact (continuous_apply j).comp continuous_subtype_val }
    let D : (Finset I)ᵒᵖ ⥤ TopCat.{u} := {
      obj := fun J => TopCat.of (A J.unop)
      map := fun {J K} f =>
        mapObj (J := J.unop) (K := K.unop) (leOfHom f.unop)
      map_id := by
        intro J
        ext y k
        rfl
      map_comp := by
        intro J K L f g
        ext y k
        rfl }
    have hfinite : ∀ j, Finite (D.obj j) := by
      intro j
      exact Finite.of_injective (fun y : D.obj j => y.1) Subtype.val_injective
    have hsober : ∀ j, QuasiSober (D.obj j) := by
      intro j
      let _ : Finite (D.obj j) := hfinite j
      exact quasiSober_of_finite
    have ht0 : ∀ j, T0Space (D.obj j) := by
      intro j
      exact inferInstance
    let cπ : ∀ j : (Finset I)ᵒᵖ, TopCat.Hom (TopCat.of E) (D.obj j) := fun j =>
      TopCat.ofHom
        { toFun := fun x : E =>
            (⟨p j.unop x.1, ⟨x.1, x.2, rfl⟩⟩ : A j.unop)
          continuous_toFun := by
            apply Continuous.subtype_mk
            apply continuous_pi
            intro k
            let i : I := k.1
            have hc : Continuous (fun z : (I → KrullTwoPointSpace) => z i) :=
              continuous_apply i
            change Continuous ((fun z : (I → KrullTwoPointSpace) => z i) ∘
              (fun x : E => x.1))
            exact hc.comp continuous_subtype_val }
    let C : Cone D :=
      { pt := TopCat.of E
        π :=
          { app := cπ
            naturality := by
              intro j k f
              apply TopCat.ext
              intro x
              apply Subtype.ext
              ext l
              rfl } }
    have hset : IsLimit ((CategoryTheory.forget (TopCat.{u})).mapCone C) := by
      exact Classical.choice ((Types.isLimit_iff _).mpr (by
        intro s hs
        let y : I → KrullTwoPointSpace := fun i =>
          (s (Opposite.op ({i} : Finset I))).1 ⟨i, by simp⟩
        have hyE : y ∈ E := by
          by_contra hy
          obtain ⟨F, hF, hFU⟩ :=
            constructibleOpen_contains_finite_coordinate_cylinder hE.isOpen_compl hy
          rcases (s (Opposite.op F)).property with ⟨z, hz, hzy⟩
          have hzy' : ∀ i, i ∈ F → z i = y i := by
            intro i hi
            let f : (Opposite.op F) ⟶ (Opposite.op ({i} : Finset I)) :=
              (homOfLE (show ({i} : Finset I) ⊆ F by
                intro j hj
                rcases Finset.mem_singleton.mp hj with rfl
                exact hi)).op
            have hn := hs f
            have hn' := congrArg (fun q => q.1 ⟨i, by simp⟩) hn
            calc
              z i = (p F z) ⟨i, hi⟩ := by rfl
              _ = (s (Opposite.op F)).1 ⟨i, hi⟩ := congrFun hzy ⟨i, hi⟩
              _ = (s (Opposite.op ({i} : Finset I))).1 ⟨i, by simp⟩ := by
                simpa [D, mapObj, restrict] using hn'
              _ = y i := by rfl
          have hzcyl : z ∈ (F : Set I).pi (fun i => ({y i} : Set KrullTwoPointSpace)) := by
            intro i hi
            simpa only [Set.mem_singleton_iff] using hzy' i hi
          exact (hFU hzcyl) hz
        refine ⟨⟨y, hyE⟩, ?_, ?_⟩
        · intro j
          apply Subtype.ext
          funext k
          let i : I := k.1
          let f : (Opposite.op j.unop) ⟶ (Opposite.op ({i} : Finset I)) :=
            (homOfLE (show ({i} : Finset I) ⊆ j.unop by
              intro l hl
              rcases Finset.mem_singleton.mp hl with rfl
              exact k.2)).op
          have hn := hs f
          have hn' := congrArg (fun q => q.1 ⟨i, by simp⟩) hn
          simpa [C, D, cπ, p, mapObj, restrict, y] using hn'.symm
        · intro w hw
          apply Subtype.ext
          funext i
          have hi := congrArg (fun q => q.1 ⟨i, by simp⟩)
            (hw (Opposite.op ({i} : Finset I)))
          simpa [C, cπ, p, y] using hi
        ))
    have hbasis : IsTopologicalBasis
        {U : Set E | ∃ (j : (Finset I)ᵒᵖ) (V : Set (D.obj j)),
          IsOpen V ∧ U = (cπ j).hom ⁻¹' V} := by
      apply isTopologicalBasis_of_isOpen_of_nhds
      · rintro U ⟨j, V, hV, rfl⟩
        exact hV.preimage (cπ j).hom.2
      · intro x U hx hUopen
        obtain ⟨T, hT, hxT, hTU⟩ :=
          (isTopologicalBasis_subtype
            (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens))
            (fun z : I → KrullTwoPointSpace => z ∈ E)).isOpen_iff.mp
            hUopen x hx
        rcases hT with ⟨T, ⟨W, F, hW, rfl⟩, rfl⟩
        let W' : F → Set KrullTwoPointSpace := fun i => W i.1
        let T' : Set (F → KrullTwoPointSpace) :=
          (Set.univ : Set F).pi W'
        let V : Set (A F) := {z | z.1 ∈ T'}
        have hVopen : IsOpen V := by
          apply isOpen_induced_iff.mpr
          refine ⟨T', isOpen_set_pi (Set.toFinite (Set.univ : Set F)) (fun i hi => ?_), ?_⟩
          · simpa [W'] using hW i.1 i.2
          rfl
        refine ⟨(cπ (Opposite.op F)).hom ⁻¹' V,
          ⟨Opposite.op F, V, hVopen, rfl⟩, ?_, ?_⟩
        · change (⟨p F x.1, ⟨x.1, x.2, rfl⟩⟩ : A F) ∈ V
          change p F x.1 ∈ T'
          intro i hi
          simpa [T', W', p] using hxT i.1 i.2
        · intro y hy
          apply hTU
          change y.1 ∈ (F : Set I).pi W
          intro i hi
          have hy' : p F y.1 ∈ T' := by
            change (⟨p F y.1, ⟨y.1, y.2, rfl⟩⟩ : A F) ∈ V at hy
            change p F y.1 ∈ T' at hy
            exact hy
          simpa [W', p] using hy' ⟨i, hi⟩ (by simp)
    have hlim : IsLimit C :=
      Formalization.Books.Topology.Unit14.isLimit_of_set_limit_of_open_preimage_basis
        C hset hbasis
    let _ : Preorder (Finset I) := inferInstance
    let _ : IsDirectedOrder (Finset I) := inferInstance
    let _ : Nonempty (Finset I) := ⟨∅⟩
    let eE : E ≃ₜ ((limit D : TopCat.{u}) : Type u) :=
      TopCat.homeoOfIso (hlim.conePointUniqueUpToIso (limit.isLimit D))
    exact ⟨{
      index := Finset I
      preorder := inferInstance
      directed := inferInstance
      nonempty := inferInstance
      diagram := D
      finite := hfinite
      sober := hsober
      t0 := ht0
      homeomorph := e.trans eE }⟩
  · rintro ⟨P⟩
    let _ : Preorder P.index := P.preorder
    let _ : IsDirectedOrder P.index := P.directed
    let _ : Nonempty P.index := P.nonempty
    have hL : SpectralSpace ((limit P.diagram : TopCat.{u}) : Type u) :=
      spectralSpace_of_directed_inverse_limit_finite_sober
        P.diagram P.finite P.sober P.t0
    let _ : SpectralSpace ((limit P.diagram : TopCat.{u}) : Type u) := hL
    have hT0 : T0Space X := P.homeomorph.isEmbedding.t0Space
    have hcompact : CompactSpace X := P.homeomorph.symm.compactSpace
    have hquasiSober : QuasiSober X := P.homeomorph.isOpenEmbedding.quasiSober
    have hquasiSeparated : QuasiSeparatedSpace X :=
      (quasiSeparatedSpace_congr P.homeomorph).mpr inferInstance
    have hprespectral : PrespectralSpace X :=
      PrespectralSpace.of_isInducing P.homeomorph P.homeomorph.isInducing
        P.homeomorph.isProperMap.isSpectralMap
    exact spectralSpace_iff_source_conditions.mpr
      ⟨hT0, hcompact, hquasiSober, hquasiSeparated, hprespectral⟩

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
