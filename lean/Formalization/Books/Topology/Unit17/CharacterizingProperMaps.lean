import Mathlib.Data.Set.Prod
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Filter

/-!
# Topology, Chapter 17: Characterizing proper maps

The source uses `IsClosedMap` for closed maps, `IsSeparatedMap` for separated
maps, `IsCompact` for quasi-compact subsets, and Mathlib's `IsProperMap` for
the Bourbaki-proper condition.  The source's universal-closed condition is
phrased using the concrete topological pullback `Function.Pullback`; it is
defined here because it is the base-change formulation, whereas Mathlib's
`IsProperMap` is the canonical Bourbaki-proper interface.
-/

namespace Formalization.Books.Topology.Unit17

open Set Function

universe u v w

section CharacterizingProperMaps

variable {X : Type u} [TopologicalSpace X]

/-! ### The Tube lemma -/

/- The source's closed-map terminology is Mathlib's existing `IsClosedMap`.
   Its Tube lemma is exactly `generalized_tube_lemma`, so the chapter-facing
   name below is a direct reuse of that result. -/

theorem tube_lemma {Y : Type v} [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {W : Set (X × Y)}
    (hA : IsCompact A) (hB : IsCompact B) (hW : IsOpen W)
    (hAB : A ×ˢ B ⊆ W) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ U ×ˢ V ⊆ W := by
  exact generalized_tube_lemma hA hB hW hAB

/-! ### Properness notions -/

/-!
The source's Bourbaki-proper map is Mathlib's `IsProperMap`.  Mathlib's
definition includes continuity, which is already part of the source's
standing hypothesis that `f` is a continuous map.
-/

/- A map is quasi-proper when inverse images of quasi-compact subsets are
   quasi-compact. -/
def IsQuasiProper {Y : Type v} [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ ⦃V : Set Y⦄, IsCompact V → IsCompact (f ⁻¹' V)

/- The introductory comparison with the usual locally compact Hausdorff
   terminology is Mathlib's compact-preimage characterization of
   `IsProperMap`. -/
theorem isProperMap_iff_isQuasiProper_of_locallyCompact_Hausdorff
    {Y : Type v} [TopologicalSpace Y]
    [LocallyCompactSpace Y] [T2Space Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ IsQuasiProper f := by
  exact isProperMap_iff_isCompact_preimage

/- A map is universally closed when every continuous base change has a closed
   projection to the base.  `Function.Pullback.snd` is the projection from
   `X ×_Y Z` to `Z`, with the factors ordered so that the source factor is
   first. -/
def IsUniversallyClosed {Y : Type v} [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ (Z : Type w) [TopologicalSpace Z] (g : Z → Y), Continuous g →
    IsClosedMap (@Function.Pullback.snd X Y Z f g)

/- The source's proper map includes the standing continuity requirement, and
   then asks for separatedness and universal closedness.  The longer name
   distinguishes it from Mathlib's `IsProperMap`, which intentionally denotes
   Bourbaki properness without the extra separatedness condition. -/
def IsProperTopologicalMap {Y : Type v} [TopologicalSpace Y] (f : X → Y) : Prop :=
  Continuous f ∧ IsSeparatedMap f ∧ IsUniversallyClosed.{u, v, w} f

/-! ### Characterization of quasi-compact spaces -/

theorem compactSpace_iff_isClosedMap_prod_fst :
    CompactSpace X ↔
      ∀ (Z : Type u) [TopologicalSpace Z],
        IsClosedMap (Prod.fst : Z × X → Z) := by
  constructor
  · intro h Z _
    exact @isClosedMap_fst_of_compactSpace Z X _ _ h
  · intro h
    apply isCompact_univ_iff.mp
    rw [isCompact_iff_ultrafilter_le_nhds]
    intro 𝒰 _
    let s : Set (Filter X × X) := {p | p.1 = pure p.2}
    have hsclosed : IsClosed ((Prod.fst : Filter X × X → Filter X) '' closure s) :=
      h (Filter X) (closure s) isClosed_closure
    have hUimage : (𝒰 : Filter X) ∈ (Prod.fst : Filter X × X → Filter X) '' closure s := by
      apply hsclosed.closure_subset
      rw [mem_closure_iff_nhds]
      intro t ht
      have hxe : ∀ᶠ x in (𝒰 : Filter X), pure x ∈ t :=
        (Filter.tendsto_pure_self (𝒰 : Filter X)) ht
      rcases Filter.Eventually.exists hxe with ⟨x, hx⟩
      exact ⟨pure x, hx, ⟨⟨pure x, x⟩, subset_closure rfl, rfl⟩⟩
    rcases hUimage with ⟨⟨F, x⟩, hx, rfl⟩
    refine ⟨x, mem_univ x, ?_⟩
    intro U hU
    by_cases hUmem : U ∈ 𝒰
    · exact hUmem
    · have hUc : Uᶜ ∈ 𝒰 := Ultrafilter.compl_mem_iff_notMem.mpr hUmem
      rw [mem_closure_iff_nhds] at hx
      rcases hx ({G : Filter X | Uᶜ ∈ G} ×ˢ U)
        (prod_mem_nhds (Filter.isOpen_setOfPred_mem.mem_nhds hUc) hU) with
        ⟨⟨G, y⟩, ⟨⟨hy', hy⟩, hG⟩⟩
      have hG' : Uᶜ ∈ (pure y : Filter X) := hG ▸ hy'
      exact False.elim ((show y ∈ Uᶜ from hG') hy)

/-! ### Characterization of Bourbaki-proper and universally closed maps -/

theorem proper_map_characterization_TFAE {Y : Type v} [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) :
    List.TFAE
      [IsQuasiProper f ∧ IsClosedMap f,
        IsProperMap f,
        IsUniversallyClosed.{u, v, max u v} f,
        IsClosedMap f ∧ ∀ y, IsCompact (f ⁻¹' {y})] := by
  tfae_have 1 → 4 := by
    rintro ⟨hquasi, hclosed⟩
    exact ⟨hclosed, fun y => hquasi isCompact_singleton⟩
  tfae_have 4 → 2 := by
    intro h
    exact isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hf, h.1, h.2⟩
  tfae_have 2 → 1 := by
    intro h
    exact ⟨fun {K} hK => h.isCompact_preimage hK, h.isClosedMap⟩
  tfae_have 4 → 3 := by
    rintro ⟨hclosed, hfiber⟩ Z _ g hg
    intro P hP
    obtain ⟨P', hP', hP'eq⟩ := (Topology.IsInducing.subtypeVal.isClosed_iff).mp hP
    apply isClosed_iff_nhds.2
    intro z hz
    by_contra hzP
    by_cases hzrange : g z ∈ range f
    · have hAB : (f ⁻¹' ({g z} : Set Y)) ×ˢ ({z} : Set Z) ⊆ P'ᶜ := by
        rintro ⟨x, z'⟩ ⟨hx, hz'⟩ hP'q
        have hz'z : z' = z := by simpa using hz'
        subst z'
        have hfx : f x = g z := by simpa using hx
        let p : Function.Pullback f g := ⟨(x, z), hfx⟩
        have hp : p ∈ P := by
          rw [← hP'eq]
          exact hP'q
        exact hzP ⟨p, hp, rfl⟩
      obtain ⟨U, V, hUopen, hVopen, hKsub, hzV, hUV⟩ :=
        tube_lemma (hfiber (g z)) isCompact_singleton hP'.isOpen_compl hAB
      have hfUclosed : IsClosed (f '' Uᶜ) := hclosed _ hUopen.isClosed_compl
      have hNopen : IsOpen (V ∩ g ⁻¹' (f '' Uᶜ)ᶜ) :=
        hVopen.inter (hfUclosed.isOpen_compl.preimage hg)
      have hzN : z ∈ V ∩ g ⁻¹' (f '' Uᶜ)ᶜ := by
        refine ⟨hzV (mem_singleton z), ?_⟩
        intro hzimage
        rcases hzimage with ⟨x, hxU, hfx⟩
        have hxK : x ∈ f ⁻¹' {g z} := by simp [hfx]
        exact hxU (hKsub hxK)
      rcases hz (V ∩ g ⁻¹' (f '' Uᶜ)ᶜ) (hNopen.mem_nhds hzN) with
        ⟨z', hz'N, ⟨p, hp, hps⟩⟩
      have hxU : p.val.1 ∈ U := by
        by_contra hxU
        apply hz'N.2
        exact ⟨p.val.1, hxU, p.property.trans (congr_arg g hps)⟩
      have hp' : p.val ∈ P' := by
        change p ∈ Subtype.val ⁻¹' P'
        exact hP'eq.symm ▸ hp
      have hz'pV : p.val.2 ∈ V := by
        change Pullback.snd p ∈ V
        rw [hps]
        exact hz'N.1
      exact (hUV ⟨hxU, hz'pV⟩) hp'
    · have hUopen : IsOpen (g ⁻¹' (range f)ᶜ) :=
        hclosed.isClosed_range.isOpen_compl.preimage hg
      rcases hz (g ⁻¹' (range f)ᶜ) (hUopen.mem_nhds hzrange) with
        ⟨z', hz'z, ⟨p, hp, hps⟩⟩
      have hz'not : g (Pullback.snd p) ∉ range f := by
        rw [← hps] at hz'z
        exact hz'z
      exact hz'not ⟨p.val.1, p.property⟩
  tfae_have 3 → 4 := by
    intro h
    let graph : X → Function.Pullback f (ULift.down : ULift.{max u v} Y → Y) :=
      fun x => ⟨(x, ULift.up (f x)), rfl⟩
    have hgraph : IsHomeomorph graph := by
      apply isHomeomorph_iff_exists_inverse.mpr
      refine ⟨?_, ?_⟩
      · exact
          (continuous_id.prodMk (continuous_uliftUp.comp hf)).subtype_mk (fun x => rfl)
      · refine ⟨fun p : Function.Pullback f (ULift.down : ULift.{max u v} Y → Y) =>
          p.val.1, ?_, ?_, ?_⟩
        · intro x
          rfl
        · intro p
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · exact congrArg ULift.up p.property
        · exact continuous_fst.comp continuous_subtype_val
    have hclosed : IsClosedMap f := by
      have hpullback :
          IsClosedMap
            (@Function.Pullback.snd X Y (ULift.{max u v} Y) f
              (ULift.down : ULift.{max u v} Y → Y)) :=
        h (ULift.{max u v} Y) (ULift.down : ULift.{max u v} Y → Y)
          continuous_uliftDown
      have hcomp : IsClosedMap
          ((@Function.Pullback.snd X Y (ULift.{max u v} Y) f
            (ULift.down : ULift.{max u v} Y → Y)) ∘ graph) :=
        hpullback.comp hgraph.isClosedMap
      have hdown : IsClosedMap (ULift.down : ULift.{max u v} Y → Y) :=
        (Homeomorph.ulift (X := Y)).isClosedMap
      have hcomp' : IsClosedMap
          ((ULift.down : ULift.{max u v} Y → Y) ∘
            ((@Function.Pullback.snd X Y (ULift.{max u v} Y) f
              (ULift.down : ULift.{max u v} Y → Y)) ∘ graph)) :=
        hdown.comp hcomp
      have hfun :
          (ULift.down : ULift.{max u v} Y → Y) ∘
              ((@Function.Pullback.snd X Y (ULift.{max u v} Y) f
                (ULift.down : ULift.{max u v} Y → Y)) ∘ graph) = f := by
        funext x
        rfl
      exact hfun ▸ hcomp'
    refine ⟨hclosed, ?_⟩
    intro y
    rw [isCompact_iff_compactSpace]
    apply (compactSpace_iff_isClosedMap_prod_fst (X := f ⁻¹' {y})).2
    intro Z _
    let e : Z × (f ⁻¹' {y}) →
        Function.Pullback f (fun _ : ULift.{max u v} Z => y) :=
      fun p => ⟨(p.2.1, ULift.up p.1), by
        change f p.2.1 = y
        simpa only [mem_preimage, mem_singleton_iff] using p.2.2⟩
    let e' : Function.Pullback f (fun _ : ULift.{max u v} Z => y) → Z × (f ⁻¹' {y}) :=
      fun p => (ULift.down p.val.2, ⟨p.val.1, by simpa using p.property⟩)
    have he : IsHomeomorph e := by
      apply isHomeomorph_iff_exists_inverse.mpr
      refine ⟨?_, ?_⟩
      · exact
          ((continuous_subtype_val.comp continuous_snd).prodMk
            (continuous_uliftUp.comp continuous_fst)).subtype_mk
            (fun p => by
              change f p.2.1 = y
              simpa only [mem_preimage, mem_singleton_iff] using p.2.2)
      · refine ⟨e', ?_, ?_, ?_⟩
        · intro p
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            rfl
        · intro p
          change e (e' p) = p
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · simp [e, e']
        · exact
            (continuous_uliftDown.comp
              (continuous_snd.comp continuous_subtype_val)).prodMk
              ((continuous_fst.comp continuous_subtype_val).subtype_mk
                (fun p => by simpa using p.property))
    have hpullback :
        IsClosedMap
          (@Function.Pullback.snd X Y (ULift.{max u v} Z) f
            (fun _ : ULift.{max u v} Z => y)) :=
      h (ULift.{max u v} Z) (fun _ : ULift.{max u v} Z => y) continuous_const
    have hdown : IsClosedMap (ULift.down : ULift.{max u v} Z → Z) :=
      (Homeomorph.ulift (X := Z)).isClosedMap
    have hcomp : IsClosedMap
        ((ULift.down : ULift.{max u v} Z → Z) ∘
          ((@Function.Pullback.snd X Y (ULift.{max u v} Z) f
            (fun _ : ULift.{max u v} Z => y)) ∘ e)) :=
      hdown.comp (hpullback.comp he.isClosedMap)
    have hfun :
        (ULift.down : ULift.{max u v} Z → Z) ∘
            ((@Function.Pullback.snd X Y (ULift.{max u v} Z) f
              (fun _ : ULift.{max u v} Z => y)) ∘ e) =
          (Prod.fst : Z × (f ⁻¹' {y}) → Z) := by
      funext p
      rfl
    exact hfun ▸ hcomp
  tfae_finish

/-! ### Compact-to-Hausdorff and bijective-map consequences -/

theorem isUniversallyClosed_of_compactSpace_of_t2Space
    {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) [CompactSpace X] [T2Space Y] :
    IsUniversallyClosed.{u, v, w} f := by
  intro Z _ g hg
  have hclosed : IsClosed {p : X × Z | f p.1 = g p.2} := by
    apply isClosed_eq
    · exact hf.comp continuous_fst
    · exact hg.comp continuous_snd
  change IsClosedMap
    ({p : X × Z | f p.1 = g p.2}.domRestrict (Prod.snd : X × Z → Z))
  exact (isClosedMap_snd_of_compactSpace (X := X) (Y := Z)).domRestrict hclosed

theorem isHomeomorph_of_continuous_bijective_of_compactSpace_of_t2Space
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hbij : Function.Bijective f) [CompactSpace X] :
    IsHomeomorph f := by
  exact isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hbij⟩

end CharacterizingProperMaps

end Formalization.Books.Topology.Unit17
