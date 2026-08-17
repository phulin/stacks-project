import Formalization.Books.Topology.Unit09.NoetherianSpaces
import Formalization.Books.Topology.Unit15.ConstructibleSets

/-!
# Topology, Chapter 16: Constructible sets and Noetherian spaces

The source's constructible sets are Mathlib's `IsConstructible` predicate,
locally closed sets are `IsLocallyClosed`, and Noetherian spaces are
`NoetherianSpace`.  Relative open sets and density on a subset are expressed
using the induced topology on its subtype.
-/

namespace Formalization.Books.Topology.Unit16

open Set Function _root_.Topology TopologicalSpace

universe u v

section ConstructibleSetsAndNoetherianSpaces

variable {X : Type u} [TopologicalSpace X]

/-!
### Constructible sets and Noetherian spaces

The following declarations formalize the five lemmas in the source section,
in their source order.  A finite union of locally closed sets is represented
by a finite set of subsets and `Set.sUnion`; for a subset `Z`, an open or dense
intersection with `E` is represented by the preimage along the subtype
inclusion `Z → X`.
-/

/- The source's first lemma, using the finite-union normal form already exposed
   for constructible sets in Chapter 15. -/
theorem isConstructible_iff_finite_union_isLocallyClosed
    [NoetherianSpace X] {E : Set X} :
    IsConstructible E ↔
      ∃ S : Set (Set X), S.Finite ∧
        (∀ T ∈ S, IsLocallyClosed T) ∧ E = ⋃₀ S := by
  constructor
  · exact Formalization.Books.Topology.Unit15.isConstructible_isFiniteUnion_isLocallyClosed
  · rintro ⟨S, hSfinite, hSlocallyClosed, rfl⟩
    apply IsConstructible.sUnion hSfinite
    intro T hT
    rcases hSlocallyClosed T hT with ⟨U, Z, hUopen, hZclosed, rfl⟩
    have hU : IsConstructible U := by
      exact (NoetherianSpace.isCompact U).isRetrocompact hUopen |>.isConstructible hUopen
    have hZc : IsConstructible Zᶜ := by
      exact (NoetherianSpace.isCompact Zᶜ).isRetrocompact hZclosed.isOpen_compl |>.isConstructible
        hZclosed.isOpen_compl
    simpa only [compl_compl] using hU.inter hZc.compl

/- The source's second lemma: continuous preimages preserve the finite-union
   locally-closed description when both spaces are Noetherian. -/
theorem isConstructible_preimage_of_continuous
    {Y : Type v} [TopologicalSpace Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (f : X → Y) (hf : Continuous f) {E : Set Y}
    (hE : IsConstructible E) :
    IsConstructible (f ⁻¹' E) := by
  exact hE.preimage hf (by
    intro V hVopen hVretrocompact U hUcompact hUopen
    exact NoetherianSpace.isCompact _)

/- The source's third lemma, with "contains a nonempty open of Z" and
   "dense in Z" written in the subtype topology on Z. -/
theorem isConstructible_iff_irreducible_closed
    [NoetherianSpace X] {E : Set X} :
    IsConstructible E ↔
      ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
        ((∃ U : Set Z,
            IsOpen U ∧ U.Nonempty ∧
              U ⊆ (Subtype.val : Z → X) ⁻¹' E) ∨
          ¬ Dense ((Subtype.val : Z → X) ⁻¹' E)) := by
  constructor
  · intro hE Z hZirreducible hZclosed
    obtain ⟨S, hSfinite, hSlocallyClosed, hSE⟩ :=
      Formalization.Books.Topology.Unit15.isConstructible_isFiniteUnion_isLocallyClosed hE
    by_cases hEdense : Dense ((Subtype.val : Z → X) ⁻¹' E)
    · left
      rcases (Formalization.Books.Topology.Unit15.dense_preimage_of_finite_locallyClosed_union_iff
        hZirreducible ⟨S, hSfinite, hSlocallyClosed, hSE⟩).mpr hEdense with
        ⟨U, hUopen, hUdense, hUE⟩
      let _ : Nonempty Z := hZirreducible.nonempty.to_subtype
      exact ⟨U, hUopen, hUdense.nonempty, hUE⟩
    · exact Or.inr hEdense
  · intro hEcondition
    have hopen_constructible : ∀ {U : Set X}, IsOpen U → IsConstructible U := by
      intro U hUopen
      exact (NoetherianSpace.isCompact U).isRetrocompact hUopen |>.isConstructible hUopen
    have hclosed_constructible : ∀ {Z : Set X}, IsClosed Z → IsConstructible Z := by
      intro Z hZclosed
      have hZc : IsConstructible Zᶜ := by
        exact (NoetherianSpace.isCompact Zᶜ).isRetrocompact hZclosed.isOpen_compl |>.isConstructible
          hZclosed.isOpen_compl
      simpa only [compl_compl] using hZc.compl
    have hP : ∀ C : Closeds X, IsConstructible (E ∩ (C : Set X)) := by
      intro C
      induction C using WellFoundedLT.induction with
      | ind C ih =>
          have hCclosed : IsClosed (C : Set X) := C.isClosed
          by_cases hCirreducible : IsIrreducible (C : Set X)
          · rcases hEcondition (C : Set X) hCirreducible hCclosed with hCopen | hCnotdense
            · rcases hCopen with ⟨U, hUopen, hUnonempty, hUE⟩
              rcases IsInducing.subtypeVal.isOpen_iff.mp hUopen with ⟨O, hOopen, hOU⟩
              have hOCsubset : O ∩ (C : Set X) ⊆ E := by
                intro x hx
                have hxU : (⟨x, hx.2⟩ : C) ∈ U := by
                  rw [← hOU]
                  exact hx.1
                exact hUE hxU
              let D : Set X := (C : Set X) ∩ Oᶜ
              have hDclosed : IsClosed D := hCclosed.inter hOopen.isClosed_compl
              have hDsubset : D ⊆ (C : Set X) := inter_subset_left
              have hDne : (⟨D, hDclosed⟩ : Closeds X) ≠ C := by
                intro hDC
                rcases hUnonempty with ⟨x, hx⟩
                have hxC : (x : X) ∈ (C : Set X) := x.property
                have hxO : (x : X) ∈ O := by
                  have hxpre : x ∈ (Subtype.val : C → X) ⁻¹' O := by
                    exact hOU.symm ▸ hx
                  exact hxpre
                have hxD : (x : X) ∈ (⟨D, hDclosed⟩ : Closeds X) := by
                  rw [hDC]
                  exact hxC
                change (x : X) ∈ (C : Set X) ∩ Oᶜ at hxD
                exact hxD.2 hxO
              have hDlt : (⟨D, hDclosed⟩ : Closeds X) < C :=
                lt_of_le_of_ne hDsubset hDne
              have hEDconstructible : IsConstructible (E ∩ D) := by
                have h := ih (⟨D, hDclosed⟩ : Closeds X) hDlt
                simpa only [Closeds.coe_mk] using h
              have hOCconstructible : IsConstructible (O ∩ (C : Set X)) :=
                (hopen_constructible hOopen).inter (hclosed_constructible hCclosed)
              have hEC : E ∩ (C : Set X) =
                  (O ∩ (C : Set X)) ∪ (E ∩ D) := by
                ext x
                constructor
                · intro hx
                  by_cases hxO : x ∈ O
                  · exact Or.inl ⟨hxO, hx.2⟩
                  · exact Or.inr ⟨hx.1, ⟨hx.2, hxO⟩⟩
                · intro hx
                  rcases hx with hxO | hxD
                  · exact ⟨hOCsubset hxO, hxO.2⟩
                  · exact ⟨hxD.1, hxD.2.1⟩
              rw [hEC]
              exact hOCconstructible.union hEDconstructible
            · have hnot_subset : ¬ (C : Set X) ⊆ closure (E ∩ (C : Set X)) := by
                intro hsubset
                apply hCnotdense
                apply Subtype.dense_iff.mpr
                simpa only [Set.image_preimage_eq_inter_range, Subtype.range_coe] using hsubset
              let D : Set X := closure (E ∩ (C : Set X))
              have hDclosed : IsClosed D := isClosed_closure
              have hDsubset : D ⊆ (C : Set X) :=
                closure_minimal inter_subset_right hCclosed
              have hDne : (⟨D, hDclosed⟩ : Closeds X) ≠ C := by
                intro hDC
                apply hnot_subset
                have hDCset : D = (C : Set X) := congrArg (fun Z : Closeds X => (Z : Set X)) hDC
                intro x hxC
                have hxD : x ∈ D := by
                  rw [hDCset]
                  exact hxC
                simpa only [D] using hxD
              have hDlt : (⟨D, hDclosed⟩ : Closeds X) < C :=
                lt_of_le_of_ne hDsubset hDne
              have hEDconstructible : IsConstructible (E ∩ D) := by
                have h := ih (⟨D, hDclosed⟩ : Closeds X) hDlt
                simpa only [Closeds.coe_mk] using h
              have hEC : E ∩ (C : Set X) = E ∩ D := by
                ext x
                constructor
                · intro hx
                  exact ⟨hx.1, subset_closure hx⟩
                · intro hx
                  exact ⟨hx.1, hDsubset hx.2⟩
              rw [hEC]
              exact hEDconstructible
          · obtain ⟨S, hSfinite, hSclosed, hSirreducible, hSC⟩ :=
              NoetherianSpace.exists_finite_set_isClosed_irreducible hCclosed
            have hSpieces : ∀ T ∈ S, IsConstructible (E ∩ T) := by
              intro T hT
              have hTC : T ⊆ (C : Set X) := by
                rw [hSC]
                exact Set.subset_sUnion_of_mem hT
              have hTne : T ≠ (C : Set X) := by
                intro hTCeq
                exact hCirreducible (by
                  rw [← hTCeq]
                  exact hSirreducible T hT)
              have hTlt : (⟨T, hSclosed T hT⟩ : Closeds X) < C := by
                apply lt_of_le_of_ne hTC
                intro hEq
                exact hTne hEq
              have h := ih (⟨T, hSclosed T hT⟩ : Closeds X) hTlt
              simpa only [Closeds.coe_mk] using h
            have hSunion : IsConstructible (⋃ T ∈ S, E ∩ T) :=
              IsConstructible.biUnion hSfinite hSpieces
            have hEC : E ∩ (C : Set X) = ⋃ T ∈ S, E ∩ T := by
              rw [hSC]
              ext x
              simp
            rw [hEC]
            exact hSunion
    have hglobal := hP (⟨Set.univ, isClosed_univ⟩ : Closeds X)
    simpa only [Closeds.coe_mk, inter_univ] using hglobal

/- The source's fourth lemma.  Membership in `𝓝 x` is the canonical
   neighborhood predicate for the ambient set E. -/
theorem isConstructible_iff_mem_nhds_of_irreducible_closed
    [NoetherianSpace X] (x : X) {E : Set X}
    (hE : IsConstructible E) :
    E ∈ 𝓝 x ↔
      ∀ Y : Set X, IsIrreducible Y → IsClosed Y → x ∈ Y →
        Dense ((Subtype.val : Y → X) ⁻¹' E) := by
  constructor
  · intro hEnhds Y hYirreducible hYclosed hxY
    rcases mem_nhds_iff.mp hEnhds with ⟨U, hUE, hUopen, hxU⟩
    let _ : IrreducibleSpace Y := Subtype.irreducibleSpace hYirreducible
    let V : Set Y := (Subtype.val : Y → X) ⁻¹' U
    have hVopen : IsOpen V := hUopen.preimage continuous_subtype_val
    have hVnonempty : V.Nonempty := by
      exact ⟨⟨x, hxY⟩, hxU⟩
    have hVdense : Dense V := hVopen.dense hVnonempty
    exact hVdense.mono (by
      intro y hy
      exact hUE hy)
  · intro hEdense
    have hchar := (isConstructible_iff_irreducible_closed (E := E)).mp hE
    have hP : ∀ C : Closeds X, ∀ hx : x ∈ (C : Set X),
        ((Subtype.val : ↥(C : Set X) → X) ⁻¹' E) ∈
          𝓝 (⟨x, hx⟩ : ↥(C : Set X)) := by
      intro C
      induction C using WellFoundedLT.induction with
      | ind C ih =>
          intro hx
          have hCclosed : IsClosed (C : Set X) := C.isClosed
          by_cases hCirreducible : IsIrreducible (C : Set X)
          · have hCdense : Dense ((Subtype.val : ↥(C : Set X) → X) ⁻¹' E) :=
              hEdense (C : Set X) hCirreducible hCclosed hx
            rcases hchar (C : Set X) hCirreducible hCclosed with hCopen | hCnotdense
            · rcases hCopen with ⟨U, hUopen, hUnonempty, hUE⟩
              rcases IsInducing.subtypeVal.isOpen_iff.mp hUopen with ⟨O, hOopen, hOU⟩
              by_cases hxU : (⟨x, hx⟩ : ↥(C : Set X)) ∈ U
              · exact Filter.mem_of_superset (hUopen.mem_nhds hxU) hUE
              · let D : Set X := (C : Set X) ∩ Oᶜ
                have hDclosed : IsClosed D := hCclosed.inter hOopen.isClosed_compl
                have hDsubset : D ⊆ (C : Set X) := inter_subset_left
                have hDne : (⟨D, hDclosed⟩ : Closeds X) ≠ C := by
                  intro hDC
                  rcases hUnonempty with ⟨z, hz⟩
                  have hzC : (z : X) ∈ (C : Set X) := z.property
                  have hzO : (z : X) ∈ O := by
                    have hzpre : z ∈ (Subtype.val : ↥(C : Set X) → X) ⁻¹' O :=
                      hOU.symm ▸ hz
                    exact hzpre
                  have hzD : (z : X) ∈ (⟨D, hDclosed⟩ : Closeds X) := by
                    rw [hDC]
                    exact hzC
                  change (z : X) ∈ (C : Set X) ∩ Oᶜ at hzD
                  exact hzD.2 hzO
                have hDlt : (⟨D, hDclosed⟩ : Closeds X) < C :=
                  lt_of_le_of_ne hDsubset hDne
                have hxD : x ∈ D := by
                  exact ⟨hx, by
                    intro hxO
                    have hxpre : (⟨x, hx⟩ : ↥(C : Set X)) ∈
                        (Subtype.val : ↥(C : Set X) → X) ⁻¹' O := hxO
                    exact hxU (hOU ▸ hxpre)
                  ⟩
                have hDnhds := ih (⟨D, hDclosed⟩ : Closeds X) hDlt hxD
                rcases mem_nhds_iff.mp hDnhds with ⟨V, hVsub, hVopen, hxV⟩
                rcases IsInducing.subtypeVal.isOpen_iff.mp hVopen with ⟨W, hWopen, hWV⟩
                let Q : Set (C : Set X) :=
                  (Subtype.val : ↥(C : Set X) → X) ⁻¹' (O ∪ W)
                have hQopen : IsOpen Q :=
                  (hOopen.union hWopen).preimage continuous_subtype_val
                have hxQ : (⟨x, hx⟩ : ↥(C : Set X)) ∈ Q := by
                  change (x : X) ∈ O ∪ W
                  right
                  have hxpre : (⟨x, hxD⟩ : D) ∈
                      (Subtype.val : D → X) ⁻¹' W := hWV.symm ▸ hxV
                  exact hxpre
                have hQsub : Q ⊆ (Subtype.val : ↥(C : Set X) → X) ⁻¹' E := by
                  intro y hy
                  change (y : X) ∈ O ∪ W at hy
                  change (y : X) ∈ E
                  rcases hy with hyO | hyW
                  · have hypre : y ∈ (Subtype.val : ↥(C : Set X) → X) ⁻¹' O := hyO
                    exact hUE (hOU ▸ hypre)
                  · by_cases hyO : (y : X) ∈ O
                    · have hypre : y ∈ (Subtype.val : ↥(C : Set X) → X) ⁻¹' O := hyO
                      exact hUE (hOU ▸ hypre)
                    · have hyD : (y : X) ∈ D := ⟨y.property, hyO⟩
                      have hyV : (⟨(y : X), hyD⟩ : D) ∈ V := by
                        have hypre : (⟨(y : X), hyD⟩ : D) ∈
                            (Subtype.val : D → X) ⁻¹' W := hyW
                        exact hWV ▸ hypre
                      exact hVsub hyV
                exact Filter.mem_of_superset (hQopen.mem_nhds hxQ) hQsub
            · exact (hCnotdense hCdense).elim
          · have hCpre : ¬ IsPreirreducible (C : Set X) := by
              intro hCpre
              exact hCirreducible ⟨⟨x, hx⟩, hCpre⟩
            rw [isPreirreducible_iff_isClosed_union_isClosed] at hCpre
            push Not at hCpre
            rcases hCpre with ⟨A, B, hAclosed, hBclosed, hcover, hAnot, hBnot⟩
            let D₁ : Set X := (C : Set X) ∩ A
            let D₂ : Set X := (C : Set X) ∩ B
            have hD₁closed : IsClosed D₁ := hCclosed.inter hAclosed
            have hD₂closed : IsClosed D₂ := hCclosed.inter hBclosed
            have hD₁subset : D₁ ⊆ (C : Set X) := inter_subset_left
            have hD₂subset : D₂ ⊆ (C : Set X) := inter_subset_left
            have hD₁ne : (⟨D₁, hD₁closed⟩ : Closeds X) ≠ C := by
              intro hEq
              have hEqset : D₁ = (C : Set X) :=
                congrArg (fun Z : Closeds X => (Z : Set X)) hEq
              apply hAnot
              intro y hy
              have hyD : y ∈ D₁ := by rw [hEqset]; exact hy
              exact hyD.2
            have hD₂ne : (⟨D₂, hD₂closed⟩ : Closeds X) ≠ C := by
              intro hEq
              have hEqset : D₂ = (C : Set X) :=
                congrArg (fun Z : Closeds X => (Z : Set X)) hEq
              apply hBnot
              intro y hy
              have hyD : y ∈ D₂ := by rw [hEqset]; exact hy
              exact hyD.2
            have hD₁lt : (⟨D₁, hD₁closed⟩ : Closeds X) < C :=
              lt_of_le_of_ne hD₁subset hD₁ne
            have hD₂lt : (⟨D₂, hD₂closed⟩ : Closeds X) < C :=
              lt_of_le_of_ne hD₂subset hD₂ne
            have hDcover : (C : Set X) ⊆ D₁ ∪ D₂ := by
              intro y hy
              rcases hcover hy with hyA | hyB
              · exact Or.inl ⟨hy, hyA⟩
              · exact Or.inr ⟨hy, hyB⟩
            by_cases hxD₁ : x ∈ D₁
            · by_cases hxD₂ : x ∈ D₂
              · have hN₁ := ih (⟨D₁, hD₁closed⟩ : Closeds X) hD₁lt hxD₁
                have hN₂ := ih (⟨D₂, hD₂closed⟩ : Closeds X) hD₂lt hxD₂
                rcases mem_nhds_iff.mp hN₁ with ⟨V₁, hV₁sub, hV₁open, hxV₁⟩
                rcases mem_nhds_iff.mp hN₂ with ⟨V₂, hV₂sub, hV₂open, hxV₂⟩
                rcases IsInducing.subtypeVal.isOpen_iff.mp hV₁open with ⟨W₁, hW₁open, hW₁V⟩
                rcases IsInducing.subtypeVal.isOpen_iff.mp hV₂open with ⟨W₂, hW₂open, hW₂V⟩
                let Q : Set (C : Set X) :=
                  (Subtype.val : ↥(C : Set X) → X) ⁻¹' (W₁ ∩ W₂)
                have hQopen : IsOpen Q :=
                  (hW₁open.inter hW₂open).preimage continuous_subtype_val
                have hxQ : (⟨x, hx⟩ : ↥(C : Set X)) ∈ Q := by
                  change (x : X) ∈ W₁ ∩ W₂
                  have hxpre₁ : (⟨x, hxD₁⟩ : D₁) ∈
                      (Subtype.val : D₁ → X) ⁻¹' W₁ := hW₁V.symm ▸ hxV₁
                  have hxpre₂ : (⟨x, hxD₂⟩ : D₂) ∈
                      (Subtype.val : D₂ → X) ⁻¹' W₂ := hW₂V.symm ▸ hxV₂
                  exact ⟨hxpre₁, hxpre₂⟩
                have hQsub : Q ⊆ (Subtype.val : ↥(C : Set X) → X) ⁻¹' E := by
                  intro y hy
                  change (y : X) ∈ W₁ ∩ W₂ at hy
                  change (y : X) ∈ E
                  rcases hDcover y.property with hyD₁ | hyD₂
                  · have hyV₁ : (⟨(y : X), hyD₁⟩ : D₁) ∈ V₁ := by
                      have hypre : (⟨(y : X), hyD₁⟩ : D₁) ∈
                          (Subtype.val : D₁ → X) ⁻¹' W₁ := hy.1
                      exact hW₁V ▸ hypre
                    exact hV₁sub hyV₁
                  · have hyV₂ : (⟨(y : X), hyD₂⟩ : D₂) ∈ V₂ := by
                      have hypre : (⟨(y : X), hyD₂⟩ : D₂) ∈
                          (Subtype.val : D₂ → X) ⁻¹' W₂ := hy.2
                      exact hW₂V ▸ hypre
                    exact hV₂sub hyV₂
                exact Filter.mem_of_superset (hQopen.mem_nhds hxQ) hQsub
              · have hN₁ := ih (⟨D₁, hD₁closed⟩ : Closeds X) hD₁lt hxD₁
                rcases mem_nhds_iff.mp hN₁ with ⟨V₁, hV₁sub, hV₁open, hxV₁⟩
                rcases IsInducing.subtypeVal.isOpen_iff.mp hV₁open with ⟨W₁, hW₁open, hW₁V⟩
                let Q : Set (C : Set X) :=
                  (Subtype.val : ↥(C : Set X) → X) ⁻¹' (W₁ ∩ Bᶜ)
                have hQopen : IsOpen Q :=
                  (hW₁open.inter hBclosed.isOpen_compl).preimage continuous_subtype_val
                have hxQ : (⟨x, hx⟩ : ↥(C : Set X)) ∈ Q := by
                  change (x : X) ∈ W₁ ∩ Bᶜ
                  have hxnotB : (x : X) ∉ B := by
                    intro hxB
                    exact hxD₂ ⟨hx, hxB⟩
                  have hxpre : (⟨x, hxD₁⟩ : D₁) ∈
                      (Subtype.val : D₁ → X) ⁻¹' W₁ := hW₁V.symm ▸ hxV₁
                  exact ⟨hxpre, hxnotB⟩
                have hQsub : Q ⊆ (Subtype.val : ↥(C : Set X) → X) ⁻¹' E := by
                  intro y hy
                  change (y : X) ∈ W₁ ∩ Bᶜ at hy
                  change (y : X) ∈ E
                  have hyD₁ : (y : X) ∈ D₁ := by
                    rcases hDcover y.property with hyD₁ | hyD₂
                    · exact hyD₁
                    · exact (hy.2 hyD₂.2).elim
                  have hyV₁ : (⟨(y : X), hyD₁⟩ : D₁) ∈ V₁ := by
                    have hypre : (⟨(y : X), hyD₁⟩ : D₁) ∈
                        (Subtype.val : D₁ → X) ⁻¹' W₁ := hy.1
                    exact hW₁V ▸ hypre
                  exact hV₁sub hyV₁
                exact Filter.mem_of_superset (hQopen.mem_nhds hxQ) hQsub
            · have hxD₂ : x ∈ D₂ := (hDcover hx).resolve_left hxD₁
              have hN₂ := ih (⟨D₂, hD₂closed⟩ : Closeds X) hD₂lt hxD₂
              rcases mem_nhds_iff.mp hN₂ with ⟨V₂, hV₂sub, hV₂open, hxV₂⟩
              rcases IsInducing.subtypeVal.isOpen_iff.mp hV₂open with ⟨W₂, hW₂open, hW₂V⟩
              let Q : Set (C : Set X) :=
                (Subtype.val : ↥(C : Set X) → X) ⁻¹' (W₂ ∩ Aᶜ)
              have hQopen : IsOpen Q :=
                (hW₂open.inter hAclosed.isOpen_compl).preimage continuous_subtype_val
              have hxQ : (⟨x, hx⟩ : ↥(C : Set X)) ∈ Q := by
                change (x : X) ∈ W₂ ∩ Aᶜ
                have hxnotA : (x : X) ∉ A := by
                  intro hxA
                  exact hxD₁ ⟨hx, hxA⟩
                have hxpre : (⟨x, hxD₂⟩ : D₂) ∈
                    (Subtype.val : D₂ → X) ⁻¹' W₂ := hW₂V.symm ▸ hxV₂
                exact ⟨hxpre, hxnotA⟩
              have hQsub : Q ⊆ (Subtype.val : ↥(C : Set X) → X) ⁻¹' E := by
                intro y hy
                change (y : X) ∈ W₂ ∩ Aᶜ at hy
                change (y : X) ∈ E
                have hyD₂ : (y : X) ∈ D₂ := by
                  rcases hDcover y.property with hyD₁ | hyD₂
                  · exact (hy.2 hyD₁.2).elim
                  · exact hyD₂
                have hyV₂ : (⟨(y : X), hyD₂⟩ : D₂) ∈ V₂ := by
                  have hypre : (⟨(y : X), hyD₂⟩ : D₂) ∈
                      (Subtype.val : D₂ → X) ⁻¹' W₂ := hy.1
                  exact hW₂V ▸ hypre
                exact hV₂sub hyV₂
              exact Filter.mem_of_superset (hQopen.mem_nhds hxQ) hQsub
    have hglobal := hP (⟨Set.univ, isClosed_univ⟩ : Closeds X) (by simp)
    rcases mem_nhds_iff.mp hglobal with ⟨V, hVE, hVopen, hxV⟩
    rcases IsInducing.subtypeVal.isOpen_iff.mp hVopen with ⟨U, hUopen, hUV⟩
    have hxU : x ∈ U := by
      have hxpre : (⟨x, Set.mem_univ x⟩ : ↥(Set.univ : Set X)) ∈
          (Subtype.val : ↥(Set.univ : Set X) → X) ⁻¹' U := hUV.symm ▸ hxV
      exact hxpre
    exact Filter.mem_of_superset (hUopen.mem_nhds hxU) (by
      intro y hy
      have hyV : (⟨y, Set.mem_univ y⟩ : ↥(Set.univ : Set X)) ∈ V := by
        have hypre : (⟨y, Set.mem_univ y⟩ : ↥(Set.univ : Set X)) ∈
            (Subtype.val : ↥(Set.univ : Set X) → X) ⁻¹' U := hy
        exact hUV ▸ hypre
      exact hVE hyV)

/- The source's fifth lemma, characterizing open sets by their intersections
   with irreducible closed subsets. -/
theorem isOpen_iff_irreducible_closed
    [NoetherianSpace X] {E : Set X} :
    IsOpen E ↔
      ∀ Y : Set X, IsIrreducible Y → IsClosed Y →
        (((Subtype.val : Y → X) ⁻¹' E = ∅) ∨
          ∃ U : Set Y,
            IsOpen U ∧ U.Nonempty ∧
              U ⊆ (Subtype.val : Y → X) ⁻¹' E) := by
  constructor
  · intro hEopen Y _ _
    by_cases hEnonempty : ((Subtype.val : Y → X) ⁻¹' E).Nonempty
    · exact Or.inr ⟨(Subtype.val : Y → X) ⁻¹' E,
        hEopen.preimage continuous_subtype_val, hEnonempty, subset_rfl⟩
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hEnonempty)
  · intro hcondition
    have hEconstructible : IsConstructible E := by
      apply (isConstructible_iff_irreducible_closed (E := E)).mpr
      intro Y hYirreducible hYclosed
      rcases hcondition Y hYirreducible hYclosed with hYempty | hYopen
      · right
        let _ : Nonempty Y := hYirreducible.nonempty.to_subtype
        intro hYdense
        have hYnonempty : ((Subtype.val : Y → X) ⁻¹' E).Nonempty := hYdense.nonempty
        rw [hYempty] at hYnonempty
        simp at hYnonempty
      · exact Or.inl hYopen
    apply isOpen_iff_mem_nhds.mpr
    intro x hxE
    apply (isConstructible_iff_mem_nhds_of_irreducible_closed x hEconstructible).mpr
    intro Y hYirreducible hYclosed hxY
    rcases hcondition Y hYirreducible hYclosed with hYempty | hYopen
    · have hxpre : (⟨x, hxY⟩ : Y) ∈ (Subtype.val : Y → X) ⁻¹' E := hxE
      rw [hYempty] at hxpre
      exact hxpre.elim
    · rcases hYopen with ⟨U, hUopen, hUnonempty, hUE⟩
      let _ : IrreducibleSpace Y := Subtype.irreducibleSpace hYirreducible
      exact (hUopen.dense hUnonempty).mono hUE

end ConstructibleSetsAndNoetherianSpaces

end Formalization.Books.Topology.Unit16
