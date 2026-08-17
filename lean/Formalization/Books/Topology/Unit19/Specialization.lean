import Formalization.Books.Topology.Unit10.KrullDimension
import Formalization.Books.Topology.Unit16.ConstructibleSetsAndNoetherian
import Mathlib.Topology.Inseparable
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-!
# Topology, Chapter 19: Specialization

The source's specialization relation and its stable subsets are Mathlib's
`Specializes`, `StableUnderSpecialization`, and `StableUnderGeneralization`.
Maps for which specializations or generalizations lift are represented by the
canonical `SpecializingMap` and `GeneralizingMap` predicates.  The statements
below expose the source results in the book namespace and retain the source's
continuous-map hypotheses.
-/

namespace Formalization.Books.Topology.Unit19

open Set Function _root_.Topology TopologicalSpace

universe u v w

section Specialization

variable {X : Type u} [TopologicalSpace X]

/-!
## Specialization and stable subsets

The first source definition is already present in Mathlib: `x ⤳ y` means
`y ∈ closure ({x} : Set X)`, and the two stability predicates have exactly
the source's specialization/generalization directions.  The source's first
lemma is consequently recorded by the following source-facing interfaces.
-/

theorem isClosed_stableUnderSpecialization {F : Set X} (hF : IsClosed F) :
    StableUnderSpecialization F :=
  hF.stableUnderSpecialization

theorem isOpen_stableUnderGeneralization {U : Set X} (hU : IsOpen U) :
    StableUnderGeneralization U :=
  hU.stableUnderGeneralization

theorem stableUnderSpecialization_iff_compl_stableUnderGeneralization
    {T : Set X} :
    StableUnderSpecialization T ↔ StableUnderGeneralization Tᶜ :=
  stableUnderGeneralization_compl_iff.symm

/- The parenthetical ``directed'' union in the source is represented by the
   canonical arbitrary-union formulation; finite unions of closed sets turn
   any such representation into a directed one. -/
theorem stableUnderSpecialization_iff_union_closed {T : Set X} :
    StableUnderSpecialization T ↔
      ∃ S : Set (Set X), (∀ F ∈ S, IsClosed F) ∧ ⋃₀ S = T :=
  stableUnderSpecialization_iff_exists_sUnion_eq

/-!
## Lifting specializations and generalizations

`SpecializingMap` and `GeneralizingMap` are the source definitions.  Their
composition and image results are already proved in Mathlib; these wrappers
keep the continuous-map context and the source order visible.
-/

theorem specializingMap_comp_of_continuous
    {Y : Type v} [TopologicalSpace Y]
    {Z : Type w} [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (_hf : Continuous f) (_hg : Continuous g)
    (h₁ : SpecializingMap f) (h₂ : SpecializingMap g) :
    SpecializingMap (g ∘ f) :=
  h₁.comp h₂

theorem generalizingMap_comp_of_continuous
    {Y : Type v} [TopologicalSpace Y]
    {Z : Type w} [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (_hf : Continuous f) (_hg : Continuous g)
    (h₁ : GeneralizingMap f) (h₂ : GeneralizingMap g) :
    GeneralizingMap (g ∘ f) :=
  h₁.comp h₂

theorem specializingMap_image_stableUnderSpecialization
    {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (_hf : Continuous f) {T : Set X}
    (hT : StableUnderSpecialization T) (h : SpecializingMap f) :
    StableUnderSpecialization (f '' T) :=
  h.stableUnderSpecialization_image hT

theorem generalizingMap_image_stableUnderGeneralization
    {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (_hf : Continuous f) {T : Set X}
    (hT : StableUnderGeneralization T) (h : GeneralizingMap f) :
    StableUnderGeneralization (f '' T) :=
  h.stableUnderGeneralization_image hT

/-!
## Closed and open maps

The closed-map assertion is Mathlib's `IsClosedMap.specializingMap`.  The
open-map assertion is stated here with the source's Noetherian, generic-point,
and Kolmogorov hypotheses; it is not available as a Mathlib theorem.
-/

theorem isClosedMap_specializingMap
    {Y : Type v} [TopologicalSpace Y] (f : X → Y) (_hf : Continuous f)
    (hclosed : IsClosedMap f) :
    SpecializingMap f :=
  hclosed.specializingMap

theorem isOpenMap_generalizingMap
    {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (hopen : IsOpenMap f) [NoetherianSpace X] [QuasiSober X] [T0Space Y] :
    GeneralizingMap f := by
  intro x y hxy
  let T : Set X := f ⁻¹' ({y} : Set Y)
  have hxT : x ∈ closure T := by
    apply hopen.preimage_closure_subset_closure_preimage
    exact hxy.mem_closure
  let C : Set (Set T) := irreducibleComponents T
  have hCfinite : C.Finite := NoetherianSpace.finite_irreducibleComponents
  let D : Set (Set X) := (fun A : Set T => (Subtype.val : T → X) '' A) '' C
  have hDfinite : D.Finite := hCfinite.image _
  have hTD : T = ⋃₀ D := by
    ext z
    constructor
    · intro hz
      let z' : T := ⟨z, hz⟩
      have hz' : z' ∈ ⋃₀ C := by
        change z' ∈ ⋃₀ irreducibleComponents T
        rw [sUnion_irreducibleComponents]
        exact mem_univ z'
      rcases mem_sUnion.mp hz' with ⟨A, hAC, hzA⟩
      exact mem_sUnion.mpr ⟨(Subtype.val : T → X) '' A, ⟨A, hAC, rfl⟩,
        ⟨z', hzA, rfl⟩⟩
    · intro hz
      rcases mem_sUnion.mp hz with ⟨B, ⟨A, hAC, rfl⟩, z', hz', rfl⟩
      exact z'.property
  rw [hTD, hDfinite.closure_sUnion] at hxT
  rcases mem_iUnion.mp hxT with ⟨B, hxT⟩
  rcases mem_iUnion.mp hxT with ⟨hBD, hxB⟩
  rcases hBD with ⟨A, hAC, rfl⟩
  have hAirr : IsIrreducible A := hAC.1
  have hBirr : IsIrreducible ((Subtype.val : T → X) '' A) :=
    hAirr.image _ continuous_subtype_val.continuousOn
  have hBnonempty : ((Subtype.val : T → X) '' A).Nonempty := hAirr.nonempty.image _
  have hBsubset : (Subtype.val : T → X) '' A ⊆ T := by
    rintro z ⟨z', hz', rfl⟩
    exact z'.property
  have hBimage : f '' ((Subtype.val : T → X) '' A) = ({y} : Set Y) := by
    apply Subset.antisymm
    · rintro z ⟨z', hz', rfl⟩
      have hzT : z' ∈ T := hBsubset hz'
      change f z' ∈ ({y} : Set Y) at hzT
      exact hzT
    · intro z hz
      have hzy : z = y := by simpa using hz
      rcases hBnonempty with ⟨z', hz'⟩
      refine ⟨z', hz', ?_⟩
      have hzT : z' ∈ T := hBsubset hz'
      change f z' ∈ ({y} : Set Y) at hzT
      simpa [hzy] using hzT
  obtain ⟨x', hx'⟩ := QuasiSober.sober hBirr.closure isClosed_closure
  have hxs : x' ⤳ x := by
    rw [specializes_iff_mem_closure, hx'.def]
    exact hxB
  have hx'image := hx'.image hf
  rw [closure_image_closure hf, hBimage] at hx'image
  have hfx : f x' = y := hx'image.eq isGenericPoint_closure
  exact ⟨x', hxs, hfx⟩

/-!
## Quotients by finite equivalence classes

For a map `q : A → B`, ``finite fibres'' is expressed directly as
`∀ b, (q ⁻¹' {b}).Finite`.  The relation generated by `s` and `t` is
`fun u v => ∃ r, t r = u ∧ s r = v`; the final hypothesis says that the
surjective map `π` has exactly these equivalence classes as its fibres.
-/

theorem quotient_of_finite_generalizing_maps_is_kolmogorov
    {R : Type v} [TopologicalSpace R]
    {U : Type w} [TopologicalSpace U]
    {Y : Type u} [TopologicalSpace Y]
    (s t : R → U) (π : U → Y)
    (hs : Continuous s) (ht : Continuous t) (hπ : Continuous π)
    (hπ_open : IsOpenMap π)
    [QuasiSober U] [T0Space U]
    (hs_finite : ∀ u : U, (s ⁻¹' ({u} : Set U)).Finite)
    (ht_finite : ∀ u : U, (t ⁻¹' ({u} : Set U)).Finite)
    (hs_generalizing : GeneralizingMap s)
    (ht_generalizing : GeneralizingMap t)
    (hrel : Equivalence (fun u v : U => ∃ r : R, t r = u ∧ s r = v))
    (hquot : Surjective π ∧
      ∀ u v : U, π u = π v ↔ ∃ r : R, t r = u ∧ s r = v) :
    T0Space Y := by
  classical
  refine ⟨?_⟩
  intro y₁ y₂ hy
  have fibre_finite : ∀ z : Y, (π ⁻¹' ({z} : Set Y)).Finite := by
    intro z
    obtain ⟨u, hu⟩ := hquot.1 z
    have hsub : π ⁻¹' ({z} : Set Y) ⊆ t '' (s ⁻¹' ({u} : Set U)) := by
      intro v hv
      have hvz : π v = z := by simpa using hv
      have hp : π v = π u := hvz.trans hu.symm
      rcases (hquot.2 v u).mp hp with ⟨r, htr, hsr⟩
      refine ⟨r, ?_, htr⟩
      simpa using hsr
    exact (hs_finite u).image t |>.subset hsub
  have closure_fibre (z : Y) :
      closure (π ⁻¹' ({z} : Set Y)) =
        π ⁻¹' closure ({z} : Set Y) := by
    apply Subset.antisymm
    · exact hπ.closure_preimage_subset _
    · exact hπ_open.preimage_closure_subset_closure_preimage
  have lift_specialization (z₁ z₂ : Y) (h : z₁ ⤳ z₂) (v : U)
      (hv : v ∈ π ⁻¹' ({z₂} : Set Y)) :
      ∃ u ∈ π ⁻¹' ({z₁} : Set Y), u ⤳ v := by
    have hvz : π v = z₂ := by simpa using hv
    have hvcl : v ∈ closure (π ⁻¹' ({z₁} : Set Y)) := by
      rw [closure_fibre z₁]
      change π v ∈ closure ({z₁} : Set Y)
      rw [hvz]
      exact h.mem_closure
    have hcl :
        closure (π ⁻¹' ({z₁} : Set Y)) =
          ⋃ u ∈ π ⁻¹' ({z₁} : Set Y), closure ({u} : Set U) := by
      have hunion : π ⁻¹' ({z₁} : Set Y) =
          ⋃ u ∈ π ⁻¹' ({z₁} : Set Y), ({u} : Set U) := by
        ext u
        simp
      calc
        closure (π ⁻¹' ({z₁} : Set Y)) =
            closure (⋃ u ∈ π ⁻¹' ({z₁} : Set Y), ({u} : Set U)) :=
          congrArg closure hunion
        _ = ⋃ u ∈ π ⁻¹' ({z₁} : Set Y), closure ({u} : Set U) :=
          (fibre_finite z₁).closure_biUnion (fun u : U => ({u} : Set U))
    rw [hcl] at hvcl
    rcases mem_iUnion.mp hvcl with ⟨u, hvcl⟩
    rcases mem_iUnion.mp hvcl with ⟨hu, huv⟩
    exact ⟨u, hu, specializes_iff_mem_closure.mpr huv⟩
  let F₁ : Set U := π ⁻¹' ({y₁} : Set Y)
  let F₂ : Set U := π ⁻¹' ({y₂} : Set Y)
  have hstep (u : F₁) :
      ∃ v : F₂, ∃ u' : F₁, (v : U) ⤳ (u : U) ∧ (u' : U) ⤳ (v : U) := by
    obtain ⟨v, hv, hvu⟩ :=
      lift_specialization y₂ y₁ hy.specializes' (u : U) u.property
    obtain ⟨u', hu', huv⟩ := lift_specialization y₁ y₂ hy.specializes v hv
    exact ⟨⟨v, hv⟩, ⟨u', hu'⟩, hvu, huv⟩
  let next : F₁ → F₁ := fun u =>
    Classical.choose (Classical.choose_spec (hstep u))
  have next_rel (u : F₁) :
      ∃ v : F₂, (v : U) ⤳ (u : U) ∧ (next u : U) ⤳ (v : U) := by
    refine ⟨Classical.choose (hstep u), ?_⟩
    simpa [next] using Classical.choose_spec (Classical.choose_spec (hstep u))
  have hF₁ : F₁.Finite := by
    simpa [F₁] using fibre_finite y₁
  let _ : Finite F₁ := Set.finite_coe_iff.mpr hF₁
  obtain ⟨u₀, hu₀⟩ := hquot.1 y₁
  have hu₀' : u₀ ∈ F₁ := by
    change π u₀ ∈ ({y₁} : Set Y)
    simp [hu₀]
  let a₀ : F₁ := ⟨u₀, hu₀'⟩
  let a : ℕ → F₁ := fun n => next^[n] a₀
  obtain ⟨m, n, hmn, hmn_eq⟩ := Finite.exists_ne_map_eq_of_infinite a
  have iter_rel : ∀ k : ℕ, ∀ u : F₁,
      ((next^[k] u : F₁) : U) ⤳ (u : U) := by
    intro k
    induction k with
    | zero =>
        intro u
        simpa using (specializes_rfl : (u : U) ⤳ u)
    | succ k ih =>
        intro u
        rw [Function.iterate_succ_apply]
        obtain ⟨v, hvu, huv⟩ := next_rel u
        exact (ih (next u)).trans (huv.trans hvu)
  have cycle_eq (m n : ℕ) (hmnlt : m < n) (hmn_eq : a m = a n) : y₁ = y₂ := by
    have han : a n = next^[(n - m)] (a m) := by
      calc
        a n = next^[n] a₀ := rfl
        _ = next^[(n - m) + m] a₀ := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hmnlt)]
        _ = next^[(n - m)] (next^[m] a₀) := by
          rw [Function.iterate_add_apply]
        _ = next^[(n - m)] (a m) := rfl
    have hsub_pos : n - m ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hmnlt)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hsub_pos
    have han_next : (a n : U) ⤳ (next (a m) : U) := by
      rw [han, hk, Function.iterate_succ_apply]
      exact iter_rel k (next (a m))
    obtain ⟨v, hvu, huv⟩ := next_rel (a m)
    have hanv : (a n : U) ⤳ (v : U) := han_next.trans huv
    have hvna : (v : U) ⤳ (a n : U) := by
      simpa [hmn_eq] using hvu
    have hav : (a n : U) = (v : U) := (Specializes.antisymm hanv hvna).eq
    have hπav : π (a n : U) = π (v : U) := congrArg π hav
    have hπan : π (a n : U) = y₁ := by
      have hp := (a n).property
      change π (a n : U) ∈ ({y₁} : Set Y) at hp
      simpa using hp
    have hπv : π (v : U) = y₂ := by
      have hp := v.property
      change π (v : U) ∈ ({y₂} : Set Y) at hp
      simpa using hp
    exact hπan.symm.trans (hπav.trans hπv)
  rcases lt_or_gt_of_ne hmn with hmnlt | hnmlt
  · exact cycle_eq m n hmnlt hmn_eq
  · exact (by
      exact cycle_eq n m hnmlt hmn_eq.symm)

/-!
## Dimension and specialization lifting

The source's dimension is the canonical topological Krull dimension
`topologicalKrullDim`, and sobriety is represented by `[QuasiSober Y]`
and `[T0Space Y]`.
-/

theorem topologicalKrullDim_le_of_surjective_of_specializing_or_generalizing
    {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Surjective f)
    [QuasiSober Y] [T0Space Y]
    (hlift : SpecializingMap f ∨ GeneralizingMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · rw [Formalization.Books.Topology.Unit10.krullDimension_eq_bot_iff.mpr hY]
    exact bot_le
  · let _ : Nonempty Y := hY
    let _ : Nonempty (TopologicalSpace.IrreducibleCloseds Y) :=
      ⟨⟨closure ({Classical.choice hY} : Set Y),
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    let pointClosed : X → TopologicalSpace.IrreducibleCloseds X := fun x =>
      ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
    have generic_specializes_of_lt
        {A B : TopologicalSpace.IrreducibleCloseds Y} (hAB : A < B) :
        B.isIrreducible.genericPoint ⤳ A.isIrreducible.genericPoint := by
      apply (B.isIrreducible.isGenericPoint_genericPoint B.isClosed).specializes
      exact (le_of_lt hAB) (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).mem
    have generic_ne_of_lt
        {A B : TopologicalSpace.IrreducibleCloseds Y} (hAB : A < B) :
        A.isIrreducible.genericPoint ≠ B.isIrreducible.genericPoint := by
      intro heq
      apply ne_of_lt hAB
      apply TopologicalSpace.IrreducibleCloseds.ext
      calc
        (A : Set Y) = closure ({A.isIrreducible.genericPoint} : Set Y) :=
          (A.isIrreducible.closure_genericPoint A.isClosed).symm
        _ = closure ({B.isIrreducible.genericPoint} : Set Y) := by rw [heq]
        _ = (B : Set Y) := B.isIrreducible.closure_genericPoint B.isClosed
    have strict_point_closure {x y : X} (hxy : x ⤳ y)
        (himage : f x ≠ f y) : pointClosed y < pointClosed x := by
      have hle : pointClosed y ≤ pointClosed x := by
        change closure ({y} : Set X) ⊆ closure ({x} : Set X)
        exact specializes_iff_closure_subset.mp hxy
      have hne : pointClosed y ≠ pointClosed x := by
        intro heq
        have heq' : closure ({y} : Set X) = closure ({x} : Set X) :=
          congrArg (fun Z : TopologicalSpace.IrreducibleCloseds X => (Z : Set X)) heq
        apply himage
        have hyx : y ⤳ x := by
          rw [specializes_iff_mem_closure, heq']
          exact subset_closure (show x ∈ ({x} : Set X) from rfl)
        exact (Specializes.antisymm (hxy.map hf) (hyx.map hf)).eq
      exact lt_of_le_of_ne hle hne
    have dimension_of_series
        (hseries : ∀ C : LTSeries (TopologicalSpace.IrreducibleCloseds Y),
          ∃ D : LTSeries (TopologicalSpace.IrreducibleCloseds X), D.length = C.length) :
        topologicalKrullDim Y ≤ topologicalKrullDim X := by
      change Order.krullDim (TopologicalSpace.IrreducibleCloseds Y) ≤
        Order.krullDim (TopologicalSpace.IrreducibleCloseds X)
      rw [Order.krullDim_eq_iSup_length
        (α := TopologicalSpace.IrreducibleCloseds Y)]
      rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
      refine iSup_le (fun C : LTSeries (TopologicalSpace.IrreducibleCloseds Y) => ?_)
      obtain ⟨D, hD⟩ := hseries C
      simpa [hD] using (Order.LTSeries.length_le_krullDim D)
    rcases hlift with hs | hg
    · have lift_series_specializing :
          ∀ C : LTSeries (TopologicalSpace.IrreducibleCloseds Y),
            ∃ D : LTSeries (TopologicalSpace.IrreducibleCloseds X),
              D.length = C.length ∧
                ∃ x : X, D.head = pointClosed x ∧
                  f x = C.head.isIrreducible.genericPoint := by
        intro C
        induction C using RelSeries.inductionOn with
        | singleton Z =>
            obtain ⟨x, hx⟩ := hsurj Z.isIrreducible.genericPoint
            refine ⟨RelSeries.singleton _ (pointClosed x), rfl, x, rfl, hx⟩
        | cons p Z hZ hp =>
            obtain ⟨D, hlen, x, hDhead, hfx⟩ := hp
            have htarget : f x ⤳ Z.isIrreducible.genericPoint := by
              rw [hfx]
              exact generic_specializes_of_lt hZ
            obtain ⟨x', hxx', hfx'⟩ := hs htarget
            have hne : f x ≠ f x' := by
              intro heq
              apply (generic_ne_of_lt hZ).symm
              calc
                p.head.isIrreducible.genericPoint = f x := hfx.symm
                _ = f x' := heq
                _ = Z.isIrreducible.genericPoint := hfx'
            have hDlt : pointClosed x' < D.head := by
              rw [hDhead]
              exact strict_point_closure hxx' hne
            refine ⟨D.cons (pointClosed x') hDlt, ?_, x', ?_, hfx'⟩
            · simp [hlen]
            · rfl
      apply dimension_of_series
      intro C
      obtain ⟨D, hD, -⟩ := lift_series_specializing C
      exact ⟨D, hD⟩
    · have lift_series_generalizing :
          ∀ C : LTSeries (TopologicalSpace.IrreducibleCloseds Y),
            ∃ D : LTSeries (TopologicalSpace.IrreducibleCloseds X),
              D.length = C.length ∧
                ∃ x : X, D.last = pointClosed x ∧
                  f x = C.last.isIrreducible.genericPoint := by
        intro C
        induction C using RelSeries.inductionOn' with
        | singleton Z =>
            obtain ⟨x, hx⟩ := hsurj Z.isIrreducible.genericPoint
            refine ⟨RelSeries.singleton _ (pointClosed x), rfl, x, rfl, hx⟩
        | snoc p Z hZ hp =>
            obtain ⟨D, hlen, x, hDlast, hfx⟩ := hp
            have htarget : Z.isIrreducible.genericPoint ⤳ f x := by
              rw [hfx]
              exact generic_specializes_of_lt hZ
            obtain ⟨x', hxx', hfx'⟩ := hg htarget
            have hne : f x' ≠ f x := by
              intro heq
              apply (generic_ne_of_lt hZ).symm
              calc
                Z.isIrreducible.genericPoint = f x' := hfx'.symm
                _ = f x := heq
                _ = p.last.isIrreducible.genericPoint := hfx
            have hDlt : D.last < pointClosed x' := by
              rw [hDlast]
              exact strict_point_closure hxx' hne
            refine ⟨D.snoc (pointClosed x') hDlt, ?_, x', ?_, ?_⟩
            · simp [hlen]
            · simp
            · simpa using hfx'
      apply dimension_of_series
      intro C
      obtain ⟨D, hD, -⟩ := lift_series_generalizing C
      exact ⟨D, hD⟩

/-!
## Constructible stable subsets in Noetherian sober spaces
-/

private theorem isOpen_of_isConstructible_of_stableUnderGeneralization_aux
    (E : Set X) [NoetherianSpace X] [QuasiSober X] [T0Space X]
    (hE : IsConstructible E)
    (hstable : StableUnderGeneralization E) :
    IsOpen E := by
  rw [Formalization.Books.Topology.Unit16.isOpen_iff_irreducible_closed]
  intro Z hZirr hZclosed
  by_cases hempty : (Subtype.val : Z → X) ⁻¹' E = ∅
  · exact Or.inl hempty
  · obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨x, hx⟩ := QuasiSober.sober hZirr hZclosed
    have hxE : x ∈ E := by
      apply hstable (hx.specializes z.property)
      exact hz
    have hsingle : ({x} : Set X) ⊆
        (Subtype.val : Z → X) '' ((Subtype.val : Z → X) ⁻¹' E) := by
      intro y hy
      have hyx : y = x := by simpa using hy
      subst y
      exact ⟨⟨x, hx.mem⟩, hxE, rfl⟩
    have hdense : Dense ((Subtype.val : Z → X) ⁻¹' E) := by
      rw [Subtype.dense_iff]
      intro y hy
      rw [← hx.def] at hy
      exact closure_mono hsingle hy
    rcases
        (Formalization.Books.Topology.Unit16.isConstructible_iff_irreducible_closed.mp hE)
          Z hZirr hZclosed with hU | hnotdense
    · exact Or.inr hU
    · exact (hnotdense hdense).elim

theorem isClosed_of_isConstructible_of_stableUnderSpecialization
    (E : Set X) [NoetherianSpace X] [QuasiSober X] [T0Space X]
    (hE : IsConstructible E)
    (hstable : StableUnderSpecialization E) :
    IsClosed E := by
  apply isOpen_compl_iff.mp
  exact isOpen_of_isConstructible_of_stableUnderGeneralization_aux Eᶜ hE.compl hstable.compl

theorem isOpen_of_isConstructible_of_stableUnderGeneralization
    (E : Set X) [NoetherianSpace X] [QuasiSober X] [T0Space X]
    (hE : IsConstructible E)
    (hstable : StableUnderGeneralization E) :
    IsOpen E := by
  exact isOpen_of_isConstructible_of_stableUnderGeneralization_aux E hE hstable

end Specialization

end Formalization.Books.Topology.Unit19
