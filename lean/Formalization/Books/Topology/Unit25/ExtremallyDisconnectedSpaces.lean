import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Topology.Category.Stonean.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Topology, Chapter 25: Extremally disconnected spaces

The source definition is Mathlib's `ExtremallyDisconnected` class.  The
projectivity and Stonean-cover statements are expressed using Mathlib's
`CompactT2.Projective`, `Stonean`, and `CompHaus.presentation` interfaces.
The source-facing predicates below retain the explicit section and minimal
cover formulations where those formulations are useful to later users.
-/

namespace Formalization.Books.Topology.Unit25

open Function Set
open Formalization.Books.Topology.Unit22

universe u

noncomputable section

section IntroductoryFacts

variable {X : Type u} [TopologicalSpace X]

/- The source definition is exactly Mathlib's `ExtremallyDisconnected`; no
   parallel predicate is introduced. -/

/- The Hausdorff implication in the source is supplied by Mathlib's stronger
   `TotallySeparatedSpace` instance for extremally disconnected Hausdorff
   spaces, together with its totally disconnected consequence. -/

/-- A Hausdorff extremally disconnected space is totally disconnected. -/
theorem totallyDisconnectedSpace_of_t2Space_of_extremallyDisconnected
    [T2Space X] [ExtremallyDisconnected X] : TotallyDisconnectedSpace X := by
  infer_instance

/-- A compact Hausdorff extremally disconnected space is profinite. -/
theorem isProfiniteSpace_of_compact_t2Space_of_extremallyDisconnected
    [CompactSpace X] [T2Space X] [ExtremallyDisconnected X] :
    IsProfiniteSpace X := by
  exact (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected (X := X)).2
    ⟨inferInstance, inferInstance, inferInstance⟩

/- The source's non-converse is recorded by the explicit p-adic example below.
   Mathlib's p-adic integers use `ℤ_[p]`; the prime hypothesis is the standard
   typeclass assumption needed by that construction. -/

/-- The p-adic integers are profinite but not extremally disconnected: the
nonzero elements of even valuation form an open set whose closure is not open.
-/
theorem padicIntegers_evenValuation_example (p : ℕ) [Fact p.Prime] :
    IsProfiniteSpace (ℤ_[p]) ∧
      ¬ @ExtremallyDisconnected (ℤ_[p]) inferInstance ∧
        let U : Set (ℤ_[p]) :=
          {x | x ≠ 0 ∧ Even (PadicInt.valuation x)}
        IsOpen U ∧ closure U = U ∪ ({0} : Set (ℤ_[p])) ∧
          ¬ IsOpen (closure U) := by
  let U : Set (ℤ_[p]) := {x | x ≠ 0 ∧ Even (PadicInt.valuation x)}
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hvaluation_eq {x y : ℤ_[p]} (hx : x ≠ 0) (hy : y ≠ 0)
      (hxy : ‖x‖ = ‖y‖) : x.valuation = y.valuation := by
    rw [PadicInt.norm_eq_zpow_neg_valuation hx,
      PadicInt.norm_eq_zpow_neg_valuation hy] at hxy
    have hval : (-(x.valuation : ℤ)) = -(y.valuation : ℤ) :=
      (zpow_right_strictMono₀ hp1).injective hxy
    exact_mod_cast neg_injective hval
  have hnorm_eq {x y : ℤ_[p]} (hxy : dist x y < ‖x‖) : ‖x‖ = ‖y‖ := by
    have hle : ‖y‖ ≤ ‖x‖ := by
      calc
        ‖y‖ = dist y 0 := by simp [dist_eq_norm]
        _ ≤ max (dist y x) (dist x 0) := dist_triangle_max y x 0
        _ = ‖x‖ := by
          rw [dist_comm y x, dist_eq_norm, dist_zero_right]
          exact max_eq_right (le_of_lt hxy)
    have hge : ‖x‖ ≤ ‖y‖ := by
      by_contra h
      have hy_lt : ‖y‖ < ‖x‖ := lt_of_not_ge h
      have htri : dist x 0 ≤ max (dist x y) (dist y 0) :=
        dist_triangle_max x y 0
      have htri' : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
        simpa [dist_eq_norm] using htri
      have hlt : ‖x‖ < ‖x‖ :=
        lt_of_le_of_lt htri' (max_lt (by simpa [dist_eq_norm] using hxy) hy_lt)
      exact (lt_irrefl _ hlt).elim
    exact le_antisymm hge hle
  have hUopen : IsOpen U := by
    rw [Metric.isOpen_iff]
    intro x hx
    refine ⟨‖x‖, norm_pos_iff.mpr hx.1, ?_⟩
    intro y hy
    have hnorm : ‖x‖ = ‖y‖ :=
      hnorm_eq (by simpa [Metric.mem_ball, dist_comm] using hy)
    have hy0 : y ≠ 0 := by
      intro hy0
      rw [hy0, norm_zero] at hnorm
      exact (norm_pos_iff.mpr hx.1).ne' hnorm
    exact ⟨hy0, hvaluation_eq hx.1 hy0 hnorm ▸ hx.2⟩
  have hclosure : closure U = U ∪ ({0} : Set (ℤ_[p])) := by
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      by_cases hx0 : x = 0
      · right
        rw [hx0]
        exact mem_singleton _
      have hxnotEven : ¬ Even x.valuation := by
        intro hxEven
        exact hxU ⟨hx0, hxEven⟩
      obtain ⟨y, hyU, hxy⟩ := (Metric.mem_closure_iff.mp hx) ‖x‖
        (norm_pos_iff.mpr hx0)
      have hnorm : ‖x‖ = ‖y‖ := hnorm_eq (by simpa [dist_comm] using hxy)
      have hval := hvaluation_eq hx0 hyU.1 hnorm
      exact (hxnotEven (hval ▸ hyU.2)).elim
    · intro x hx
      rcases hx with hxU | hx0
      · exact subset_closure hxU
      · subst x
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
        let y : ℤ_[p] := (p : ℤ_[p]) ^ (2 * k)
        have hy0 : y ≠ 0 := by
          exact pow_ne_zero _ (NeZero.ne _)
        refine ⟨y, ?_, ?_⟩
        · refine ⟨hy0, ?_⟩
          simp [y]
        · rw [dist_eq_norm]
          simp only [zero_sub, norm_neg]
          rw [PadicInt.norm_eq_zpow_neg_valuation hy0]
          have hpow : (-(2 * k : ℕ) : ℤ) ≤ -(k : ℤ) := by omega
          calc
            (p : ℝ) ^ (-(y.valuation : ℤ)) =
                (p : ℝ) ^ (-(2 * k : ℕ) : ℤ) := by simp [y]
            _ ≤ (p : ℝ) ^ (-(k : ℤ)) := zpow_le_zpow_right₀ hp1.le hpow
            _ < ε := hk
  have hnotopen : ¬ IsOpen (closure U) := by
    intro hopen
    have hzero : (0 : ℤ_[p]) ∈ closure U := by
      rw [hclosure]
      exact Or.inr (mem_singleton _)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    let y : ℤ_[p] := (p : ℤ_[p]) ^ (2 * k + 1)
    have hy0 : y ≠ 0 := by
      exact pow_ne_zero _ (NeZero.ne _)
    have hyoutside : y ∉ U ∪ ({0} : Set (ℤ_[p])) := by
      intro hy
      rcases hy with hyU | hyzero
      · have : Even (2 * k + 1) := by simpa [y] using hyU.2
        exact (Nat.not_even_two_mul_add_one k) this
      · exact hy0 (mem_singleton_iff.mp hyzero)
    have hyball : y ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [sub_zero]
      rw [PadicInt.norm_eq_zpow_neg_valuation hy0]
      have hpow : (-(2 * k + 1 : ℕ) : ℤ) ≤ -(k : ℤ) := by omega
      calc
        (p : ℝ) ^ (-(y.valuation : ℤ)) =
            (p : ℝ) ^ (-(2 * k + 1 : ℕ) : ℤ) := by simp [y]
        _ ≤ (p : ℝ) ^ (-(k : ℤ)) := zpow_le_zpow_right₀ hp1.le hpow
        _ < ε := hk
    exact hyoutside (hclosure ▸ hball hyball)
  have hprof : IsProfiniteSpace (ℤ_[p]) := by
    exact (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected
      (X := ℤ_[p])).2 ⟨inferInstance, inferInstance, inferInstance⟩
  have hnotED : ¬ @ExtremallyDisconnected (ℤ_[p]) inferInstance := by
    intro hED
    exact hnotopen (hED.open_closure U hUopen)
  refine ⟨hprof, hnotED, ?_⟩
  dsimp
  refine ⟨hUopen, ?_, hnotopen⟩
  simpa [U, Set.union_comm] using hclosure

end IntroductoryFacts

section TechnicalLemmas

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous surjection satisfying the source's minimal closed-subset
condition sends every open set into the closure of the complement of the image
of its complement.  This is the source-facing form of Mathlib's
`image_subset_closure_compl_image_compl_of_isOpen`. -/
theorem image_open_subset_closure_compl_image_compl_of_minimal
    (f : X → Y) (hf : Continuous f) (hsurj : Surjective f)
    (hminimal : ∀ E : Set X, E ≠ (univ : Set X) → IsClosed E →
      f '' E ≠ (univ : Set Y))
    {U : Set X} (hU : IsOpen U) :
    f '' U ⊆ closure ((f '' Uᶜ)ᶜ) := by
  exact image_subset_closure_compl_image_compl_of_isOpen hf hsurj hminimal hU

/-- In an extremally disconnected space, disjoint open sets have disjoint
closures. -/
theorem disjoint_closure_of_disjoint_open
    [ExtremallyDisconnected X] {U V : Set X}
    (hUV : Disjoint U V) (hU : IsOpen U) (hV : IsOpen V) :
    Disjoint (closure U) (closure V) :=
  ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen hUV hU hV

/-- A continuous surjection from a compact Hausdorff space to a compact
Hausdorff extremally disconnected space satisfying the source's minimality
condition is a homeomorphism. -/
theorem isHomeomorph_of_continuous_surjective_of_minimal_closed
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [ExtremallyDisconnected Y] (f : X → Y) (hf : Continuous f)
    (hsurj : Surjective f)
    (hminimal : ∀ E : Set X, E ≠ (univ : Set X) → IsClosed E →
      f '' E ≠ (univ : Set Y)) :
    IsHomeomorph f := by
  exact (ExtremallyDisconnected.homeoCompactToT2 hf hsurj hminimal).isHomeomorph

/-- A continuous surjection between compact Hausdorff spaces has a compact
surjective subset minimal under closed-subset inclusion. -/
theorem exists_compact_surjective_minimal_subset
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Surjective f) :
    ∃ E : Set X, CompactSpace E ∧ f '' E = (univ : Set Y) ∧
      ∀ E' : Set E, E' ≠ (univ : Set E) → IsClosed E' →
        E.domRestrict f '' E' ≠ (univ : Set Y) := by
  exact exists_compact_surjective_zorn_subset hf hsurj

end TechnicalLemmas

section Projectivity

variable {X : Type u} [TopologicalSpace X]

/-- Every continuous surjection from a compact Hausdorff space onto `X` has a
continuous section. -/
def HasContinuousSections (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (f : Y → X), Continuous f → Surjective f →
      ∃ s : X → Y, Continuous s ∧ f ∘ s = id

/-- The three conditions in the source proposition are equivalent: extremal
disconnectedness, sections of compact-Hausdorff surjections, and the solid
lifting property for compact Hausdorff spaces. -/
theorem extremallyDisconnected_projectivity_characterization
    [CompactSpace X] [T2Space X] :
    List.TFAE
      [ExtremallyDisconnected X, HasContinuousSections X,
        CompactT2.Projective X] := by
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h
      exact @CompactT2.ExtremallyDisconnected.projective X _ h inferInstance inferInstance
    · exact CompactT2.Projective.extremallyDisconnected
  tfae_have 1 → 2 := by
    intro h Y _ _ _ f hf hsurj
    have hproj : CompactT2.Projective X :=
      @CompactT2.ExtremallyDisconnected.projective X _ h inferInstance inferInstance
    obtain ⟨s, hs, hsf⟩ :=
      hproj (f := (id : X → X)) (g := f) continuous_id hf hsurj
    exact ⟨s, hs, hsf⟩
  tfae_have 2 → 1 := by
    intro h
    constructor
    intro U hU
    let A : Type u := {x : X // x ∈ closure U}
    let B : Type u := {x : X // x ∈ Uᶜ}
    have hA : CompactSpace A := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
    have hB : CompactSpace B :=
      isCompact_iff_compactSpace.mp hU.isClosed_compl.isCompact
    have hAinl : IsCompact (Set.range (Sum.inl : A → A ⊕ B)) := by
      rw [← image_univ]
      exact hA.isCompact_univ.image continuous_inl
    have hBinr : IsCompact (Set.range (Sum.inr : B → A ⊕ B)) := by
      rw [← image_univ]
      exact hB.isCompact_univ.image continuous_inr
    have hAB : CompactSpace (A ⊕ B) := by
      constructor
      rw [← range_inl_union_range_inr]
      exact hAinl.union hBinr
    let g : A ⊕ B → X :=
      Sum.elim ((↑) : A → X) ((↑) : B → X)
    have hg : Continuous g := by
      simpa [g] using
        (continuous_subtype_val : Continuous ((↑) : A → X)).sumElim
          (continuous_subtype_val : Continuous ((↑) : B → X))
    have hgsurj : Surjective g := by
      intro x
      by_cases hx : x ∈ closure U
      · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inr ⟨x, fun hxU => hx (subset_closure hxU)⟩, rfl⟩
    obtain ⟨s, hs, hsg⟩ := @h (A ⊕ B) _ hAB inferInstance g hg hgsurj
    let L : Set (A ⊕ B) := Set.range (Sum.inl : A → A ⊕ B)
    have hpre : closure U = s ⁻¹' L := by
      apply Subset.antisymm
      · apply closure_minimal
        · intro x hx
          have hsgx : g (s x) = x := congr_fun hsg x
          rcases hsx : s x with a | b
          · exact ⟨a, hsx.symm⟩
          · have hbU : x ∈ Uᶜ := by
              rw [← hsgx, hsx]
              exact b.property
            exact (hbU hx).elim
        · exact isClosed_range_inl.preimage hs
      · intro x hx
        obtain ⟨a, ha⟩ := hx
        have hsgx : g (s x) = x := congr_fun hsg x
        rw [← hsgx, ← ha]
        exact a.property
    rw [hpre]
    exact isOpen_range_inl.preimage hs
  tfae_finish

end Projectivity

section Rainwater

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- A nonidentity continuous surjective selfmap of a Hausdorff space has a
proper closed subset whose union with its image is the whole space. -/
theorem exists_proper_closed_union_image_of_continuous_surjective_not_id
    (f : X → X) (hf : Continuous f) (hsurj : Surjective f)
    (hnotid : f ≠ id) :
    ∃ E : Set X, E ≠ (univ : Set X) ∧ IsClosed E ∧
      (univ : Set X) = E ∪ f '' E := by
  have hex : ∃ p : X, f p ≠ p := by
    by_contra h
    apply hnotid
    funext x
    by_contra hx
    exact h ⟨x, by simpa using hx⟩
  obtain ⟨p, hp⟩ := hex
  obtain ⟨U, V, hU, hV, hpU, hfpV, hUV⟩ := t2_separation hp.symm
  let E : Set X := (U ∩ f ⁻¹' V)ᶜ
  refine ⟨E, ?_, (hU.inter (hV.preimage hf)).isClosed_compl, ?_⟩
  · intro hE
    have hpE : p ∈ E := hE ▸ mem_univ p
    have hpnotE : p ∉ E := by
      simpa [E] using (show p ∈ U ∩ f ⁻¹' V from ⟨hpU, hfpV⟩)
    exact hpnotE hpE
  · apply Subset.antisymm
    · intro x _
      by_cases hxE : x ∈ E
      · exact Or.inl hxE
      · right
        obtain ⟨y, hy⟩ := hsurj x
        refine ⟨y, ?_, hy⟩
        by_contra hyE
        have hxUV : x ∈ U ∩ f ⁻¹' V := by simpa [E] using hxE
        have hyUV : y ∈ U ∩ f ⁻¹' V := by simpa [E] using hyE
        have hxV : x ∈ V := by simpa [hy] using hyUV.2
        exact (Set.disjoint_left.1 hUV) hxUV.1 hxV
    · intro x hx
      exact mem_univ x

end Rainwater

section StoneCech

variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

/-- The Stone--Čech compactification of a discrete space is extremally
disconnected. -/
theorem stoneCech_extremallyDisconnected :
    ExtremallyDisconnected (StoneCech X) := by
  exact CompactT2.Projective.extremallyDisconnected StoneCech.projective

/-- The Stone--Čech compactification of a discrete space has the section
property used in the source example. -/
theorem stoneCech_hasContinuousSections :
    HasContinuousSections (StoneCech X) := by
  intro Y _ _ _ f hf hsurj
  have hproj : CompactT2.Projective (StoneCech X) := StoneCech.projective
  obtain ⟨s, hs, hsf⟩ :=
    hproj (f := (id : StoneCech X → StoneCech X)) (g := f) continuous_id hf hsurj
  exact ⟨s, hs, hsf⟩

/-- The Stone--Čech compactification of a discrete space is profinite. -/
theorem stoneCech_isProfiniteSpace :
    IsProfiniteSpace (StoneCech X) := by
  have hED : ExtremallyDisconnected (StoneCech X) :=
    stoneCech_extremallyDisconnected
  have hTD : TotallyDisconnectedSpace (StoneCech X) := by
    exact @totallyDisconnectedSpace_of_t2Space_of_extremallyDisconnected
      (StoneCech X) inferInstance inferInstance hED
  exact (isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected
    (X := StoneCech X)).2 ⟨inferInstance, inferInstance, hTD⟩

end StoneCech

section ProjectiveCovers

/-- A minimal Stonean cover packages a compact Hausdorff extremally
disconnected space, a continuous surjection to `X`, and the source's
minimality condition on closed subsets. -/
structure MinimalStoneanCover (X : CompHaus.{u}) where
  space : Stonean.{u}
  projection : space.toTop → X.toTop
  continuous_projection : Continuous projection
  surjective_projection : Surjective projection
  minimal :
    ∀ E : Set space.toTop, E ≠ (univ : Set space.toTop) →
      IsClosed E → projection '' E ≠ (univ : Set X.toTop)

/-- Every compact Hausdorff space has a minimal Stonean cover. -/
theorem exists_minimalStoneanCover (X : CompHaus.{u}) :
    Nonempty (MinimalStoneanCover X) := by
  let P : Stonean := CompHaus.presentation X
  let D : Type u := (Stonean.toCompHaus.obj P).toTop
  let f : D → X.toTop := (CompHaus.presentation.π X).hom.hom
  have hf : Continuous f := by
    change Continuous (CompHaus.presentation.π X).hom.hom
    exact (CompHaus.presentation.π X).hom.hom.continuous
  have hsurj : Surjective f := by
    change Surjective (CompHaus.presentation.π X).hom.hom
    exact (CompHaus.epi_iff_surjective (CompHaus.presentation.π X)).mp inferInstance
  obtain ⟨E, hEcompact, hEonto, hEmin⟩ :=
    exists_compact_surjective_zorn_subset hf hsurj
  let p : E → X.toTop := E.domRestrict f
  have hp : Continuous p := hf.continuousOn.domRestrict
  have hpsurj : Surjective p := by
    intro x
    have hx : x ∈ f '' E := by rw [hEonto]; exact mem_univ x
    obtain ⟨y, hy, hfy⟩ := hx
    exact ⟨⟨y, hy⟩, hfy⟩
  have hEDP : ExtremallyDisconnected D := inferInstance
  have hPproj : CompactT2.Projective D :=
    @CompactT2.ExtremallyDisconnected.projective D _ hEDP
      inferInstance inferInstance
  obtain ⟨r, hr, hrcomm⟩ :=
    hPproj (f := f) (g := p) hf hp hpsurj
  let q : E → E := r ∘ (Subtype.val : E → D)
  have hq : Continuous q := hr.comp continuous_subtype_val
  have hpq : p ∘ q = p := by
    funext e
    have he := congr_fun hrcomm (e : D)
    simpa [p, q, Function.comp_def] using he
  have hqsurj : Surjective q := by
    by_contra hqnot
    have hqne : q '' (univ : Set E) ≠ (univ : Set E) := by
      intro hqeq
      apply hqnot
      intro e
      obtain ⟨e', _, he'⟩ := hqeq ▸ mem_univ e
      exact ⟨e', he'⟩
    have hqclosed : IsClosed (q '' (univ : Set E)) :=
      (hEcompact.isCompact_univ.image hq).isClosed
    have hpimage : p '' (q '' (univ : Set E)) = (univ : Set X.toTop) := by
      apply Subset.antisymm
      · exact subset_univ _
      · intro x _
        obtain ⟨e, he⟩ := hpsurj x
        refine ⟨q e, ⟨e, mem_univ _, rfl⟩, ?_⟩
        exact (congr_fun hpq e).trans he
    exact (hEmin (q '' (univ : Set E)) hqne hqclosed) hpimage
  have hqid : q = id := by
    by_contra hq_id
    obtain ⟨F, hFne, hFclosed, hFcover⟩ :=
      exists_proper_closed_union_image_of_continuous_surjective_not_id
        q hq hqsurj hq_id
    have hpqF : p '' (q '' F) ⊆ p '' F := by
      rintro z ⟨y, ⟨e, heF, rfl⟩, rfl⟩
      exact ⟨e, heF, (congr_fun hpq e).symm⟩
    have hpF : p '' F = (univ : Set X.toTop) := by
      have himage : p '' (F ∪ q '' F) = p '' F := by
        rw [image_union, union_eq_left.mpr hpqF]
      calc
        p '' F = p '' (F ∪ q '' F) := himage.symm
        _ = p '' (univ : Set E) := by rw [← hFcover]
        _ = (univ : Set X.toTop) := image_univ_of_surjective hpsurj
    exact (hEmin F hFne hFclosed) hpF
  have hEproj : CompactT2.Projective E := by
    intro Y Z _ _ _ _ _ _ a b ha hb hbsurj
    obtain ⟨l, hl, hlcomm⟩ :=
      hPproj (f := a ∘ r) (g := b) (ha.comp hr) hb hbsurj
    refine ⟨l ∘ (Subtype.val : E → D),
      hl.comp continuous_subtype_val, ?_⟩
    funext e
    have heq : r (e : D) = e := by
      have he := congr_fun hqid e
      simpa [q, Function.comp_def] using he
    have he := congr_fun hlcomm (e : D)
    simpa [Function.comp_def, heq] using he
  let S : Stonean :=
    { toTop := TopCat.of E,
      prop := @CompactT2.Projective.extremallyDisconnected E _ hEcompact inferInstance hEproj }
  refine ⟨⟨S, p, hp, hpsurj, ?_⟩⟩
  simpa [S, p] using hEmin

/-- Minimal Stonean covers are unique up to a homeomorphism over the base. -/
theorem minimalStoneanCover_unique (X : CompHaus.{u})
    (C₁ C₂ : MinimalStoneanCover X) :
    ∃ e : C₁.space.toTop ≃ₜ C₂.space.toTop,
      C₂.projection ∘ e = C₁.projection := by
  have hproj : CompactT2.Projective C₁.space.toTop :=
    @CompactT2.ExtremallyDisconnected.projective C₁.space.toTop _ C₁.space.prop
      inferInstance inferInstance
  obtain ⟨g, hg, hgcomm⟩ :=
    hproj (f := C₁.projection) (g := C₂.projection)
      C₁.continuous_projection C₂.continuous_projection C₂.surjective_projection
  have hgsurj : Surjective g := by
    by_contra hgnot
    have hgne : g '' (univ : Set C₁.space.toTop) ≠
        (univ : Set C₂.space.toTop) := by
      intro hgeq
      apply hgnot
      intro y
      obtain ⟨x, hx⟩ := hgeq ▸ mem_univ y
      exact ⟨x, hx.2⟩
    have hgclosed : IsClosed (g '' (univ : Set C₁.space.toTop)) :=
      (isCompact_univ.image hg).isClosed
    have hgimage : C₂.projection '' (g '' (univ : Set C₁.space.toTop)) =
        (univ : Set X.toTop) := by
      apply Subset.antisymm
      · exact subset_univ _
      · intro y _
        obtain ⟨x, hx⟩ := C₁.surjective_projection y
        refine ⟨g x, ⟨x, mem_univ _, rfl⟩, ?_⟩
        exact (congr_fun hgcomm x).trans hx
    exact C₂.minimal (g '' (univ : Set C₁.space.toTop)) hgne hgclosed hgimage
  have hgmin : ∀ E : Set C₁.space.toTop, E ≠ (univ : Set C₁.space.toTop) →
      IsClosed E → g '' E ≠ (univ : Set C₂.space.toTop) := by
    intro E hEne hEclosed hEimage
    apply C₁.minimal E hEne hEclosed
    apply Subset.antisymm
    · exact subset_univ _
    · intro y _
      obtain ⟨z, hz⟩ := C₂.surjective_projection y
      have hzimage : z ∈ g '' E := by rw [hEimage]; exact mem_univ z
      obtain ⟨x, hxE, hgx⟩ := hzimage
      refine ⟨x, hxE, ?_⟩
      have he := congr_fun hgcomm x
      have he' : C₂.projection z = C₁.projection x := by
        simpa [Function.comp_def, hgx] using he
      exact he'.symm.trans hz
  refine ⟨ExtremallyDisconnected.homeoCompactToT2 hg hgsurj hgmin,
    hgcomm⟩

/-- The source's canonical non-minimal projective cover is Mathlib's
`CompHaus.presentation`; its underlying map is continuous and surjective.
Minimalization and uniqueness are recorded by the cover declarations above.
-/
theorem canonicalStoneanCover_is_continuous_surjective (X : CompHaus.{u}) :
    Continuous (CompHaus.presentation.π X).hom.hom ∧
      Surjective (CompHaus.presentation.π X).hom.hom := by
  refine ⟨(CompHaus.presentation.π X).hom.hom.continuous, ?_⟩
  exact (CompHaus.epi_iff_surjective (CompHaus.presentation.π X)).mp inferInstance

/-- If `κ` is infinite and bounds the cardinality of the base, the cardinality
of a minimal Stonean cover is at most `2 ^ (2 ^ κ)`. -/
theorem minimalStoneanCover_cardinal_bound (X : CompHaus.{u})
    (C : MinimalStoneanCover X) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hX : Cardinal.mk X.toTop ≤ κ) :
    Cardinal.mk C.space.toTop ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) := by
  let f := C.projection
  obtain ⟨g, hgf⟩ := C.surjective_projection.hasRightInverse
  let S : Set C.space.toTop := Set.range g
  have hSimage : f '' S = (univ : Set X.toTop) := by
    apply Subset.antisymm
    · exact subset_univ _
    · intro x _
      refine ⟨g x, mem_range_self _, ?_⟩
      exact hgf x
  have hSdense : Dense S := by
    apply dense_iff_closure_eq.mpr
    by_contra hcl
    have hclimage : f '' closure S = (univ : Set X.toTop) := by
      apply Subset.antisymm
      · exact subset_univ _
      · intro x _
        obtain ⟨y, hyS, hfy⟩ := (hSimage ▸ mem_univ x)
        exact ⟨y, subset_closure hyS, hfy⟩
    exact (C.minimal (closure S) hcl isClosed_closure) hclimage
  let j : X.toTop → S := fun x => ⟨g x, mem_range_self x⟩
  have hj : Surjective j := by
    rintro ⟨y, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  have hSle : Cardinal.mk S ≤ Cardinal.mk X.toTop :=
    Cardinal.mk_le_of_surjective hj
  have hSleκ : Cardinal.mk S ≤ κ := hSle.trans hX
  let I : C.space.toTop → Set (Set S) := fun y =>
    {t | ∃ U : Set C.space.toTop, IsOpen U ∧ y ∈ U ∧
      t = (Subtype.val : S → C.space.toTop) ⁻¹' U}
  have hIinj : Injective I := by
    intro y z hyz
    by_contra hyz'
    obtain ⟨U, V, hU, hV, hyU, hzV, hUV⟩ := t2_separation hyz'
    have hUy : (Subtype.val : S → C.space.toTop) ⁻¹' U ∈ I y :=
      ⟨U, hU, hyU, rfl⟩
    obtain ⟨W, hW, hzW, hUW⟩ := hyz ▸ hUy
    obtain ⟨w, hwVW, hwS⟩ := hSdense.inter_open_nonempty (V ∩ W)
      (hV.inter hW) ⟨z, hzV, hzW⟩
    have hwU : w ∈ U := by
      have hwtrace : (⟨w, hwS⟩ : S) ∈
          (Subtype.val : S → C.space.toTop) ⁻¹' U := by
        rw [hUW]
        exact hwVW.2
      exact hwtrace
    exact (Set.disjoint_left.1 hUV) hwU hwVW.1
  have hcard : Cardinal.mk C.space.toTop ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Cardinal.mk S) := by
    calc
      Cardinal.mk C.space.toTop ≤ Cardinal.mk (Set (Set S)) :=
        Cardinal.mk_le_of_injective hIinj
      _ = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Cardinal.mk S) := by
        rw [Cardinal.mk_set, Cardinal.mk_set]
  have hpow : (2 : Cardinal.{u}) ^ Cardinal.mk S ≤ (2 : Cardinal.{u}) ^ κ :=
    Cardinal.power_le_power_left two_ne_zero hSleκ
  have hbound := hcard.trans <|
    (Cardinal.power_le_power_left two_ne_zero hpow)
  by_cases h : Cardinal.aleph0 ≤ κ
  · exact hbound
  · exact (h hκ).elim

end ProjectiveCovers

end

end Formalization.Books.Topology.Unit25
