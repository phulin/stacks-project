import Formalization.Books.Topology.Unit08.IrreducibleComponents
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Data.PNat.Basic
import Mathlib.Data.PNat.Interval
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
open scoped AlgebraicGeometry

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

private theorem finite_prime_chain_impossible
    {R : Type*} [CommRing R] [IsNoetherianRing R] [Finite (PrimeSpectrum R)]
    {p q r : Ideal R} (hp : p.IsPrime) (hq : q.IsPrime) (hr : r.IsPrime)
    (hpq : p < q) (hqr : q < r)
    (hbelow : ∀ s : Ideal R, s.IsPrime → s ≠ r → s ≤ r) : False := by
  let _ : p.IsPrime := hp
  let _ : q.IsPrime := hq
  let _ : r.IsPrime := hr
  have hprimes : {P : Ideal R | P.IsPrime}.Finite := by
    let _ : Finite {P : Ideal R // P.IsPrime} :=
      Finite.of_injective (PrimeSpectrum.equivSubtype R).symm
        (PrimeSpectrum.equivSubtype R).symm.injective
    exact Set.finite_coe_iff.mp (inferInstance : Finite {P : Ideal R // P.IsPrime})
  let s : Set (Ideal R) := {P | P.IsPrime} \ {r}
  have hs : s.Finite := by
    dsimp [s]
    exact hprimes.sdiff
  have hnot : ¬ ((r : Set R) ⊆ ⋃ P ∈ s, (P : Set R)) := by
    intro h
    obtain ⟨P, hPs, hle⟩ :=
      (Ideal.subset_union_prime_finite (f := fun P : Ideal R => P) hs
        (⊤ : Ideal R) (⊤ : Ideal R) (fun _ hP _ _ => hP.1)).mp h
    have hPne : P ≠ r := by simpa [s] using hPs.2
    exact hPne (le_antisymm (hbelow P hPs.1 hPne) hle)
  have hex : ∃ a : R, a ∈ r ∧ ∀ P ∈ s, a ∉ P := by
    by_contra h
    apply hnot
    intro a ha
    by_contra ha'
    apply h
    refine ⟨a, ha, ?_⟩
    intro P hP haP
    exact ha' (Set.mem_iUnion.2 ⟨P, Set.mem_iUnion.2 ⟨hP, haP⟩⟩)
  obtain ⟨a, ha, haout⟩ := hex
  have hspanle : Ideal.span ({a} : Set R) ≤ r := by
    apply Ideal.span_le.mpr
    rintro x rfl
    exact ha
  have hspan_ne_top : Ideal.span ({a} : Set R) ≠ ⊤ := by
    intro htop
    exact hr.ne_top (top_unique (htop ▸ hspanle))
  obtain ⟨P, hP⟩ := (Ideal.span ({a} : Set R)).nonempty_minimalPrimes hspan_ne_top
  have hPr : P = r := by
    by_contra hPr
    have hPs : P ∈ s := ⟨hP.isPrime, by simpa using hPr⟩
    exact haout P hPs (hP.le (Ideal.subset_span (by simp)))
  have hheight : r.height ≤ 1 := by
    rw [← hPr]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span ({a} : Set R)) P hP
  have hqheight : (1 : ℕ∞) ≤ q.height := by
    calc
      (1 : ℕ∞) = 0 + 1 := by simp
      _ ≤ p.height + 1 := add_le_add_left (show (0 : ℕ∞) ≤ p.height from bot_le) 1
      _ ≤ q.height := Ideal.height_add_one_le_of_lt_of_isPrime hpq
  have hrheight : (2 : ℕ∞) ≤ r.height := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ q.height + 1 := add_le_add_left hqheight 1
      _ ≤ r.height := Ideal.height_add_one_le_of_lt_of_isPrime hqr
  exact (not_le_of_gt (by norm_num : (1 : ℕ∞) < 2)) (hrheight.trans hheight)

/- The last sentence of the source refers to the later scheme-theoretic
   closed-point lemma.  Mathlib's canonical interface for that source notion
   is used here to state the cross-reference without importing a later project
   chapter. -/
theorem initialSegmentSpace_not_underlying_locallyNoetherian_scheme :
    ¬ ∃ S : AlgebraicGeometry.Scheme,
      AlgebraicGeometry.IsLocallyNoetherian S ∧
        Nonempty (S ≃ₜ InitialSegmentSpace) := by
  classical
  rintro ⟨S, hS, ⟨e⟩⟩
  let _ : AlgebraicGeometry.IsLocallyNoetherian S := hS
  let e₀ : InitialSegmentSpace ≃ ℕ+ :=
    WithTopology.equiv ℕ+ initialSegmentTopology
  let one : ℕ+ := ⟨1, by decide⟩
  let two : ℕ+ := ⟨2, by decide⟩
  let three : ℕ+ := ⟨3, by decide⟩
  have hspec_of_le : ∀ {a b : ℕ+}, a ≤ b → e₀.symm a ⤳ e₀.symm b := by
    intro a b hab
    apply specializes_iff_forall_open.mpr
    intro U hU hUb
    rcases initialSegmentSpace_isOpen_iff.mp hU with h0 | hu | ⟨m, hm⟩
    · rw [h0] at hUb
      exact hUb.elim
    · rw [hu]
      exact Set.mem_univ _
    · rw [hm] at hUb ⊢
      exact le_trans hab hUb
  have hInitialNotNoetherian : ¬ NoetherianSpace InitialSegmentSpace := by
    intro hN
    let _ : NoetherianSpace InitialSegmentSpace := hN
    let U : ℕ+ → Set InitialSegmentSpace := fun n => e₀ ⁻¹' Set.Iic n
    have hUopen : ∀ n : ℕ+, IsOpen (U n) := by
      intro n
      exact initialSegmentSpace_isOpen_iff.mpr (Or.inr (Or.inr ⟨n, rfl⟩))
    have hUcover : (Set.univ : Set InitialSegmentSpace) ⊆ ⋃ n, U n := by
      intro z _
      refine Set.mem_iUnion.mpr ⟨e₀ z, ?_⟩
      simp [U]
    obtain ⟨t, ht⟩ :=
      (NoetherianSpace.isCompact (Set.univ : Set InitialSegmentSpace)).elim_finite_subcover
        U hUopen hUcover
    let m : ℕ+ := t.sup id + 1
    have hlt : ∀ n ∈ t, n < m := by
      intro n hn
      have hnle : n ≤ t.sup id := by
        simpa using (Finset.le_sup (s := t) (f := id) hn)
      exact lt_of_le_of_lt hnle
        (by simpa [m, PNat.add_one] using PNat.lt_succ_self (t.sup id))
    have hmcover : e₀.symm m ∈ ⋃ n ∈ t, U n := ht (Set.mem_univ _)
    rcases Set.mem_iUnion₂.mp hmcover with ⟨n, hn, hmn⟩
    have hmn' : m ≤ n := by
      simpa [U] using hmn
    exact (not_le_of_gt (hlt n hn)) hmn'
  let x : S := e.symm (e₀.symm three)
  obtain ⟨i, y, hy⟩ := S.affineCover.exists_eq x
  let Y := S.affineCover.X i
  let f := S.affineCover.f i
  let _ : AlgebraicGeometry.IsOpenImmersion f := S.affineCover.map_prop i
  let _ : AlgebraicGeometry.IsLocallyNoetherian Y :=
    AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion f
  let _ : IsNoetherianRing Γ(Y, ⊤) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top Y⟩
  let _ : NoetherianSpace Y := AlgebraicGeometry.noetherianSpace_of_isAffine
  have hy' : f.base y = x := by
    simpa [f] using hy
  let V : Set InitialSegmentSpace := e '' Set.range f.base
  have hVopen : IsOpen V := by
    dsimp [V]
    exact e.isOpenMap _ f.isOpenEmbedding.isOpen_range
  have hVmem : e₀.symm three ∈ V := by
    refine ⟨x, ⟨y, hy'⟩, ?_⟩
    simp [x]
  rcases initialSegmentSpace_isOpen_iff.mp hVopen with hVempty | hVuniv | ⟨n, hVn⟩
  · rw [hVempty] at hVmem
    exact hVmem.elim
  · have hRangeUniv : Set.range f.base = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro z
      have hz : e z ∈ V := by rw [hVuniv]; exact Set.mem_univ _
      rcases hz with ⟨w, ⟨y', hy'⟩, hwy⟩
      rw [← hy'] at hwy
      exact ⟨y', e.injective hwy⟩
    have hRangeNoeth : NoetherianSpace (Set.range f.base) :=
      NoetherianSpace.range f.base f.continuous
    have hUnivNoeth : NoetherianSpace (Set.univ : Set S) := by
      rw [← hRangeUniv]
      exact hRangeNoeth
    have hSNoeth : NoetherianSpace S :=
      TopologicalSpace.noetherian_univ_iff.mp hUnivNoeth
    apply hInitialNotNoetherian
    exact (TopologicalSpace.noetherianSpace_iff_of_homeomorph e).mp hSNoeth
  · have h3n : three ≤ n := by
      rw [hVn] at hVmem
      simpa [e₀] using hVmem
    have hmem : ∀ m : ℕ+, m ≤ n → ∃ y : Y, e (f.base y) = e₀.symm m := by
      intro m hm
      have hmV : e₀.symm m ∈ V := by
        rw [hVn]
        simpa [e₀] using hm
      rcases hmV with ⟨w, ⟨y', rfl⟩, hwy⟩
      exact ⟨y', hwy⟩
    have h12 : one ≤ two := by norm_num [one, two]
    have h23 : two ≤ three := by norm_num [two, three]
    have h23lt : two < three := by norm_num [two, three]
    have h2n : two ≤ n := le_trans h23 h3n
    have h1n : one ≤ n := le_trans h12 h2n
    obtain ⟨y1, hy1⟩ := hmem one h1n
    obtain ⟨y2, hy2⟩ := hmem two h2n
    obtain ⟨yn, hyn⟩ := hmem n le_rfl
    let zp : PrimeSpectrum Γ(Y, ⊤) := Y.isoSpec.hom.base y1
    let zq : PrimeSpectrum Γ(Y, ⊤) := Y.isoSpec.hom.base y2
    let zr : PrimeSpectrum Γ(Y, ⊤) := Y.isoSpec.hom.base yn
    let p : Ideal Γ(Y, ⊤) := zp.asIdeal
    let q : Ideal Γ(Y, ⊤) := zq.asIdeal
    let r : Ideal Γ(Y, ⊤) := zr.asIdeal
    have hp : p.IsPrime := by
      simpa [p] using zp.isPrime
    have hq : q.IsPrime := by
      simpa [q] using zq.isPrime
    have hr : r.IsPrime := by
      simpa [r] using zr.isPrime
    have hspec12 : y1 ⤳ y2 := by
      apply f.isOpenEmbedding.isInducing.specializes_iff.mp
      apply e.isInducing.specializes_iff.mp
      rw [hy1, hy2]
      exact hspec_of_le h12
    have hspec2n : y2 ⤳ yn := by
      apply f.isOpenEmbedding.isInducing.specializes_iff.mp
      apply e.isInducing.specializes_iff.mp
      rw [hy2, hyn]
      exact hspec_of_le h2n
    have hpqle : p ≤ q := by
      change zp.asIdeal ≤ zq.asIdeal
      have hzpq : zp ⤳ zq := by
        apply (Y.isoSpec.inv.homeomorph.isInducing.specializes_iff).mp
        simpa [zp, zq] using hspec12
      exact (PrimeSpectrum.asIdeal_le_asIdeal zp zq).mpr
        ((PrimeSpectrum.le_iff_specializes zp zq).mpr hzpq)
    have hqrle : q ≤ r := by
      change zq.asIdeal ≤ zr.asIdeal
      have hzqr : zq ⤳ zr := by
        apply (Y.isoSpec.inv.homeomorph.isInducing.specializes_iff).mp
        simpa [zq, zr] using hspec2n
      exact (PrimeSpectrum.asIdeal_le_asIdeal zq zr).mpr
        ((PrimeSpectrum.le_iff_specializes zq zr).mpr hzqr)
    have hpqne : p ≠ q := by
      intro hpq
      have hzpq : zp = zq := by
        apply PrimeSpectrum.ext
        exact hpq
      have hy12 : y1 = y2 := by
        simpa [zp, zq] using congrArg Y.isoSpec.inv.base hzpq
      have hone_two : one = two := by
        apply e₀.symm.injective
        rw [← hy1, ← hy2]
        exact congrArg (fun y : Y => e (f.base y)) hy12
      exact (by norm_num [one, two] : one ≠ two) hone_two
    have h2nlt : two < n := lt_of_lt_of_le h23lt h3n
    have hqrne : q ≠ r := by
      intro hqr
      have hzqr : zq = zr := by
        apply PrimeSpectrum.ext
        exact hqr
      have hy2n : y2 = yn := by
        simpa [zq, zr] using congrArg Y.isoSpec.inv.base hzqr
      have htwo_n : two = n := by
        apply e₀.symm.injective
        rw [← hy2, ← hyn]
        exact congrArg (fun y : Y => e (f.base y)) hy2n
      exact h2nlt.ne htwo_n
    have hpq : p < q := lt_of_le_of_ne hpqle hpqne
    have hqr : q < r := lt_of_le_of_ne hqrle hqrne
    have hbelow : ∀ s : Ideal Γ(Y, ⊤), s.IsPrime → s ≠ r → s ≤ r := by
      intro s hs hsr
      let z : PrimeSpectrum Γ(Y, ⊤) := ⟨s, hs⟩
      let y' : Y := Y.isoSpec.inv.base z
      let m : ℕ+ := e₀ (e (f.base y'))
      have hm_eq : e (f.base y') = e₀.symm m := by
        dsimp [m]
        exact (e₀.symm_apply_apply _).symm
      have hm : m ≤ n := by
        have hmV : e₀.symm m ∈ V := by
          exact ⟨f.base y', ⟨y', rfl⟩, hm_eq⟩
        rw [hVn] at hmV
        simpa [m, e₀] using hmV
      have hspec' : e (f.base y') ⤳ e (f.base yn) := by
        have h0 := hspec_of_le hm
        rw [← hm_eq, ← hyn] at h0
        exact h0
      have hy' : y' ⤳ yn := by
        apply f.isOpenEmbedding.isInducing.specializes_iff.mp
        apply e.isInducing.specializes_iff.mp
        exact hspec'
      have hz : z ⤳ zr := by
        apply (Y.isoSpec.inv.homeomorph.isInducing.specializes_iff).mp
        change (Y.isoSpec.inv.base z) ⤳ (Y.isoSpec.inv.base zr)
        simpa [y', zr] using hy'
      change z.asIdeal ≤ zr.asIdeal
      exact (PrimeSpectrum.asIdeal_le_asIdeal z zr).mpr
        ((PrimeSpectrum.le_iff_specializes z zr).mpr hz)
    have hVfin : V.Finite := by
      rw [hVn]
      exact (Set.finite_Iic n).preimage e₀.injective.injOn
    have hRangeFin : (Set.range f.base).Finite := by
      apply Set.Finite.of_finite_image (f := e) ?_ e.injective.injOn
      simpa [V] using hVfin
    let _ : Finite Y := (Set.finite_range_iff f.isOpenEmbedding.injective).mp hRangeFin
    let _ : Finite (PrimeSpectrum Γ(Y, ⊤)) :=
      Finite.of_injective Y.isoSpec.inv.homeomorph Y.isoSpec.inv.homeomorph.injective
    exact finite_prime_chain_impossible hp hq hr hpq hqr hbelow

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
