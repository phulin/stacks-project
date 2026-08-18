import Formalization.Books.Topology.Unit08.IrreducibleComponents
import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 26: Irreducible components of spectra

The canonical Mathlib notions `PrimeSpectrum.zeroLocus`, `IsIrreducible`,
`irreducibleComponents`, and `IsProfiniteSpace` are used for the statements in
this chapter.  The unfinished ninth item in the final source list is not
translated into a mathematical proposition below.
-/

namespace Formalization.Books.Algebra.Unit26

open Set _root_.Topology

universe u

/-! ## Irreducible components of spectra -/

section Irreducible

variable {R : Type u} [CommRing R]

/-! ### Closure of a prime and irreducible closed subsets -/

/-- The closure of a point of the prime spectrum is its vanishing locus. -/
theorem closure_singleton_prime (p : PrimeSpectrum R) :
    closure ({p} : Set (PrimeSpectrum R)) =
      PrimeSpectrum.zeroLocus (p.asIdeal : Set R) :=
  PrimeSpectrum.closure_singleton p

/-- The irreducible closed subsets of a prime spectrum are the vanishing
loci of prime ideals. -/
theorem isClosed_and_isIrreducible_iff_zeroLocus_prime
    (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ∧ IsIrreducible Z ↔
      ∃ p : PrimeSpectrum R,
        Z = PrimeSpectrum.zeroLocus (p.asIdeal : Set R) := by
  constructor
  · rintro ⟨hZclosed, hZirreducible⟩
    let P : Ideal R := PrimeSpectrum.vanishingIdeal Z
    have hPprime : P.IsPrime :=
      (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime).mp hZirreducible
    refine ⟨⟨P, hPprime⟩, ?_⟩
    exact hZclosed.closure_eq.symm.trans
      (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z).symm
  · rintro ⟨p, rfl⟩
    refine ⟨PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
    rw [← PrimeSpectrum.closure_singleton p]
    exact isIrreducible_singleton.closure

/-- The irreducible components of a prime spectrum are exactly the vanishing
loci of its minimal prime ideals. -/
theorem zeroLocus_minimalPrimes_eq_irreducibleComponents :
    PrimeSpectrum.zeroLocus ∘ (↑) '' minimalPrimes R =
      irreducibleComponents (PrimeSpectrum R) := by
  exact PrimeSpectrum.zeroLocus_minimalPrimes R

/-! The source's accompanying generic-point assertion. -/

/-- Every irreducible closed subset of a prime spectrum has a unique generic
point. -/
theorem irreducibleClosed_existsUnique_genericPoint :
    ∀ Z : Set (PrimeSpectrum R), IsIrreducible Z → IsClosed Z →
      ∃! p : PrimeSpectrum R, IsGenericPoint p Z := by
  exact
    (Formalization.Books.Topology.Unit08.quasiSober_and_t0_iff_unique_genericPoint
      (X := PrimeSpectrum R)).mp ⟨inferInstance, inferInstance⟩

/- The source's sober-space assertion is represented by Mathlib's canonical
`QuasiSober` and `T0Space` pair. -/
theorem primeSpectrum_is_sober :
    QuasiSober (PrimeSpectrum R) ∧ T0Space (PrimeSpectrum R) := by
  exact ⟨inferInstance, inferInstance⟩

/-! ### Spectrality -/

/-- The spectrum of a commutative ring is a spectral space. -/
theorem primeSpectrum_is_spectral : SpectralSpace (PrimeSpectrum R) := by
  infer_instance

/-! ### Components through a point -/

/-- Irreducible closed subsets through a prime correspond to primes of the
localization at that prime. -/
theorem irreducibleClosedSets_through_prime_correspond_localization
    (p : PrimeSpectrum R) :
    Nonempty
      ({Z : Set (PrimeSpectrum R) // IsClosed Z ∧ IsIrreducible Z ∧ p ∈ Z} ≃
        PrimeSpectrum (Localization.AtPrime p.asIdeal)) := by
  let e : Set.Iic p ≃
      {Z : Set (PrimeSpectrum R) // IsClosed Z ∧ IsIrreducible Z ∧ p ∈ Z} :=
    { toFun := fun q =>
        ⟨PrimeSpectrum.zeroLocus (q.1.asIdeal : Set R),
          PrimeSpectrum.isClosed_zeroLocus _,
          by
            rw [← PrimeSpectrum.closure_singleton q.1]
            exact isIrreducible_singleton.closure,
          (PrimeSpectrum.mem_zeroLocus p _).2 q.2⟩
      invFun := fun Z =>
        ⟨⟨PrimeSpectrum.vanishingIdeal Z.1,
            (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp Z.2.2.1)⟩,
          (PrimeSpectrum.mem_zeroLocus p _).1 <|
            (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z.1).symm ▸ by
              rw [Z.2.1.closure_eq]
              exact Z.2.2.2⟩
      left_inv := fun q => by
        apply Subtype.ext
        apply PrimeSpectrum.ext
        dsimp
        rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
        exact q.1.2.radical
      right_inv := fun Z => by
        apply Subtype.ext
        exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z.1).trans
          Z.2.1.closure_eq }
  exact ⟨e.symm.trans (IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.asIdeal) p.asIdeal).symm⟩

/-- Irreducible components through a prime correspond to minimal primes of the
localization at that prime. -/
theorem irreducibleComponents_through_prime_correspond_minimalPrimes_localization
    (p : PrimeSpectrum R) :
    Nonempty
      ({C : Set (PrimeSpectrum R) //
          C ∈ irreducibleComponents (PrimeSpectrum R) ∧ p ∈ C} ≃
        {q : PrimeSpectrum (Localization.AtPrime p.asIdeal) //
          q.asIdeal ∈ minimalPrimes (Localization.AtPrime p.asIdeal)}) := by
  let e :
      {C : Set (PrimeSpectrum R) //
          C ∈ irreducibleComponents (PrimeSpectrum R) ∧ p ∈ C} ≃
        {q : Set.Iic p // q.1.asIdeal ∈ minimalPrimes R} :=
    { toFun := fun C =>
        ⟨⟨⟨PrimeSpectrum.vanishingIdeal C.1,
              PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp C.2.1.1⟩,
            (PrimeSpectrum.mem_zeroLocus p _).1 <|
              (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure C.1).symm ▸ by
                rw [(Formalization.Books.Topology.Unit08.irreducibleComponent_isClosed C.2.1).closure_eq]
                exact C.2.2⟩,
          (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes).2 <|
            by
              simpa only [
                (Formalization.Books.Topology.Unit08.irreducibleComponent_isClosed
                  C.2.1).closure_eq] using C.2.1⟩
      invFun := fun q =>
        ⟨PrimeSpectrum.zeroLocus (q.1.1.asIdeal : Set R),
          (PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents).2 <| by
            rw [q.1.1.2.radical]
            exact q.2,
          (PrimeSpectrum.mem_zeroLocus p _).2 q.1.2⟩
      left_inv := fun C => by
        apply Subtype.ext
        exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure C.1).trans
          (Formalization.Books.Topology.Unit08.irreducibleComponent_isClosed C.2.1).closure_eq
      right_inv := fun q => by
        apply Subtype.ext
        apply Subtype.ext
        apply PrimeSpectrum.ext
        dsimp
        rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
        exact q.1.1.2.radical }
  let o := IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.asIdeal) p.asIdeal
  let m :
      {q : Set.Iic p // q.1.asIdeal ∈ minimalPrimes R} ≃
        {q : PrimeSpectrum (Localization.AtPrime p.asIdeal) //
          q.asIdeal ∈ minimalPrimes (Localization.AtPrime p.asIdeal)} :=
    { toFun := fun q =>
        ⟨o.symm q.1, by
          have h := IsLocalization.minimalPrimes_map p.asIdeal.primeCompl
            (Localization.AtPrime p.asIdeal) (⊥ : Ideal R)
          have h' : minimalPrimes (Localization.AtPrime p.asIdeal) =
              Ideal.under R ⁻¹' minimalPrimes R := by
            simpa only [Ideal.map_bot] using h
          rw [h']
          change Ideal.under R (o.symm q.1).asIdeal ∈ minimalPrimes R
          have ho : Ideal.under R (o.symm q.1).asIdeal = q.1.1.asIdeal := by
            change (o (o.symm q.1)).1.asIdeal = q.1.1.asIdeal
            rw [o.apply_symm_apply]
          rw [ho]
          exact q.2⟩
      invFun := fun q =>
        ⟨o q.1, by
          have h := IsLocalization.minimalPrimes_map p.asIdeal.primeCompl
            (Localization.AtPrime p.asIdeal) (⊥ : Ideal R)
          have h' : minimalPrimes (Localization.AtPrime p.asIdeal) =
              Ideal.under R ⁻¹' minimalPrimes R := by
            simpa only [Ideal.map_bot] using h
          have hq : q.1.asIdeal ∈ Ideal.under R ⁻¹' minimalPrimes R := by
            rw [← h']
            exact q.2
          change Ideal.under R q.1.asIdeal ∈ minimalPrimes R
          exact hq⟩
      left_inv := fun q => by simp [o]
      right_inv := fun q => by simp [o] }
  exact ⟨e.trans m⟩

/-! ### A standard open avoiding a minimal prime -/

/-- A quasi-compact open avoiding a minimal prime is disjoint from a standard
open containing that minimal prime. -/
theorem exists_basicOpen_disjoint_of_minimalPrime
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    {W : Set (PrimeSpectrum R)} (hWopen : IsOpen W) (hWcompact : IsCompact W)
    (hpW : p ∉ W) :
    ∃ f : R, f ∉ p.asIdeal ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩ W = ∅ := by
  classical
  let ι := {f : R // (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ W}
  let U : ι → Set (PrimeSpectrum R) := fun f =>
    PrimeSpectrum.basicOpen f.1
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact PrimeSpectrum.isOpen_basicOpen
  have hcover : W ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hWopen
    rcases hV with ⟨f, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨f, hVW⟩, hxV⟩
  obtain ⟨t, ht⟩ := hWcompact.elim_finite_subcover U hUopen hcover
  have hlocal (i : ι) (hi : i ∈ t) :
      ∃ n : ℕ, 0 < n ∧ ∃ a : R, a ∉ p.asIdeal ∧ a * i.1 ^ n = 0 := by
    have hfi : i.1 ∈ p.asIdeal := by
      by_contra hfi
      apply hpW
      exact i.2 ((PrimeSpectrum.mem_basicOpen i.1 p).2 hfi)
    have hrad :
        (⊥ : Ideal (Localization.AtPrime p.asIdeal)).radical =
          p.asIdeal.map (algebraMap R (Localization.AtPrime p.asIdeal)) := by
      simpa only [Ideal.map_bot] using
        (IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
          (A := Localization.AtPrime p.asIdeal) (q := p.asIdeal)
          (I := (⊥ : Ideal R)) hp)
    have hmem :
        algebraMap R (Localization.AtPrime p.asIdeal) i.1 ∈
          (⊥ : Ideal (Localization.AtPrime p.asIdeal)).radical := by
      rw [hrad]
      exact Ideal.mem_map_of_mem _ hfi
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hmem
    refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
    have hzero :
        algebraMap R (Localization.AtPrime p.asIdeal) (i.1 ^ (n + 1)) = 0 := by
      rw [map_pow, pow_succ, hn, zero_mul]
    obtain ⟨a, ha⟩ :=
      (IsLocalization.mk'_eq_zero_iff
        (S := Localization.AtPrime p.asIdeal) (i.1 ^ (n + 1))
        (1 : p.asIdeal.primeCompl)).mp (by
          rw [IsLocalization.mk'_one]
          exact hzero)
    exact ⟨a, a.2, ha⟩
  have hprod :
      ∀ s : Finset ι,
        (∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ ∃ a : R, a ∉ p.asIdeal ∧
          a * i.1 ^ n = 0) →
        ∃ f : R, f ∉ p.asIdeal ∧
          ∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ f * i.1 ^ n = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro hs
        refine ⟨1, ?_, ?_⟩
        · intro h
          exact p.2.ne_top ((p.asIdeal.eq_top_iff_one).mpr h)
        · simp
    | @insert i s hi ih =>
        intro hs
        obtain ⟨ni, hni, ai, hai, hia⟩ := hs i (by simp)
        obtain ⟨f, hf, hfs⟩ := ih (fun j hj => hs j (by simp [hj]))
        refine ⟨ai * f, ?_, ?_⟩
        · intro h
          rcases p.2.mul_mem_iff_mem_or_mem.mp h with h_ai | h_f
          · exact hai h_ai
          · exact hf h_f
        · intro j hj'
          rcases Finset.mem_insert.mp hj' with hji | hj'
          · subst j
            refine ⟨ni, hni, ?_⟩
            calc
              (ai * f) * i.1 ^ ni = f * (ai * i.1 ^ ni) := by
                ac_rfl
              _ = 0 := by rw [hia, mul_zero]
          · obtain ⟨nj, hnj, hjzero⟩ := hfs j hj'
            refine ⟨nj, hnj, ?_⟩
            rw [mul_assoc, hjzero, mul_zero]
  obtain ⟨f, hf, hfi⟩ := hprod t (fun i hi => hlocal i hi)
  refine ⟨f, hf, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx.2)
  obtain ⟨n, hn, hzero⟩ := hfi i hi
  have hmem : f * i.1 ^ n ∈ x.asIdeal := by
    rw [hzero]
    exact Ideal.zero_mem x.asIdeal
  rcases x.2.mul_mem_iff_mem_or_mem.mp hmem with hfx | hix
  · exact (PrimeSpectrum.mem_basicOpen f x).mp hx.1 hfx
  · exact (PrimeSpectrum.mem_basicOpen i.1 x).mp hxi
      ((x.2.pow_mem_iff_mem n hn).mp hix)

/-! ### Rings with no nontrivial prime inclusions -/

/-- The eight substantive conditions listed in the source are equivalent for
the spectrum of a commutative ring. -/
theorem isProfinite_TFAE_primeSpectrum_separation_conditions :
    List.TFAE
      [Formalization.Books.Topology.Unit22.IsProfiniteSpace (PrimeSpectrum R),
        T2Space (PrimeSpectrum R),
        TotallyDisconnectedSpace (PrimeSpectrum R),
        (∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U),
        (∀ p q : Ideal R, p.IsPrime → q.IsPrime → p ≤ q → p = q),
        (∀ p : Ideal R, p.IsPrime → p.IsMaximal),
        (∀ p : Ideal R, p.IsPrime → p ∈ minimalPrimes R),
        (∀ f : R, IsClosed (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)))] := by
  tfae_have 1 → 2 := by
    intro h
    exact
      ((Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected
        (X := PrimeSpectrum R)).mp h).1
  tfae_have 2 → 6 := by
    intro h I hI
    let _ : T2Space (PrimeSpectrum R) := h
    let p : PrimeSpectrum R := ⟨I, hI⟩
    simpa [p] using
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp isClosed_singleton)
  tfae_have 6 → 5 := by
    intro h p q hp hq hpq
    exact (h p hp).eq_of_le hq.ne_top hpq
  tfae_have 5 → 7 := by
    intro h p hp
    let _ : p.IsPrime := hp
    obtain ⟨q, hq, hqp⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := p) bot_le
    have heq : q = p := h q p hq.isPrime hp hqp
    exact heq ▸ hq
  tfae_have 7 → 4 := by
    intro h U hUopen hUcompact
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro p hpU
    obtain ⟨f, hf, hdisj⟩ :=
      exists_basicOpen_disjoint_of_minimalPrime p (h p p.2) hUopen hUcompact hpU
    refine Filter.mem_of_superset
      (PrimeSpectrum.isOpen_basicOpen.mem_nhds
        ((PrimeSpectrum.mem_basicOpen f p).2 hf)) ?_
    intro x hx
    intro hxU
    have hxint : x ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩ U :=
      ⟨hx, hxU⟩
    rw [hdisj] at hxint
    exact hxint
  tfae_have 4 → 2 := by
    intro h
    refine ⟨fun p q hpq => ?_⟩
    have hne : p.asIdeal ≠ q.asIdeal := by
      intro heq
      apply hpq
      exact PrimeSpectrum.ext heq
    by_cases hpqle : p.asIdeal ≤ q.asIdeal
    · have hnle : ¬ q.asIdeal ≤ p.asIdeal := by
        intro hle
        exact hne (le_antisymm hpqle hle)
      obtain ⟨f, hfq, hfp⟩ := not_subset.mp hnle
      let V := (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
      have hVclosed : IsClosed V :=
        h V PrimeSpectrum.isOpen_basicOpen (PrimeSpectrum.isCompact_basicOpen f)
      refine ⟨V, Vᶜ, PrimeSpectrum.isOpen_basicOpen, hVclosed.isOpen_compl,
        (PrimeSpectrum.mem_basicOpen f p).2 hfp, ?_, disjoint_compl_right⟩
      exact fun hqV => (PrimeSpectrum.mem_basicOpen f q).mp hqV hfq
    · obtain ⟨f, hfp, hfq⟩ := not_subset.mp hpqle
      let V := (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
      have hVclosed : IsClosed V :=
        h V PrimeSpectrum.isOpen_basicOpen (PrimeSpectrum.isCompact_basicOpen f)
      refine ⟨Vᶜ, V, hVclosed.isOpen_compl, PrimeSpectrum.isOpen_basicOpen,
        ?_, (PrimeSpectrum.mem_basicOpen f q).2 hfq, disjoint_compl_left⟩
      exact fun hpV => (PrimeSpectrum.mem_basicOpen f p).mp hpV hfp
  tfae_have 4 → 3 := by
    intro h
    rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
    intro p
    apply Set.Subset.antisymm
    · intro q hq
      by_contra hpq
      have hne : p.asIdeal ≠ q.asIdeal := by
        intro heq
        apply hpq
        exact PrimeSpectrum.ext heq.symm
      by_cases hpqle : p.asIdeal ≤ q.asIdeal
      · have hnle : ¬ q.asIdeal ≤ p.asIdeal := by
          intro hle
          exact hne (le_antisymm hpqle hle)
        obtain ⟨f, hfq, hfp⟩ := not_subset.mp hnle
        let V := (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
        have hVclopen : IsClopen V := ⟨
          h V PrimeSpectrum.isOpen_basicOpen (PrimeSpectrum.isCompact_basicOpen f),
          PrimeSpectrum.isOpen_basicOpen⟩
        have hpV : p ∈ V := (PrimeSpectrum.mem_basicOpen f p).2 hfp
        have hqV : q ∈ V := by
          apply (PrimeSpectrum.mem_basicOpen f q).mp
          exact
            (Set.mem_iInter.mp
              ((connectedComponent_subset_iInter_isClopen (x := p)) hq))
              ⟨V, hVclopen, hpV⟩
        exact (PrimeSpectrum.mem_basicOpen f q).mp hqV hfq
      · obtain ⟨f, hfp, hfq⟩ := not_subset.mp hpqle
        let V := (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
        have hVclopen : IsClopen V := ⟨
          h V PrimeSpectrum.isOpen_basicOpen (PrimeSpectrum.isCompact_basicOpen f),
          PrimeSpectrum.isOpen_basicOpen⟩
        have hpVc : p ∈ Vᶜ := fun hpV =>
          (PrimeSpectrum.mem_basicOpen f p).mp hpV hfp
        have hqV : q ∈ V := (PrimeSpectrum.mem_basicOpen f q).2 hfq
        have hqVc : q ∈ Vᶜ :=
          (Set.mem_iInter.mp
            ((connectedComponent_subset_iInter_isClopen (x := p)) hq))
            ⟨Vᶜ, hVclopen.compl, hpVc⟩
        exact hqVc hqV
    · exact singleton_subset_iff.mpr mem_connectedComponent
  tfae_have 3 → 5 := by
    intro h p q hp hq hpq
    let _ : TotallyDisconnectedSpace (PrimeSpectrum R) := h
    let p' : PrimeSpectrum R := ⟨p, hp⟩
    let q' : PrimeSpectrum R := ⟨q, hq⟩
    have hqcl : q' ∈ closure ({p'} : Set (PrimeSpectrum R)) := by
      rw [PrimeSpectrum.closure_singleton]
      exact (PrimeSpectrum.mem_zeroLocus q' _).2 hpq
    have hcomp : q' ∈ connectedComponent p' := by
      have hsub : closure ({p'} : Set (PrimeSpectrum R)) ⊆
          connectedComponent p' :=
        isConnected_singleton.closure.subset_connectedComponent
          (subset_closure (mem_singleton p'))
      exact hsub hqcl
    rw [totallyDisconnectedSpace_iff_connectedComponent_singleton.mp h p'] at hcomp
    have heq : q' = p' := Set.mem_singleton_iff.mp hcomp
    exact (congrArg PrimeSpectrum.asIdeal heq).symm
  tfae_have 8 → 4 := by
    intro h U hUopen hUcompact
    classical
    let ι := {f : R // (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ U}
    let B : ι → Set (PrimeSpectrum R) := fun f => PrimeSpectrum.basicOpen f.1
    have hBo : ∀ i, IsOpen (B i) := by
      intro i
      exact PrimeSpectrum.isOpen_basicOpen
    have hBU : U ⊆ ⋃ i, B i := by
      intro x hx
      obtain ⟨V, hV, hxV, hVU⟩ :=
        PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hUopen
      rcases hV with ⟨f, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨f, hVU⟩, hxV⟩
    obtain ⟨t, ht⟩ := hUcompact.elim_finite_subcover B hBo hBU
    have heq : U = ⋃ i ∈ t, B i := by
      apply Set.Subset.antisymm ht
      exact Set.iUnion_subset fun i => Set.iUnion_subset fun _ => i.2
    rw [heq]
    exact isClosed_biUnion_finset (fun i hi => h i.1)
  tfae_have 4 → 8 := by
    intro h f
    let V := (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
    exact h V PrimeSpectrum.isOpen_basicOpen (PrimeSpectrum.isCompact_basicOpen f)
  tfae_have 4 → 1 := by
    intro h
    let _ : T2Space (PrimeSpectrum R) := tfae_4_to_2 h
    let _ : TotallyDisconnectedSpace (PrimeSpectrum R) := tfae_4_to_3 h
    exact
      (Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected
        (X := PrimeSpectrum R)).mpr
        ⟨inferInstance, inferInstance, inferInstance⟩
  tfae_finish

end Irreducible

end Formalization.Books.Algebra.Unit26
