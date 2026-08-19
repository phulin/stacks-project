import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit63
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Commutative Algebra, Chapter 66: weakly associated primes

Weak association is represented on `PrimeSpectrum` points, as in Chapter 63's
source-facing associated-prime API.  The minimal-prime condition itself uses
Mathlib's `Ideal.minimalPrimes`, and localization, support, finite maps, and
tensor products use their canonical Mathlib constructions.
-/

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Definition and localization -/

/-- A prime point is weakly associated to `M` when it is minimal over the
annihilator of one of its elements. -/
def IsWeaklyAssociatedPrime
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) (M : Type v)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ m : M,
    p.asIdeal ∈ ((⊥ : Submodule R M).colon ({m} : Set M)).minimalPrimes

/-- The weakly associated-prime set of an `R`-module. -/
def weaklyAssociatedPrimes
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] : Set (PrimeSpectrum R) :=
  {p | IsWeaklyAssociatedPrime p M}

/-- Weak association can be characterized after localizing at the prime, or
by the radical of a localized element annihilator. -/
theorem weaklyAssociated_local
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    List.TFAE [
      p ∈ weaklyAssociatedPrimes R M,
      IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) ∈
        weaklyAssociatedPrimes (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M),
      ∃ m : LocalizedModule.AtPrime p.asIdeal M,
        (((⊥ : Submodule (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)).colon ({m} : Set _)).radical =
          (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)).asIdeal)] := by
  let S := p.asIdeal.primeCompl
  let A := Localization.AtPrime p.asIdeal
  let f := LocalizedModule.mkLinearMap S M
  have hmax (I : Ideal A) :
      IsLocalRing.maximalIdeal A ∈ I.minimalPrimes ↔
        I.radical = IsLocalRing.maximalIdeal A := by
    constructor
    · intro hI
      apply le_antisymm
      · exact (Ideal.IsPrime.radical_le_iff
          (IsLocalRing.maximalIdeal.isMaximal A).isPrime).mpr hI.le
      · rw [Ideal.radical_eq_sInf]
        refine le_sInf ?_
        intro q hq
        exact hI.2 ⟨hq.2, hq.1⟩
          (@IsLocalRing.le_maximalIdeal_of_isPrime A _ _ q hq.2)
    · intro hI
      refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal A).isPrime, ?_⟩, ?_⟩
      · rw [← hI]
        exact Ideal.le_radical
      · intro q hq hqmax
        rw [← hI]
        exact hq.1.radical_le_iff.mpr hq.2
  apply List.tfae_cons_cons.mpr
  constructor
  · constructor
    · rintro ⟨m, hm⟩
      let m' : LocalizedModule.AtPrime p.asIdeal M :=
        IsLocalizedModule.mk' f m (1 : S)
      refine ⟨m', ?_⟩
      have hmap :
          (Ideal.map (algebraMap R A)
            ((⊥ : Submodule R M).colon ({m} : Set M))) ≤
            (⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
              ({m'} : Set _) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hx
        rw [Ideal.mem_comap, Submodule.mem_colon_singleton]
        change algebraMap R A x • m' = 0
        rw [← IsLocalization.mk'_one (M := S) A x]
        rw [IsLocalizedModule.mk'_smul_mk' A f x m (1 : S) (1 : S)]
        simp [f, hx]
      have hJmin :
          IsLocalRing.maximalIdeal A ∈
            ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
              ({m'} : Set _)).minimalPrimes := by
        refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal A).isPrime, ?_⟩, ?_⟩
        · have hm'ne : m' ≠ 0 := by
            intro hm'zero
            obtain ⟨s, hs⟩ := (IsLocalizedModule.mk'_eq_zero' f (1 : S)).mp hm'zero
            have hsI : (s : R) ∈
                (⊥ : Submodule R M).colon ({m} : Set M) := by
              rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
              simpa only [Submonoid.smul_def] using hs
            exact s.2 (hm.le hsI)
          have hJne :
              ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
                ({m'} : Set _)) ≠ ⊤ := by
            intro hJtop
            have hm'zero : m' = 0 := by
              have hm'zero_mem : m' ∈
                  (⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)) :=
                (Submodule.colon_eq_top_iff_subset ({m'} : Set _)).mp hJtop (by simp)
              simpa using hm'zero_mem
            exact hm'ne hm'zero
          exact IsLocalRing.le_maximalIdeal hJne
        · intro q hq hqmax
          let q' := q.under R
          have hq' : q'.IsPrime ∧ Disjoint (S : Set R) q' :=
            (IsLocalization.isPrime_iff_isPrime_disjoint S A q).mp hq.1
          have hIleq' : (⊥ : Submodule R M).colon ({m} : Set M) ≤ q' := by
            apply (Ideal.map_le_iff_le_comap).mp
            exact hmap.trans hq.2
          have hq'p : q' ≤ p.asIdeal := by
            exact Ideal.comap_mono hqmax |>.trans_eq
              (Localization.AtPrime.under_maximalIdeal (I := p.asIdeal))
          have hpq' := hm.2 ⟨hq'.1, hIleq'⟩ hq'p
          rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
          exact (Ideal.map_le_iff_le_comap).mpr hpq'
      exact hJmin
    · intro h
      rcases h with ⟨m', hm'⟩
      rcases IsLocalizedModule.mk'_surjective S f m' with ⟨⟨m, s⟩, rfl⟩
      refine ⟨m, ?_⟩
      refine ⟨⟨p.2, ?_⟩, ?_⟩
      · intro x hx
        have hx' : algebraMap R A x ∈
            (⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
              ({IsLocalizedModule.mk' f m s} : Set _) := by
          rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hx
          rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
          rw [← IsLocalization.mk'_one (M := S) A x]
          rw [IsLocalizedModule.mk'_smul_mk' A f x m (1 : S) s]
          simp [hx]
        have hxmax : algebraMap R A x ∈ IsLocalRing.maximalIdeal A :=
          hm'.le hx'
        rw [← Ideal.mem_under, Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)] at hxmax
        exact hxmax
      · intro q hq hqp
        let Q := q.map (algebraMap R A)
        have hQprime : Q.IsPrime :=
          @Ideal.isPrime_map_of_isLocalizationAtPrime R _ p.asIdeal p.2 A _ _ _ q hq.1 hqp
        have hQmax : Q ≤ IsLocalRing.maximalIdeal A := by
          rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
          exact Ideal.map_mono hqp
        have hunder :
            ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
              ({IsLocalizedModule.mk' f m s} : Set _)).under R ≤ q := by
          intro x hx
          change algebraMap R A x ∈
            (⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
              ({IsLocalizedModule.mk' f m s} : Set _) at hx
          rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hx
          rw [← IsLocalization.mk'_one (M := S) A x] at hx
          have hxzero : IsLocalizedModule.mk' f (x • m) ((1 : S) * s) = 0 := by
            rw [← IsLocalizedModule.mk'_smul_mk' A f x m (1 : S) s]
            exact hx
          obtain ⟨t, htx⟩ := (IsLocalizedModule.mk'_eq_zero' f ((1 : S) * s)).mp hxzero
          have htxq : (t : R) * x ∈ q := hq.2 (by
            rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
            simpa only [mul_smul, Submonoid.smul_def] using htx)
          have htxnot : (t : R) ∉ q := fun ht => t.2 (hqp ht)
          exact (hq.1.mem_or_mem htxq).resolve_left htxnot
        have hJQ :
            ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
              ({IsLocalizedModule.mk' f m s} : Set _)) ≤ Q := by
          rw [← IsLocalization.map_under S A
            ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
              ({IsLocalizedModule.mk' f m s} : Set _))]
          exact Ideal.map_mono hunder
        have hmaxQ : IsLocalRing.maximalIdeal A ≤ Q := by
          exact hm'.2 ⟨hQprime, hJQ⟩ hQmax
        have hpq : p.asIdeal ≤ q := by
          have h : (IsLocalRing.maximalIdeal A).under R ≤ Q.under R :=
            Ideal.comap_mono hmaxQ
          rw [Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)] at h
          have hQunder : Q.under R = q :=
            @Ideal.under_map_of_isLocalizationAtPrime R _ p.asIdeal p.2 A _ _ _ q hq.1 hqp
          rw [hQunder] at h
          exact h
        exact hpq
  · apply List.tfae_cons_cons.mpr
    constructor
    · simp only [weaklyAssociatedPrimes, IsWeaklyAssociatedPrime,
        IsLocalRing.closedPoint]
      constructor
      · rintro ⟨m, hm⟩
        exact ⟨m, (hmax _).mp hm⟩
      · rintro ⟨m, hm⟩
        exact ⟨m, (hmax _).mpr hm⟩
    · exact List.tfae_singleton _

/-! ## Reduced rings and exact sequences -/

/-- For a reduced ring, the weakly associated primes of the ring are its
minimal primes. -/
theorem weaklyAssociatedPrimes_eq_minimalPrimes_of_reduced
    {R : Type u} [CommRing R] [IsReduced R] :
    weaklyAssociatedPrimes R R =
      {p : PrimeSpectrum R | p.asIdeal ∈ minimalPrimes R} := by
  classical
  ext p
  constructor
  · intro hp
    have hp3 : ∃ m : LocalizedModule.AtPrime p.asIdeal R,
        (((⊥ : Submodule (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal R)).colon ({m} : Set _)).radical =
          (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)).asIdeal) :=
      ((weaklyAssociated_local p).out 0 2).mp hp
    rcases hp3 with ⟨m, hm⟩
    let A := Localization.AtPrime p.asIdeal
    let J : Ideal A :=
      (⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal R)).colon ({m} : Set _)
    change J.radical = IsLocalRing.maximalIdeal A at hm
    have hred : IsReduced A :=
      isReduced_localizationPreserves p.asIdeal.primeCompl A inferInstance
    have hmaxzero : IsLocalRing.maximalIdeal A = (⊥ : Ideal A) := by
      by_cases hmmax : m ∈ IsLocalRing.maximalIdeal A
      · have hmrad : m ∈ J.radical := by rw [hm]; exact hmmax
        obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff.mp hmrad)
        have hmn : m ^ (n + 1) = 0 := by
          rw [pow_succ]
          simpa [J, Submodule.mem_colon_singleton, smul_eq_mul] using hn
        have hmzero : m = 0 := hred.eq_zero m ⟨n + 1, hmn⟩
        have hJtop : J = ⊤ := by
          simp [J, hmzero]
        have hmaxtop : IsLocalRing.maximalIdeal A = ⊤ := by
          rw [← hm, hJtop, Ideal.radical_top]
        exact ((IsLocalRing.maximalIdeal.isMaximal A).ne_top hmaxtop).elim
      · have hmunit : IsUnit m := IsLocalRing.notMem_maximalIdeal.mp hmmax
        have hJbot : J = (⊥ : Ideal A) := by
          apply le_antisymm
          · intro x hx
            have hxzero : x * m = 0 := by
              simpa [J, Submodule.mem_colon_singleton, smul_eq_mul] using hx
            exact (IsUnit.mul_left_eq_zero hmunit).mp hxzero
          · exact bot_le
        have hbotrad : (⊥ : Ideal A).IsRadical :=
          Ideal.isRadical_bot_iff.mpr hred
        rw [← hm, hJbot, hbotrad.radical]
    refine ⟨⟨p.2, bot_le⟩, ?_⟩
    intro q hq hqp
    let Q := q.map (algebraMap R A)
    have hQprime : Q.IsPrime :=
      @Ideal.isPrime_map_of_isLocalizationAtPrime R _ p.asIdeal p.2 A _ _ _ q hq.1 hqp
    have hQmax : Q ≤ IsLocalRing.maximalIdeal A := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
      exact Ideal.map_mono hqp
    have hQbot : Q = (⊥ : Ideal A) := by
      apply le_antisymm
      · rw [hmaxzero] at hQmax
        exact hQmax
      · exact bot_le
    calc
      p.asIdeal = (IsLocalRing.maximalIdeal A).under R :=
        (Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)).symm
      _ = (⊥ : Ideal A).under R := congrArg (Ideal.under R) hmaxzero
      _ = Q.under R := by rw [hQbot]
      _ ≤ q :=
        (@Ideal.under_map_of_isLocalizationAtPrime R _ p.asIdeal p.2 A _ _ _ q hq.1 hqp).le
  · intro hp
    have hpmin : p.asIdeal ∈ minimalPrimes R := hp
    refine ⟨(1 : R), ?_⟩
    have hcol :
        (⊥ : Submodule R R).colon ({(1 : R)} : Set R) = (⊥ : Ideal R) := by
      ext x
      simp [Submodule.mem_colon_singleton, smul_eq_mul]
    rw [hcol]
    exact hpmin

/-- The weakly associated-prime inclusions for a short exact sequence. -/
theorem weaklyAssociatedPrimes_short_exact
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    weaklyAssociatedPrimes R M' ⊆ weaklyAssociatedPrimes R M ∧
      weaklyAssociatedPrimes R M ⊆
        weaklyAssociatedPrimes R M' ∪ weaklyAssociatedPrimes R M'' := by
  constructor
  · intro p hp'
    have hp3 := ((weaklyAssociated_local p).out 0 2).mp hp'
    rcases hp3 with ⟨x, hx⟩
    let S := p.asIdeal.primeCompl
    let A := Localization.AtPrime p.asIdeal
    let F := LocalizedModule.map S f
    have hF : Function.Injective F := LocalizedModule.map_injective S f hf
    have hannF (y : LocalizedModule.AtPrime p.asIdeal M') :
        ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
          ({F y} : Set _)) =
          ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M')).colon
            ({y} : Set _)) := by
      ext a
      rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton]
      constructor
      · intro h
        apply hF
        simpa using h
      · intro h
        rw [Submodule.mem_bot] at h ⊢
        simpa using congrArg F h
    refine ((weaklyAssociated_local (M := M) p).out 0 2).mpr ?_
    refine ⟨F x, ?_⟩
    rw [hannF x]
    exact hx
  · intro p hp'
    have hp3 := ((weaklyAssociated_local p).out 0 2).mp hp'
    rcases hp3 with ⟨x, hx⟩
    let S := p.asIdeal.primeCompl
    let A := Localization.AtPrime p.asIdeal
    let F := LocalizedModule.map S f
    let G := LocalizedModule.map S g
    have hF : Function.Injective F := LocalizedModule.map_injective S f hf
    have hex : Function.Exact F G := LocalizedModule.map_exact S f g hfg
    have hGsurj : Function.Surjective G := LocalizedModule.map_surjective S g hg
    have hannF (y : LocalizedModule.AtPrime p.asIdeal M') :
        ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon
          ({F y} : Set _)) =
          ((⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M')).colon
            ({y} : Set _)) := by
      ext a
      rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton]
      constructor
      · intro h
        apply hF
        simpa using h
      · intro h
        rw [Submodule.mem_bot] at h ⊢
        simpa using congrArg F h
    by_cases hG : G x = 0
    · obtain ⟨y, hy⟩ := (hex x).mp hG
      left
      refine ((weaklyAssociated_local (M := M') p).out 0 2).mpr ?_
      refine ⟨y, ?_⟩
      rw [← hannF y, hy]
      exact hx
    · right
      refine ((weaklyAssociated_local (M := M'') p).out 0 2).mpr ?_
      refine ⟨G x, ?_⟩
      let J : Ideal A :=
        (⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M)).colon ({x} : Set _)
      let K : Ideal A :=
        (⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M'')).colon ({G x} : Set _)
      have hJleK : J ≤ K := by
        intro a ha
        rw [Submodule.mem_colon_singleton] at ha ⊢
        simpa [J, K] using congrArg G ha
      have hKne : K ≠ ⊤ := by
        intro hK
        have hzero : G x = 0 := by
          have hzero_mem : G x ∈
              (⊥ : Submodule A (LocalizedModule.AtPrime p.asIdeal M'')) :=
            (Submodule.colon_eq_top_iff_subset ({G x} : Set _)).mp hK (by simp)
          simpa using hzero_mem
        obtain ⟨y, hy⟩ := hGsurj (G x)
        apply hG
        calc
          G x = G y := hy.symm
          _ = 0 := by rw [hy]; exact hzero
      have hKle : K ≤ IsLocalRing.maximalIdeal A :=
        IsLocalRing.le_maximalIdeal hKne
      have hradle : K.radical ≤ IsLocalRing.maximalIdeal A := by
        exact (Ideal.IsPrime.radical_le_iff
          (IsLocalRing.maximalIdeal.isMaximal A).isPrime).mpr hKle
      have hradge : IsLocalRing.maximalIdeal A ≤ K.radical := by
        have hradge' : (IsLocalRing.closedPoint A).asIdeal ≤ K.radical := by
          rw [← hx]
          exact Ideal.radical_mono hJleK
        simpa only [IsLocalRing.closedPoint] using hradge'
      simpa only [IsLocalRing.closedPoint] using le_antisymm hradle hradge

/-! ## Existence, support, and zerodivisors -/

/-- A module is zero exactly when it has no weakly associated prime. -/
theorem weaklyAssociatedPrimes_eq_empty_iff_subsingleton
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Subsingleton M ↔ weaklyAssociatedPrimes R M = ∅ := by
  constructor
  · intro hM
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨m, hm⟩
    have hm0 : m = 0 := Subsingleton.elim _ _
    have htop : (⊥ : Submodule R M).colon ({m} : Set M) = ⊤ := by
      rw [Submodule.colon_eq_top_iff_subset]
      simp [hm0]
    rw [htop, Ideal.minimalPrimes_top] at hm
    exact Set.notMem_empty p hm
  · intro h
    classical
    by_contra hM
    have hnontrivial : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    obtain ⟨m, hm⟩ := @exists_ne M hnontrivial (0 : M)
    have hI : (⊥ : Submodule R M).colon ({m} : Set M) ≠ ⊤ := by
      intro htop
      have hm0 : m ∈ (⊥ : Submodule R M) :=
        (Submodule.colon_eq_top_iff_subset ({m} : Set M)).mp htop (by simp)
      exact hm (by simpa using hm0)
    obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hI
    let p : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hp : p ∈ weaklyAssociatedPrimes R M := ⟨m, hq⟩
    rw [h] at hp
    exact Set.notMem_empty p hp

/-- Associated primes are weakly associated, and weakly associated primes lie
in the support. -/
theorem associatedPrimes_subset_weaklyAssociatedPrimes_subset_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Formalization.Books.Algebra.Unit63.associatedPrimes R M ⊆
        weaklyAssociatedPrimes R M ∧
      weaklyAssociatedPrimes R M ⊆ Module.support R M := by
  constructor
  · intro p hp
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
    rcases hp with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    exact ⟨⟨p.2, le_rfl⟩, fun q hq _ => hq.2⟩
  · intro p hp
    change ∃ m, p.asIdeal ∈ ((⊥ : Submodule R M).colon ({m} : Set M)).minimalPrimes at hp
    rcases hp with ⟨m, hm⟩
    rw [Module.mem_support_iff']
    refine ⟨m, ?_⟩
    intro r hr hzero
    apply hr
    apply hm.1.2
    rw [Submodule.mem_colon_singleton]
    simp [hzero]

/-- The union of weakly associated primes is the set of module
zerodivisors. -/
theorem iUnion_weaklyAssociatedPrimes_eq_module_zeroDivisors
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    (⋃ p : {p : PrimeSpectrum R // p ∈ weaklyAssociatedPrimes R M},
        (p.1.asIdeal : Set R)) =
      {x : R | ∃ m : M, m ≠ 0 ∧ x • m = 0} := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
    have hp := p.2
    change ∃ m, p.1.asIdeal ∈
      ((⊥ : Submodule R M).colon ({m} : Set M)).minimalPrimes at hp
    rcases hp with ⟨m, hm⟩
    obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hm hx
    refine ⟨y • m, ?_, ?_⟩
    · intro hzero
      apply hy
      rw [Submodule.mem_colon_singleton]
      simp [hzero]
    · rw [smul_smul]
      rw [Submodule.mem_colon_singleton] at hxy
      simpa [mul_comm] using hxy
  · rintro ⟨m, hmne, hxm⟩
    have hI : (⊥ : Submodule R M).colon ({m} : Set M) ≠ ⊤ := by
      intro htop
      have hmzero : m ∈ (⊥ : Submodule R M) :=
        (Submodule.colon_eq_top_iff_subset ({m} : Set M)).mp htop (by simp)
      exact hmne (by simpa using hmzero)
    obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hI
    let p : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hp : p ∈ weaklyAssociatedPrimes R M := ⟨m, hq⟩
    refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    apply hq.le
    rw [Submodule.mem_colon_singleton]
    exact hxm

/-- A minimal point of the support of a module is weakly associated. -/
theorem weaklyAssociated_of_minimal_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hminimal : Minimal (fun q : PrimeSpectrum R => q ∈ Module.support R M) p) :
    p ∈ weaklyAssociatedPrimes R M := by
  let S := p.asIdeal.primeCompl
  let A := Localization.AtPrime p.asIdeal
  let f := LocalizedModule.mkLinearMap S M
  let N := LocalizedModule.AtPrime p.asIdeal M
  have hN : Nontrivial N := Module.mem_support_iff.mp hp
  have hne : weaklyAssociatedPrimes A N ≠ ∅ := by
    intro hzero
    have hsub : Subsingleton N :=
      (weaklyAssociatedPrimes_eq_empty_iff_subsingleton (R := A) (M := N)).mpr hzero
    exact (not_subsingleton_iff_nontrivial.mpr hN) hsub
  obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hq_support : q ∈ Module.support A N :=
    (associatedPrimes_subset_weaklyAssociatedPrimes_subset_support
      (R := A) (M := N)).2 hq
  obtain ⟨z, hz⟩ := Module.mem_support_iff'.mp hq_support
  rcases IsLocalizedModule.mk'_surjective S f z with ⟨⟨m, s⟩, rfl⟩
  let q'ideal : Ideal R := q.asIdeal.under R
  have hqprime : q'ideal.IsPrime ∧
      Disjoint (S : Set R) q'ideal :=
    (IsLocalization.isPrime_iff_isPrime_disjoint S A q.asIdeal).mp q.2
  let q' : PrimeSpectrum R := ⟨q'ideal, hqprime.1⟩
  have hq'_support : q' ∈ Module.support R M := by
    rw [Module.mem_support_iff']
    refine ⟨m, ?_⟩
    intro r hr hrzero
    apply hz (algebraMap R A r)
    · intro hrq
      apply hr
      rw [Ideal.mem_under]
      exact hrq
    · change algebraMap R A r • IsLocalizedModule.mk' f m s = 0
      rw [← IsLocalization.mk'_one (M := S) A r]
      rw [IsLocalizedModule.mk'_smul_mk' A f r m (1 : S) s]
      simp [hrzero]
  have hqle : q.asIdeal.under R ≤ p.asIdeal := by
    calc
      q.asIdeal.under R ≤ (IsLocalRing.maximalIdeal A).under R :=
        Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.2.ne_top)
      _ = p.asIdeal := Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)
  have hple : p.asIdeal ≤ q.asIdeal.under R := hminimal.2 hq'_support hqle
  have hmaxle : IsLocalRing.maximalIdeal A ≤ q.asIdeal := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
    exact (Ideal.map_le_iff_le_comap).mpr hple
  have hqeq : q.asIdeal = IsLocalRing.maximalIdeal A :=
    le_antisymm (IsLocalRing.le_maximalIdeal q.2.ne_top) hmaxle
  have hqpoint : q = IsLocalRing.closedPoint A := by
    apply PrimeSpectrum.ext
    simpa only [IsLocalRing.closedPoint] using hqeq
  apply ((weaklyAssociated_local p).out 0 1).mpr
  rw [← hqpoint]
  exact hq

/-! ## Finitely generated primes and functoriality -/

/-- At a finitely generated prime, weak association agrees with exact
association. -/
theorem associated_iff_weaklyAssociated_of_fg
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (hfg : p.asIdeal.FG) :
    p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ↔
      p ∈ weaklyAssociatedPrimes R M := by
  constructor
  · intro hp
    exact (associatedPrimes_subset_weaklyAssociatedPrimes_subset_support
      (R := R) (M := M)).1 hp
  · intro hp
    classical
    have hfg0 := hfg
    let S := p.asIdeal.primeCompl
    let A := Localization.AtPrime p.asIdeal
    let f := LocalizedModule.mkLinearMap S M
    let N := LocalizedModule.AtPrime p.asIdeal M
    obtain ⟨m, hm⟩ := ((weaklyAssociated_local p).out 0 2).mp hp
    have hmA :
        ((⊥ : Submodule A N).colon ({m} : Set N)).radical =
          IsLocalRing.maximalIdeal A := by
      simpa [A, N, IsLocalRing.closedPoint] using hm
    have hmne : m ≠ 0 := by
      intro hmzero
      have hJtop :
          (⊥ : Submodule A N).colon ({m} : Set N) = ⊤ := by
        simp [hmzero]
      have hmaxtop : IsLocalRing.maximalIdeal A = ⊤ := by
        rw [← hmA, hJtop, Ideal.radical_top]
      exact ((IsLocalRing.maximalIdeal.isMaximal A).ne_top hmaxtop).elim
    have hmaxfg : (IsLocalRing.maximalIdeal A).FG := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
      exact hfg.map (algebraMap R A)
    obtain ⟨U, hU⟩ := hmaxfg
    have hrad : ∀ a : A, a ∈ (U : Set A) → ∃ n : ℕ, a ^ n • m = 0 := by
      intro a ha
      have haMax : a ∈ IsLocalRing.maximalIdeal A := by
        rw [← hU]
        exact Ideal.subset_span ha
      have haRad : a ∈
          ((⊥ : Submodule A N).colon ({m} : Set N)).radical := by
        rw [hmA]
        exact haMax
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp haRad
      refine ⟨n, ?_⟩
      rw [Submodule.mem_colon_singleton] at hn
      exact hn
    have hprocess : ∀ V : Finset A, V ⊆ U →
        ∃ z : N, z ≠ 0 ∧
          (∀ a ∈ V, a • z = 0) ∧
          (∀ a ∈ U, ∃ n : ℕ, a ^ n • z = 0) := by
      intro V
      induction V using Finset.induction_on with
      | empty =>
          intro hVU
          refine ⟨m, hmne, ?_, ?_⟩
          · simp
          · exact hrad
      | @insert a V ha ih =>
          intro hVU
          obtain ⟨z, hzne, hkill, hradz⟩ := ih (by
            intro b hb
            exact hVU (Finset.mem_insert_of_mem hb))
          have haU : a ∈ U := hVU (Finset.mem_insert_self a V)
          obtain ⟨n, hn⟩ := hradz a haU
          let H : ∃ n : ℕ, a ^ n • z = 0 := ⟨n, hn⟩
          have he : Nat.find H ≠ 0 := by
            intro hezero
            apply hzne
            simpa [hezero] using Nat.find_spec H
          let z' := a ^ (Nat.find H - 1) • z
          have hz'ne : z' ≠ 0 := by
            dsimp [z']
            exact Nat.find_min H (Nat.sub_one_lt he)
          have hazero : a • z' = 0 := by
            dsimp [z']
            rw [smul_smul, mul_comm, ← pow_succ, tsub_add_cancel_of_le
              (Nat.one_le_iff_ne_zero.mpr he)]
            exact Nat.find_spec H
          refine ⟨z', hz'ne, ?_, ?_⟩
          · intro b hb
            rcases Finset.mem_insert.mp hb with rfl | hb
            · exact hazero
            · simpa [z', smul_smul, mul_comm] using
                congrArg (fun w => a ^ (Nat.find H - 1) • w) (hkill b hb)
          · intro b hb
            obtain ⟨k, hk⟩ := hradz b hb
            refine ⟨k, ?_⟩
            simpa [z', smul_smul, mul_comm] using
              congrArg (fun w => a ^ (Nat.find H - 1) • w) hk
    obtain ⟨m', hm'ne, hm'kill, _⟩ := hprocess U (by intro a ha; exact ha)
    have hle : IsLocalRing.maximalIdeal A ≤
        (⊥ : Submodule A N).colon ({m'} : Set N) := by
      rw [← hU, Ideal.span_le]
      intro a ha
      change a ∈ (⊥ : Submodule A N).colon ({m'} : Set N)
      exact (Submodule.mem_colon_singleton).mpr (hm'kill a ha)
    have hge : (⊥ : Submodule A N).colon ({m'} : Set N) ≤
        IsLocalRing.maximalIdeal A := by
      intro r hr
      by_contra hrmax
      have hunit : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp hrmax
      apply hm'ne
      apply (IsUnit.smul_eq_zero hunit).mp
      rw [Submodule.mem_colon_singleton] at hr
      exact hr
    have hcolon : (⊥ : Submodule A N).colon ({m'} : Set N) =
        IsLocalRing.maximalIdeal A := le_antisymm hge hle
    rcases hfg0 with ⟨T, hT⟩
    rcases IsLocalizedModule.mk'_surjective S f m' with ⟨⟨m, s⟩, rfl⟩
    simp only [Function.uncurry_apply_pair] at hcolon
    have hmem (a : T) : ∃ g : S, (g : R) • ((a : R) • m) = 0 := by
      have ha : (a : R) ∈ p.asIdeal := by
        rw [← hT]
        exact Ideal.subset_span a.2
      have haMax : algebraMap R A (a : R) ∈ IsLocalRing.maximalIdeal A := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
        exact Ideal.mem_map_of_mem (algebraMap R A) ha
      have haColon : algebraMap R A (a : R) ∈
          (⊥ : Submodule A N).colon
            ({IsLocalizedModule.mk' f m s} : Set N) := by
        rw [hcolon]
        exact haMax
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at haColon
      rw [← IsLocalization.mk'_one (M := S) A (a : R)] at haColon
      rw [IsLocalizedModule.mk'_smul_mk' A f (a : R) m (1 : S) s] at haColon
      exact (IsLocalizedModule.mk'_eq_zero' f ((1 : S) * s)).mp haColon
    choose g hg using hmem
    refine ⟨(∏ a, g a).1 • m, ?_⟩
    apply le_antisymm
    · intro r hr
      have hrzero : r • ((∏ a, g a).1 • m) = 0 := by
        rw [Submodule.mem_colon_singleton] at hr
        exact hr
      have hprod : ((∏ a, g a).1 : R) • (r • m) = 0 := by
        simpa [smul_smul, mul_comm] using hrzero
      have hmkzero : IsLocalizedModule.mk' f (r • m) s = 0 :=
        (IsLocalizedModule.mk'_eq_zero' f s).mpr ⟨∏ a, g a, hprod⟩
      have hlocalzero : algebraMap R A r •
          IsLocalizedModule.mk' f m s = 0 := by
        rw [← IsLocalization.mk'_one (M := S) A r]
        rw [IsLocalizedModule.mk'_smul_mk' A f r m (1 : S) s]
        simpa using hmkzero
      have hrmax : algebraMap R A r ∈ IsLocalRing.maximalIdeal A := by
        rw [← hcolon, Submodule.mem_colon_singleton]
        exact hlocalzero
      have hrunder : r ∈ (IsLocalRing.maximalIdeal A).under R := by
        rw [Ideal.mem_under]
        exact hrmax
      rw [Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)] at hrunder
      exact hrunder
    · rw [← hT, Ideal.span_le]
      intro a ha
      change a ∈ (⊥ : Submodule R M).colon
        ({(∏ a, g a).1 • m} : Set M)
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ (∏ a, g a) := by
        apply Finset.dvd_prod_of_mem g (Finset.mem_univ ⟨a, ha⟩)
      rw [hu, Submonoid.coe_mul, smul_smul, ← mul_assoc, mul_comm,
        ← smul_smul, mul_comm, ← smul_smul]
      exact smul_eq_zero_of_right u.1 (hg ⟨a, ha⟩)

/-- Over a Noetherian ring, associated and weakly associated primes coincide. -/
theorem associatedPrimes_eq_weaklyAssociatedPrimes_of_noetherian
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    Formalization.Books.Algebra.Unit63.associatedPrimes R M =
      weaklyAssociatedPrimes R M := by
  sorry

/-! ### The non-functoriality example -/

/-- The polynomial ring in the `x_i`, used as the base ring in the example. -/
abbrev weaklyAssociatedExampleBaseRing (k : Type u) [Field k] :=
  MvPolynomial ℕ k

/-- The polynomial ring in the `x_i` and `y_i` before imposing relations. -/
abbrev weaklyAssociatedExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (ℕ ⊕ ℕ) k

/-- The two families of variables in the example. -/
def weaklyAssociatedExampleX (k : Type u) [Field k] (i : ℕ) :
    weaklyAssociatedExamplePolynomialRing k :=
  MvPolynomial.X (.inl i)

def weaklyAssociatedExampleY (k : Type u) [Field k] (i : ℕ) :
    weaklyAssociatedExamplePolynomialRing k :=
  MvPolynomial.X (.inr i)

/-- The displayed relations `x_i y_i`. -/
def weaklyAssociatedExampleRelations (k : Type u) [Field k] :
    Set (weaklyAssociatedExamplePolynomialRing k) :=
  Set.range fun i : ℕ => weaklyAssociatedExampleX k i *
    weaklyAssociatedExampleY k i

/-- The ideal generated by the relations `x_i y_i`. -/
def weaklyAssociatedExampleRelationIdeal (k : Type u) [Field k] :
    Ideal (weaklyAssociatedExamplePolynomialRing k) :=
  Ideal.span (weaklyAssociatedExampleRelations k)

/-- The quotient ring `S` in the example. -/
abbrev weaklyAssociatedExampleRing (k : Type u) [Field k] :=
  weaklyAssociatedExamplePolynomialRing k ⧸
    weaklyAssociatedExampleRelationIdeal k

/-- The ring map `R → S` sending `x_i` to its copy in `S`. -/
def weaklyAssociatedExampleMap (k : Type u) [Field k] :
    weaklyAssociatedExampleBaseRing k →+* weaklyAssociatedExampleRing k :=
  (Ideal.Quotient.mk (weaklyAssociatedExampleRelationIdeal k)).comp
    (MvPolynomial.eval₂Hom
      (MvPolynomial.C : k →+* weaklyAssociatedExamplePolynomialRing k)
      (fun i : ℕ => weaklyAssociatedExampleX k i))

/-- The ideal `q = ∑ x_i S` in the example ring. -/
def weaklyAssociatedExampleQ (k : Type u) [Field k] :
    Ideal (weaklyAssociatedExampleRing k) :=
  Ideal.span (Set.range fun i : ℕ =>
    Ideal.Quotient.mk (weaklyAssociatedExampleRelationIdeal k)
      (weaklyAssociatedExampleX k i))

/-- The ideal `(x_1, x_2, ...)` in the base ring. -/
def weaklyAssociatedExampleP (k : Type u) [Field k] :
    Ideal (weaklyAssociatedExampleBaseRing k) :=
  Ideal.span (Set.range (fun i : ℕ => MvPolynomial.X i))

/-- The quotient ring has a weakly associated prime whose pullback is not
weakly associated over the base ring.  The final conjunct records the
finitely generated-annihilator observation in the source example. -/
theorem weaklyAssociated_nonFunctoriality_example
    (k : Type u) [Field k] :
    ∃ hq : (weaklyAssociatedExampleQ k).IsPrime,
      weaklyAssociatedExampleQ k ∈
          minimalPrimes (weaklyAssociatedExampleRing k) ∧
      (⟨weaklyAssociatedExampleQ k, hq⟩ :
          PrimeSpectrum (weaklyAssociatedExampleRing k)) ∈
        weaklyAssociatedPrimes (weaklyAssociatedExampleRing k)
          (weaklyAssociatedExampleRing k) ∧
      (letI : Module (weaklyAssociatedExampleBaseRing k)
          (weaklyAssociatedExampleRing k) :=
          Module.compHom (weaklyAssociatedExampleRing k)
            (weaklyAssociatedExampleMap k)
       PrimeSpectrum.comap (weaklyAssociatedExampleMap k)
           (⟨weaklyAssociatedExampleQ k, hq⟩ :
             PrimeSpectrum (weaklyAssociatedExampleRing k)) ∉
         weaklyAssociatedPrimes (weaklyAssociatedExampleBaseRing k)
           (weaklyAssociatedExampleRing k)) ∧
      (∀ s : weaklyAssociatedExampleRing k, s ≠ 0 →
        (letI : Module (weaklyAssociatedExampleBaseRing k)
            (weaklyAssociatedExampleRing k) :=
            Module.compHom (weaklyAssociatedExampleRing k)
              (weaklyAssociatedExampleMap k)
         ((⊥ : Submodule (weaklyAssociatedExampleBaseRing k)
             (weaklyAssociatedExampleRing k)).colon ({s} : Set _)).FG)) ∧
      (weaklyAssociatedExampleQ k).comap (weaklyAssociatedExampleMap k) =
        weaklyAssociatedExampleP k := by
  sorry

/-- Weakly associated primes pull back along every ring map. -/
theorem weaklyAssociatedPrimes_reverse_functorial
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (φ : R →+* S) :
    (letI : Module R M := Module.compHom M φ;
      weaklyAssociatedPrimes R M ⊆
        PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M) := by
  sorry

/-- The associated/weakly associated spectrum-map inclusion chain. -/
theorem associated_weaklyAssociated_functorial_chain
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (φ : R →+* S) :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ ''
            Formalization.Books.Algebra.Unit63.associatedPrimes S M ⊆
          Formalization.Books.Algebra.Unit63.associatedPrimes R M ∧
        Formalization.Books.Algebra.Unit63.associatedPrimes R M ⊆
          weaklyAssociatedPrimes R M ∧
        weaklyAssociatedPrimes R M ⊆
          PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M) := by
  sorry

/-- If the target ring is Noetherian, every inclusion in the preceding chain
is an equality. -/
theorem associated_weaklyAssociated_functorial_eq_of_noetherian
    {R S M : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing S] [AddCommGroup M] [Module S M]
    (φ : R →+* S) :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ ''
            Formalization.Books.Algebra.Unit63.associatedPrimes S M =
          Formalization.Books.Algebra.Unit63.associatedPrimes R M ∧
        Formalization.Books.Algebra.Unit63.associatedPrimes R M =
          weaklyAssociatedPrimes R M ∧
        weaklyAssociatedPrimes R M =
          PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M) := by
  sorry

/-! ## Finite maps, quotients, and localization -/

/-- A finite ring map preserves the weakly associated-prime set after mapping
the spectrum. -/
theorem weaklyAssociatedPrimes_finite_ring_map
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (hφ : RingHom.Finite φ) :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M =
        weaklyAssociatedPrimes R M) := by
  sorry

/-- Passing from `R` to `R/I` preserves weakly associated primes via the
canonical injection of spectra. -/
theorem weaklyAssociatedPrimes_quotient_ring
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module (R ⧸ I) M] :
    (letI : Module R M := Module.compHom M (Ideal.Quotient.mk I);
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ''
          weaklyAssociatedPrimes (R ⧸ I) M = weaklyAssociatedPrimes R M) := by
  sorry

/-- The two weakly associated-prime localization equalities. -/
theorem weaklyAssociatedPrimes_localize
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      PrimeSpectrum.comap (algebraMap R (Localization S)) ''
          weaklyAssociatedPrimes (Localization S)
            (LocalizedModule S M) =
        weaklyAssociatedPrimes R (LocalizedModule S M) ∧
      weaklyAssociatedPrimes R M ∩
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
        weaklyAssociatedPrimes R (LocalizedModule S M)) := by
  sorry

/-- Localization at elements that are all module nonzerodivisors does not
change the weakly associated-prime set over the original ring. -/
theorem weaklyAssociatedPrimes_localize_of_regular
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R)
    (hS : ∀ s : S, IsSMulRegular M (s : R)) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      weaklyAssociatedPrimes R M =
        weaklyAssociatedPrimes R (LocalizedModule S M)) := by
  sorry

/-! ## Detection by localizations -/

/-- The canonical map from a module to the product of its localizations at
its weakly associated primes. -/
def localizationAtWeaklyAssociatedPrimesMap
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    M →ₗ[R]
      ∀ p : {p : PrimeSpectrum R // p ∈ weaklyAssociatedPrimes R M},
        LocalizedModule.AtPrime p.1.asIdeal M :=
  LinearMap.pi fun p =>
    LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl M

/-- The weakly associated-prime localizations detect every module element. -/
theorem localizationAtWeaklyAssociatedPrimesMap_injective
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Function.Injective
      (localizationAtWeaklyAssociatedPrimesMap (R := R) (M := M)) := by
  sorry

/-! ## The post-Bourbaki localization statement -/

/-- For a flat module over a domain, passing to the fraction field preserves
weakly associated primes after identifying the localized spectrum with the
original spectrum. -/
theorem weaklyAssociatedPrimes_post_bourbaki
    {R S N K : Type*} [CommRing R] [CommRing S] [Field K]
    [IsDomain R] [Algebra R S] [Algebra R K]
    [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Flat R N] [IsFractionRing R K] :
    letI : Algebra R S := (algebraMap R S).toAlgebra
    letI : Algebra R K := (algebraMap R K).toAlgebra
    PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            S →+* S ⊗[R] K) ''
        weaklyAssociatedPrimes (S ⊗[R] K)
          (Formalization.Books.Algebra.Unit14.baseChangeModule
            (M := N) (algebraMap R S) (algebraMap R K)) =
      weaklyAssociatedPrimes S N := by
  sorry

/-! ## Change of fields -/

/-- Weakly associated primes descend along extension of the coefficient
field. -/
theorem weaklyAssociatedPrimes_change_fields
    {k K R M : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R]
    [AddCommGroup M] [Module R M] :
    letI : Algebra k R := (algebraMap k R).toAlgebra
    letI : Algebra k K := (algebraMap k K).toAlgebra
    ∀ (q : PrimeSpectrum (R ⊗[k] K)) (p : PrimeSpectrum R),
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            R →+* R ⊗[k] K) q = p →
        q ∈ weaklyAssociatedPrimes (R ⊗[k] K)
          (Formalization.Books.Algebra.Unit14.baseChangeModule
            (M := M) (algebraMap k R) (algebraMap k K)) →
          p ∈ weaklyAssociatedPrimes R M := by
  sorry

end

end Formalization.Books.Algebra.Unit66
