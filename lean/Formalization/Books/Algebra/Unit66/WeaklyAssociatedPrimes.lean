import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit63.AssociatedPrimes
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Free
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
  ext p
  exact associated_iff_weaklyAssociated_of_fg p
    p.asIdeal.fg_of_isNoetherianRing

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
  classical
  let A := weaklyAssociatedExamplePolynomialRing k
  let L := weaklyAssociatedExampleRelationIdeal k
  let mk : A →+* weaklyAssociatedExampleRing k := Ideal.Quotient.mk L
  let K : Ideal A := Ideal.span (Set.range fun i : ℕ => weaklyAssociatedExampleX k i)
  let V : Ideal (MvPolynomial ℕ (MvPolynomial ℕ k)) :=
    MvPolynomial.idealOfVars ℕ (MvPolynomial ℕ k)
  have hVker : V = RingHom.ker (MvPolynomial.constantCoeff :
      MvPolynomial ℕ (MvPolynomial ℕ k) →+* MvPolynomial ℕ k) := by
    ext f
    change f ∈ Ideal.span (Set.range MvPolynomial.X) ↔ _
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    constructor
    · intro hf
      rw [RingHom.mem_ker, MvPolynomial.constantCoeff_eq]
      by_contra h0
      have hmem : (0 : ℕ →₀ ℕ) ∈ f.support :=
        MvPolynomial.mem_support_iff.mpr h0
      obtain ⟨i, _, hi⟩ := hf 0 hmem
      exact hi (by simp)
    · intro hf m hm
      rw [RingHom.mem_ker] at hf
      by_contra hzero
      have hmzero : m = 0 := by
        ext i
        by_contra hi
        exact hzero ⟨i, Set.mem_univ _, hi⟩
      have hmcoeff := MvPolynomial.mem_support_iff.mp hm
      apply hmcoeff
      simpa [hmzero, MvPolynomial.constantCoeff_eq] using hf
  have hVprime : V.IsPrime := by
    rw [hVker]
    exact RingHom.ker_isPrime _
  have hKprime : K.IsPrime := by
    let e := MvPolynomial.sumAlgEquiv k ℕ ℕ
    have hem : Ideal.map e.toRingEquiv K = V := by
      change Ideal.map e.toRingEquiv
          (Ideal.span (Set.range fun i : ℕ => weaklyAssociatedExampleX k i)) =
        Ideal.span (Set.range MvPolynomial.X)
      rw [Ideal.map_span]
      congr 1
      ext z
      constructor
      · rintro ⟨a, ⟨i, rfl⟩, h⟩
        exact ⟨i, by simpa [weaklyAssociatedExampleX, e] using h⟩
      · rintro ⟨i, rfl⟩
        exact ⟨weaklyAssociatedExampleX k i, ⟨i, rfl⟩,
          by simp [weaklyAssociatedExampleX, e]⟩
    let : V.IsPrime := hVprime
    have hcomp : (Ideal.map e.toRingEquiv K).comap e.toRingEquiv = K :=
      Ideal.comap_map_of_bijective e.toRingEquiv e.bijective (I := K)
    rw [hem] at hcomp
    rw [← hcomp]
    exact Ideal.comap_isPrime e.toRingEquiv V
  have hLleK : L ≤ K := by
    change Ideal.span (Set.range fun i : ℕ =>
      weaklyAssociatedExampleX k i * weaklyAssociatedExampleY k i) ≤ K
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have hx : weaklyAssociatedExampleX k i ∈
        Ideal.span (Set.range fun i : ℕ => weaklyAssociatedExampleX k i) :=
      Ideal.subset_span (Set.mem_range_self i)
    change weaklyAssociatedExampleX k i * weaklyAssociatedExampleY k i ∈
      Ideal.span (Set.range fun i : ℕ => weaklyAssociatedExampleX k i)
    simpa [mul_comm] using @Ideal.mul_mem_left A _
      (Ideal.span (Set.range fun i : ℕ => weaklyAssociatedExampleX k i))
      (weaklyAssociatedExampleY k i) (weaklyAssociatedExampleX k i) hx
  have hQmap : weaklyAssociatedExampleQ k = Ideal.map mk K := by
    change Ideal.span (Set.range fun i : ℕ => mk (weaklyAssociatedExampleX k i)) =
      Ideal.map mk (Ideal.span (Set.range fun i : ℕ => weaklyAssociatedExampleX k i))
    rw [Ideal.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨weaklyAssociatedExampleX k i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hQprime : (weaklyAssociatedExampleQ k).IsPrime := by
    rw [hQmap]
    let : K.IsPrime := hKprime
    apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    simpa [mk, L] using hLleK
  have hQmin : weaklyAssociatedExampleQ k ∈
      minimalPrimes (weaklyAssociatedExampleRing k) := by
    refine ⟨⟨hQprime, bot_le⟩, ?_⟩
    intro q hq hqle
    let : q.IsPrime := hq.1
    have hqA : (q.comap mk).IsPrime := Ideal.comap_isPrime mk q
    have hLq : L ≤ q.comap mk := by
      simpa [mk, L] using (Ideal.ker_le_comap (K := q) mk)
    have hqAleK : q.comap mk ≤ K := by
      rw [hQmap] at hqle
      exact (Ideal.comap_mono hqle).trans_eq <| by
        rw [Ideal.comap_map_of_surjective mk Ideal.Quotient.mk_surjective]
        apply sup_eq_left.mpr
        rw [← RingHom.ker_eq_comap_bot]
        change RingHom.ker (Ideal.Quotient.mk L) ≤ K
        rw [Ideal.mk_ker]
        exact hLleK
    have hyK : ∀ i : ℕ, weaklyAssociatedExampleY k i ∉ K := by
      intro i hy
      have hset :
            (MvPolynomial.X : (ℕ ⊕ ℕ) → MvPolynomial (ℕ ⊕ ℕ) k) ''
            (Set.range (fun j : ℕ => (Sum.inl j : ℕ ⊕ ℕ))) =
          Set.range (fun j : ℕ =>
            (MvPolynomial.X (Sum.inl j : ℕ ⊕ ℕ) : MvPolynomial (ℕ ⊕ ℕ) k)) := by
        ext z
        constructor
        · rintro ⟨a, ⟨j, rfl⟩, rfl⟩
          exact ⟨j, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨Sum.inl j, ⟨j, rfl⟩, rfl⟩
      have hy' : weaklyAssociatedExampleY k i ∈
          Ideal.span ((MvPolynomial.X : (ℕ ⊕ ℕ) → MvPolynomial (ℕ ⊕ ℕ) k) ''
            (Set.range (fun j : ℕ => (Sum.inl j : ℕ ⊕ ℕ)))) := by
        rw [hset]
        simpa [K, weaklyAssociatedExampleX] using hy
      rw [MvPolynomial.mem_ideal_span_X_image] at hy'
      have hysupp : (Finsupp.single (Sum.inr i) 1 : (ℕ ⊕ ℕ) →₀ ℕ) ∈
          (weaklyAssociatedExampleY k i).support := by
        apply MvPolynomial.mem_support_iff.mpr
        simp [weaklyAssociatedExampleY]
      obtain ⟨m, hm, hm'⟩ := hy' _ hysupp
      rcases hm with ⟨j, rfl⟩
      simp at hm'
    have hKq : K ≤ q.comap mk := by
      change Ideal.span (Set.range fun i : ℕ => weaklyAssociatedExampleX k i) ≤
        q.comap mk
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hrel : weaklyAssociatedExampleX k i *
          weaklyAssociatedExampleY k i ∈ q.comap mk := hLq (by
        exact Ideal.subset_span ⟨i, rfl⟩)
      exact (hqA.mem_or_mem hrel).resolve_right (fun h => hyK i (hqAleK h))
    rw [hQmap]
    exact Ideal.map_le_iff_le_comap.mpr hKq
  let q' : PrimeSpectrum (weaklyAssociatedExampleRing k) :=
    ⟨weaklyAssociatedExampleQ k, hQprime⟩
  have hqweak : q' ∈ weaklyAssociatedPrimes
      (weaklyAssociatedExampleRing k) (weaklyAssociatedExampleRing k) := by
    change ∃ m : weaklyAssociatedExampleRing k,
      weaklyAssociatedExampleQ k ∈
        ((⊥ : Submodule (weaklyAssociatedExampleRing k)
          (weaklyAssociatedExampleRing k)).colon ({m} : Set _)).minimalPrimes
    refine ⟨1, ?_⟩
    have hcol :
        (⊥ : Submodule (weaklyAssociatedExampleRing k)
          (weaklyAssociatedExampleRing k)).colon ({(1 : weaklyAssociatedExampleRing k)} : Set _) =
          (⊥ : Ideal (weaklyAssociatedExampleRing k)) := by
      ext x
      simp [Submodule.mem_colon_singleton, smul_eq_mul]
    rw [hcol]
    exact hQmin
  let ψ : weaklyAssociatedExampleBaseRing k →+*
      weaklyAssociatedExamplePolynomialRing k :=
    (MvPolynomial.rename (Sum.inl : ℕ → ℕ ⊕ ℕ) :
      weaklyAssociatedExampleBaseRing k →ₐ[k]
        weaklyAssociatedExamplePolynomialRing k).toRingHom
  let κ : weaklyAssociatedExamplePolynomialRing k →+*
      weaklyAssociatedExampleBaseRing k :=
    (MvPolynomial.killCompl (Sum.inl_injective : Function.Injective
      (Sum.inl : ℕ → ℕ ⊕ ℕ))).toRingHom
  have hψmap : weaklyAssociatedExampleMap k = mk.comp ψ := by
    ext z
    · simp [weaklyAssociatedExampleMap, ψ, mk, L,
        MvPolynomial.rename_eq_aeval]
    · simp [weaklyAssociatedExampleMap, ψ, mk, L,
        weaklyAssociatedExampleX, MvPolynomial.rename_eq_aeval]
  have hPmap : Ideal.map ψ (weaklyAssociatedExampleP k) ≤ K := by
    change Ideal.map ψ (Ideal.span (Set.range MvPolynomial.X)) ≤ K
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro z ⟨a, ⟨i, rfl⟩, hz⟩
    rw [← hz]
    have hψX : ψ (MvPolynomial.X i) = weaklyAssociatedExampleX k i := by
      simp [ψ, weaklyAssociatedExampleX]
    rw [hψX]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hKmap : Ideal.map κ K ≤ weaklyAssociatedExampleP k := by
    change Ideal.map κ
        (Ideal.span (Set.range fun i : ℕ => weaklyAssociatedExampleX k i)) ≤
      Ideal.span (Set.range MvPolynomial.X)
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro z ⟨a, ⟨i, rfl⟩, hz⟩
    rw [← hz]
    have hi : κ (weaklyAssociatedExampleX k i) = MvPolynomial.X i := by
      simpa [κ, weaklyAssociatedExampleX] using
        (MvPolynomial.killCompl_rename_app
          (Sum.inl_injective : Function.Injective (Sum.inl : ℕ → ℕ ⊕ ℕ))
          (MvPolynomial.X i))
    rw [hi]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hPcomap : (weaklyAssociatedExampleP k) = K.comap ψ := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mp hPmap
    · intro f hf
      have hmem : ψ f ∈ K := hf
      have hmem' : κ (ψ f) ∈ Ideal.map κ K :=
        Ideal.mem_map_of_mem κ hmem
      have hcomp : κ (ψ f) = f := by
        simp [ψ, κ]
      rw [hcomp] at hmem'
      exact hKmap hmem'
  refine ⟨hQprime, hQmin, hqweak, ?_⟩
  have hQcomap : (weaklyAssociatedExampleQ k).comap mk = K := by
    rw [hQmap, Ideal.comap_map_of_surjective mk Ideal.Quotient.mk_surjective]
    apply sup_eq_left.mpr
    rw [← RingHom.ker_eq_comap_bot]
    change RingHom.ker (Ideal.Quotient.mk L) ≤ K
    rw [Ideal.mk_ker]
    exact hLleK
  have hcomap :
        (weaklyAssociatedExampleQ k).comap (weaklyAssociatedExampleMap k) =
        weaklyAssociatedExampleP k := by
    rw [hψmap]
    ext f
    change ψ f ∈ (weaklyAssociatedExampleQ k).comap mk ↔
      f ∈ weaklyAssociatedExampleP k
    rw [hQcomap, hPcomap]
    simp only [Ideal.mem_comap]
  let : Module (weaklyAssociatedExampleBaseRing k)
      (weaklyAssociatedExampleRing k) :=
    Module.compHom (weaklyAssociatedExampleRing k)
      (weaklyAssociatedExampleMap k)
  have hfinite_ann : ∀ s : weaklyAssociatedExampleRing k, s ≠ 0 →
      ((⊥ : Submodule (weaklyAssociatedExampleBaseRing k)
          (weaklyAssociatedExampleRing k)).colon ({s} : Set _)).FG := by
    intro s hs
    have hvar_prime : ∀ (t : Finset ℕ),
        (Ideal.span (MvPolynomial.X '' (t : Set ℕ)) :
          Ideal (MvPolynomial ℕ k)).IsPrime := by
      intro t
      let f : MvPolynomial ℕ k →+* MvPolynomial {i : ℕ // i ∉ t} k :=
        (MvPolynomial.killCompl
          (Subtype.val_injective : Function.Injective
            (fun i : {i : ℕ // i ∉ t} => i.1))).toRingHom
      have hker : RingHom.ker f =
          Ideal.span (MvPolynomial.X '' (t : Set ℕ)) := by
        apply le_antisymm
        · intro p hp
          rw [MvPolynomial.mem_ideal_span_X_image]
          intro m hm
          by_contra hno
          have hsub : (m.support : Set ℕ) ⊆
              Set.range (fun i : {i : ℕ // i ∉ t} => i.1) := by
            intro i hi
            by_cases hit : i ∈ t
            · exact False.elim (hno ⟨i, hit,
                Finsupp.mem_support_iff.mp hi⟩)
            · exact ⟨⟨i, hit⟩, rfl⟩
          let n : {i : ℕ // i ∉ t} →₀ ℕ :=
            Finsupp.comapDomain (fun i : {i : ℕ // i ∉ t} => i.1) m
              (Subtype.val_injective.injOn)
          have hmap : Finsupp.mapDomain
                (fun i : {i : ℕ // i ∉ t} => i.1) n = m := by
            exact Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hsub
          have hp0 : f p = 0 := hp
          have hp' : (f p).coeff n = 0 := by rw [hp0]; simp
          have hcoeff : p.coeff m = 0 := by
            simpa [f, n, MvPolynomial.coeff_killCompl, hmap] using hp'
          exact (Finsupp.mem_support_iff.mp hm) hcoeff
        · rw [Ideal.span_le]
          rintro _ ⟨i, hit, rfl⟩
          have hirange : i ∉ Set.range
              (fun j : {j : ℕ // j ∉ t} => j.1) := by
            rintro ⟨j, hj⟩
            exact j.2 (by simpa [hj] using hit)
          change f (MvPolynomial.X i) = 0
          change (MvPolynomial.killCompl
            (Subtype.val_injective : Function.Injective
              (fun j : {j : ℕ // j ∉ t} => j.1))) (MvPolynomial.X i) = 0
          rw [MvPolynomial.killCompl, MvPolynomial.aeval_X]
          exact dif_neg hirange
      rw [← hker]
      exact RingHom.ker_isPrime f
    let e : A ≃ₐ[k] MvPolynomial ℕ (MvPolynomial ℕ k) :=
      (MvPolynomial.renameEquiv k (Equiv.sumComm ℕ ℕ)).trans
        (MvPolynomial.sumAlgEquiv k ℕ ℕ)
    let L' : Ideal (MvPolynomial ℕ (MvPolynomial ℕ k)) :=
      Ideal.span (Set.range fun i : ℕ =>
        MvPolynomial.X i * MvPolynomial.C (MvPolynomial.X i))
    have heL : Ideal.map e.toRingEquiv L = L' := by
      change Ideal.map e.toRingEquiv
          (Ideal.span (Set.range fun i : ℕ =>
            weaklyAssociatedExampleX k i * weaklyAssociatedExampleY k i)) = L'
      rw [Ideal.map_span]
      congr 1
      ext z
      constructor
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simp [e, weaklyAssociatedExampleX,
          weaklyAssociatedExampleY, mul_comm]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨weaklyAssociatedExampleX k i * weaklyAssociatedExampleY k i,
          ⟨i, rfl⟩, by simp [e, weaklyAssociatedExampleX,
            weaklyAssociatedExampleY, mul_comm]⟩
    let I : (ℕ →₀ ℕ) → Ideal (MvPolynomial ℕ k) := fun d =>
      Ideal.span (MvPolynomial.X '' (d.support : Set ℕ))
    have hLcoeff : ∀ p : MvPolynomial ℕ (MvPolynomial ℕ k),
        p ∈ L' ↔ ∀ d : ℕ →₀ ℕ, p.coeff d ∈ I d := by
      intro p
      constructor
      · intro hp
        induction hp using Submodule.span_induction with
        | mem p hp =>
            rcases hp with ⟨i, rfl⟩
            intro d
            change MvPolynomial.coeff d
              (MvPolynomial.X i * MvPolynomial.C (MvPolynomial.X i)) ∈ I d
            by_cases hi : i ∈ d.support
            · rw [mul_comm, MvPolynomial.C_mul_X_eq_monomial]
              rw [MvPolynomial.coeff_monomial]
              split_ifs with hd
              · subst d
                exact Ideal.subset_span ⟨i, by simp⟩
              · simp
            · rw [mul_comm, MvPolynomial.C_mul_X_eq_monomial]
              rw [MvPolynomial.coeff_monomial]
              split_ifs with hd
              · subst d
                exact (hi (by simp)).elim
              · simp
        | zero =>
            intro d
            simp [I]
        | add p q hp hq ihp ihq =>
            intro d
            simpa only [MvPolynomial.coeff_add] using (I d).add_mem (ihp d) (ihq d)
        | smul r p hp ihp =>
            intro d
            rw [smul_eq_mul, MvPolynomial.coeff_mul]
            apply (I d).sum_mem
            intro x hx
            have hsum : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
            have hx2le : x.2 ≤ d := by
              rw [← hsum]
              exact le_add_left le_rfl
            have hsub : (x.2.support : Set ℕ) ⊆ (d.support : Set ℕ) := by
              intro i hi
              by_contra hdi
              have hdi' : d i = 0 := by
                simpa [Finsupp.mem_support_iff] using hdi
              have hxi : x.2 i = 0 := by
                exact Nat.eq_zero_of_le_zero (by simpa [hdi'] using hx2le i)
              exact (Finsupp.mem_support_iff.mp hi) hxi
            have hI : I x.2 ≤ I d := by
              exact Ideal.span_mono (Set.image_mono hsub)
            exact (I d).mul_mem_left _ (hI (ihp x.2))
      · intro hp
        rw [show p = ∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d) by
          simp]
        apply Submodule.sum_mem
        intro d hd
        have hd' : p.coeff d ∈ I d := hp d
        have hmon : ∀ a : MvPolynomial ℕ k, a ∈ I d →
            MvPolynomial.monomial d a ∈ L' := by
          intro a ha
          induction ha using Submodule.span_induction with
          | mem a ha =>
              rcases ha with ⟨i, hi, rfl⟩
              have hle : Finsupp.single i 1 ≤ d := by
                rw [Finsupp.single_le_iff]
                exact Nat.one_le_iff_ne_zero.mpr
                  (Finsupp.mem_support_iff.mp hi)
              rw [← tsub_add_cancel_of_le hle, add_comm,
                MvPolynomial.monomial_single_add]
              simpa [pow_one, MvPolynomial.C_mul_monomial, mul_assoc,
                mul_comm, mul_left_comm] using
                L'.mul_mem_left
                  (MvPolynomial.monomial (d - Finsupp.single i 1) 1)
                  (Ideal.subset_span ⟨i, rfl⟩)
          | zero => simp
          | add a b ha hb iha ihb => simpa using L'.add_mem iha ihb
          | smul r a ha iha =>
              simpa [MvPolynomial.C_mul_monomial, mul_assoc] using
                L'.mul_mem_left (MvPolynomial.C r) iha
        exact hmon _ hd'
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hfL : f ∉ L := by
      intro h
      apply hs
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h
    let g := e f
    have heψ : ∀ r : MvPolynomial ℕ k, e (ψ r) =
        MvPolynomial.C r := by
      intro r
      induction r using MvPolynomial.induction_on with
      | C c =>
          have hC :
              (MvPolynomial.renameEquiv k (Equiv.sumComm ℕ ℕ))
                  (MvPolynomial.C c) = MvPolynomial.C c := by
            change MvPolynomial.rename (Equiv.sumComm ℕ ℕ)
                (MvPolynomial.C c) = MvPolynomial.C c
            rw [MvPolynomial.rename_C]
          change (MvPolynomial.sumAlgEquiv k ℕ ℕ)
              ((MvPolynomial.renameEquiv k (Equiv.sumComm ℕ ℕ))
                ((MvPolynomial.rename Sum.inl) (MvPolynomial.C c))) = _
          rw [MvPolynomial.rename_C, hC]
          exact (MvPolynomial.sumAlgEquiv k ℕ ℕ).commutes c
      | add p q hp hq => simpa [map_add] using congrArg₂ (· + ·) hp hq
      | mul_X p i hp =>
          have hmul : ψ (p * MvPolynomial.X i) =
              ψ p * ψ (MvPolynomial.X i) := map_mul ψ p (MvPolynomial.X i)
          rw [hmul, map_mul, hp]
          have hX : e (ψ (MvPolynomial.X i)) =
              MvPolynomial.C (MvPolynomial.X i) := by
            have hrename :
                (MvPolynomial.renameEquiv k (Equiv.sumComm ℕ ℕ))
                    (MvPolynomial.X (Sum.inl i)) =
                  MvPolynomial.X (Sum.inr i) := by
              change MvPolynomial.rename (Equiv.sumComm ℕ ℕ)
                  (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (Sum.inr i)
              rw [MvPolynomial.rename_X]
              rfl
            change (MvPolynomial.sumAlgEquiv k ℕ ℕ)
                ((MvPolynomial.renameEquiv k (Equiv.sumComm ℕ ℕ))
                  ((MvPolynomial.rename Sum.inl) (MvPolynomial.X i))) = _
            rw [MvPolynomial.rename_X, hrename]
            exact MvPolynomial.sumAlgEquiv_X_inr k ℕ ℕ i
          rw [hX]
          simp [MvPolynomial.C_mul]
    have hann : ∀ r : MvPolynomial ℕ k,
        r ∈ (⊥ : Submodule (MvPolynomial ℕ k)
          (weaklyAssociatedExampleRing k)).colon
            ({Ideal.Quotient.mk L f} : Set _) ↔
          ∀ d : ℕ →₀ ℕ, r * (g.coeff d) ∈ I d := by
      intro r
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      change (weaklyAssociatedExampleMap k r) •
          (Ideal.Quotient.mk L f) = 0 ↔ _
      rw [hψmap]
      change (Ideal.Quotient.mk L) (ψ r) * (Ideal.Quotient.mk L) f = 0 ↔ _
      rw [← map_mul]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hmem : ψ r * f ∈ L ↔ e (ψ r * f) ∈ L' := by
        have hcomap : Ideal.comap e.toRingEquiv L' = L := by
          rw [← heL, Ideal.comap_map_of_surjective e.toRingEquiv
            e.toRingEquiv.surjective]
          have hker : Ideal.comap e.toRingEquiv (⊥ : Ideal _) = ⊥ := by
            ext a
            simp [Ideal.mem_comap]
          rw [hker, sup_bot_eq]
        constructor
        · intro h
          rw [← heL]
          exact Ideal.mem_map_of_mem e.toRingEquiv h
        · intro h
          have h' : ψ r * f ∈ Ideal.comap e.toRingEquiv L' := h
          rw [hcomap] at h'
          exact h'
      rw [hmem]
      rw [show e (ψ r * f) = MvPolynomial.C r * g by
        simp [g, heψ]]
      rw [hLcoeff]
      simp [g, MvPolynomial.coeff_C_mul]
    let D : Finset (ℕ →₀ ℕ) :=
      g.support.filter (fun d => g.coeff d ∉ I d)
    let U : Finset ℕ := D.biUnion (fun d => d.support)
    let T : Finset (Finset ℕ) :=
      U.powerset.filter (fun t => ∀ d ∈ D, (t ∩ d.support).Nonempty)
    let gens : Finset (ℕ →₀ ℕ) :=
      T.image (fun t => Finsupp.indicator t (fun _ _ => 1))
    let J : Ideal (MvPolynomial ℕ k) :=
      Ideal.span ((fun m : ℕ →₀ ℕ => MvPolynomial.monomial m 1) ''
        (gens : Set (ℕ →₀ ℕ)))
    have hJfg : J.FG := by
      apply Submodule.fg_span
      exact gens.finite_toSet.image _
    have hAnn :
        (⊥ : Submodule (MvPolynomial ℕ k)
          (weaklyAssociatedExampleRing k)).colon
            ({Ideal.Quotient.mk L f} : Set _) = J := by
      apply le_antisymm
      · intro r hr
        rw [MvPolynomial.mem_ideal_span_monomial_image]
        intro m hm
        have hrall := (hann r).mp hr
        have hId : ∀ d ∈ D, r ∈ I d := by
          intro d hd
          have hprod : r * g.coeff d ∈ I d := hrall d
          have hnot : g.coeff d ∉ I d := (Finset.mem_filter.mp hd).2
          have hprime : (I d).IsPrime := by
            simpa [I] using hvar_prime d.support
          rcases hprime.mem_or_mem hprod with h | h
          · exact h
          · exact (hnot h).elim
        let t := m.support ∩ U
        have htU : t ∈ U.powerset := by
          exact Finset.mem_powerset.mpr Finset.inter_subset_right
        have htD : ∀ d ∈ D, (t ∩ d.support).Nonempty := by
          intro d hd
          have hmem := (MvPolynomial.mem_ideal_span_X_image.mp
            (hId d hd)) m hm
          rcases hmem with ⟨i, hiD, him⟩
          refine ⟨i, ?_⟩
          apply Finset.mem_inter.mpr
          exact ⟨Finset.mem_inter.mpr ⟨Finsupp.mem_support_iff.mpr him,
            Finset.mem_biUnion.mpr ⟨d, hd, hiD⟩⟩, hiD⟩
        have ht : t ∈ T := Finset.mem_filter.mpr ⟨htU, htD⟩
        let mt := Finsupp.indicator t (fun _ _ => 1)
        have hle : mt ≤ m := by
          intro i
          by_cases hi : i ∈ t
          · have him : i ∈ m.support :=
              (Finset.mem_inter.mp hi).1
            have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
            simpa [mt, hi] using
              (Nat.one_le_iff_ne_zero.mpr hmi)
          · simp [mt, hi]
        refine ⟨mt, ?_, hle⟩
        exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨m, hm, rfl⟩
        change m ∈ gens at hm
        rcases Finset.mem_image.mp hm with ⟨t, ht, rfl⟩
        let m : ℕ →₀ ℕ := Finsupp.indicator t (fun _ _ => 1)
        change MvPolynomial.monomial m 1 ∈
          (⊥ : Submodule (MvPolynomial ℕ k)
            (weaklyAssociatedExampleRing k)).colon
              ({Ideal.Quotient.mk L f} : Set _)
        apply (hann _).mpr
        intro d
        by_cases hd : d ∈ D
        · have htd := (Finset.mem_filter.mp ht).2 d hd
          rcases htd with ⟨i, hi⟩
          have hiD : i ∈ d.support := (Finset.mem_inter.mp hi).2
          have hle : Finsupp.single i 1 ≤ m := by
            rw [Finsupp.single_le_iff]
            exact Nat.one_le_iff_ne_zero.mpr (by
              simp [m, Finsupp.indicator, (Finset.mem_inter.mp hi).1])
          have hgen :
              MvPolynomial.monomial m 1 ∈ I d := by
            rw [← tsub_add_cancel_of_le hle, add_comm,
              MvPolynomial.monomial_single_add]
            simpa [pow_one, MvPolynomial.C_mul_monomial, mul_assoc,
              mul_comm, mul_left_comm] using
              (I d).mul_mem_left
                (MvPolynomial.monomial (m - Finsupp.single i 1) 1)
                (Ideal.subset_span ⟨i, hiD, rfl⟩)
          simpa [mul_comm] using (I d).mul_mem_left (g.coeff d) hgen
        · by_cases hdg : d ∈ g.support
          · have hcoeff : g.coeff d ∈ I d := by
              by_contra hnot
              exact hd (Finset.mem_filter.mpr ⟨hdg, hnot⟩)
            exact (I d).mul_mem_left _ hcoeff
          · have hzero : g.coeff d = 0 := by
              by_contra h
              exact hdg (Finsupp.mem_support_iff.mpr h)
            rw [hzero, mul_zero]
            exact (I d).zero_mem
    rw [hAnn]
    exact hJfg

  refine ⟨?_, ?_, hcomap⟩
  · intro hp
    change ∃ s : weaklyAssociatedExampleRing k,
      (weaklyAssociatedExampleQ k).comap (weaklyAssociatedExampleMap k) ∈
        ((⊥ : Submodule (weaklyAssociatedExampleBaseRing k)
            (weaklyAssociatedExampleRing k)).colon ({s} : Set _)).minimalPrimes at hp
    rw [hcomap] at hp
    rcases hp with ⟨s, hsm⟩
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      have hone : (1 : MvPolynomial ℕ k) ∈
          weaklyAssociatedExampleP k := by
        have htop : (⊤ : Ideal (MvPolynomial ℕ k)) ≤
            weaklyAssociatedExampleP k := by
          have htop0 :
              (⊥ : Submodule (weaklyAssociatedExampleBaseRing k)
                (weaklyAssociatedExampleRing k)).colon
                  ({0} : Set _) = ⊤ := by
            ext r
            simp [Submodule.mem_colon_singleton]
          rw [← htop0]
          exact hsm.1.2
        exact htop (by simp)
      rw [weaklyAssociatedExampleP] at hone
      rw [show Set.range (fun i : ℕ => MvPolynomial.X i) =
          MvPolynomial.X '' (Set.univ : Set ℕ) by
            ext z
            simp] at hone
      rw [MvPolynomial.mem_ideal_span_X_image] at hone
      simp at hone
    let ann : Ideal (MvPolynomial ℕ k) :=
      (⊥ : Submodule (weaklyAssociatedExampleBaseRing k)
        (weaklyAssociatedExampleRing k)).colon ({s} : Set _)
    have hann_fg : ann.FG := by
      exact hfinite_ann s hs0
    rcases hann_fg with ⟨G, hG⟩
    let U : Finset ℕ := G.biUnion (fun a => a.vars)
    obtain ⟨j, hj⟩ := U.exists_notMem
    let qjMap : MvPolynomial ℕ k →+* MvPolynomial {i : ℕ // i = j} k :=
      (MvPolynomial.killCompl
        (Subtype.val_injective : Function.Injective
          (fun i : {i : ℕ // i = j} => i.1))).toRingHom
    let Qj : Ideal (MvPolynomial ℕ k) :=
      Ideal.span (MvPolynomial.X '' {i : ℕ | i ≠ j})
    have hker : RingHom.ker qjMap = Qj := by
      apply le_antisymm
      · intro p hp
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_contra hno
        have hsub : (m.support : Set ℕ) ⊆
            Set.range (fun i : {i : ℕ // i = j} => i.1) := by
          intro i hi
          by_cases hij : i = j
          · exact ⟨⟨i, hij⟩, rfl⟩
          · exact False.elim (hno ⟨i, hij,
              Finsupp.mem_support_iff.mp hi⟩)
        let n : {i : ℕ // i = j} →₀ ℕ :=
          Finsupp.comapDomain (fun i : {i : ℕ // i = j} => i.1) m
            (Subtype.val_injective.injOn)
        have hmap : Finsupp.mapDomain
              (fun i : {i : ℕ // i = j} => i.1) n = m := by
          exact Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hsub
        have hp0 : qjMap p = 0 := hp
        have hp' : (qjMap p).coeff n = 0 := by rw [hp0]; simp
        have hcoeff : p.coeff m = 0 := by
          simpa [qjMap, n, MvPolynomial.coeff_killCompl, hmap] using hp'
        exact (Finsupp.mem_support_iff.mp hm) hcoeff
      · rw [Ideal.span_le]
        rintro _ ⟨i, hi, rfl⟩
        have hirange : i ∉ Set.range
            (fun l : {l : ℕ // l = j} => l.1) := by
          rintro ⟨l, hl⟩
          exact hi (hl.symm.trans l.2)
        change qjMap (MvPolynomial.X i) = 0
        change (MvPolynomial.killCompl
          (Subtype.val_injective : Function.Injective
            (fun l : {l : ℕ // l = j} => l.1))) (MvPolynomial.X i) = 0
        rw [MvPolynomial.killCompl, MvPolynomial.aeval_X]
        exact dif_neg hirange
    have hQjprime : Qj.IsPrime := by
      rw [← hker]
      exact RingHom.ker_isPrime qjMap
    have hAnnQj : ann ≤ Qj := by
      rw [← hG]
      rw [Ideal.span_le]
      intro a ha
      have haP : a ∈ weaklyAssociatedExampleP k := by
        have haann : a ∈ ann := by
          rw [← hG]
          exact Ideal.subset_span ha
        exact hsm.1.2 haann
      have haP' : a ∈
          Ideal.span (MvPolynomial.X '' (Set.univ : Set ℕ)) := by
        simpa [weaklyAssociatedExampleP, Set.image_univ] using haP
      rw [MvPolynomial.mem_ideal_span_X_image] at haP'
      change a ∈ Ideal.span (MvPolynomial.X '' {i : ℕ | i ≠ j})
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      rcases haP' m hm with ⟨i, hi, him⟩
      have hvars : i ∈ a.vars := by
        rw [MvPolynomial.mem_vars_iff_mem_support]
        exact ⟨m, hm, Finsupp.mem_support_iff.mpr him⟩
      have hne : i ≠ j := by
        intro hij
        apply hj
        subst j
        exact Finset.mem_biUnion.mpr ⟨a, ha, hvars⟩
      exact ⟨i, hne, him⟩
    have hQj_le_P : Qj ≤ weaklyAssociatedExampleP k := by
      change Ideal.span (MvPolynomial.X '' {i : ℕ | i ≠ j}) ≤
        Ideal.span (Set.range (fun i : ℕ => MvPolynomial.X i))
      rw [Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact Ideal.subset_span ⟨i, rfl⟩
    have hxjP : MvPolynomial.X j ∈ weaklyAssociatedExampleP k := by
      rw [weaklyAssociatedExampleP]
      exact Ideal.subset_span ⟨j, rfl⟩
    have hxjQ : MvPolynomial.X j ∈ Qj :=
      (hsm.2 ⟨hQjprime, hAnnQj⟩ hQj_le_P) hxjP
    have hxjnot : MvPolynomial.X j ∉ Qj := by
      intro hx
      have hzero : qjMap (MvPolynomial.X j) = 0 := by
        have hxker : MvPolynomial.X j ∈ RingHom.ker qjMap := by
          rw [hker]
          exact hx
        exact hxker
      have hmapj : qjMap (MvPolynomial.X j) =
          MvPolynomial.X ⟨j, rfl⟩ := by
        change (MvPolynomial.killCompl
          (Subtype.val_injective : Function.Injective
            (fun l : {l : ℕ // l = j} => l.1))) (MvPolynomial.X j) = _
        rw [MvPolynomial.killCompl, MvPolynomial.aeval_X]
        have hmem : j ∈ Set.range
            (fun l : {l : ℕ // l = j} => l.1) :=
          ⟨⟨j, rfl⟩, rfl⟩
        rw [dif_pos hmem]
        congr 1
        apply Subtype.ext
        have hh := congrArg
          (fun z : Set.range (fun l : {l : ℕ // l = j} => l.1) => z.1)
          ((Equiv.ofInjective Subtype.val
              (Subtype.val_injective : Function.Injective
                (fun l : {l : ℕ // l = j} => l.1))).apply_symm_apply
            (⟨j, hmem⟩ : Set.range
              (fun l : {l : ℕ // l = j} => l.1)))
        exact hh
      rw [hmapj] at hzero
      exact (MvPolynomial.X_ne_zero (⟨j, rfl⟩ : {i : ℕ // i = j})) hzero
    exact hxjnot hxjQ
  · intro s hs
    exact hfinite_ann s hs

/-- Weakly associated primes pull back along every ring map. -/
theorem weaklyAssociatedPrimes_reverse_functorial
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (φ : R →+* S) :
    (letI : Module R M := Module.compHom M φ;
      weaklyAssociatedPrimes R M ⊆
        PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M) := by
  let : Module R M := Module.compHom M φ
  intro p hp
  change ∃ m : M,
    p.asIdeal ∈ ((⊥ : Submodule R M).colon ({m} : Set M)).minimalPrimes at hp
  rcases hp with ⟨m, hm⟩
  let I : Ideal R := (⊥ : Submodule R M).colon ({m} : Set M)
  let J : Ideal S := (⊥ : Submodule S M).colon ({m} : Set M)
  let T : Submonoid S := p.asIdeal.primeCompl.map φ
  let B := Localization T
  have hdisj : Disjoint (T : Set S) (J : Set S) := by
    rw [Set.disjoint_left]
    rintro s hsT hsJ
    rcases hsT with ⟨r, hr, rfl⟩
    have hsJ' : φ r • m = 0 := by
      simpa [J, Submodule.mem_colon_singleton, Submodule.mem_bot] using hsJ
    apply hr
    have hrI : r ∈ I := by
      simp only [I, Submodule.mem_colon_singleton, Submodule.mem_bot]
      change φ r • m = 0
      exact hsJ'
    exact hm.le hrI
  have hmapne : J.map (algebraMap S B) ≠ ⊤ := by
    exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint T B J).mpr hdisj
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hmapne
  have hqprime : q.IsPrime := hq.isPrime
  have hqS : q.under S ∈ J.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map T B J] at hq
    exact hq
  let qS : Ideal S := q.under S
  have hqSprime : qS.IsPrime := by
    exact (IsLocalization.isPrime_iff_isPrime_disjoint T B q).mp hqprime |>.1
  have hqSle : qS.comap φ ≤ p.asIdeal := by
    apply (Ideal.disjoint_map_primeCompl_iff_comap_le
      (f := φ) (p := p.asIdeal) (I := qS)).mp
    simpa [qS, T] using
      ((IsLocalization.isPrime_iff_isPrime_disjoint T B q).mp hqprime).2.symm
  have hIle : I ≤ qS.comap φ := by
    intro r hr
    rw [Ideal.mem_comap]
    have hrJ : φ r ∈ J := by
      simp only [J, Submodule.mem_colon_singleton, Submodule.mem_bot]
      change φ r • m = 0
      simp only [I, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
      change φ r • m = 0 at hr
      exact hr
    exact hqS.le hrJ
  have hpq : p.asIdeal ≤ qS.comap φ :=
    hm.2 ⟨Ideal.comap_isPrime φ qS, hIle⟩ hqSle
  have hpqeq : qS.comap φ = p.asIdeal := le_antisymm hqSle hpq
  let q' : PrimeSpectrum S := ⟨qS, hqSprime⟩
  have hqweak : q' ∈ weaklyAssociatedPrimes S M := by
    exact ⟨m, hqS⟩
  refine ⟨q', hqweak, ?_⟩
  apply PrimeSpectrum.ext
  exact hpqeq

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
  let : Module R M := Module.compHom M φ
  exact ⟨Formalization.Books.Algebra.Unit63.ass_functorial φ,
    associatedPrimes_subset_weaklyAssociatedPrimes_subset_support.1,
    weaklyAssociatedPrimes_reverse_functorial φ⟩

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
  let : Module R M := Module.compHom M φ
  have hchain := associated_weaklyAssociated_functorial_chain
    (R := R) (S := S) (M := M) φ
  have hS := associatedPrimes_eq_weaklyAssociatedPrimes_of_noetherian
      (R := S) (M := M)
  rcases hchain with ⟨h₁, h₂, h₃⟩
  have hSimage : PrimeSpectrum.comap φ ''
      Formalization.Books.Algebra.Unit63.associatedPrimes S M =
      PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M :=
    congrArg (fun T : Set (PrimeSpectrum S) => PrimeSpectrum.comap φ '' T) hS
  have h₃' : weaklyAssociatedPrimes R M ⊆
      PrimeSpectrum.comap φ ''
        Formalization.Books.Algebra.Unit63.associatedPrimes S M :=
    h₃.trans_eq hSimage.symm
  have h₄ : PrimeSpectrum.comap φ '' weaklyAssociatedPrimes S M ⊆
      Formalization.Books.Algebra.Unit63.associatedPrimes R M := by
    rw [← hSimage]
    exact h₁
  exact ⟨le_antisymm h₁ (h₂.trans h₃'),
    le_antisymm h₂ (h₃'.trans h₁),
    le_antisymm h₃ (h₄.trans h₂)⟩

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
  classical
  let : Algebra R S := φ.toAlgebra
  let : Module.Finite R S := hφ
  let : Algebra.IsIntegral R S := ⟨RingHom.Finite.to_isIntegral hφ⟩
  let : Module R M := Module.compHom M φ
  apply le_antisymm
  · rintro p ⟨q, hq, rfl⟩
    change ∃ m : M,
      (q.asIdeal.comap φ) ∈
        ((⊥ : Submodule R M).colon ({m} : Set M)).minimalPrimes
    change ∃ m : M,
      q.asIdeal ∈
        ((⊥ : Submodule S M).colon ({m} : Set M)).minimalPrimes at hq
    rcases hq with ⟨m, hq⟩
    let I : Ideal S :=
      (⊥ : Submodule S M).colon ({m} : Set M)
    let J : Ideal R :=
      (⊥ : Submodule R M).colon ({m} : Set M)
    have hJ : J = I.comap φ := by
      ext r
      simp only [J, I, Ideal.mem_comap, Submodule.mem_colon_singleton,
        Submodule.mem_bot]
      change r • m = 0 ↔ φ r • m = 0
      rfl
    have hfin : (q.asIdeal.comap φ).primesOver S |>.Finite := by
      simpa [Ideal.under_def] using
        (Algebra.QuasiFinite.finite_primesOver
          (R := R) (S := S) (q.asIdeal.comap φ))
    let T : Set (Ideal S) :=
      {Q | Q ∈ (q.asIdeal.comap φ).primesOver S ∧ Q ≠ q.asIdeal}
    have hT : T.Finite := hfin.subset (by
      intro Q hQ
      exact hQ.1)
    have hnotle : ∀ Q ∈ T, ¬ q.asIdeal ≤ Q := by
      intro Q hQT hle
      have hQprime : Q.IsPrime := hQT.1.1
      let : q.asIdeal.IsPrime := q.2
      let : Q.IsPrime := hQprime
      have hlt : q.asIdeal < Q := lt_of_le_of_ne hle hQT.2.symm
      have hcomaplt : q.asIdeal.comap (algebraMap R S) <
          Q.comap (algebraMap R S) :=
        Ideal.IsIntegral.comap_lt_comap hlt
      have hqover : q.asIdeal.comap (algebraMap R S) =
          q.asIdeal.comap φ := rfl
      have hQover : Q.comap (algebraMap R S) =
          q.asIdeal.comap φ := by
        simpa [Ideal.under_def] using hQT.1.2.over.symm
      exact (ne_of_lt hcomaplt) (hqover.trans hQover.symm)
    have hqnotunion : ¬ ((q.asIdeal : Set S) ⊆
        ⋃ Q ∈ T, (Q : Set S)) := by
      intro hsub
      rcases (Ideal.subset_union_prime_finite hT q.asIdeal q.asIdeal
        (f := fun Q : Ideal S => Q)
        (by
          intro Q hQ _ _
          exact hQ.1.1)).mp hsub with ⟨Q, hQT, hle⟩
      exact hnotle Q hQT hle
    obtain ⟨x, hxq, hxT⟩ := Set.not_subset.mp hqnotunion
    have hxnot : ∀ Q ∈ T, x ∉ Q := by
      intro Q hQ hx
      exact hxT (Set.mem_iUnion₂.mpr ⟨Q, hQ, hx⟩)
    let A := Localization.AtPrime q.asIdeal
    let U := q.asIdeal.primeCompl
    let f := LocalizedModule.mkLinearMap U M
    have hqweak : q ∈ weaklyAssociatedPrimes S M := by
      change ∃ m, q.asIdeal ∈
        ((⊥ : Submodule S M).colon ({m} : Set M)).minimalPrimes
      exact ⟨m, hq⟩
    obtain ⟨m', hmrad⟩ :=
      ((weaklyAssociated_local (M := M) q).out 0 2).mp hqweak
    have hmrad' :
        ((⊥ : Submodule A (LocalizedModule.AtPrime q.asIdeal M)).colon
          ({m'} : Set _)).radical = IsLocalRing.maximalIdeal A := by
      simpa [A, IsLocalRing.closedPoint] using hmrad
    have hm'ne : m' ≠ 0 := by
      intro hm'zero
      have hJtop :
          (⊥ : Submodule A (LocalizedModule.AtPrime q.asIdeal M)).colon
            ({m'} : Set _) = ⊤ := by
        simp [hm'zero]
      have hmaxtop : IsLocalRing.maximalIdeal A = ⊤ := by
        rw [← hmrad', hJtop, Ideal.radical_top]
      exact ((IsLocalRing.maximalIdeal.isMaximal A).ne_top hmaxtop).elim
    rcases IsLocalizedModule.mk'_surjective U f m' with ⟨⟨m, s⟩, rfl⟩
    let J' : Ideal A :=
      (⊥ : Submodule A (LocalizedModule.AtPrime q.asIdeal M)).colon
        ({IsLocalizedModule.mk' f m s} : Set _)
    have hmrad'' : J'.radical = IsLocalRing.maximalIdeal A := by
      simpa [J', Function.uncurry] using hmrad'
    have hxmax : algebraMap S A x ∈ IsLocalRing.maximalIdeal A := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)]
      exact Ideal.mem_map_of_mem (algebraMap S A) hxq
    have hxrad : algebraMap S A x ∈ J'.radical := by
      change algebraMap S A x ∈
        ((⊥ : Submodule A (LocalizedModule.AtPrime q.asIdeal M)).colon
          ({IsLocalizedModule.mk' f m s} : Set _)).radical
      rw [hmrad'']
      exact hxmax
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxrad
    rw [Submodule.mem_colon_singleton] at hn
    rw [Submodule.mem_bot, ← map_pow] at hn
    rw [← IsLocalization.mk'_one (M := U) A (x ^ n)] at hn
    rw [IsLocalizedModule.mk'_smul_mk' A f (x ^ n) m (1 : U) s] at hn
    obtain ⟨t, ht⟩ :=
      (IsLocalizedModule.mk'_eq_zero' f ((1 : U) * s)).mp hn
    let z : M := (t : S) • m
    have hz : z ≠ 0 := by
      intro hz
      apply hm'ne
      apply (IsLocalizedModule.mk'_eq_zero' f s).mpr
      exact ⟨t, hz⟩
    have hxz : x ^ n • z = 0 := by
      change x ^ n • ((t : S) • m) = 0
      rw [smul_smul]
      have ht' : (t : S) • (x ^ n • m) = 0 := by
        change (t : S) • (x ^ n • m) = 0 at ht
        exact ht
      simpa [smul_smul, mul_comm] using ht'
    have hzloc :
        IsLocalizedModule.mk' f z s =
          (t : S) • IsLocalizedModule.mk' f m s := by
      dsimp [z]
      simpa [IsLocalization.mk'_one] using
        (IsLocalizedModule.mk'_smul_mk' A f (t : S) m (1 : U) s).symm
    have hqz : q.asIdeal ∈
        ((⊥ : Submodule S M).colon ({z} : Set M)).minimalPrimes := by
      let : q.asIdeal.IsPrime := q.2
      have hIleq :
          (⊥ : Submodule S M).colon ({z} : Set M) ≤ q.asIdeal := by
        intro r hr
        have hloc : algebraMap S A r •
            IsLocalizedModule.mk' f z s = 0 := by
          rw [← IsLocalization.mk'_one (M := U) A r]
          rw [IsLocalizedModule.mk'_smul_mk' A f r z (1 : U) s]
          have hr0 : r • z = 0 := by
            simpa [Submodule.mem_colon_singleton, Submodule.mem_bot] using hr
          simp [hr0]
        by_contra hrq
        have hru : IsUnit (algebraMap S A r) :=
          IsLocalization.map_units (R := S) (S := A) (M := U) ⟨r, hrq⟩
        have htu : IsUnit (algebraMap S A (t : S)) :=
          IsLocalization.map_units (R := S) (S := A) (M := U) t
        apply hm'ne
        apply (IsUnit.smul_eq_zero htu).mp
        apply (IsUnit.smul_eq_zero hru).mp
        simpa [hzloc, mul_comm] using hloc
      refine ⟨⟨q.2, hIleq⟩, ?_⟩
      intro Q hQ hQle r hr
      have hrrad : algebraMap S A r ∈ J'.radical := by
        rw [hmrad'']
        rw [← Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)]
        exact Ideal.mem_map_of_mem (algebraMap S A) hr
      obtain ⟨d, hd⟩ := Ideal.mem_radical_iff.mp hrrad
      rw [Submodule.mem_colon_singleton] at hd
      rw [Submodule.mem_bot, ← map_pow] at hd
      rw [← IsLocalization.mk'_one (M := U) A (r ^ d)] at hd
      rw [IsLocalizedModule.mk'_smul_mk' A f (r ^ d) m (1 : U) s] at hd
      obtain ⟨a, ha⟩ :=
        (IsLocalizedModule.mk'_eq_zero' f ((1 : U) * s)).mp hd
      have har : (a : S) * r ^ d ∈ Q := hQ.2 (by
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
        change ((a : S) * r ^ d) • z = 0
        change ((a : S) * r ^ d) • ((t : S) • m) = 0
        rw [smul_smul]
        have ha' : (a : S) • (r ^ d • m) = 0 := by
          exact ha
        calc
          ((a : S) * r ^ d * (t : S)) • m =
              (t : S) • ((a : S) • (r ^ d • m)) := by
                simp [smul_smul, mul_comm]
          _ = 0 := by rw [ha']; simp)
      have hanot : (a : S) ∉ Q := by
        intro haQ
        exact a.2 (hQle haQ)
      exact hQ.1.mem_of_pow_mem d ((hQ.1.mem_or_mem har).resolve_left hanot)
    let K : Ideal R :=
      (⊥ : Submodule R M).colon ({z} : Set M)
    have hK : K =
        ((⊥ : Submodule S M).colon ({z} : Set M)).comap φ := by
      ext r
      simp only [K, Ideal.mem_comap, Submodule.mem_colon_singleton,
        Submodule.mem_bot]
      change r • z = 0 ↔ φ r • z = 0
      rfl
    have hKle : K ≤ q.asIdeal.comap φ := by
      rw [hK]
      exact Ideal.comap_mono hqz.1.2
    have hpmin : q.asIdeal.comap φ ∈ K.minimalPrimes := by
      let : q.asIdeal.IsPrime := q.2
      refine ⟨⟨Ideal.comap_isPrime φ q.asIdeal, hKle⟩, ?_⟩
      intro P hP hPle
      let : P.IsPrime := hP.1
      let I' : Ideal S :=
        (⊥ : Submodule S M).colon ({z} : Set M)
      have hKalg : K = I'.comap (algebraMap R S) := by
        ext r
        simp only [K, I', Ideal.mem_comap, Submodule.mem_colon_singleton,
          Submodule.mem_bot]
        change r • z = 0 ↔ algebraMap R S r • z = 0
        rfl
      have hI'comap : I'.comap (algebraMap R S) ≤ P := by
        rw [← hKalg]
        exact hP.2
      obtain ⟨Q, hIQ, hQprime, hQover⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral P I' hI'comap
      let : Q.IsPrime := hQprime
      have hQle : Q.comap (algebraMap R S) ≤
          q.asIdeal.comap φ := by
        rw [hQover]
        exact hPle
      obtain ⟨Q', hQQ', hQ'prime, hQ'over⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral
          (q.asIdeal.comap φ) Q hQle
      let : Q'.IsPrime := hQ'prime
      have hQ'mem : Q' ∈ T ∨ Q' = q.asIdeal := by
        by_cases hQ'eq : Q' = q.asIdeal
        · exact Or.inr hQ'eq
        · exact Or.inl ⟨⟨hQ'prime, ⟨hQ'over.symm⟩⟩, hQ'eq⟩
      rcases hQ'mem with hQ'T | rfl
      · have hxI' : x ^ n ∈ I' := by
          simpa [I', Submodule.mem_colon_singleton, Submodule.mem_bot] using hxz
        have hxQ' : x ^ n ∈ Q' := hQQ' (hIQ hxI')
        exact False.elim ((hxnot Q' hQ'T)
          (hQ'prime.mem_of_pow_mem n hxQ'))
      · have hqleQ : q.asIdeal ≤ Q := hqz.2
            ⟨hQprime, hIQ⟩ hQQ'
        have hQeq : Q = q.asIdeal := le_antisymm hQQ' hqleQ
        have hPeq : q.asIdeal.comap φ = P := by
          have h := hQover
          rw [hQeq] at h
          exact h
        exact hPeq.le
    exact ⟨z, by simpa [K] using hpmin⟩
  · exact weaklyAssociatedPrimes_reverse_functorial φ

/-- Passing from `R` to `R/I` preserves weakly associated primes via the
canonical injection of spectra. -/
theorem weaklyAssociatedPrimes_quotient_ring
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module (R ⧸ I) M] :
    (letI : Module R M := Module.compHom M (Ideal.Quotient.mk I);
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ''
          weaklyAssociatedPrimes (R ⧸ I) M = weaklyAssociatedPrimes R M) := by
  exact weaklyAssociatedPrimes_finite_ring_map (Ideal.Quotient.mk I)
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

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
  let moduleR : Module R (LocalizedModule S M) := inferInstance
  have hmodule :
      Module.compHom (LocalizedModule S M) (algebraMap R (Localization S)) = moduleR := by
    exact Module.ext' _ _ fun r z =>
      IsScalarTower.algebraMap_smul (Localization S) r z
  let f := LocalizedModule.mkLinearMap S M
  have hweak_iff (p : PrimeSpectrum R)
      (hpdisj : Disjoint (S : Set R) p.asIdeal) :
      p ∈ weaklyAssociatedPrimes R M ↔
        p ∈ weaklyAssociatedPrimes R (LocalizedModule S M) := by
    constructor
    · intro hp
      change ∃ m : M,
        p.asIdeal ∈
          ((⊥ : Submodule R M).colon ({m} : Set M)).minimalPrimes at hp
      rcases hp with ⟨m, hm⟩
      let z : LocalizedModule S M :=
        IsLocalizedModule.mk' f m (1 : S)
      let J : Ideal R :=
        (⊥ : Submodule R (LocalizedModule S M)).colon ({z} : Set _)
      have hIleJ :
          (⊥ : Submodule R M).colon ({m} : Set M) ≤ J := by
        intro r hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr ⊢
        change r • IsLocalizedModule.mk' f m (1 : S) = 0
        rw [← IsScalarTower.algebraMap_smul (Localization S) r]
        rw [← IsLocalization.mk'_one (M := S) (Localization S) r]
        rw [IsLocalizedModule.mk'_smul_mk' (Localization S) f r m
          (1 : S) (1 : S)]
        simp [hr]
      have hJlep : J ≤ p.asIdeal := by
        intro r hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
        change r • IsLocalizedModule.mk' f m (1 : S) = 0 at hr
        rw [← IsScalarTower.algebraMap_smul (Localization S) r] at hr
        have hzero : IsLocalizedModule.mk' f (r • m) (1 : S) = 0 := by
          rw [← IsLocalization.mk'_one (M := S) (Localization S) r] at hr
          rw [IsLocalizedModule.mk'_smul_mk' (Localization S) f r m
            (1 : S) (1 : S)] at hr
          simpa only [one_mul] using hr
        obtain ⟨s, hs⟩ :=
          (IsLocalizedModule.mk'_eq_zero' f (1 : S)).mp hzero
        have hsr : (s : R) * r ∈
            (⊥ : Submodule R M).colon ({m} : Set M) := by
          rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
          simpa [smul_smul, Submonoid.smul_def] using hs
        have hsnot : (s : R) ∉ p.asIdeal := by
          intro hsp
          exact Set.disjoint_left.mp hpdisj s.2 hsp
        exact (p.2.mem_or_mem (hm.le hsr)).resolve_left hsnot
      refine ⟨z, ?_⟩
      refine ⟨⟨p.2, hJlep⟩, ?_⟩
      intro q hq hpq
      exact hm.2 ⟨hq.1, hIleJ.trans hq.2⟩ hpq
    · intro hp
      change ∃ z : LocalizedModule S M,
        p.asIdeal ∈
          ((⊥ : Submodule R (LocalizedModule S M)).colon ({z} : Set _)).minimalPrimes at hp
      rcases hp with ⟨z, hz⟩
      rcases IsLocalizedModule.mk'_surjective S f z with ⟨⟨m, s⟩, rfl⟩
      let I : Ideal R :=
        (⊥ : Submodule R M).colon ({m} : Set M)
      let J : Ideal R :=
        (⊥ : Submodule R (LocalizedModule S M)).colon
          ({IsLocalizedModule.mk' f m s} : Set _)
      have hIleJ : I ≤ J := by
        intro r hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr ⊢
        change r • IsLocalizedModule.mk' f m s = 0
        rw [← IsScalarTower.algebraMap_smul (Localization S) r]
        rw [← IsLocalization.mk'_one (M := S) (Localization S) r]
        rw [IsLocalizedModule.mk'_smul_mk' (Localization S) f r m
          (1 : S) s]
        simp [hr]
      have hsat : ∀ r ∈ J, ∃ t : S, (t : R) * r ∈ I := by
        intro r hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
        change r • IsLocalizedModule.mk' f m s = 0 at hr
        rw [← IsScalarTower.algebraMap_smul (Localization S) r] at hr
        have hzero : IsLocalizedModule.mk' f (r • m) ((1 : S) * s) = 0 := by
          rw [← IsLocalization.mk'_one (M := S) (Localization S) r] at hr
          rw [IsLocalizedModule.mk'_smul_mk' (Localization S) f r m
            (1 : S) s] at hr
          simpa only [one_mul] using hr
        obtain ⟨t, ht⟩ :=
          (IsLocalizedModule.mk'_eq_zero' f ((1 : S) * s)).mp hzero
        refine ⟨t, ?_⟩
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
        simpa [smul_smul, Submonoid.smul_def] using ht
      refine ⟨m, ?_⟩
      refine ⟨⟨p.2, hIleJ.trans hz.1.2⟩, ?_⟩
      intro q hq hqp
      have hJleq : J ≤ q := by
        intro r hr
        obtain ⟨t, htr⟩ := hsat r hr
        have htrq : (t : R) * r ∈ q := hq.2 htr
        have htnot : (t : R) ∉ q := by
          intro htq
          exact (Set.disjoint_left.mp hpdisj t.2 (hqp htq))
        exact (hq.1.mem_or_mem htrq).resolve_left htnot
      exact hz.2 ⟨hq.1, hJleq⟩ hqp
  have hfirst :
      PrimeSpectrum.comap (algebraMap R (Localization S)) ''
          weaklyAssociatedPrimes (Localization S)
            (LocalizedModule S M) =
        weaklyAssociatedPrimes R (LocalizedModule S M) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change ∃ m : LocalizedModule S M,
        q.asIdeal.comap (algebraMap R (Localization S)) ∈
          ((⊥ : Submodule R (LocalizedModule S M)).colon
            ({m} : Set _)).minimalPrimes
      change ∃ m : LocalizedModule S M,
        q.asIdeal ∈
          ((⊥ : Submodule (Localization S) (LocalizedModule S M)).colon
            ({m} : Set _)).minimalPrimes at hq
      rcases hq with ⟨m, hm⟩
      let I : Ideal R :=
        (⊥ : Submodule R (LocalizedModule S M)).colon ({m} : Set _)
      let J : Ideal (Localization S) :=
        (⊥ : Submodule (Localization S) (LocalizedModule S M)).colon
          ({m} : Set _)
      have hIJ : I = J.comap (algebraMap R (Localization S)) := by
        ext r
        simp only [I, J, Ideal.mem_comap, Submodule.mem_colon_singleton,
          Submodule.mem_bot]
        change r • m = 0 ↔ algebraMap R (Localization S) r • m = 0
        simp only [IsScalarTower.algebraMap_smul]
      have hpmin : q.asIdeal.comap (algebraMap R (Localization S)) ∈
          (J.comap (algebraMap R (Localization S))).minimalPrimes := by
        rw [IsLocalization.minimalPrimes_comap S (Localization S) J]
        exact ⟨q.asIdeal, hm, rfl⟩
      exact ⟨m, by rw [← hIJ] at hpmin; exact hpmin⟩
    · rintro hp
      change ∃ m : LocalizedModule S M,
        p.asIdeal ∈
          ((⊥ : Submodule R (LocalizedModule S M)).colon ({m} : Set _)).minimalPrimes at hp
      rcases hp with ⟨m, hm⟩
      let I : Ideal R :=
        (⊥ : Submodule R (LocalizedModule S M)).colon ({m} : Set _)
      let J : Ideal (Localization S) :=
        (⊥ : Submodule (Localization S) (LocalizedModule S M)).colon
          ({m} : Set _)
      have hIJ : I = J.comap (algebraMap R (Localization S)) := by
        ext r
        simp only [I, J, Ideal.mem_comap, Submodule.mem_colon_singleton,
          Submodule.mem_bot]
        change r • m = 0 ↔ algebraMap R (Localization S) r • m = 0
        simp only [IsScalarTower.algebraMap_smul]
      have hpmin : p.asIdeal ∈
          (J.comap (algebraMap R (Localization S))).minimalPrimes := by
        rw [← hIJ]
        exact hm
      rw [IsLocalization.minimalPrimes_comap S (Localization S) J] at hpmin
      rcases hpmin with ⟨q, hq, hqp⟩
      let q' : PrimeSpectrum (Localization S) := ⟨q, hq.isPrime⟩
      refine ⟨q', ?_, ?_⟩
      · exact ⟨m, hq⟩
      · apply PrimeSpectrum.ext
        exact hqp
  have hsecond :
      weaklyAssociatedPrimes R M ∩
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
        weaklyAssociatedPrimes R (LocalizedModule S M) := by
    have hiff (p : PrimeSpectrum R)
        (hpdisj : Disjoint (S : Set R) p.asIdeal) :=
      hweak_iff p hpdisj
    ext p
    constructor
    · rintro ⟨hpM, ⟨q, hqeq⟩⟩
      have hqprime : q.asIdeal.IsPrime := q.2
      have hpdisj : Disjoint (S : Set R) p.asIdeal := by
        have h := (IsLocalization.isPrime_iff_isPrime_disjoint S
          (Localization S) q.asIdeal).mp hqprime
        have hp_eq : q.asIdeal.comap (algebraMap R (Localization S)) = p.asIdeal := by
          simpa using congrArg PrimeSpectrum.asIdeal hqeq
        rw [← hp_eq]
        exact h.2
      exact (hiff p hpdisj).mp hpM
    · intro hpN
      have hpimage : p ∈ PrimeSpectrum.comap (algebraMap R (Localization S)) ''
          weaklyAssociatedPrimes (Localization S) (LocalizedModule S M) := by
        rw [hfirst]
        exact hpN
      rcases hpimage with ⟨q, hq, rfl⟩
      have hqprime : q.asIdeal.IsPrime := q.2
      have hdisj : Disjoint (S : Set R)
          (q.asIdeal.comap (algebraMap R (Localization S))) := by
        exact (IsLocalization.isPrime_iff_isPrime_disjoint S
          (Localization S) q.asIdeal).mp hqprime |>.2
      refine ⟨(hiff _ hdisj).mpr ?_, ⟨q, rfl⟩⟩
      exact hpN
  constructor
  · rw [hmodule]
    exact hfirst
  · rw [hmodule]
    exact hsecond

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
  have hloc := weaklyAssociatedPrimes_localize (R := R) (M := M) S
  apply le_antisymm
  · intro p hp
    rw [← hloc.2]
    refine ⟨hp, ?_⟩
    change ∃ q : PrimeSpectrum (Localization S),
      PrimeSpectrum.comap (algebraMap R (Localization S)) q = p
    change ∃ m : M,
      p.asIdeal ∈
        ((⊥ : Submodule R M).colon ({m} : Set M)).minimalPrimes at hp
    rcases hp with ⟨m, hm⟩
    have hpdisj : Disjoint (S : Set R) p.asIdeal := by
      rw [Set.disjoint_left]
      intro s hsS hsp
      obtain ⟨t, htI, hstI⟩ :=
        Ideal.exists_mul_mem_of_mem_minimalPrimes hm hsp
      have hstzero0 : (s * t) • m = 0 := by
        simpa [Submodule.mem_colon_singleton, Submodule.mem_bot] using hstI
      have hstzero : (s : R) • ((t : R) • m) = 0 := by
        simpa [smul_smul] using hstzero0
      apply htI
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact (hS ⟨s, hsS⟩).right_eq_zero_of_smul hstzero
    have hqprime :
        (p.asIdeal.map (algebraMap R (Localization S))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint S (Localization S)
        p.asIdeal p.2 hpdisj
    let q : PrimeSpectrum (Localization S) :=
      ⟨p.asIdeal.map (algebraMap R (Localization S)), hqprime⟩
    refine ⟨q, ?_⟩
    apply PrimeSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint S (Localization S)
      p.2 hpdisj
  · intro p hp
    rw [← hloc.2] at hp
    exact hp.1

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
  intro x y hxy
  by_contra hxy'
  let z : M := x - y
  have hz : z ≠ 0 := by
    intro hz
    apply hxy'
    exact sub_eq_zero.mp hz
  let I : Ideal R := (⊥ : Submodule R M).colon ({z} : Set M)
  have hItop : I ≠ ⊤ := by
    intro htop
    have hzbot : z ∈ (⊥ : Submodule R M) :=
      (Submodule.colon_eq_top_iff_subset ({z} : Set M)).mp htop (by simp)
    exact hz (by simpa using hzbot)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hItop
  let p : {p : PrimeSpectrum R // p ∈ weaklyAssociatedPrimes R M} :=
    ⟨⟨q, hq.isPrime⟩, ⟨z, hq⟩⟩
  have hzero :
      localizationAtWeaklyAssociatedPrimesMap (R := R) (M := M) z = 0 := by
    dsimp [z]
    rw [map_sub, hxy, sub_self]
  have hcoord := congrFun hzero p
  change LocalizedModule.mkLinearMap
      (@Ideal.primeCompl R _ p.1.asIdeal p.1.2) M z = 0 at hcoord
  obtain ⟨s, hsS, hsz⟩ :=
    (LocalizedModule.mem_ker_mkLinearMap_iff
      (S := @Ideal.primeCompl R _ p.1.asIdeal p.1.2)
      (M := M) (m := z)).mp hcoord
  have hsq : (s : R) ∈ q := by
    apply hq.le
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact hsz
  exact hsS hsq

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
  classical
  let oldAlgS : Algebra R S := inferInstance
  let oldAlgK : Algebra R K := inferInstance
  let oldTower : IsScalarTower R S N := inferInstance
  let oldFrac : @IsLocalization R _ (nonZeroDivisors R) K _ oldAlgK := inferInstance
  have hAlgS : oldAlgS = (algebraMap R S).toAlgebra := by
    exact Algebra.algebra_ext _ _ (fun r => rfl)
  have hAlgK : oldAlgK = (algebraMap R K).toAlgebra := by
    exact Algebra.algebra_ext _ _ (fun r => rfl)
  have hsmulS :
      (@Algebra.toSMul R S _ _ oldAlgS) =
        (@Algebra.toSMul R S _ _ ((algebraMap R S).toAlgebra)) :=
    congrArg (fun a : Algebra R S => @Algebra.toSMul R S _ _ a) hAlgS
  let : Algebra R S := (algebraMap R S).toAlgebra
  let : Algebra R K := (algebraMap R K).toAlgebra
  let : IsScalarTower R S N := hsmulS ▸ oldTower
  let : @IsLocalization R _ (nonZeroDivisors R) K _ ((algebraMap R K).toAlgebra) :=
    hAlgK ▸ oldFrac
  let U : Submonoid R := nonZeroDivisors R
  let V : Submonoid S := Algebra.algebraMapSubmonoid S U
  let : Algebra S (S ⊗[R] K) := Algebra.TensorProduct.leftAlgebra
  let : IsLocalization V (S ⊗[R] K) := by
    change @IsLocalization S _ (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
      (S ⊗[R] K) _ Algebra.TensorProduct.leftAlgebra
    infer_instance
  let Pobj :=
    (ModuleCat.extendScalars (Unit14.baseChangeAlgebraMap
      (algebraMap R S) (algebraMap R K))).obj (ModuleCat.of S N)
  let Bobj :=
    (ModuleCat.restrictScalars (Unit14.baseChangeAlgebraMap
      (algebraMap R S) (algebraMap R K))).obj
      (ModuleCat.of (S ⊗[R] K) (S ⊗[R] K))
  let : AddCommGroup (Pobj : Type _) := Pobj.isAddCommGroup
  let : AddCommMonoid (Pobj : Type _) := Pobj.isAddCommGroup.toAddCommMonoid
  let : Module (S ⊗[R] K) (Pobj : Type _) := Pobj.isModule
  let : Module S (Pobj : Type _) :=
    Module.compHom _ (Algebra.TensorProduct.includeLeftRingHom : S →+* (S ⊗[R] K))
  let : IsScalarTower S (S ⊗[R] K) (Pobj : Type _) :=
    IsScalarTower.of_compHom S (S ⊗[R] K) (Pobj : Type _)
  let Uobj := Bobj
  let : IsScalarTower S (S ⊗[R] K) (Uobj : Type _) :=
    IsScalarTower.of_compHom S (S ⊗[R] K) (Uobj : Type _)
  let eU : (S ⊗[R] K) ≃ₗ[S ⊗[R] K] (Uobj : Type _) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  let eP : TensorProduct S (S ⊗[R] K) N ≃ₗ[S ⊗[R] K] (Pobj : Type _) :=
    TensorProduct.AlgebraTensorModule.congr eU (LinearEquiv.refl S N)
  let : Module (S ⊗[R] K) (TensorProduct S (S ⊗[R] K) N) :=
    TensorProduct.leftModule
  let fstd : N →ₗ[S] TensorProduct S (S ⊗[R] K) N :=
    TensorProduct.mk S (S ⊗[R] K) N 1
  have hfstd : IsLocalizedModule V fstd := by infer_instance
  let ePS : TensorProduct S (S ⊗[R] K) N ≃ₗ[S] (Pobj : Type _) :=
    eP.restrictScalars S
  let fP : N →ₗ[S] (Pobj : Type _) := ePS.toLinearMap.comp fstd
  have hfP : IsLocalizedModule V fP := by infer_instance
  let : Module (S ⊗[R] K) (LocalizedModule V N) :=
    IsLocalizedModule.module V (LocalizedModule.mkLinearMap V N)
  let : IsScalarTower S (S ⊗[R] K) (LocalizedModule V N) :=
    IsLocalizedModule.isScalarTower_module V (LocalizedModule.mkLinearMap V N)
  let eS : LocalizedModule V N ≃ₗ[S] (Pobj : Type _) :=
    IsLocalizedModule.iso V fP
  let eB : LocalizedModule V N ≃ₗ[S ⊗[R] K] (Pobj : Type _) :=
    eS.extendScalarsOfIsLocalization V (S ⊗[R] K)
  have hWAeB :
      weaklyAssociatedPrimes (S ⊗[R] K) (LocalizedModule V N) =
        weaklyAssociatedPrimes (S ⊗[R] K) (Pobj : Type _) := by
    ext p
    constructor
    · intro hp
      change ∃ x : LocalizedModule V N,
        p.asIdeal ∈
          ((⊥ : Submodule (S ⊗[R] K) (LocalizedModule V N)).colon
            ({x} : Set (LocalizedModule V N))).minimalPrimes at hp
      rcases hp with ⟨x, hx⟩
      change ∃ y : (Pobj : Type _),
        p.asIdeal ∈
          ((⊥ : Submodule (S ⊗[R] K) (Pobj : Type _)).colon
            ({y} : Set (Pobj : Type _))).minimalPrimes
      refine ⟨eB x, ?_⟩
      have hcolon :
          ((⊥ : Submodule (S ⊗[R] K) (LocalizedModule V N)).colon
              ({x} : Set (LocalizedModule V N))) =
            ((⊥ : Submodule (S ⊗[R] K) (Pobj : Type _)).colon
              ({eB x} : Set (Pobj : Type _))) := by
        ext b
        simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
        constructor
        · intro h
          rw [← eB.map_smul, h, map_zero]
        · intro h
          apply eB.injective
          rw [eB.map_smul, h, map_zero]
      rw [← hcolon]
      exact hx
    · intro hp
      change ∃ y : (Pobj : Type _),
        p.asIdeal ∈
          ((⊥ : Submodule (S ⊗[R] K) (Pobj : Type _)).colon
            ({y} : Set (Pobj : Type _))).minimalPrimes at hp
      rcases hp with ⟨y, hy⟩
      change ∃ x : LocalizedModule V N,
        p.asIdeal ∈
          ((⊥ : Submodule (S ⊗[R] K) (LocalizedModule V N)).colon
            ({x} : Set (LocalizedModule V N))).minimalPrimes
      refine ⟨eB.symm y, ?_⟩
      have hcolon :
          ((⊥ : Submodule (S ⊗[R] K) (LocalizedModule V N)).colon
              ({eB.symm y} : Set (LocalizedModule V N))) =
            ((⊥ : Submodule (S ⊗[R] K) (Pobj : Type _)).colon
              ({y} : Set (Pobj : Type _))) := by
        ext b
        simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
        constructor
        · intro h
          apply eB.symm.injective
          rw [eB.symm.map_smul, h, map_zero]
        · intro h
          rw [← eB.symm.map_smul, h, map_zero]
      rw [hcolon]
      exact hy
  have hfirstB :
      (letI : Module S (LocalizedModule V N) :=
        Module.compHom (LocalizedModule V N) (algebraMap S (Localization V))
       PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom :
          S →+* S ⊗[R] K) '' weaklyAssociatedPrimes (S ⊗[R] K)
          (LocalizedModule V N) =
        weaklyAssociatedPrimes S (LocalizedModule V N)) := by
    let moduleS : Module S (LocalizedModule V N) := inferInstance
    have hmodule :
        Module.compHom (LocalizedModule V N) (algebraMap S (Localization V)) =
          moduleS := by
      exact Module.ext' _ _ fun s z =>
        IsScalarTower.algebraMap_smul (Localization V) s z
    rw [hmodule]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change ∃ m : LocalizedModule V N,
        q.asIdeal.comap (algebraMap S (S ⊗[R] K)) ∈
          ((⊥ : Submodule S (LocalizedModule V N)).colon
            ({m} : Set (LocalizedModule V N))).minimalPrimes
      change ∃ m : LocalizedModule V N,
        q.asIdeal ∈
          ((⊥ : Submodule (S ⊗[R] K) (LocalizedModule V N)).colon
            ({m} : Set (LocalizedModule V N))).minimalPrimes at hq
      rcases hq with ⟨m, hm⟩
      let I : Ideal S :=
        (⊥ : Submodule S (LocalizedModule V N)).colon ({m} : Set _)
      let J : Ideal (S ⊗[R] K) :=
        (⊥ : Submodule (S ⊗[R] K) (LocalizedModule V N)).colon
          ({m} : Set _)
      have hIJ : I = J.comap (algebraMap S (S ⊗[R] K)) := by
        ext s
        simp only [I, J, Ideal.mem_comap, Submodule.mem_colon_singleton,
          Submodule.mem_bot]
        constructor
        · intro h
          rw [IsScalarTower.algebraMap_smul (S ⊗[R] K) s m]
          exact h
        · intro h
          rw [← IsScalarTower.algebraMap_smul (S ⊗[R] K) s m]
          exact h
      have hpmin : q.asIdeal.comap
          (algebraMap S (S ⊗[R] K)) ∈
            (J.comap (algebraMap S (S ⊗[R] K))).minimalPrimes := by
        rw [IsLocalization.minimalPrimes_comap V (S ⊗[R] K) J]
        exact ⟨q.asIdeal, hm, rfl⟩
      exact ⟨m, by rw [← hIJ] at hpmin; exact hpmin⟩
    · intro hp
      change ∃ m : LocalizedModule V N,
        p.asIdeal ∈
          ((⊥ : Submodule S (LocalizedModule V N)).colon
            ({m} : Set _)).minimalPrimes at hp
      rcases hp with ⟨m, hm⟩
      let I : Ideal S :=
        (⊥ : Submodule S (LocalizedModule V N)).colon ({m} : Set _)
      let J : Ideal (S ⊗[R] K) :=
        (⊥ : Submodule (S ⊗[R] K) (LocalizedModule V N)).colon
          ({m} : Set _)
      have hIJ : I = J.comap (algebraMap S (S ⊗[R] K)) := by
        ext s
        simp only [I, J, Ideal.mem_comap, Submodule.mem_colon_singleton,
          Submodule.mem_bot]
        constructor
        · intro h
          rw [IsScalarTower.algebraMap_smul (S ⊗[R] K) s m]
          exact h
        · intro h
          rw [← IsScalarTower.algebraMap_smul (S ⊗[R] K) s m]
          exact h
      have hpmin : p.asIdeal ∈
          (J.comap (algebraMap S (S ⊗[R] K))).minimalPrimes := by
        rw [← hIJ]
        exact hm
      rw [IsLocalization.minimalPrimes_comap V (S ⊗[R] K) J] at hpmin
      rcases hpmin with ⟨q, hq, hqp⟩
      let q' : PrimeSpectrum (S ⊗[R] K) := ⟨q, hq.isPrime⟩
      refine ⟨q', ?_, ?_⟩
      · exact ⟨m, hq⟩
      · apply PrimeSpectrum.ext
        exact hqp
  have hreg : ∀ s : V, IsSMulRegular N (s : S) := by
    rintro ⟨s, hs⟩
    rcases hs with ⟨r, hr, rfl⟩
    intro x y hxy
    apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := N) hr
    change (algebraMap R S r) • x = (algebraMap R S r) • y at hxy
    rw [IsScalarTower.algebraMap_smul S r x,
      IsScalarTower.algebraMap_smul S r y] at hxy
    exact hxy
  have hSN :
      (letI : Module S (LocalizedModule V N) :=
        Module.compHom (LocalizedModule V N) (algebraMap S (Localization V))
       weaklyAssociatedPrimes S N =
         weaklyAssociatedPrimes S (LocalizedModule V N)) :=
    weaklyAssociatedPrimes_localize_of_regular V hreg
  change PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom :
      S →+* S ⊗[R] K) '' weaklyAssociatedPrimes (S ⊗[R] K) (Pobj : Type _) =
    weaklyAssociatedPrimes S N
  rw [← hWAeB, hfirstB, ← hSN]

private theorem weaklyAssociatedPrimes_linearEquiv
    {A X Y : Type*} [CommRing A] [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] (e : X ≃ₗ[A] Y) (p : PrimeSpectrum A) :
    p ∈ weaklyAssociatedPrimes A X ↔
      p ∈ weaklyAssociatedPrimes A Y := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    have hcolon :
        ((⊥ : Submodule A X).colon ({x} : Set X)) =
          ((⊥ : Submodule A Y).colon ({e x} : Set Y)) := by
      ext a
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      constructor
      · intro h
        rw [← e.map_smul, h, map_zero]
      · intro h
        apply e.injective
        rw [e.map_smul, h, map_zero]
    rw [← hcolon]
    exact hx
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    have hcolon :
        ((⊥ : Submodule A X).colon ({e.symm y} : Set X)) =
          ((⊥ : Submodule A Y).colon ({y} : Set Y)) := by
      ext a
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      constructor
      · intro h
        apply e.symm.injective
        rw [e.symm.map_smul, h, map_zero]
      · intro h
        rw [← e.symm.map_smul, h, map_zero]
    rw [hcolon]
    exact hy

private theorem weaklyAssociatedPrimes_finsupp
    {A X ι : Type*} [CommRing A] [AddCommGroup X] [Module A X]
    (p : PrimeSpectrum A) :
    p ∈ weaklyAssociatedPrimes A (ι →₀ X) →
      p ∈ weaklyAssociatedPrimes A X := by
  classical
  intro hp
  change ∃ z : ι →₀ X,
    p.asIdeal ∈ ((⊥ : Submodule A (ι →₀ X)).colon ({z} : Set (ι →₀ X))).minimalPrimes at hp
  rcases hp with ⟨z, hp⟩
  let I : ι → Ideal A := fun i =>
    (⊥ : Submodule A X).colon ({z i} : Set X)
  have hprod :
      ∀ (s : Finset ι), (∀ i ∈ s, ¬ I i ≤ p.asIdeal) →
        ∃ a : A, a ∉ p.asIdeal ∧ ∀ i ∈ s, a ∈ I i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        have hone : (1 : A) ∉ p.asIdeal := by
          intro h
          exact p.2.ne_top ((Ideal.eq_top_iff_one p.asIdeal).2 h)
        exact ⟨1, hone, by simp⟩
    | @insert i s hi ih =>
        intro hs
        obtain ⟨b, hbI, hbp⟩ := not_subset.mp (hs i (by simp))
        obtain ⟨a, hap, ha⟩ := ih (by
          intro j hj
          exact hs j (by simp [hj]))
        refine ⟨a * b, ?_, ?_⟩
        · intro habp
          exact (p.2.mem_or_mem habp).elim hap hbp
        · intro j hj
          by_cases hji : j = i
          · subst j
            exact (I i).mul_mem_left a hbI
          · exact (I j).mul_mem_right b
              (ha j (by simpa [Finset.mem_insert, hji] using hj))
  have hsome : ∃ i ∈ z.support, I i ≤ p.asIdeal := by
    by_contra hnone
    push Not at hnone
    obtain ⟨a, hap, ha⟩ := hprod z.support hnone
    have hacol :
        a ∈ (⊥ : Submodule A (ι →₀ X)).colon ({z} : Set (ι →₀ X)) := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      ext i
      by_cases hi : i ∈ z.support
      · have hai := ha i hi
        simpa [I, Submodule.mem_colon_singleton, Submodule.mem_bot] using hai
      · have hzi : z i = 0 := by
          by_contra hzi
          exact hi (Finsupp.mem_support_iff.mpr hzi)
        simp [hzi]
    exact hap (hp.1.2 hacol)
  obtain ⟨i, hi, hIp⟩ := hsome
  refine ⟨z i, ?_⟩
  refine ⟨⟨p.2, hIp⟩, ?_⟩
  intro P hP hPle
  have hIP : I i ≤ P := by
    simpa [I] using hP.2
  have hP' : P.IsPrime ∧
      (⊥ : Submodule A (ι →₀ X)).colon ({z} : Set (ι →₀ X)) ≤ P := by
    refine ⟨hP.1, ?_⟩
    intro a ha
    have hai : a • z i = 0 := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
      exact congrArg (fun v : ι →₀ X => v i) ha
    exact hIP (by simpa [I, Submodule.mem_colon_singleton, Submodule.mem_bot] using hai)
  exact hp.2 hP' hPle

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
  classical
  let oldAlgR : Algebra k R := inferInstance
  let oldAlgK : Algebra k K := inferInstance
  have hAlgR : oldAlgR = (algebraMap k R).toAlgebra := by
    exact Algebra.algebra_ext _ _ (fun r => rfl)
  have hAlgK : oldAlgK = (algebraMap k K).toAlgebra := by
    exact Algebra.algebra_ext _ _ (fun r => rfl)
  let : Algebra k R := (algebraMap k R).toAlgebra
  let : Algebra k K := (algebraMap k K).toAlgebra
  let B := R ⊗[k] K
  let Pobj :=
    (ModuleCat.extendScalars (Unit14.baseChangeAlgebraMap
      (algebraMap k R) (algebraMap k K))).obj (ModuleCat.of R M)
  let : AddCommGroup (Pobj : Type _) := Pobj.isAddCommGroup
  let : AddCommMonoid (Pobj : Type _) := Pobj.isAddCommGroup.toAddCommMonoid
  let : Module B (Pobj : Type _) := Pobj.isModule
  change ∀ (q : PrimeSpectrum B) (p : PrimeSpectrum R),
    PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* B) q = p →
      q ∈ weaklyAssociatedPrimes B (Pobj : Type _) →
        p ∈ weaklyAssociatedPrimes R M
  intro q p hpq hq
  let b := Module.Free.chooseBasis k K
  let Bobj :=
    (ModuleCat.restrictScalars (Unit14.baseChangeAlgebraMap
      (algebraMap k R) (algebraMap k K))).obj
      (ModuleCat.of B B)
  let : IsScalarTower R B (Bobj : Type _) :=
    IsScalarTower.of_compHom R B (Bobj : Type _)
  let eU : B ≃ₗ[B] (Bobj : Type _) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  let eP : TensorProduct R B M ≃ₗ[B] (Pobj : Type _) :=
    TensorProduct.AlgebraTensorModule.congr eU (LinearEquiv.refl R M)
  have hqstd : q ∈ weaklyAssociatedPrimes B (TensorProduct R B M) := by
    exact (weaklyAssociatedPrimes_linearEquiv eP q).2 hq
  let eB : B ≃ₗ[R] ((Module.Free.ChooseBasisIndex k K) →₀ R) :=
    Algebra.TensorProduct.equivFinsuppOfBasis R b
  let ePstd : TensorProduct R B M ≃ₗ[R]
      TensorProduct R ((Module.Free.ChooseBasisIndex k K) →₀ R) M :=
    LinearEquiv.rTensor M eB
  let eF : TensorProduct R ((Module.Free.ChooseBasisIndex k K) →₀ R) M ≃ₗ[R]
      ((Module.Free.ChooseBasisIndex k K) →₀ M) :=
    TensorProduct.equivFinsuppOfBasisLeft (Finsupp.basisSingleOne
      (R := R) (ι := Module.Free.ChooseBasisIndex k K))
  let eall : TensorProduct R B M ≃ₗ[R]
      ((Module.Free.ChooseBasisIndex k K) →₀ M) := ePstd.trans eF
  let : Module R (Pobj : Type _) :=
    Module.compHom _ (Algebra.TensorProduct.includeLeftRingHom : R →+* B)
  let : IsScalarTower R B (Pobj : Type _) :=
    IsScalarTower.of_compHom R B (Pobj : Type _)
  let ePR : TensorProduct R B M ≃ₗ[R] (Pobj : Type _) := eP.restrictScalars R
  have hp_of_regular :
      (∀ f : B, f ∉ p.asIdeal.map
          (Algebra.TensorProduct.includeLeftRingHom : R →+* B) →
        IsSMulRegular (Pobj : Type _) f) →
        p ∈ weaklyAssociatedPrimes R (Pobj : Type _) := by
    intro hreg
    change ∃ z : (Pobj : Type _),
      p.asIdeal ∈ ((⊥ : Submodule R (Pobj : Type _)).colon
        ({z} : Set (Pobj : Type _))).minimalPrimes
    change ∃ z : (Pobj : Type _),
      q.asIdeal ∈ ((⊥ : Submodule B (Pobj : Type _)).colon
        ({z} : Set (Pobj : Type _))).minimalPrimes at hq
    rcases hq with ⟨z, hz⟩
    let IR : Ideal R :=
      (⊥ : Submodule R (Pobj : Type _)).colon ({z} : Set (Pobj : Type _))
    let IB : Ideal B :=
      (⊥ : Submodule B (Pobj : Type _)).colon ({z} : Set (Pobj : Type _))
    have hcomap : q.asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B) = p.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg (fun x : PrimeSpectrum R => x.asIdeal) hpq
    have hIRle : IR ≤ p.asIdeal := by
      intro r hr
      have hrB : Algebra.TensorProduct.includeLeftRingHom r ∈ q.asIdeal := by
        apply hz.1.2
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
        change r • z = 0
        simpa [IR, Submodule.mem_colon_singleton, Submodule.mem_bot] using hr
      have : r ∈ q.asIdeal.comap
          (Algebra.TensorProduct.includeLeftRingHom : R →+* B) := hrB
      rw [hcomap] at this
      exact this
    have hpRad : p.asIdeal ≤ IR.radical := by
      intro r hr
      have hrq : Algebra.TensorProduct.includeLeftRingHom r ∈ q.asIdeal := by
        have hr' : r ∈ q.asIdeal.comap
            (Algebra.TensorProduct.includeLeftRingHom : R →+* B) := by
          rw [hcomap]
          exact hr
        exact hr'
      let A := Localization.AtPrime (R := B) q.asIdeal
      have hradloc :
          (IB.map (algebraMap B A)).radical =
            q.asIdeal.map (algebraMap B A) := by
        exact IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
          (R := B) (A := A) q.asIdeal IB (by simpa [IB] using hz)
      have hmul (x : B) (hx : x ∈ q.asIdeal) :
          ∃ n : ℕ, ∃ g : B, g ∉ q.asIdeal ∧ g * x ^ n ∈ IB := by
        have hxloc : algebraMap B A x ∈
            (IB.map (algebraMap B A)).radical := by
          rw [hradloc]
          exact Ideal.mem_map_of_mem (algebraMap B A) hx
        obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxloc
        have hpowloc : algebraMap B A (x ^ n) ∈
            IB.map (algebraMap B A) := by
          simpa only [map_pow] using hn
        obtain ⟨g, hg, hgmul⟩ :=
          (IsLocalization.algebraMap_mem_map_algebraMap_iff
            q.asIdeal.primeCompl A IB (x ^ n)).mp hpowloc
        exact ⟨n, g, by simpa using hg, hgmul⟩
      obtain ⟨n, g, hgq, hgr⟩ := hmul
        (Algebra.TensorProduct.includeLeftRingHom r) hrq
      have hgr0 : (g * (Algebra.TensorProduct.includeLeftRingHom r) ^ n) • z = 0 := by
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hgr
        exact hgr
      have hpow :
          ((Algebra.TensorProduct.includeLeftRingHom : R →+* B) r) ^ n • z = 0 := by
        have hmaple : p.asIdeal.map
            (Algebra.TensorProduct.includeLeftRingHom : R →+* B) ≤ q.asIdeal := by
          rw [Ideal.map_le_iff_le_comap, hcomap]
        have hgmap : g ∉ p.asIdeal.map
            (Algebra.TensorProduct.includeLeftRingHom : R →+* B) := by
          intro hg
          exact hgq (hmaple hg)
        have hreg' := hreg g hgmap
        exact hreg'.right_eq_zero_of_smul (by
          simpa [mul_smul] using hgr0)
      have hpowR : r ^ n • z = 0 := by
        change ((Algebra.TensorProduct.includeLeftRingHom : R →+* B) (r ^ n)) • z = 0
        simpa only [map_pow] using hpow
      exact Ideal.mem_radical_iff.mpr ⟨n, by
        simpa [IR, Submodule.mem_colon_singleton, Submodule.mem_bot] using hpowR⟩
    have hrad : IR.radical = p.asIdeal := le_antisymm
      ((Ideal.IsPrime.radical_le_iff p.2).mpr hIRle) hpRad
    refine ⟨z, ⟨⟨p.2, hIRle⟩, ?_⟩⟩
    intro P hP hPle
    rw [← hrad]
    exact (Ideal.IsPrime.radical_le_iff hP.1).mpr (by simpa [IR] using hP.2)
  sorry
end

end Formalization.Books.Algebra.Unit66
