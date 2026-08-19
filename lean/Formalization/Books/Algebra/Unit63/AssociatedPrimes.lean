import Formalization.Books.Algebra.Unit62
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 63: associated primes

The source uses the exact annihilator definition of an associated prime.  This
file therefore records the source notion on `PrimeSpectrum` points, while the
bridge to Mathlib's `associatedPrimes` is available under Noetherian
hypotheses, where Mathlib's radical-based definition has the same description.
-/

namespace Formalization.Books.Algebra.Unit63

open Set

universe u v

noncomputable section

/-! ## The definition and the support inclusion -/

/-- A prime point is associated to `M` when it is the annihilator of an element
of `M`.  The prime condition is carried by the `PrimeSpectrum` point. -/
def IsAssociatedPrime
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) (M : Type v)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ m : M, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal

/-- The exact-annihilator associated primes of an `R`-module. -/
def associatedPrimes
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] : Set (PrimeSpectrum R) :=
  {p | IsAssociatedPrime p M}

/-- Under Noetherian hypotheses, the source definition agrees with Mathlib's
canonical associated-prime set after forgetting the spectrum-point wrapper. -/
theorem associatedPrimes_toIdeal_eq_mathlib
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    (fun p : PrimeSpectrum R => p.asIdeal) '' associatedPrimes R M =
      _root_.associatedPrimes R M := by
  ext I
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [_root_.AssociatedPrimes.mem_iff, _root_.isAssociatedPrime_iff]
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
    rcases hp with ⟨m, hm⟩
    exact ⟨p.isPrime, m, hm.symm⟩
  · intro hI
    rw [_root_.AssociatedPrimes.mem_iff, _root_.isAssociatedPrime_iff] at hI
    obtain ⟨hprime, m, hm⟩ := hI
    refine ⟨⟨I, hprime⟩, ?_, rfl⟩
    exact ⟨m, hm.symm⟩

/-- Associated primes lie in the support. -/
theorem ass_subset_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    associatedPrimes R M ⊆ Module.support R M := by
  intro p hp
  change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
  obtain ⟨m, hm⟩ := hp
  rw [Module.mem_support_iff']
  refine ⟨m, ?_⟩
  intro r hr hzero
  apply hr
  rw [← hm, Submodule.mem_colon_singleton]
  simp [hzero]

/-! ## Filtrations and finiteness -/

/-- A finite filtration with prime cyclic factors, without imposing finiteness
of the individual stages. -/
structure PrimeFiltration
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] where
  length : ℕ
  stage : Fin (length + 1) → Submodule R M
  prime : Fin length → Ideal R
  zero : stage 0 = ⊥
  top : stage (Fin.last length) = ⊤
  strict_step : ∀ i : Fin length,
    stage (Fin.castSucc i) < stage (Fin.succ i)
  prime_isPrime : ∀ i : Fin length, (prime i).IsPrime
  quotient : ∀ i : Fin length, Nonempty
    (((stage (Fin.succ i)) ⧸
      (stage (Fin.castSucc i)).comap (stage (Fin.succ i)).subtype) ≃ₗ[R]
        (R ⧸ prime i))

private lemma exact_ann_le_primeFiltration_factor
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) (i : Fin F.length) (m : M)
    (hm : m ∈ F.stage (Fin.succ i))
    (hmnot : m ∉ F.stage (Fin.castSucc i))
    (p : PrimeSpectrum R)
    (hp : (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal) :
    p.asIdeal ≤ F.prime i := by
  let N : Submodule R (F.stage (Fin.succ i)) :=
    (F.stage (Fin.castSucc i)).comap (F.stage (Fin.succ i)).subtype
  let x : F.stage (Fin.succ i) := ⟨m, hm⟩
  let q : (F.stage (Fin.succ i) ⧸ N) := N.mkQ x
  have hqne : q ≠ 0 := by
    intro hq
    apply hmnot
    have hxN : x ∈ N := (Submodule.Quotient.mk_eq_zero N).mp hq
    exact hxN
  obtain ⟨e⟩ := F.quotient i
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e q)
  have hsnot : s ∉ F.prime i := by
    intro hs'
    apply hqne
    apply e.injective
    rw [← hs, Ideal.Quotient.eq_zero_iff_mem.mpr hs', e.map_zero]
  intro r hr
  have hrzero : r • m = 0 := by
    rw [← hp, Submodule.mem_colon_singleton] at hr
    simpa using hr
  have hqx : r • q = 0 := by
    change r • (N.mkQ x) = 0
    rw [← N.mkQ.map_smul]
    have hrx : r • x = 0 := by
      ext
      exact hrzero
    rw [hrx, map_zero]
  have hzeroQ : (r : R ⧸ F.prime i) • e q = 0 := by
    exact (e.map_smul r q).symm.trans (by rw [hqx, e.map_zero])
  have hmulQ : Ideal.Quotient.mk (F.prime i) (r * s) = 0 := by
    rw [map_mul]
    rw [← hs] at hzeroQ
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hzeroQ
  exact (F.prime_isPrime i).mem_or_mem
    (Ideal.Quotient.eq_zero_iff_mem.mp hmulQ) |>.resolve_right hsnot

private lemma exact_ann_smul_of_mem_primeFiltration_factor
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) (i : Fin F.length) (m : M)
    (hm : m ∈ F.stage (Fin.succ i))
    (p : PrimeSpectrum R)
    (hp : (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal)
    (f : R) (hf : f ∈ F.prime i) (hfp : f ∉ p.asIdeal) :
    f • m ∈ F.stage (Fin.castSucc i) ∧
      (⊥ : Submodule R M).colon ({f • m} : Set M) = p.asIdeal := by
  let N : Submodule R (F.stage (Fin.succ i)) :=
    (F.stage (Fin.castSucc i)).comap (F.stage (Fin.succ i)).subtype
  let x : F.stage (Fin.succ i) := ⟨m, hm⟩
  let q : (F.stage (Fin.succ i) ⧸ N) := N.mkQ x
  obtain ⟨e⟩ := F.quotient i
  have hqf : f • q = 0 := by
    apply e.injective
    rw [e.map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hf, zero_mul, e.map_zero]
  have hxN : f • x ∈ N := by
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQ (f • x) = 0
    rw [N.mkQ.map_smul, hqf]
  have hfm : f • m ∈ F.stage (Fin.castSucc i) := hxN
  refine ⟨hfm, ?_⟩
  ext r
  rw [Submodule.mem_colon_singleton, ← hp, Submodule.mem_colon_singleton]
  change r • (f • m) = 0 ↔ r • m = 0
  constructor
  · intro h
    have hrf : r * f ∈ p.asIdeal := by
      rw [← hp, Submodule.mem_colon_singleton]
      simpa [smul_smul, mul_comm] using h
    have hrp : r ∈ p.asIdeal :=
      (p.isPrime.mem_or_mem hrf).resolve_right hfp
    rw [← hp, Submodule.mem_colon_singleton] at hrp
    simpa using hrp
  · intro h
    simpa [smul_smul, mul_comm] using congrArg (fun z : M => f • z) h

/-- A prime filtration bounds the associated-prime set by its factors. -/
theorem ass_subset_primeFiltration
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (F : PrimeFiltration R M) :
    associatedPrimes R M ⊆
      {p : PrimeSpectrum R | p.asIdeal ∈ Set.range F.prime} := by
  intro p hp
  change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
  obtain ⟨m, hm⟩ := hp
  have hdesc : ∀ (j : ℕ) (hj : j ≤ F.length) (m : M),
      m ∈ F.stage ⟨j, Nat.lt_succ_of_le hj⟩ →
      (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal →
      p.asIdeal ∈ Set.range F.prime := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hj m hmj hmann
        by_cases hjzero : j = 0
        · subst j
          have hmzero : m = 0 := by
            simpa [F.zero] using hmj
          have htop : p.asIdeal = ⊤ := by
            rw [← hmann]
            simp [hmzero]
          exact (p.isPrime.ne_top htop).elim
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjzero
          let i : Fin F.length :=
            ⟨j, Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj⟩
          have hmj' : m ∈ F.stage (Fin.succ i) := hmj
          by_cases hm_prev : m ∈ F.stage (Fin.castSucc i)
          · exact ih j (Nat.lt_succ_self j)
              (Nat.le_trans (Nat.le_succ j) hj) m hm_prev hmann
          · have hle : p.asIdeal ≤ F.prime i :=
              exact_ann_le_primeFiltration_factor F i m hmj' hm_prev p hmann
            by_cases heq : p.asIdeal = F.prime i
            · exact ⟨i, heq.symm⟩
            · have hnot : ¬ F.prime i ≤ p.asIdeal := by
                intro hle'
                exact heq (le_antisymm hle hle')
              obtain ⟨f, hf, hfp⟩ := SetLike.not_le_iff_exists.mp hnot
              obtain ⟨hfm, hmannfm⟩ :=
                exact_ann_smul_of_mem_primeFiltration_factor
                  F i m hmj' p hmann f hf hfp
              exact ih j (Nat.lt_succ_self j)
                (Nat.le_trans (Nat.le_succ j) hj) (f • m) hfm hmannfm
  apply hdesc F.length le_rfl m
  · change m ∈ F.stage (Fin.last F.length)
    rw [F.top]
    trivial
  · exact hm

/-- The minimal points of a subset of the spectrum. -/
def minimalPoints {R : Type u} [CommRing R]
    (s : Set (PrimeSpectrum R)) : Set (PrimeSpectrum R) :=
  {p | p ∈ s ∧ Minimal (fun q : PrimeSpectrum R => q ∈ s) p}

/-- For a finite module over a Noetherian ring, the associated-prime set is
finite. -/
theorem finite_ass
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] :
    (associatedPrimes R M).Finite := by
  apply Set.Finite.of_finite_image (f := fun p : PrimeSpectrum R => p.asIdeal)
  · rw [associatedPrimes_toIdeal_eq_mathlib]
    exact _root_.associatedPrimes.finite R M
  · intro p hp q hq heq
    exact PrimeSpectrum.ext heq

/-- The minimal primes in the support, in the associated-prime set, and among
the factors of any prime filtration coincide. -/
theorem minimal_primes_associated_primes
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (F : PrimeFiltration R M) :
    minimalPoints (Module.support R M) =
        minimalPoints (associatedPrimes R M) ∧
      minimalPoints (associatedPrimes R M) =
        minimalPoints {p : PrimeSpectrum R |
          p.asIdeal ∈ Set.range F.prime} := by
  have exists_min_support_le :
      ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
        ∃ q : PrimeSpectrum R,
          q ∈ Module.support R M ∧
            Minimal (fun x : PrimeSpectrum R => x ∈ Module.support R M) q ∧
              q ≤ p := by
    intro p hp
    have hpann : Module.annihilator R M ≤ p.asIdeal :=
      Module.annihilator_le_of_mem_support hp
    obtain ⟨qI, hqI, hqle⟩ := Ideal.exists_minimalPrimes_le hpann
    let q : PrimeSpectrum R := ⟨qI, hqI.isPrime⟩
    have hqmem : q ∈ Module.support R M :=
      Module.mem_support_iff_of_finite.mpr hqI.le
    have hqmin :
        Minimal (fun x : PrimeSpectrum R => x ∈ Module.support R M) q := by
      refine ⟨hqmem, ?_⟩
      intro r hr hrq
      exact hqI.2
        ⟨r.isPrime, Module.annihilator_le_of_mem_support hr⟩ hrq
    exact ⟨q, hqmem, hqmin, hqle⟩

  have minimal_support_mem_associated :
      ∀ p : PrimeSpectrum R,
        p ∈ Module.support R M →
        Minimal (fun x : PrimeSpectrum R => x ∈ Module.support R M) p →
        p ∈ associatedPrimes R M := by
    intro p hp hminimal
    have hpann : Module.annihilator R M ≤ p.asIdeal :=
      Module.mem_support_iff_of_finite.mp hp
    have hpminann :
        p.asIdeal ∈ (Module.annihilator R M).minimalPrimes := by
      refine ⟨⟨p.isPrime, hpann⟩, ?_⟩
      intro q hq hqp
      let q' : PrimeSpectrum R := ⟨q, hq.1⟩
      have hqmem : q' ∈ Module.support R M :=
        Module.mem_support_iff_of_finite.mpr hq.2
      exact hminimal.2 hqmem hqp
    have hroot : p.asIdeal ∈ _root_.associatedPrimes R M :=
      Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        R M hpminann
    rw [_root_.AssociatedPrimes.mem_iff, _root_.isAssociatedPrime_iff] at hroot
    obtain ⟨hprime, m, hm⟩ := hroot
    exact ⟨m, hm.symm⟩

  have hsupport_factor :
      {p : PrimeSpectrum R | p.asIdeal ∈ Set.range F.prime} ⊆
        Module.support R M := by
    rintro p ⟨i, hi⟩
    have hp : p = (⟨F.prime i, F.prime_isPrime i⟩ : PrimeSpectrum R) :=
      PrimeSpectrum.ext hi.symm
    subst p
    let N : Submodule R (F.stage (Fin.succ i)) :=
      (F.stage (Fin.castSucc i)).comap (F.stage (Fin.succ i)).subtype
    obtain ⟨e⟩ := F.quotient i
    have hq :
        (⟨F.prime i, F.prime_isPrime i⟩ : PrimeSpectrum R) ∈
          Module.support R (F.stage (Fin.succ i) ⧸ N) := by
      rw [Module.mem_support_iff']
      refine ⟨e.symm 1, ?_⟩
      intro r hr hzero
      apply hr
      have hzero' : r • (1 : R ⧸ F.prime i) = 0 := by
        calc
          r • (1 : R ⧸ F.prime i) = e (r • e.symm 1) := by
            rw [e.map_smul, e.apply_symm_apply]
          _ = e 0 := by rw [hzero]
          _ = 0 := e.map_zero
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hzero')
    have hstage :
        (⟨F.prime i, F.prime_isPrime i⟩ : PrimeSpectrum R) ∈
          Module.support R (F.stage (Fin.succ i)) :=
      Module.support_subset_of_surjective (Submodule.mkQ N)
        (Submodule.mkQ_surjective N) hq
    exact Module.support_subset_of_injective
      (F.stage (Fin.succ i)).subtype Subtype.val_injective hstage

  have hass_support :
      minimalPoints (Module.support R M) ⊆
        minimalPoints (associatedPrimes R M) := by
    intro p hp
    have hpass : p ∈ associatedPrimes R M :=
      minimal_support_mem_associated p hp.1 hp.2
    refine ⟨hpass, ⟨hpass, ?_⟩⟩
    intro q hq hqp
    exact hp.2.2 (ass_subset_support hq) hqp

  have hsupport_ass :
      minimalPoints (associatedPrimes R M) ⊆
        minimalPoints (Module.support R M) := by
    intro p hp
    obtain ⟨q, hq, hqmin, hqp⟩ :=
      exists_min_support_le p (ass_subset_support hp.1)
    have hqass : q ∈ associatedPrimes R M :=
      minimal_support_mem_associated q hq hqmin
    have hpq : p ≤ q := hp.2.2 hqass hqp
    have hqp' : q = p := le_antisymm hqp hpq
    subst p
    exact ⟨hq, hqmin⟩

  have hass_factor :
      minimalPoints (associatedPrimes R M) ⊆
        minimalPoints {p : PrimeSpectrum R |
          p.asIdeal ∈ Set.range F.prime} := by
    intro p hp
    have hpfactor : p ∈ {p : PrimeSpectrum R |
        p.asIdeal ∈ Set.range F.prime} :=
      ass_subset_primeFiltration F hp.1
    refine ⟨hpfactor, ⟨hpfactor, ?_⟩⟩
    intro q hq hqp
    obtain ⟨r, hr, hrmin, hrq⟩ :=
      exists_min_support_le q (hsupport_factor hq)
    have hrass : r ∈ associatedPrimes R M :=
      minimal_support_mem_associated r hr hrmin
    exact (hp.2.2 hrass (hrq.trans hqp)).trans hrq

  have hfactor_ass :
      minimalPoints {p : PrimeSpectrum R |
          p.asIdeal ∈ Set.range F.prime} ⊆
        minimalPoints (associatedPrimes R M) := by
    intro p hp
    obtain ⟨q, hq, hqmin, hqp⟩ :=
      exists_min_support_le p (hsupport_factor hp.1)
    have hqass : q ∈ associatedPrimes R M :=
      minimal_support_mem_associated q hq hqmin
    have hqfactor : q ∈ {p : PrimeSpectrum R |
        p.asIdeal ∈ Set.range F.prime} :=
      ass_subset_primeFiltration F hqass
    have hpq : p ≤ q := hp.2.2 hqfactor hqp
    have hqp' : q = p := le_antisymm hqp hpq
    subst p
    refine ⟨hqass, ⟨hqass, ?_⟩⟩
    intro r hr hrp
    exact hqmin.2 (ass_subset_support hr) hrp

  exact ⟨Set.Subset.antisymm hass_support hsupport_ass,
    Set.Subset.antisymm hass_factor hfactor_ass⟩

/-! ## Exact sequences, zero modules, and zerodivisors -/

/-- The two associated-prime inclusions for a short exact sequence. -/
theorem ass_subset_ass_of_short_exact
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    associatedPrimes R M' ⊆ associatedPrimes R M ∧
      associatedPrimes R M ⊆
        associatedPrimes R M' ∪ associatedPrimes R M'' := by
  have _hg : Function.Surjective g := hg
  constructor
  · intro p hp
    change ∃ m, (⊥ : Submodule R M').colon ({m} : Set M') = p.asIdeal at hp
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal
    obtain ⟨m, hm⟩ := hp
    refine ⟨f m, ?_⟩
    ext r
    rw [Submodule.mem_colon_singleton, ← hm, Submodule.mem_colon_singleton]
    change r • f m = 0 ↔ r • m = 0
    constructor
    · intro hr
      apply hf
      rw [map_smul, hr, map_zero]
    · intro hr
      rw [← map_smul, hr, map_zero]
  · intro p hp
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
    obtain ⟨m, hm⟩ := hp
    by_cases h : ∃ a ∈ p.asIdeal.primeCompl, ∃ y : M', ∃ k, f y = a ^ k • m
    · obtain ⟨a, ha, y, k, hy⟩ := h
      left
      refine ⟨y, ?_⟩
      ext b
      rw [Submodule.mem_colon_singleton, ← hm, Submodule.mem_colon_singleton]
      change b • y = 0 ↔ b • m = 0
      have ha' : a ∉ p.asIdeal := by simpa using ha
      have hpow : a ^ k ∉ p.asIdeal := by
        intro hak
        exact ha' (p.isPrime.mem_of_pow_mem k hak)
      constructor
      · intro hby
        have hba : b * a ^ k ∈ p.asIdeal := by
          rw [← hm, Submodule.mem_colon_singleton]
          rw [← smul_smul, ← hy, ← map_smul, hby, map_zero]
          simp
        have hb : b ∈ p.asIdeal :=
          (p.isPrime.mem_or_mem hba).resolve_right hpow
        rw [← hm, Submodule.mem_colon_singleton] at hb
        simpa using hb
      · intro hbm
        apply hf
        calc
          f (b • y) = b • f y := map_smul f b y
          _ = b • (a ^ k • m) := by rw [hy]
          _ = a ^ k • (b • m) := by rw [smul_smul, smul_smul, mul_comm]
          _ = 0 := by rw [hbm, smul_zero]
          _ = f 0 := (map_zero f).symm
    · right
      refine ⟨g m, ?_⟩
      ext b
      rw [Submodule.mem_colon_singleton, ← hm, Submodule.mem_colon_singleton]
      change b • g m = 0 ↔ b • m = 0
      constructor
      · intro hbg
        have hbker : b • m ∈ LinearMap.ker g := by
          rw [← map_smul] at hbg
          rw [LinearMap.mem_ker]
          exact hbg
        rw [hfg.linearMap_ker_eq] at hbker
        obtain ⟨y, hy⟩ := hbker
        have hb : b ∈ p.asIdeal := by
          by_contra hb'
          apply h
          refine ⟨b, ?_, y, 1, ?_⟩
          simpa using hb'
          simpa [pow_one] using hy
        rw [← hm, Submodule.mem_colon_singleton] at hb
        simpa using hb
      · intro hbm
        rw [← map_smul, hbm, map_zero]

/-- The associated-prime set of a binary direct sum, represented by the
product module `M' × M''`. -/
theorem ass_prod
    {R : Type u} {M' M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M''] :
    associatedPrimes R (M' × M'') =
      associatedPrimes R M' ∪ associatedPrimes R M'' := by
  let h₁ := ass_subset_ass_of_short_exact
    (f := LinearMap.inl R M' M'') (g := LinearMap.snd R M' M'')
    LinearMap.inl_injective (fun z => ⟨(0, z), rfl⟩) Function.Exact.inl_snd
  let h₂ := ass_subset_ass_of_short_exact
    (f := LinearMap.inr R M' M'') (g := LinearMap.fst R M' M'')
    LinearMap.inr_injective (fun z => ⟨(z, 0), rfl⟩) Function.Exact.inr_fst
  exact h₁.2.antisymm (Set.union_subset_iff.2 ⟨h₁.1, h₂.1⟩)

/-- Over a Noetherian ring, a module is zero exactly when it has no associated
prime. -/
theorem ass_eq_empty_iff_subsingleton
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    Subsingleton M ↔ associatedPrimes R M = ∅ := by
  constructor
  · intro hM
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hp
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
    obtain ⟨m, hm⟩ := hp
    have hm0 : m = 0 := Subsingleton.elim _ _
    have htop : (⊥ : Submodule R M).colon ({m} : Set M) = ⊤ := by
      rw [Submodule.colon_eq_top_iff_subset]
      simp [hm0]
    exact p.isPrime.ne_top (by rw [← hm, htop])
  · intro h
    classical
    by_contra hM
    have hnontrivial : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    obtain ⟨I, hI⟩ := _root_.associatedPrimes.nonempty R M
    rw [_root_.AssociatedPrimes.mem_iff, _root_.isAssociatedPrime_iff] at hI
    obtain ⟨hprime, m, hm⟩ := hI
    let p : PrimeSpectrum R := ⟨I, hprime⟩
    have hp : p ∈ associatedPrimes R M := ⟨m, hm.symm⟩
    rw [h] at hp
    exact Set.notMem_empty p hp

/-- Every minimal point of the support of a module over a Noetherian ring is
associated. -/
theorem ass_of_minimal_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hminimal : Minimal (fun q : PrimeSpectrum R => q ∈ Module.support R M) p) :
    p ∈ associatedPrimes R M := by
  sorry

/-- The union of the associated primes is the set of module zerodivisors. -/
theorem iUnion_associatedPrimes_eq_module_zeroDivisors
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    (⋃ p : {p : PrimeSpectrum R // p ∈ associatedPrimes R M},
        (p.1.asIdeal : Set R)) =
      {x : R | ∃ m : M, m ≠ 0 ∧ x • m = 0} := by
  sorry

/-! ## One equation -/

/-- The quotient `M/fM`, written using the canonical ideal action on a
submodule. -/
abbrev quotientByElement
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) : Type v :=
  M ⧸ (Ideal.span ({f} : Set R) • (⊤ : Submodule R M))

/-- The support-dimension inequalities for one equation, together with the
minimal-support and regular-element criteria for equality. -/
theorem one_equation_module
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (f : R)
    (hf : f ∈ IsLocalRing.maximalIdeal R) :
    Module.supportDim R (quotientByElement R M f) ≤ Module.supportDim R M ∧
      Module.supportDim R M ≤
        Module.supportDim R (quotientByElement R M f) + 1 ∧
      ((∀ p : PrimeSpectrum R,
          p ∈ minimalPoints (Module.support R M) → f ∉ p.asIdeal) →
        Module.supportDim R M =
          Module.supportDim R (quotientByElement R M f) + 1) ∧
      (IsSMulRegular M f →
        ∀ p : PrimeSpectrum R,
          p ∈ minimalPoints (Module.support R M) → f ∉ p.asIdeal) := by
  sorry

/-! ## Functoriality -/

/-- Associated primes map forward along the map on spectra induced by a ring
map.  The `R`-module structure is the one induced from the `S`-module by the
ring map. -/
theorem ass_functorial
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] (φ : R →+* S) [Module S M] :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ '' associatedPrimes S M ⊆
        associatedPrimes R M) := by
  sorry

/-! ### The reverse-inclusion example -/

/-- The polynomial relation ideal generated by the squares of all variables. -/
def reverseFunctorialityExampleIdeal (k : Type u) [Field k] :
    Ideal (MvPolynomial ℕ k) :=
  Ideal.span (Set.range fun i : ℕ =>
    (MvPolynomial.X i : MvPolynomial ℕ k) ^ 2)

/-- The infinitely generated square-zero-variable quotient used in the source
as a counterexample to reverse functoriality. -/
abbrev reverseFunctorialityExampleRing (k : Type u) [Field k] :=
  MvPolynomial ℕ k ⧸ reverseFunctorialityExampleIdeal k

/-- The displayed example has associated primes over the base field but none
over the quotient ring itself, so the reverse inclusion fails. -/
theorem ass_reverse_functoriality_example
    (k : Type u) [Field k] :
    (associatedPrimes k (reverseFunctorialityExampleRing k)).Nonempty ∧
      associatedPrimes (reverseFunctorialityExampleRing k)
          (reverseFunctorialityExampleRing k) = ∅ ∧
      ¬ (associatedPrimes k (reverseFunctorialityExampleRing k) ⊆
        PrimeSpectrum.comap (algebraMap k (reverseFunctorialityExampleRing k)) ''
          associatedPrimes (reverseFunctorialityExampleRing k)
            (reverseFunctorialityExampleRing k)) := by
  sorry

/-- If the target ring is Noetherian, the functoriality inclusion is an
equality. -/
theorem ass_functorial_eq_of_noetherian
    {R S M : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing S] [AddCommGroup M]
    (φ : R →+* S) [Module S M] :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ '' associatedPrimes S M =
        associatedPrimes R M) := by
  sorry

/-! ## Quotients and localization -/

/-- Passing from `R` to `R/I` preserves associated primes via the canonical
injection of spectra. -/
theorem ass_quotient_ring
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module (R ⧸ I) M] :
    (letI : Module R M := Module.compHom M (Ideal.Quotient.mk I);
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ''
          associatedPrimes (R ⧸ I) M = associatedPrimes R M) := by
  sorry

/-- Localization sends an associated prime to the closed point of the
localized module.  If the prime is finitely generated, the converse holds. -/
theorem associated_primes_localize_at_prime
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    (p ∈ associatedPrimes R M →
      IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) ∈
        associatedPrimes (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) ∧
      (p.asIdeal.FG →
        (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) ∈
            associatedPrimes (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M) →
          p ∈ associatedPrimes R M)) := by
  sorry

/-- The associated-prime set of a localized module, viewed over the localized
ring, maps to the associated-prime set viewed over the original ring. -/
theorem ass_localize_eq_over_localization
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      PrimeSpectrum.comap (algebraMap R (Localization S)) ''
          associatedPrimes (Localization S) (LocalizedModule S M) =
        associatedPrimes R (LocalizedModule S M)) := by
  sorry

/-- Associated primes of a module that survive in the localization remain
associated after localization. -/
theorem ass_localize_subset
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      associatedPrimes R M ∩
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) ⊆
        associatedPrimes R (LocalizedModule S M)) := by
  sorry

/-- For a Noetherian ring, the preceding localization inclusion is an
equality. -/
theorem ass_localize_eq_of_noetherian
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] (S : Submonoid R) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      associatedPrimes R M ∩
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
        associatedPrimes R (LocalizedModule S M)) := by
  sorry

/-- If every element of the multiplicative set is regular on `M`, localization
does not change the associated-prime set over `R`. -/
theorem ass_localize_eq_of_regular
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R)
    (hS : ∀ s : S, IsSMulRegular M (s : R)) :
    (letI : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S));
      associatedPrimes R M = associatedPrimes R (LocalizedModule S M)) := by
  sorry

/-! ## Regular elements and detection at associated primes -/

/-- An ideal contained in the maximal ideal contains a module nonzerodivisor
exactly when it is contained in no associated prime. -/
theorem ideal_contains_regular_iff
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    (∃ x : R, x ∈ I ∧ IsSMulRegular M x) ↔
      ∀ q : PrimeSpectrum R, q ∈ associatedPrimes R M → ¬ I ≤ q.asIdeal := by
  sorry

/-- The canonical map from a module to the product of its localizations at
its associated primes. -/
def localizationAtAssociatedPrimesMap
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    M →ₗ[R]
      ∀ p : {p : PrimeSpectrum R // p ∈ associatedPrimes R M},
        LocalizedModule.AtPrime p.1.asIdeal M :=
  LinearMap.pi fun p =>
    LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl M

/-- Over a Noetherian ring, the associated-prime localizations detect every
module element. -/
theorem localizationAtAssociatedPrimesMap_injective
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    Function.Injective (localizationAtAssociatedPrimesMap (R := R) (M := M)) := by
  sorry

/-! ## A dimension-one auxiliary statement -/

/-- A positive-dimensional finite-type algebra over a field has a regular
nonunit. -/
theorem exists_nonzerodivisor_nonunit_of_finiteType_of_positive_dimension
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S]
    (hdim : 0 < ringKrullDim S) :
    ∃ f : S, f ∈ nonZeroDivisors S ∧ ¬ IsUnit f := by
  sorry

end

end Formalization.Books.Algebra.Unit63
