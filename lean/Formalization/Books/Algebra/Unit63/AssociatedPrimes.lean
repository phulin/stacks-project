import Formalization.Books.Algebra.Unit62
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Commutative Algebra, Chapter 63: associated primes

The source uses the exact annihilator definition of an associated prime.  This
file therefore records the source notion on `PrimeSpectrum` points, while the
bridge to Mathlib's `associatedPrimes` is available under Noetherian
hypotheses, where Mathlib's radical-based definition has the same description.
-/

namespace Formalization.Books.Algebra.Unit63

open Set
open scoped Pointwise

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
  classical
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hp
  let N : Submodule R M := R ∙ m
  have hmpN : p ∈ Module.support R N := by
    rw [Module.mem_support_iff']
    refine ⟨⟨m, Submodule.mem_span_singleton_self m⟩, ?_⟩
    intro r hr hzero
    apply hm r hr
    exact congrArg Subtype.val hzero
  have hpann : Module.annihilator R N ≤ p.asIdeal :=
    Module.annihilator_le_of_mem_support hmpN
  obtain ⟨qI, hqI, hqle⟩ := Ideal.exists_minimalPrimes_le hpann
  let q : PrimeSpectrum R := ⟨qI, hqI.1.1⟩
  have hqN : q ∈ Module.support R N :=
    Module.mem_support_iff_of_finite.mpr hqI.1.2
  have hqM : q ∈ Module.support R M :=
    Module.support_subset_of_injective N.subtype N.subtype_injective hqN
  have hqass : qI ∈ _root_.associatedPrimes R N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      R N hqI
  rw [_root_.AssociatedPrimes.mem_iff, _root_.isAssociatedPrime_iff] at hqass
  obtain ⟨_, n, hn⟩ := hqass
  have hqp : q ≤ p := hqle
  have hpq : p ≤ q := hminimal.2 hqM hqp
  have hqeq : q = p := le_antisymm hqp hpq
  rw [← hqeq]
  refine ⟨n.1, ?_⟩
  ext r
  rw [Submodule.mem_colon_singleton]
  change r • (n : M) = 0 ↔ r ∈ qI
  rw [hn, Submodule.mem_colon_singleton]
  change r • (n : M) = 0 ↔ r • n = 0
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg Subtype.val h

/-- The union of the associated primes is the set of module zerodivisors. -/
theorem iUnion_associatedPrimes_eq_module_zeroDivisors
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] :
    (⋃ p : {p : PrimeSpectrum R // p ∈ associatedPrimes R M},
        (p.1.asIdeal : Set R)) =
      {x : R | ∃ m : M, m ≠ 0 ∧ x • m = 0} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    have hp := p.2
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.1.asIdeal at hp
    obtain ⟨m, hm⟩ := hp
    refine ⟨m, ?_, ?_⟩
    · intro hm0
      apply p.1.isPrime.ne_top
      rw [← hm, Submodule.colon_eq_top_iff_subset]
      simp [hm0]
    · have hxp' : x ∈ p.1.asIdeal := hxp
      rw [← hm] at hxp'
      simpa [Submodule.mem_colon_singleton] using hxp'
  · rintro ⟨m, hm, hxm⟩
    let K : Submodule R M :=
      { carrier := {y | x • y = 0}
        zero_mem' := by simp
        add_mem' := by
          intro y z hy hz
          change x • y = 0 at hy
          change x • z = 0 at hz
          change x • (y + z) = 0
          rw [smul_add, hy, hz, add_zero]
        smul_mem' := by
          intro r y hy
          change x • y = 0 at hy
          change x • (r • y) = 0
          rw [smul_smul, mul_comm, ← smul_smul, hy, smul_zero] }
    have hKnontrivial : Nontrivial K := by
      refine ⟨⟨m, hxm⟩, 0, ?_⟩
      intro heq
      apply hm
      exact congrArg Subtype.val heq
    obtain ⟨I, hI⟩ :=
      @_root_.associatedPrimes.nonempty R _ K _ _ _ hKnontrivial
    rw [_root_.AssociatedPrimes.mem_iff, _root_.isAssociatedPrime_iff] at hI
    obtain ⟨hprime, n, hn⟩ := hI
    let q : PrimeSpectrum R := ⟨I, hprime⟩
    have hnM : (⊥ : Submodule R M).colon ({(n : M)} : Set M) = q.asIdeal := by
      ext r
      rw [Submodule.mem_colon_singleton]
      change r • (n : M) = 0 ↔ r ∈ I
      rw [hn, Submodule.mem_colon_singleton]
      change r • (n : M) = 0 ↔ r • n = 0
      constructor
      · intro h
        apply Subtype.ext
        exact h
      · intro h
        exact congrArg Subtype.val h
    apply Set.mem_iUnion.mpr
    refine ⟨⟨q, ?_⟩, ?_⟩
    · change IsAssociatedPrime q M
      exact ⟨n.1, hnM⟩
    · rw [← hnM]
      have hnK : x • (n : M) = 0 := by
        exact n.property
      have hz : x • (n : M) ∈ (⊥ : Submodule R M) := by
        simpa using hnK
      have hx' : x ∈ (⊥ : Submodule R M).colon ({(n : M)} : Set M) := by
        rw [Submodule.mem_colon_singleton]
        exact hz
      exact hx'

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
  have e :
      quotientByElement R M f ≃ₗ[R] QuotSMulTop f M :=
    Submodule.quotEquivOfEq
      (Ideal.span ({f} : Set R) • (⊤ : Submodule R M))
      (f • (⊤ : Submodule R M))
      (Submodule.ideal_span_singleton_smul f (⊤ : Submodule R M))
  have hdimEq :
      Module.supportDim R (quotientByElement R M f) =
        Module.supportDim R (QuotSMulTop f M) :=
    Module.supportDim_eq_of_equiv e
  have hsecondQ :
      Module.supportDim R M ≤ Module.supportDim R (QuotSMulTop f M) + 1 :=
    Module.supportDim_le_supportDim_quotSMulTop_succ hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Module.supportDim_le_of_surjective
    exact Submodule.mkQ_surjective _
  · rw [hdimEq]
    exact hsecondQ
  · intro hmin
    have hnot :
        ∀ q ∈ (Module.annihilator R M).minimalPrimes, f ∉ q := by
      intro q hq
      let p : PrimeSpectrum R := ⟨q, hq.1.1⟩
      have hp : p ∈ Module.support R M :=
        Module.mem_support_iff_of_finite.mpr hq.1.2
      have hpmin :
          Minimal (fun r : PrimeSpectrum R => r ∈ Module.support R M) p := by
        refine ⟨hp, ?_⟩
        intro r hr hrp
        exact hq.2
          ⟨r.isPrime, Module.annihilator_le_of_mem_support hr⟩ hrp
      exact hmin p ⟨hp, hpmin⟩
    have heqQ :
        Module.supportDim R (QuotSMulTop f M) + 1 =
          Module.supportDim R M :=
      Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
        hnot hf
    rw [← hdimEq] at heqQ
    exact heqQ.symm
  · intro hreg p hp
    have hass := ass_of_minimal_support p hp.1 hp.2
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hass
    obtain ⟨m, hm⟩ := hass
    intro hfp
    have hfm : f ∈ (⊥ : Submodule R M).colon ({m} : Set M) := by
      rw [hm]
      exact hfp
    have hzero : f • m = 0 := by
      rw [Submodule.mem_colon_singleton] at hfm
      simpa using hfm
    have hmne : m ≠ 0 := by
      intro hm0
      apply p.isPrime.ne_top
      rw [← hm, Submodule.colon_eq_top_iff_subset]
      simp [hm0]
    exact hmne (hreg (by simpa using hzero))

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
  change
    PrimeSpectrum.comap φ ''
        (@associatedPrimes S M _ _ inferInstance) ⊆
      (@associatedPrimes R M _ _ (Module.compHom M φ))
  intro p hp
  obtain ⟨q, hq, hqp⟩ := hp
  subst p
  change ∃ m,
    (@Submodule.colon R M _ _ (Module.compHom M φ)
      (⊥ : @Submodule R M _ _ (Module.compHom M φ)) ({m} : Set M)) =
        (PrimeSpectrum.comap φ q).asIdeal
  change ∃ m, (⊥ : Submodule S M).colon ({m} : Set M) = q.asIdeal at hq
  obtain ⟨m, hm⟩ := hq
  refine ⟨m, ?_⟩
  ext r
  rw [@Submodule.mem_colon_singleton R M _ _ (Module.compHom M φ)]
  change φ r • m = 0 ↔ r ∈ (PrimeSpectrum.comap φ q).asIdeal
  change φ r • m = 0 ↔ φ r ∈ q.asIdeal
  rw [← hm, Submodule.mem_colon_singleton]
  rfl

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
  classical
  let Q := reverseFunctorialityExampleRing k
  let P := MvPolynomial ℕ k
  let I := reverseFunctorialityExampleIdeal k
  have hgen :
      (Set.range (fun i : ℕ => (MvPolynomial.X i : P) ^ 2)) =
        (fun d : ℕ →₀ ℕ => MvPolynomial.monomial d (1 : k)) ''
          Set.range (fun i : ℕ => Finsupp.single i 2) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨Finsupp.single i 2, ⟨i, rfl⟩, ?_⟩
      exact (MvPolynomial.X_pow_eq_monomial (R := k) (σ := ℕ) (e := 2) (n := i)).symm
    · rintro ⟨d, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, MvPolynomial.X_pow_eq_monomial (R := k) (σ := ℕ) (e := 2) (n := i)⟩
  have hIcrit (f : P) :
      f ∈ I ↔ ∀ d ∈ f.support, ∃ i : ℕ, Finsupp.single i 2 ≤ d := by
    change f ∈ Ideal.span (Set.range (fun i : ℕ => (MvPolynomial.X i : P) ^ 2)) ↔ _
    rw [hgen, MvPolynomial.mem_ideal_span_monomial_image]
    simp only [Set.mem_range]
    constructor
    · intro h d hd
      obtain ⟨si, ⟨i, rfl⟩, hsi⟩ := h d hd
      exact ⟨i, hsi⟩
    · intro h d hd
      obtain ⟨i, hi⟩ := h d hd
      exact ⟨Finsupp.single i 2, ⟨i, rfl⟩, hi⟩
  have hQnontrivial : Nontrivial Q := by
    let hev : MvPolynomial ℕ k →+* k :=
      MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ℕ => 0)
    have hIker : I ≤ RingHom.ker hev := by
      change reverseFunctorialityExampleIdeal k ≤ RingHom.ker hev
      rw [reverseFunctorialityExampleIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change (MvPolynomial.X i : P) ^ 2 ∈ RingHom.ker hev
      change hev ((MvPolynomial.X i : P) ^ 2) = 0
      change MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ℕ => 0)
        ((MvPolynomial.X i : P) ^ 2) = 0
      simp
    refine ⟨1, 0, ?_⟩
    intro hzero
    have hmem : (1 : P) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have : hev 1 = 0 := hIker hmem
    simpa using this
  have hnonempty : (associatedPrimes k Q).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro h
    have hsub : Subsingleton Q :=
      (ass_eq_empty_iff_subsingleton (R := k) (M := Q)).mpr h
    exact not_subsingleton_iff_nontrivial.mpr hQnontrivial hsub
  have hQempty : associatedPrimes Q Q = ∅ := by
    ext p
    constructor
    · intro hp
      change ∃ m, (⊥ : Submodule Q Q).colon ({m} : Set Q) = p.asIdeal at hp
      obtain ⟨m, hm⟩ := hp
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective m
      have hxi (i : ℕ) :
          Ideal.Quotient.mk I (MvPolynomial.X i : P) ∈ p.asIdeal := by
        apply p.isPrime.mem_of_pow_mem 2
        have hsq : (Ideal.Quotient.mk I (MvPolynomial.X i : P)) ^ 2 = 0 := by
          rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (Set.mem_range_self i)
        rw [hsq]
        exact p.asIdeal.zero_mem
      have hkill (i : ℕ) :
          (MvPolynomial.X i : P) * f ∈ I := by
        have hxmem : Ideal.Quotient.mk I (MvPolynomial.X i : P) ∈
            (⊥ : Submodule Q Q).colon
              ({Ideal.Quotient.mk I f} : Set Q) := by
          rw [hm]
          exact hxi i
        rw [Submodule.mem_colon_singleton] at hxmem
        have hxzero : Ideal.Quotient.mk I
            ((MvPolynomial.X i : P) * f) = 0 := by
          simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
            using hxmem
        exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
      have hfI : f ∈ I := by
        by_contra hf
        have hnot : ¬ (∀ d ∈ f.support,
            ∃ i : ℕ, Finsupp.single i 2 ≤ d) := by
          intro hall
          exact hf ((hIcrit f).mpr hall)
        push_neg at hnot
        obtain ⟨d, hd, hnone⟩ := hnot
        obtain ⟨i, hi⟩ := d.support.exists_notMem
        have he : Finsupp.single i 1 + d ∈
            (MvPolynomial.X i * f).support := by
          rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul]
          exact MvPolynomial.mem_support_iff.mp hd
        obtain ⟨j, hj⟩ :=
          ((hIcrit (MvPolynomial.X i * f)).mp (hkill i))
            (Finsupp.single i 1 + d) he
        by_cases hji : j = i
        · subst j
          have hdi : d i = 0 := by
            by_contra hdi
            exact hi (Finsupp.mem_support_iff.mpr hdi)
          have := hj i
          simp [Finsupp.single_apply, hdi] at this
        · apply hnone j
          intro l
          by_cases hlj : j = l
          · subst l
            have h := hj j
            simpa [Finsupp.single_apply, hji] using h
          · simp [Finsupp.single_apply, hlj]
      have hmzero : Ideal.Quotient.mk I f = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hfI
      apply p.isPrime.ne_top
      rw [← hm, hmzero]
      rw [Submodule.colon_singleton_zero]
    · simp
  refine ⟨hnonempty, hQempty, ?_⟩
  intro hsubset
  obtain ⟨p, hp⟩ := hnonempty
  obtain ⟨q, hq, hqp⟩ := hsubset hp
  rw [hQempty] at hq
  exact Set.notMem_empty q hq

/-- If the target ring is Noetherian, the functoriality inclusion is an
equality. -/
theorem ass_functorial_eq_of_noetherian
    {R S M : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing S] [AddCommGroup M]
    (φ : R →+* S) [Module S M] :
    (letI : Module R M := Module.compHom M φ;
      PrimeSpectrum.comap φ '' associatedPrimes S M =
        associatedPrimes R M) := by
  letI : Module R M := Module.compHom M φ
  change PrimeSpectrum.comap φ '' associatedPrimes S M = associatedPrimes R M
  apply Set.Subset.antisymm (ass_functorial φ)
  intro p hp
  change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
  obtain ⟨m, hm⟩ := hp
  let I : Ideal S := (⊥ : Submodule S M).colon ({m} : Set M)
  have hIcomap : I.comap φ = p.asIdeal := by
    ext r
    change φ r ∈ I ↔ r ∈ p.asIdeal
    change φ r ∈ (⊥ : Submodule S M).colon ({m} : Set M) ↔ _
    rw [Submodule.mem_colon_singleton, ← hm, Submodule.mem_colon_singleton]
    rfl
  have hpmin : p.asIdeal ∈ (I.comap φ).minimalPrimes := by
    rw [hIcomap]
    exact ⟨⟨p.isPrime, le_rfl⟩, fun q hq hqp => hq.2⟩
  obtain ⟨qI, hqI, hqcomap⟩ :=
    Ideal.exists_minimalPrimes_comap_eq φ p.asIdeal hpmin
  let q : PrimeSpectrum S := ⟨qI, hqI.isPrime⟩
  have hq_support : q ∈ Module.support S (S ⧸ I) := by
    apply Module.mem_support_iff_of_finite.mpr
    simpa only [Ideal.annihilator_quotient] using hqI.le
  have hq_minimal :
      Minimal (fun r : PrimeSpectrum S => r ∈ Module.support S (S ⧸ I)) q := by
    refine ⟨hq_support, ?_⟩
    intro r hr hrq
    have hrI : I ≤ r.asIdeal := by
      simpa only [Ideal.annihilator_quotient] using
        (Module.annihilator_le_of_mem_support hr)
    exact hqI.2 ⟨r.isPrime, hrI⟩ hrq
  have hqass : q ∈ associatedPrimes S (S ⧸ I) :=
    ass_of_minimal_support q hq_support hq_minimal
  change ∃ x, (⊥ : Submodule S (S ⧸ I)).colon ({x} : Set (S ⧸ I)) = qI
    at hqass
  obtain ⟨x, hx⟩ := hqass
  let f₀ : S →ₗ[S] M := LinearMap.toSpanSingleton S M m
  have hker : I = LinearMap.ker f₀ := by
    ext r
    change r ∈ (⊥ : Submodule S M).colon ({m} : Set M) ↔ r • m = 0
    rw [Submodule.mem_colon_singleton]
    simp
  let f : (S ⧸ I) →ₗ[S] M := I.liftQ f₀ hker.le
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot' I f₀ hker
  have hqM : q ∈ associatedPrimes S M := by
    change ∃ y, (⊥ : Submodule S M).colon ({y} : Set M) = qI
    refine ⟨f x, ?_⟩
    ext r
    rw [Submodule.mem_colon_singleton, ← hx, Submodule.mem_colon_singleton]
    change r • f x = 0 ↔ r • x = 0
    constructor
    · intro hr
      apply hf
      rw [map_smul, hr, map_zero]
    · intro hr
      rw [← map_smul, hr, map_zero]
  refine ⟨q, hqM, ?_⟩
  exact PrimeSpectrum.ext hqcomap

/-! ## Quotients and localization -/

/-- Passing from `R` to `R/I` preserves associated primes via the canonical
injection of spectra. -/
theorem ass_quotient_ring
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module (R ⧸ I) M] :
    (letI : Module R M := Module.compHom M (Ideal.Quotient.mk I);
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ''
          associatedPrimes (R ⧸ I) M = associatedPrimes R M) := by
  letI : Module R M := Module.compHom M (Ideal.Quotient.mk I)
  change PrimeSpectrum.comap (Ideal.Quotient.mk I) ''
      associatedPrimes (R ⧸ I) M = associatedPrimes R M
  apply Set.Subset.antisymm (ass_functorial (Ideal.Quotient.mk I))
  intro p hp
  change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
  obtain ⟨m, hm⟩ := hp
  have hIp : I ≤ p.asIdeal := by
    intro r hr
    rw [← hm, Submodule.mem_colon_singleton]
    change r • m = 0
    have hrzero : Ideal.Quotient.mk I r = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hr
    change (Ideal.Quotient.mk I r) • m = 0
    rw [hrzero, zero_smul]
  let qI : Ideal (R ⧸ I) := p.asIdeal.map (Ideal.Quotient.mk I)
  have hqI : qI.IsPrime := by
    dsimp [qI]
    exact Ideal.isPrime_map_quotientMk_of_isPrime hIp
  let q : PrimeSpectrum (R ⧸ I) := ⟨qI, hqI⟩
  have hcomap : qI.comap (Ideal.Quotient.mk I) = p.asIdeal := by
    dsimp [qI]
    exact Ideal.comap_map_mk hIp
  refine ⟨q, ?_, ?_⟩
  · change ∃ m, (⊥ : Submodule (R ⧸ I) M).colon ({m} : Set M) = q.asIdeal
    refine ⟨m, ?_⟩
    ext x
    rw [Submodule.mem_colon_singleton]
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change r • m = 0 ↔ r ∈ qI.comap (Ideal.Quotient.mk I)
    rw [hcomap, ← hm, Submodule.mem_colon_singleton]
    simp
  · apply PrimeSpectrum.ext
    exact hcomap

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
  constructor
  · intro hp
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
    obtain ⟨m, hm⟩ := hp
    change ∃ m, (⊥ : Submodule (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)).colon ({m} : Set _) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)
    refine ⟨LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m, ?_⟩
    ext t
    rw [Submodule.mem_colon_singleton]
    rcases IsLocalization.exists_mk'_eq p.asIdeal.primeCompl t with ⟨r, s, hrs⟩
    change t • LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m = 0 ↔
      t ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)
    rw [← hrs, ← IsLocalizedModule.mk'_one p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) m,
      IsLocalizedModule.mk'_smul_mk', mul_one,
      IsLocalizedModule.mk'_eq_zero', IsLocalization.mk'_mem_iff,
      ← Ideal.mem_under, Localization.AtPrime.under_maximalIdeal]
    constructor
    · rintro ⟨s', hs'⟩
      have hsrm : ((s' : R) * r) • m = 0 := by
        calc
          ((s' : R) * r) • m = (s' : R) • (r • m) := by rw [smul_smul]
          _ = 0 := by
            change s' • (r • m) = 0
            exact hs'
      have hsr : (s' : R) * r ∈ p.asIdeal := by
        have hmem : (s' : R) * r ∈
            (⊥ : Submodule R M).colon ({m} : Set M) := by
          rw [Submodule.mem_colon_singleton]
          exact hsrm
        rw [hm] at hmem
        exact hmem
      exact (p.isPrime.mem_or_mem hsr).resolve_left s'.property
    · intro hr
      refine ⟨1, ?_⟩
      have hrm : r • m = 0 := by
        have hmem : r ∈ (⊥ : Submodule R M).colon ({m} : Set M) := by
          rw [hm]
          exact hr
        simpa [Submodule.mem_colon_singleton] using hmem
      simpa [smul_smul] using hrm
  · intro hfg hass
    change p.asIdeal.FG at hfg
    change ∃ x, (⊥ : Submodule (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)).colon ({x} : Set _) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) at hass
    obtain ⟨x, hx⟩ := hass
    rcases hfg with ⟨T, hT⟩
    rcases IsLocalizedModule.mk'_surjective p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) x with
      ⟨⟨m, s⟩, rfl⟩
    simp only [Function.uncurry_apply_pair] at hx
    have mem (a : T) : (a : R) ∈ p.asIdeal := by
      simpa [← hT] using Ideal.subset_span a.2
    have memzero (a : T) : ∃ g : p.asIdeal.primeCompl,
        (g : R) • ((a : R) • m) = 0 := by
      have ha : algebraMap R (Localization.AtPrime p.asIdeal) (a : R) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
        rw [← Ideal.mem_under, Localization.AtPrime.under_maximalIdeal]
        exact mem a
      have ha' : algebraMap R (Localization.AtPrime p.asIdeal) (a : R) ∈
          (⊥ : Submodule (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)).colon
            ({IsLocalizedModule.mk' (LocalizedModule.mkLinearMap
              p.asIdeal.primeCompl M) m s} : Set _) := by
        rw [hx]
        exact ha
      rw [Submodule.mem_colon_singleton] at ha'
      rw [algebraMap_smul, ← IsLocalizedModule.mk'_smul] at ha'
      have ha0 : IsLocalizedModule.mk'
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
          ((a : R) • m) s = 0 := by
        simpa only [Submodule.mem_bot] using ha'
      rw [IsLocalizedModule.mk'_eq_zero'] at ha0
      exact ha0
    choose g hg using memzero
    change ∃ n, (⊥ : Submodule R M).colon ({n} : Set M) = p.asIdeal
    refine ⟨(∏ a, g a).1 • m, ?_⟩
    have hple : p.asIdeal ≤
        (⊥ : Submodule R M).colon ({(∏ a, g a).1 • m} : Set M) := by
      apply hT.symm.le.trans
      rw [Ideal.span_le]
      intro a ha
      have hmem : a ∈
          (⊥ : Submodule R M).colon ({(∏ a, g a).1 • m} : Set M) := by
        rw [Submodule.mem_colon_singleton]
        obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ (∏ a, g a) := by
          apply Finset.dvd_prod_of_mem g (Finset.mem_univ ⟨a, ha⟩)
        rw [hu, Submonoid.coe_mul, smul_smul, ← mul_assoc, mul_comm,
          ← smul_smul, mul_comm, ← smul_smul]
        exact smul_eq_zero_of_right u.1 (hg ⟨a, ha⟩)
      exact hmem
    ext r
    constructor
    · intro hr
      have hr' : r • ((∏ a, g a).1 • m) = 0 := by
        rw [Submodule.mem_colon_singleton] at hr
        exact hr
      have hrg : r * (∏ a, g a).1 ∈ p.asIdeal := by
        have hrzero : (r * (∏ a, g a).1) • m = 0 := by
          simpa [smul_smul] using hr'
        have hloc : algebraMap R (Localization.AtPrime p.asIdeal)
              (r * (∏ a, g a).1) ∈
            IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
          rw [← hx, Submodule.mem_colon_singleton]
          rw [algebraMap_smul, ← IsLocalizedModule.mk'_smul, hrzero]
          simp
        have hloc' : r * (∏ a, g a).1 ∈
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).under R :=
          (Ideal.mem_under R
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))).2 hloc
        simpa only [Localization.AtPrime.under_maximalIdeal] using hloc'
      exact (p.isPrime.mem_or_mem hrg).resolve_right (∏ a, g a).property
    · intro hr
      have hmem := hple hr
      simpa [Submodule.mem_colon_singleton] using hmem

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
