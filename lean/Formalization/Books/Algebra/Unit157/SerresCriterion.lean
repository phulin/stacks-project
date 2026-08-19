import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit62.SupportAndDimension
import Formalization.Books.Algebra.Unit63.AssociatedPrimes
import Formalization.Books.Algebra.Unit67.EmbeddedPrimes
import Formalization.Books.Algebra.Unit72.Depth
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Commutative Algebra, Chapter 157: Serre's criterion for normality

This file records the source's `(R_k)` and `(S_k)` conditions and the
equivalences and height-one localization statements that make up Serre's
criterion for normality.  The depth and support-dimension expressions use
the canonical interfaces from Chapters 62 and 72.
-/

namespace Formalization.Books.Algebra.Unit157

open Set
open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit67
open Formalization.Books.Algebra.Unit72

universe u v

noncomputable section

/-! ## The `(R_k)` and `(S_k)` conditions -/

/-- A ring has property `(R_k)` when every prime of height at most `k` has
regular localization.  The Noetherian hypothesis from the source is retained
on the theorems using this condition; the predicate itself is also useful as
a local property without that hypothesis. -/
def HasPropertyRk (R : Type u) [CommRing R] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    p.asIdeal.height ≤ (k : ℕ∞) →
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)

/-- The source's alternate name for property `(R_k)`. -/
abbrev IsRegularInCodimensionLe (R : Type u) [CommRing R] (k : ℕ) : Prop :=
  HasPropertyRk R k

/-- A Noetherian ring has property `(S_k)` when the depth at every prime is
at least the minimum of `k` and the dimension of the corresponding local
ring. -/
def HasPropertySk (R : Type u) [CommRing R] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    min ((k : ℕ∞) : WithBot ℕ∞)
        (ringKrullDim (Localization.AtPrime p.asIdeal)) ≤
      ((localDepth (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal) : ℕ∞) : WithBot ℕ∞)

/-- The module form of property `(S_k)`: the localized module has depth at
least the minimum of `k` and the dimension of its localized support. -/
def HasPropertySkModule
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    min ((k : ℕ∞) : WithBot ℕ∞)
        (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) ≤
      ((localDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M) : ℕ∞) : WithBot ℕ∞)

/-- Every Noetherian ring has property `(S_0)`. -/
theorem hasPropertySk_zero
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    HasPropertySk R 0 := by
  simp [HasPropertySk]

/-- Every finite module over a Noetherian ring has property `(S_0)`. -/
theorem hasPropertySkModule_zero
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasPropertySkModule R M 0 := by
  simp [HasPropertySkModule]

/-- A zero module has property `(S_k)` for every `k`.  A `Subsingleton`
module is the type-theoretic representation of the zero module. -/
theorem hasPropertySkModule_of_subsingleton
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Subsingleton M] (k : ℕ) :
    HasPropertySkModule R M k := by
  simp [HasPropertySkModule, Module.supportDim_eq_bot_of_subsingleton,
    Formalization.Books.Algebra.Unit72.depth_eq_top_of_subsingleton]

/-! ## The three main equivalences -/

/-- A finite module over a Noetherian ring has no embedded associated prime
exactly when it satisfies `(S_1)`. -/
theorem criterion_no_embedded_primes
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    embeddedAssociatedPrimes (R := R) (M := M) = ∅ ↔
      HasPropertySkModule R M 1 := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h p
    let S := p.asIdeal.primeCompl
    change min ((1 : ℕ∞) : WithBot ℕ∞)
        (Module.supportDim (Localization S) (LocalizedModule S M)) ≤
      ((localDepth (Localization S) (LocalizedModule S M) : ℕ∞) : WithBot ℕ∞)
    by_cases hsub : Subsingleton (LocalizedModule S M)
    · let _ : Subsingleton (LocalizedModule S M) := hsub
      simp [Module.supportDim_eq_bot_of_subsingleton]
    · let _ : Nontrivial (LocalizedModule S M) :=
        not_subsingleton_iff_nontrivial.mp hsub
      by_contra hfail
      have hdepthlt :
          ((localDepth (Localization S) (LocalizedModule S M) : ℕ∞) : WithBot ℕ∞) <
            (1 : WithBot ℕ∞) := by
        by_contra hn
        have hone : (1 : WithBot ℕ∞) ≤
            ((localDepth (Localization S) (LocalizedModule S M) : ℕ∞) : WithBot ℕ∞) :=
          le_of_not_gt hn
        exact hfail (le_trans (min_le_left _ _) hone)
      have hdepth0 : localDepth (Localization S) (LocalizedModule S M) = 0 := by
        cases hd : localDepth (Localization S) (LocalizedModule S M) with
        | top => simp [hd] at hdepthlt
        | coe n =>
          rw [hd] at hdepthlt
          have hn' : (n : ℕ∞) < 1 :=
            WithBot.coe_lt_coe.mp hdepthlt
          have hn : n < 1 := by
            exact_mod_cast hn'
          have hn0 : n = 0 := by
            exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
          rw [hn0]
          rfl
      have hdim : (1 : WithBot ℕ∞) ≤
          Module.supportDim (Localization S) (LocalizedModule S M) := by
        by_contra hn
        have hlt : Module.supportDim (Localization S) (LocalizedModule S M) <
            (1 : WithBot ℕ∞) := lt_of_not_ge hn
        cases hs : Module.supportDim (Localization S) (LocalizedModule S M) with
        | bot => simp [hs, hdepth0] at hfail
        | coe d =>
          cases hd : d with
          | top => simp [hs, hd] at hlt
          | coe n =>
            have hn : n < 1 := by
              apply WithBot.coe_lt_coe.mp
              simpa [hs, hd] using hlt
            have hn0 : n = 0 := by
              exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
            subst n
            simp [hs, hd, hdepth0] at hfail
      have hdim' : 1 ≤
          Order.krullDim (Module.support (Localization S) (LocalizedModule S M)) := by
        simpa [Module.supportDim] using hdim
      obtain ⟨r, s, hrs⟩ :=
        Order.one_le_krullDim_iff.mp hdim'
      have hr : r.1 ∈ Module.support (Localization S) (LocalizedModule S M) := r.2
      obtain ⟨I, hI, hIr⟩ :=
        Ideal.exists_minimalPrimes_le (J := r.1.asIdeal)
          (Module.mem_support_iff_of_finite.mp hr)
      let q' : PrimeSpectrum (Localization S) := ⟨I, hI.isPrime⟩
      have hq'supp : q' ∈ Module.support (Localization S) (LocalizedModule S M) := by
        rw [Module.support_eq_zeroLocus]
        exact hI.1.2
      have hq'min : Minimal
          (fun q : PrimeSpectrum (Localization S) =>
            q ∈ Module.support (Localization S) (LocalizedModule S M)) q' := by
        refine ⟨hq'supp, ?_⟩
        intro z hz hzq
        exact hI.2 ⟨z.isPrime, Module.mem_support_iff_of_finite.mp hz⟩ hzq
      have hq'ass :
          q' ∈ Formalization.Books.Algebra.Unit63.associatedPrimes (Localization S)
            (LocalizedModule S M) :=
        Formalization.Books.Algebra.Unit63.ass_of_minimal_support q' hq'supp hq'min
      have hqle_r : q' ≤ r := hIr
      have hq'lt_s : q' < s := lt_of_le_of_lt hqle_r hrs
      have hq'lt : q' < IsLocalRing.closedPoint (Localization S) :=
        lt_of_lt_of_le hq'lt_s (IsLocalRing.le_maximalIdeal s.1.isPrime.ne_top)
      let _ : Module R (LocalizedModule S M) :=
        Module.compHom (LocalizedModule S M) (algebraMap R (Localization S))
      have hclosed : Ideal.comap (algebraMap R (Localization S))
          (IsLocalRing.maximalIdeal (Localization S)) = p.asIdeal := by
        ext r
        change algebraMap R (Localization S) r ∈
            IsLocalRing.maximalIdeal (Localization S) ↔ r ∈ p.asIdeal
        rw [← Ideal.mem_under, Localization.AtPrime.under_maximalIdeal]
      let q : PrimeSpectrum R :=
        PrimeSpectrum.comap (algebraMap R (Localization S)) q'
      have hqglobal : q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M := by
        have hqRloc :
            q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R
              (LocalizedModule S M) := by
          have hqOver :=
            Formalization.Books.Algebra.Unit63.ass_localize_eq_over_localization
              (R := R) (M := M) S
          rw [← hqOver]
          exact ⟨q', hq'ass, rfl⟩
        have hassloc :=
          Formalization.Books.Algebra.Unit63.ass_localize_eq_of_noetherian
            (R := R) (M := M) S
        have hqint : q ∈
            Formalization.Books.Algebra.Unit63.associatedPrimes R M ∩
              Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) := by
          rw [hassloc]
          exact hqRloc
        exact hqint.1
      have hqle : q ≤ p := by
        change Ideal.comap (algebraMap R (Localization S)) q'.asIdeal ≤ p.asIdeal
        calc
          _ ≤ Ideal.comap (algebraMap R (Localization S))
              (IsLocalRing.maximalIdeal (Localization S)) :=
            Ideal.comap_mono (IsLocalRing.le_maximalIdeal q'.isPrime.ne_top)
          _ = p.asIdeal := hclosed
      have hqnotle : ¬ p ≤ q := by
        intro hpq
        have hpeq : q = p := le_antisymm hqle hpq
        have hcomap :
            PrimeSpectrum.comap (algebraMap R (Localization S)) q' =
              PrimeSpectrum.comap (algebraMap R (Localization S))
                (IsLocalRing.closedPoint (Localization S)) := by
          calc
            PrimeSpectrum.comap (algebraMap R (Localization S)) q' = q := rfl
            _ = p := hpeq
            _ = PrimeSpectrum.comap (algebraMap R (Localization S))
                (IsLocalRing.closedPoint (Localization S)) := by
              apply PrimeSpectrum.ext
              change p.asIdeal =
                Ideal.comap (algebraMap R (Localization S))
                  (IsLocalRing.maximalIdeal (Localization S))
              exact hclosed.symm
        exact hq'lt.ne ((PrimeSpectrum.localization_comap_injective
          (R := R) (S := Localization S) (M := S)) hcomap)
      have hdepthchar :=
        (Formalization.Books.Algebra.Unit72.depth_eq_zero_iff
          (IsLocalRing.maximalIdeal (Localization S))
          (LocalizedModule S M)).mp hdepth0
      have hnotmax : ¬ ∀ q0 : PrimeSpectrum (Localization S),
          q0 ∈ Formalization.Books.Algebra.Unit63.associatedPrimes (Localization S)
            (LocalizedModule S M) →
          ¬ IsLocalRing.maximalIdeal (Localization S) ≤ q0 := by
        intro hall
        apply hdepthchar.2
        exact
          (Formalization.Books.Algebra.Unit63.ideal_contains_regular_iff
            (R := Localization S) (M := LocalizedModule S M)
            (IsLocalRing.maximalIdeal (Localization S)) le_rfl).mpr hall
      push Not at hnotmax
      obtain ⟨q0, hq0, hmaxq0⟩ := hnotmax
      have hq0eq : q0 = IsLocalRing.closedPoint (Localization S) :=
        le_antisymm (IsLocalRing.le_maximalIdeal q0.isPrime.ne_top) hmaxq0
      have hplocal :
          IsLocalRing.closedPoint (Localization S) ∈
            Formalization.Books.Algebra.Unit63.associatedPrimes (Localization S)
              (LocalizedModule S M) := by
        simpa [hq0eq] using hq0
      have hpglobal : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M :=
        (Formalization.Books.Algebra.Unit63.associated_primes_localize_at_prime p).2
          (((isNoetherianRing_iff_ideal_fg R).mp inferInstance) p.asIdeal) hplocal
      have hpnot := h p
      change ¬ (p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ∧
        ¬ Minimal (fun q : PrimeSpectrum R =>
          q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) p) at hpnot
      apply hpnot
      refine ⟨hpglobal, ?_⟩
      intro hmin
      exact hqnotle (hmin.2 hqglobal hqle)
  · intro h p hp
    change p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ∧
      ¬ Minimal (fun q : PrimeSpectrum R =>
        q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) p at hp
    have hpmin := hp.2
    change ¬ (p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M ∧
      ∀ q : PrimeSpectrum R,
        q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M →
        q ≤ p → p ≤ q) at hpmin
    push Not at hpmin
    have hp' := hpmin hp.1
    obtain ⟨q, hq, hqle, hqnotle⟩ := hp'
    let S := p.asIdeal.primeCompl
    let _ : Module R (LocalizedModule S M) :=
      Module.compHom (LocalizedModule S M) (algebraMap R (Localization S))
    have hqrange : q ∈ Set.range
        (PrimeSpectrum.comap (algebraMap R (Localization S))) := by
      rw [PrimeSpectrum.localization_comap_range (R := R) (S := Localization S) (M := S)]
      change Disjoint (S : Set R) q.asIdeal
      rw [Set.disjoint_left]
      intro s hs hsq
      exact hs (hqle hsq)
    have hqRloc : q ∈
        Formalization.Books.Algebra.Unit63.associatedPrimes R
          (LocalizedModule S M) := by
      have hassloc :=
        Formalization.Books.Algebra.Unit63.ass_localize_eq_of_noetherian
          (R := R) (M := M) S
      rw [← hassloc]
      exact ⟨hq, hqrange⟩
    have hqOver := Formalization.Books.Algebra.Unit63.ass_localize_eq_over_localization
      (R := R) (M := M) S
    have hqRloc' :
        q ∈ PrimeSpectrum.comap (algebraMap R (Localization S)) ''
          Formalization.Books.Algebra.Unit63.associatedPrimes (Localization S)
            (LocalizedModule S M) := by
      rw [hqOver]
      exact hqRloc
    obtain ⟨q', hq', hqmap⟩ := hqRloc'
    have hqmap' : q'.asIdeal.comap
        (algebraMap R (Localization S)) = q.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg PrimeSpectrum.asIdeal hqmap
    have hq'lt : q' < IsLocalRing.closedPoint (Localization S) := by
      apply lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q'.isPrime.ne_top)
      intro heq
      apply hqnotle
      change p.asIdeal ≤ q.asIdeal
      have hclosed : Ideal.comap (algebraMap R (Localization S))
          (IsLocalRing.maximalIdeal (Localization S)) = p.asIdeal := by
        ext r
        change algebraMap R (Localization S) r ∈
            IsLocalRing.maximalIdeal (Localization S) ↔ r ∈ p.asIdeal
        rw [← Ideal.mem_under, Localization.AtPrime.under_maximalIdeal]
      have hpeq : q.asIdeal = p.asIdeal := by
        rw [← hqmap', heq, hclosed]
      rw [hpeq]
    have hp' : IsLocalRing.closedPoint (Localization S) ∈
        Formalization.Books.Algebra.Unit63.associatedPrimes (Localization S)
          (LocalizedModule S M) :=
      (Formalization.Books.Algebra.Unit63.associated_primes_localize_at_prime p).1 hp.1
    have hq'supp : q' ∈ Module.support (Localization S) (LocalizedModule S M) :=
      Formalization.Books.Algebra.Unit63.ass_subset_support hq'
    have hp'supp : IsLocalRing.closedPoint (Localization S) ∈
        Module.support (Localization S) (LocalizedModule S M) :=
      Formalization.Books.Algebra.Unit63.ass_subset_support hp'
    have hdim : (1 : WithBot ℕ∞) ≤
        Module.supportDim (Localization S) (LocalizedModule S M) := by
      change (1 : WithBot ℕ∞) ≤
        Order.krullDim (Module.support (Localization S) (LocalizedModule S M))
      exact Order.one_le_krullDim_iff.mpr
        ⟨⟨q', hq'supp⟩,
          ⟨IsLocalRing.closedPoint (Localization S), hp'supp⟩, hq'lt⟩
    have hdepth0 : localDepth (Localization S) (LocalizedModule S M) = 0 := by
      apply (Formalization.Books.Algebra.Unit72.depth_eq_zero_iff
        (IsLocalRing.maximalIdeal (Localization S)) (LocalizedModule S M)).2
      have hnontr : Nontrivial (LocalizedModule S M) := by
        by_contra hnon
        have hsub : Subsingleton (LocalizedModule S M) :=
          not_nontrivial_iff_subsingleton.mp hnon
        have hempty :
            Formalization.Books.Algebra.Unit63.associatedPrimes (Localization S)
              (LocalizedModule S M) = ∅ :=
          (Formalization.Books.Algebra.Unit63.ass_eq_empty_iff_subsingleton
            (R := Localization S) (M := LocalizedModule S M)).mp hsub
        rw [hempty] at hp'
        exact Set.notMem_empty _ hp'
      refine ⟨hnontr, ?_⟩
      rintro ⟨x, hx, hreg⟩
      have hno :=
        (Formalization.Books.Algebra.Unit63.ideal_contains_regular_iff
          (R := Localization S) (M := LocalizedModule S M)
          (IsLocalRing.maximalIdeal (Localization S)) le_rfl).mp
          ⟨x, hx, hreg⟩
      exact hno _ hp' le_rfl
    have hineq := h p
    change min ((1 : ℕ∞) : WithBot ℕ∞)
        (Module.supportDim (Localization S) (LocalizedModule S M)) ≤
      ((localDepth (Localization S) (LocalizedModule S M) : ℕ∞) : WithBot ℕ∞) at hineq
    have hmin : min ((1 : ℕ∞) : WithBot ℕ∞)
        (Module.supportDim (Localization S) (LocalizedModule S M)) =
        ((1 : ℕ∞) : WithBot ℕ∞) :=
      min_eq_left hdim
    rw [hmin, hdepth0] at hineq
    have hnot : ¬ ((1 : ℕ∞) : WithBot ℕ∞) ≤ 0 := by simp
    exact hnot hineq

/-- Serre's reducedness criterion: reduced is equivalent to `(R_0)` plus
`(S_1)`. -/
theorem criterion_reduced
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsReduced R ↔ HasPropertyRk R 0 ∧ HasPropertySk R 1 := by
  sorry

/-- Serre's criterion for normality: normal is equivalent to `(R_1)` plus
`(S_2)`. -/
theorem criterion_normal
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsNormalRing R ↔ HasPropertyRk R 1 ∧ HasPropertySk R 2 := by
  sorry

/-- A regular ring is normal.  `IsRegularRing` is Mathlib's canonical
Noetherian regular-ring class, while `IsNormalRing` is the source-facing
normal-ring predicate from Chapter 37. -/
theorem regularRing_isNormal
    {R : Type u} [CommRing R] [IsRegularRing R] :
    IsNormalRing R := by
  sorry

/-! ## Height-one localizations of a normal domain -/

/-- For a nonzero element of a Noetherian normal domain, the quotient by the
principal ideal has no embedded associated primes and all its associated
primes have height one. -/
theorem normalDomain_principal_quotient_height_one
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsNormalDomain R) :
    ∀ {a : R}, a ≠ 0 →
      embeddedAssociatedPrimes (R := R)
          (M := R ⧸ Ideal.span ({a} : Set R)) = ∅ ∧
        ∀ p : PrimeSpectrum R,
          p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R
            (R ⧸ Ideal.span ({a} : Set R)) →
            p.asIdeal.height = 1 := by
  sorry

/-- The intersection of the height-one localizations, viewed inside a fixed
fraction field.  The explicit domain argument supplies the nonzerodivisor
condition needed to realize each localization as a subalgebra of the field. -/
noncomputable def heightOneLocalizationIntersection
    (R : Type u) (K : Type u) [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (hR : IsDomain R) : Set K := by
  letI : IsDomain R := hR
  exact ⋂ p : {p : PrimeSpectrum R // p.asIdeal.height = 1},
    (Localization.subalgebra.ofField K p.1.asIdeal.primeCompl
      p.1.asIdeal.primeCompl_le_nonZeroDivisors : Set K)

/-- The displayed intersection identity for a Noetherian normal domain,
written as equality of the image of `R` in its fraction field with the
intersection of the height-one localization subalgebras. -/
theorem normalDomain_eq_heightOneLocalizationIntersection
    (R : Type u) (K : Type u) [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsNormalDomain R) :
    Set.range (algebraMap R K) =
      heightOneLocalizationIntersection R K hR.1 := by
  sorry

/- The source's proof of the intersection identity uses the following
membership form: `b ∈ aR` exactly when `b` belongs to `aR_p` at every
height-one prime.  It is recorded separately because it is often the most
convenient form for applications and avoids choosing fraction representatives. -/
theorem principal_mem_iff_mem_all_heightOne_localizations
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R]
    {a b : R} (ha : a ≠ 0) :
    (∃ c : R, b = a * c) ↔
      ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
        ∃ z : Localization.AtPrime p.asIdeal,
          algebraMap R (Localization.AtPrime p.asIdeal) b =
            algebraMap R (Localization.AtPrime p.asIdeal) a * z := by
  sorry

/-- The fractional ideal `R ∩ xR`, represented as the comap of the
`R`-submodule generated by `x` in the fraction field. -/
def fractionIntersectionIdeal
    (R : Type u) (K : Type u) [CommRing R] [Field K]
    [Algebra R K] (x : K) : Ideal R :=
  Submodule.comap (Algebra.linearMap R K)
    (Submodule.span R ({x} : Set K))

/-- For a nonzero fraction `x`, the quotient by `R ∩ xR` has no embedded
associated primes and all of its associated primes have height one. -/
theorem fractionIntersection_criterion
    (R : Type u) (K : Type u) [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsNormalDomain R) :
    ∀ {x : K}, x ≠ 0 →
      embeddedAssociatedPrimes (R := R)
          (M := R ⧸ fractionIntersectionIdeal R K x) = ∅ ∧
        ∀ p : PrimeSpectrum R,
          p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R
            (R ⧸ fractionIntersectionIdeal R K x) →
          p.asIdeal.height = 1 := by
  sorry

end

end Formalization.Books.Algebra.Unit157
