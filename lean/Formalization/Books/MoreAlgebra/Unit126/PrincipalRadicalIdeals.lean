/-
# More on Algebra, Chapter 126: Principal radical ideals
-/

import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit52.Length
import Formalization.Books.Algebra.Unit59.NoetherianLocalRings
import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit105.CatenaryRings
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Algebra.Module.SnakeLemma

/-!
This file records the definitions and theorem interfaces in the source chapter.
Length is represented by the existing natural-valued wrapper around
`Module.length`, while systems of parameters, normality, catenarity, radical
ideals, and reduced quotients use the established project and Mathlib APIs.
-/

namespace Formalization.Books.MoreAlgebra.Unit126

noncomputable section

open Set
open Formalization.Books.Algebra.Unit60

/-! ## Quotient lengths -/

/-- The natural-valued length of a quotient by an ideal. -/
def idealQuotientLength {R : Type*} [CommRing R] (I : Ideal R) : ℕ :=
  Formalization.Books.Algebra.Unit59.moduleLengthNat (R := R) (M := R ⧸ I)

/-- The function `n ↦ length (R / x^n R)` used in the first lemma. -/
def principalPowerQuotientLength
    {R : Type*} [CommRing R] (x : R) (n : ℕ) : ℕ :=
  idealQuotientLength (Ideal.span ({x ^ n} : Set R))

/-! ## One-dimensional length estimates -/

/-- Lengths of powers of a parameter grow at most linearly, with equality for
nonzerodivisors. -/
theorem lemma_polypoly
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ∉ p) :
    (∀ n : ℕ,
      principalPowerQuotientLength x n ≤
        n * principalPowerQuotientLength x 1) ∧
      (x ∈ nonZeroDivisors R →
        ∀ n : ℕ,
          principalPowerQuotientLength x n =
            n * principalPowerQuotientLength x 1) := by
  have hR : Nontrivial R := by
    by_contra h
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have hqdim (n : ℕ) (hn : 0 < n) :
      ringKrullDim (R ⧸ Ideal.span ({x ^ n} : Set R)) = 0 := by
    have hpow : x ^ n ∈ IsLocalRing.maximalIdeal R :=
      Ideal.pow_mem_of_mem _ hx n hn
    have hpowmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ^ n ∉ p := by
      intro p hp hxp
      exact hmin p hp ((Ideal.IsMinimalPrime.isPrime hp).mem_of_pow_mem n hxp)
    have h := one_equation_dimension_eq_of_not_mem_minimalPrimes
      R hR (x ^ n) hpow hpowmin
    rw [hdim] at h
    apply ENat.WithBot.add_one_cancel.mp
    simpa [zero_add] using h.symm
  let I : ℕ → Ideal R := fun n => Ideal.span ({x ^ n} : Set R)
  have hfin : ∀ n : ℕ, IsFiniteLength R (R ⧸ I n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hI : I 0 = (⊤ : Ideal R) := by simp [I]
      rw [hI]
      exact IsFiniteLength.of_subsingleton
    · have hpow : x ^ n ∈ IsLocalRing.maximalIdeal R :=
        Ideal.pow_mem_of_mem _ hx n (Nat.pos_of_ne_zero hn)
      have hIle : I n ≤ IsLocalRing.maximalIdeal R := by
        exact Ideal.span_le.mpr (by simpa [I] using hpow)
      have hItop : I n ≠ ⊤ := by
        intro htop
        have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
          apply hIle
          rw [htop]
          exact Set.mem_univ 1
        exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1
      let Q := R ⧸ I n
      letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hItop
      letI : IsLocalRing Q :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (I n))
          Ideal.Quotient.mk_surjective
      letI : IsLocalHom (Ideal.Quotient.mk (I n)) :=
        IsLocalHom.of_surjective (Ideal.Quotient.mk (I n))
          Ideal.Quotient.mk_surjective
      letI : Ring.KrullDimLE 0 Q :=
        (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr (by
          simpa [Q, I] using hqdim n (Nat.pos_of_ne_zero hn))
      have hradq : (⊥ : Ideal Q).radical = IsLocalRing.maximalIdeal Q :=
        Ring.KrullDimLE.radical_eq_maximalIdeal (⊥ : Ideal Q) bot_ne_top
      have hdef : Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R (I n) := by
        unfold Formalization.Books.Algebra.Unit59.IsIdealOfDefinition
        calc
          (I n).radical =
              Ideal.comap (Ideal.Quotient.mk (I n))
                ((⊥ : Ideal Q).radical) := by
            rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          _ = Ideal.comap (Ideal.Quotient.mk (I n))
                (IsLocalRing.maximalIdeal Q) := by rw [hradq]
          _ = IsLocalRing.maximalIdeal R := IsLocalRing.maximalIdeal_comap _
      have hkill : (I n) ^ 1 • (⊤ : Submodule R Q) = ⊥ := by
        rw [Ideal.smul_top_eq_map]
        have hmapzero : ((I n) ^ 1).map (algebraMap R Q) = ⊥ := by
          rw [Ideal.map_eq_bot_iff_le_ker]
          intro z hz
          rw [RingHom.mem_ker]
          change Ideal.Quotient.mk (I n) z = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          simpa [pow_one] using hz
        rw [hmapzero]
        rfl
      exact Formalization.Books.Algebra.Unit59.finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition
        (I n) hdef ⟨1, by simpa [pow_one] using hkill⟩
  have hstep_all (n : ℕ) :
      principalPowerQuotientLength x (n + 1) ≤
        principalPowerQuotientLength x n +
          principalPowerQuotientLength x 1 ∧
        ∀ hxreg : x ∈ nonZeroDivisors R,
          principalPowerQuotientLength x (n + 1) =
            principalPowerQuotientLength x n +
              principalPowerQuotientLength x 1 := by
    have hIle : I (n + 1) ≤ I 1 := by
      apply Ideal.span_le.mpr
      rintro z ⟨rfl⟩
      exact Ideal.mem_span_singleton'.mpr ⟨x ^ n, by simp [pow_succ, mul_comm]⟩
    have hfker : I n ≤ LinearMap.ker
        ((I (n + 1)).mkQ.comp (LinearMap.mulLeft R x)) := by
      intro z hz
      rw [LinearMap.mem_ker]
      change (I (n + 1)).mkQ (x * z) = 0
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      apply Ideal.mem_span_singleton'.mpr
      change z ∈ Ideal.span ({x ^ n} : Set R) at hz
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨a, ?_⟩
      rw [← ha]
      simp [pow_succ, mul_comm, mul_left_comm]
    let f : R ⧸ I n →ₗ[R] R ⧸ I (n + 1) :=
      (I n).liftQ ((I (n + 1)).mkQ.comp (LinearMap.mulLeft R x)) hfker
    have hgker : I (n + 1) ≤ LinearMap.ker (I 1).mkQ := by
      simpa [Submodule.ker_mkQ] using hIle
    let g : R ⧸ I (n + 1) →ₗ[R] R ⧸ I 1 :=
      (I (n + 1)).liftQ (I 1).mkQ hgker
    have hf (z : R) : f ((I n).mkQ z) = (I (n + 1)).mkQ (x * z) := by
      change (((I n).liftQ
        ((I (n + 1)).mkQ.comp (LinearMap.mulLeft R x)) hfker).comp
          (I n).mkQ) z = (I (n + 1)).mkQ (x * z)
      rw [Submodule.liftQ_mkQ]
      rfl
    have hg (z : R) : g ((I (n + 1)).mkQ z) = (I 1).mkQ z := by
      change (((I (n + 1)).liftQ (I 1).mkQ hgker).comp
        (I (n + 1)).mkQ) z = (I 1).mkQ z
      rw [Submodule.liftQ_mkQ]
    have hex : Function.Exact f g := by
      rw [LinearMap.exact_iff]
      ext y
      constructor
      · intro hy
        refine Submodule.Quotient.induction_on (p := I (n + 1)) y ?_ hy
        intro z hz
        rw [LinearMap.mem_ker] at hz
        have hz' : g ((I (n + 1)).mkQ z) = 0 := by
          simpa only [Submodule.mkQ_apply] using hz
        rw [hg] at hz'
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hz'
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hz'
        refine ⟨(I n).mkQ a, ?_⟩
        rw [hf]
        rw [← ha]
        simp [mul_comm]
      · rintro ⟨z, rfl⟩
        refine Submodule.Quotient.induction_on (p := I n) z ?_
        intro a
        rw [LinearMap.mem_ker]
        change g (f ((I n).mkQ a)) = 0
        rw [hf, hg]
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        simpa [I] using
          (Ideal.mem_span_singleton'.mpr ⟨a, by simp [mul_comm]⟩)
    have hgsurj : Function.Surjective g := by
      intro y
      refine Submodule.Quotient.induction_on (p := I 1) y ?_
      intro z
      exact ⟨(I (n + 1)).mkQ z, rfl⟩
    have hfr : Function.Surjective
        (f.codRestrict (LinearMap.range f)
          (fun y => LinearMap.mem_range_self f y)) := by
      intro y
      rcases y.property with ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
    have hex' : Function.Exact (LinearMap.range f).subtype g := by
      rw [LinearMap.exact_iff, Submodule.range_subtype]
      exact LinearMap.exact_iff.mp hex
    have hseq := Module.length_eq_add_of_exact
      (LinearMap.range f).subtype g (Submodule.subtype_injective _) hgsurj hex'
    have hrle := Module.length_le_of_surjective
      (f.codRestrict (LinearMap.range f)
        (fun y => LinearMap.mem_range_self f y)) hfr
    have hrnat :
        (Module.length R (LinearMap.range f)).toNat ≤
          (Module.length R (R ⧸ I n)).toNat :=
      ENat.toNat_le_toNat hrle (Module.length_ne_top_iff.mpr (hfin n))
    have hfrfin : IsFiniteLength R (LinearMap.range f) :=
      IsFiniteLength.of_surjective (hfin n) hfr
    constructor
    · have hnat := congrArg ENat.toNat hseq
      rw [ENat.toNat_add] at hnat
      · calc
          principalPowerQuotientLength x (n + 1) =
              (Module.length R (LinearMap.range f)).toNat +
                (Module.length R (R ⧸ I 1)).toNat := by
            simpa [principalPowerQuotientLength, idealQuotientLength,
              Formalization.Books.Algebra.Unit59.moduleLengthNat, I] using hnat
          _ ≤ principalPowerQuotientLength x n +
                principalPowerQuotientLength x 1 := by
            simpa [principalPowerQuotientLength, idealQuotientLength,
              Formalization.Books.Algebra.Unit59.moduleLengthNat, I] using
              Nat.add_le_add_right hrnat (Module.length R (R ⧸ I 1)).toNat
      · exact Module.length_ne_top_iff.mpr hfrfin
      · exact Module.length_ne_top_iff.mpr (hfin 1)
    · intro hxreg
      have hf_inj : Function.Injective f := by
        apply LinearMap.ker_eq_bot.mp
        ext y
        constructor
        · intro hy
          refine Submodule.Quotient.induction_on (p := I n) y ?_ hy
          intro z hz
          rw [LinearMap.mem_ker] at hz
          have hz' : f ((I n).mkQ z) = 0 := by simpa using hz
          rw [hf] at hz'
          rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hz'
          obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hz'
          have hzero : x * (z - a * x ^ n) = 0 := by
            rw [mul_sub, ← ha]
            simp [pow_succ, mul_comm, mul_left_comm]
          have hcancel : z - a * x ^ n = 0 :=
            (mem_nonZeroDivisors_iff.mp hxreg).1 _ hzero
          rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
          apply Ideal.mem_span_singleton'.mpr
          exact ⟨a, sub_eq_zero.mp hcancel |>.symm⟩
        · intro hy
          rw [Submodule.mem_bot] at hy
          rw [hy]
          simp
      have hseqeq := Module.length_eq_add_of_exact f g hf_inj hgsurj hex
      have hnat := congrArg ENat.toNat hseqeq
      rw [ENat.toNat_add] at hnat
      · simpa [principalPowerQuotientLength, idealQuotientLength,
          Formalization.Books.Algebra.Unit59.moduleLengthNat, I] using hnat
      · exact Module.length_ne_top_iff.mpr (hfin n)
      · exact Module.length_ne_top_iff.mpr (hfin 1)
  constructor
  · intro n
    induction n with
    | zero =>
        simp [principalPowerQuotientLength, idealQuotientLength,
          Formalization.Books.Algebra.Unit59.moduleLengthNat]
    | succ n ih =>
        calc
          principalPowerQuotientLength x (Nat.succ n) ≤
              principalPowerQuotientLength x n +
                principalPowerQuotientLength x 1 := by
            simpa [Nat.succ_eq_add_one] using (hstep_all n).1
          _ ≤ n * principalPowerQuotientLength x 1 +
                principalPowerQuotientLength x 1 :=
            Nat.add_le_add_right ih _
          _ = (Nat.succ n) * principalPowerQuotientLength x 1 := by
            simp [Nat.succ_mul]
  · intro hxreg n
    induction n with
    | zero =>
        simp [principalPowerQuotientLength, idealQuotientLength,
          Formalization.Books.Algebra.Unit59.moduleLengthNat]
    | succ n ih =>
        calc
          principalPowerQuotientLength x (Nat.succ n) =
              principalPowerQuotientLength x n +
                principalPowerQuotientLength x 1 := by
            exact (hstep_all n).2 hxreg
          _ = n * principalPowerQuotientLength x 1 +
                principalPowerQuotientLength x 1 := by rw [ih]
          _ = (Nat.succ n) * principalPowerQuotientLength x 1 := by
            simp [Nat.succ_mul]

/-! ## Minimal primes in dimension one -/

/-- The number of minimal primes is bounded by the length of a principal
parameter quotient. -/
theorem lemma_minprimespoly
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, x ∉ p) :
    Nat.card {p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes} ≤
      principalPowerQuotientLength x 1 := by
  have hR : Nontrivial R := by
    by_contra h
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  let S := R ⧸ nilradical R
  have hniltop : nilradical R ≠ (⊤ : Ideal R) := by
    intro htop
    have h1 : (1 : R) ∈ nilradical R := by rw [htop]; exact Set.mem_univ 1
    obtain ⟨n : ℕ, hn⟩ := (mem_nilradical.mp h1)
    exact (one_ne_zero : (1 : R) ≠ 0) (by simpa using hn)
  letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hniltop
  letI : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (nilradical R))
      Ideal.Quotient.mk_surjective
  letI : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk (nilradical R))
      Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk (nilradical R)) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk (nilradical R))
      Ideal.Quotient.mk_surjective
  letI : IsReduced S := by
    refine (RingHom.ker_isRadical_iff_reduced_of_surjective
      (f := Ideal.Quotient.mk (nilradical R))
      Ideal.Quotient.mk_surjective).mp ?_
    rw [Ideal.mk_ker]
    exact Ideal.radical_isRadical (⊥ : Ideal R)
  have hdimS : ringKrullDim S = 1 := by
    have hdimred : ringKrullDim S = ringKrullDim R := by
      rw [ringKrullDim_quotient, PrimeSpectrum.zeroLocus_nilradical]
      exact Order.krullDim_eq_of_orderIso (OrderIso.Set.univ)
    rw [hdimred, hdim]
  let xS : S := Ideal.Quotient.mk (nilradical R) x
  have hxS : xS ∈ IsLocalRing.maximalIdeal S := by
    change x ∈ Ideal.comap (Ideal.Quotient.mk (nilradical R))
      (IsLocalRing.maximalIdeal S)
    rw [IsLocalRing.maximalIdeal_comap]
    exact hx
  have hminS : ∀ p ∈ (⊥ : Ideal S).minimalPrimes, xS ∉ p := by
    intro q hq hqx
    let p : Ideal R := Ideal.comap (Ideal.Quotient.mk (nilradical R)) q
    have hp : p ∈ (⊥ : Ideal R).minimalPrimes := by
      rw [show (⊥ : Ideal R).minimalPrimes = (nilradical R).minimalPrimes by
        simpa [nilradical] using
          (Ideal.radical_minimalPrimes (I := (⊥ : Ideal R))).symm]
      rw [Ideal.minimalPrimes_eq_comap]
      exact ⟨q, by simpa [S] using hq, rfl⟩
    exact hmin p hp hqx
  have hxregS : xS ∈ nonZeroDivisors S := by
    by_contra hreg
    have hxzero : xS ∈
        Formalization.Books.Algebra.Unit25.zeroDivisors (R := S) := hreg
    rw [← Formalization.Books.Algebra.Unit25.iUnion_minimalPrimeSpectrum_eq_zeroDivisors]
      at hxzero
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxzero
    exact hminS p.1.asIdeal p.2 hxp
  have hSbound := lemma_polypoly S hdimS xS hxS hminS
  have hfin_pow : ∀ k : ℕ, 0 < k →
      IsFiniteLength S (S ⧸ Ideal.span ({xS ^ k} : Set S)) := by
    intro k hk
    have hpow : xS ^ k ∈ IsLocalRing.maximalIdeal S :=
      Ideal.pow_mem_of_mem _ hxS k hk
    have hpowmin : ∀ p ∈ (⊥ : Ideal S).minimalPrimes, xS ^ k ∉ p := by
      intro p hp hxp
      exact hminS p hp ((Ideal.IsMinimalPrime.isPrime hp).mem_of_pow_mem k hxp)
    have hqdim :
        ringKrullDim (S ⧸ Ideal.span ({xS ^ k} : Set S)) = 0 := by
      have h := one_equation_dimension_eq_of_not_mem_minimalPrimes
        S (by infer_instance) (xS ^ k) hpow hpowmin
      rw [hdimS] at h
      apply ENat.WithBot.add_one_cancel.mp
      simpa [zero_add] using h.symm
    let I : Ideal S := Ideal.span ({xS ^ k} : Set S)
    have hItop : I ≠ ⊤ := by
      intro htop
      have hIle : I ≤ IsLocalRing.maximalIdeal S := by
        apply Ideal.span_le.mpr
        simpa [I] using hpow
      have h1 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
        apply hIle
        rw [htop]
        exact Set.mem_univ 1
      exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1
    let Q' := S ⧸ I
    letI : Nontrivial Q' := Ideal.Quotient.nontrivial_iff.mpr hItop
    letI : IsLocalRing Q' :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    letI : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    letI : Ring.KrullDimLE 0 Q' :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr (by
        simpa [Q', I] using hqdim)
    have hradq : (⊥ : Ideal Q').radical = IsLocalRing.maximalIdeal Q' :=
      Ring.KrullDimLE.radical_eq_maximalIdeal (⊥ : Ideal Q') bot_ne_top
    have hdef : Formalization.Books.Algebra.Unit59.IsIdealOfDefinition S I := by
      unfold Formalization.Books.Algebra.Unit59.IsIdealOfDefinition
      calc
        I.radical = Ideal.comap (Ideal.Quotient.mk I)
            ((⊥ : Ideal Q').radical) := by
          rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        _ = Ideal.comap (Ideal.Quotient.mk I)
            (IsLocalRing.maximalIdeal Q') := by rw [hradq]
        _ = IsLocalRing.maximalIdeal S := IsLocalRing.maximalIdeal_comap _
    have hkill : I ^ 1 • (⊤ : Submodule S Q') = ⊥ := by
      simp only [pow_one]
      rw [Ideal.smul_top_eq_map]
      have hmapzero : I.map (algebraMap S Q') = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker]
        intro z hz
        rw [RingHom.mem_ker]
        change Ideal.Quotient.mk I z = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact hz
      rw [hmapzero]
      rfl
    exact Formalization.Books.Algebra.Unit59.finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition
      I hdef ⟨1, by simpa [Q', I, pow_one] using hkill⟩
  let P := {p : Ideal S // p ∈ (⊥ : Ideal S).minimalPrimes}
  have hPfin : (⊥ : Ideal S).minimalPrimes.Finite :=
    minimalPrimes.finite_of_isNoetherianRing S
  letI : Finite P := hPfin.to_subtype
  letI : Fintype P := Fintype.ofFinite P
  let f : S →ₗ[S] (∀ p : P, S ⧸ p.1) :=
    { toFun := fun a p => Ideal.Quotient.mk p.1 a
      map_add' := by
        intro a b
        funext p
        simp
      map_smul' := by
        intro a b
        funext p
        change Ideal.Quotient.mk p.1 (a * b) =
          Ideal.Quotient.mk p.1 a * Ideal.Quotient.mk p.1 b
        simp }
  have hf : Function.Injective f := by
    intro a b hab
    apply sub_eq_zero.mp
    have hab' : a - b ∈ (⊥ : Ideal S).radical := by
      rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro p hp
      have he : Ideal.Quotient.mk p a = Ideal.Quotient.mk p b := by
        exact congrFun hab (⟨p, hp⟩ : P)
      have hp' : Ideal.Quotient.mk p (a - b) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr he
      rw [Ideal.Quotient.eq_zero_iff_mem] at hp'
      exact hp'
    have hrad : (⊥ : Ideal S).radical = ⊥ :=
      Ideal.radical_eq_iff.mpr Ideal.isRadical_bot
    rw [hrad] at hab'
    exact hab'
  let Jp : P → Ideal S := fun p =>
    ∏ q ∈ (Finset.univ.erase p), (q.1 : Ideal S)
  have hJpnot : ∀ p : P, ¬ Jp p ≤ p.1 := by
    intro p hle
    obtain ⟨q, hq, hqp⟩ :=
      (Ideal.IsPrime.prod_le (Ideal.IsMinimalPrime.isPrime p.2)).mp hle
    have hneq : q ≠ p := by
      exact (Finset.mem_erase.mp hq).1
    have hpmin : Minimal (fun I : Ideal S => I.IsPrime) p.1 :=
      (IsMinimalPrime.iff_minimal p.1).mp p.2
    have heq : p.1 = q.1 :=
      (hpmin.eq_of_le (Ideal.IsMinimalPrime.isPrime q.2) hqp).symm
    exact hneq (Subtype.ext heq.symm)
  have hb : ∀ p : P, ∃ y : S, y ∈ Jp p ∧ y ∉ p.1 := by
    intro p
    have hnotall : ¬ (∀ ⦃y : S⦄, y ∈ Jp p → y ∈ p.1) := by
      exact hJpnot p
    push_neg at hnotall
    exact hnotall
  choose b hbJ hbnot using hb
  let a : P → S := fun p => xS * b p
  have hanot : ∀ p : P, a p ∉ p.1 := by
    intro p ha
    have hmul : xS * b p ∈ p.1 := by simpa [a] using ha
    exact (Ideal.IsMinimalPrime.isPrime p.2).mem_or_mem hmul |>.elim
      (hminS p.1 p.2) (hbnot p)
  let J : Ideal S := Ideal.span (Set.range a)
  have hJle : J ≤ IsLocalRing.maximalIdeal S := by
    apply Ideal.span_le.mpr
    rintro z ⟨p, rfl⟩
    exact (IsLocalRing.maximalIdeal S).mul_mem_right _ hxS
  have hJnot : ∀ p : P, ¬ J ≤ p.1 := by
    intro p hle
    exact hanot p (hle (Ideal.subset_span ⟨p, rfl⟩))
  have hprime_max : ∀ q : Ideal S, q.IsPrime → J ≤ q →
      q = IsLocalRing.maximalIdeal S := by
    intro q hq hJq
    letI : q.IsPrime := hq
    obtain ⟨p, hp, hpq⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := q) bot_le
    have hpqne : p ≠ q := by
      intro heq
      apply hJnot ⟨p, hp⟩
      simpa [heq] using hJq
    have hpq' : p < q := lt_of_le_of_ne hpq hpqne
    letI : p.IsPrime := Ideal.IsMinimalPrime.isPrime hp
    have hqone : (1 : ℕ∞) ≤ q.height := by
      calc
        (1 : ℕ∞) = 1 + 0 := by simp
        _ ≤ 1 + p.height := by
          simpa [add_comm] using
            (add_le_add_left (show (0 : ℕ∞) ≤ p.height from bot_le) 1)
        _ = p.height + 1 := add_comm _ _
        _ ≤ q.height :=
          Ideal.height_add_one_le_of_lt_of_isPrime hpq'
    have hqle : q.height ≤ (1 : ℕ∞) := by
      have hqle' := q.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
      rw [hdimS] at hqle'
      exact WithBot.coe_le_coe.mp hqle'
    have hqheight : q.height = ringKrullDim S := by
      rw [hdimS]
      have hqeq : q.height = (1 : ℕ∞) := le_antisymm hqle hqone
      exact_mod_cast hqeq
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_of_height_eq_ringKrullDim hqheight)
  have hJrad : J.radical = IsLocalRing.maximalIdeal S := by
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · apply sInf_le
      exact ⟨hJle, (IsLocalRing.maximalIdeal.isMaximal S).isPrime⟩
    · apply le_sInf
      intro q hq
      exact (hprime_max q hq.2 hq.1).ge
  let M := (∀ p : P, S ⧸ p.1)
  let Q := M ⧸ LinearMap.range f
  have hJann : J ≤ Module.annihilator S Q := by
    apply Ideal.span_le.mpr
    rintro z ⟨p, rfl⟩
    change a p ∈ Module.annihilator S Q
    rw [Module.mem_annihilator]
    intro y
    refine Submodule.Quotient.induction_on (p := LinearMap.range f) y ?_
    intro m
    obtain ⟨r, hr⟩ := (Ideal.Quotient.mk_surjective (I := p.1)) (m p)
    have hJpq : ∀ q : P, q ≠ p → Jp p ≤ q.1 := by
      intro q hqp
      apply (Ideal.prod_le_inf.trans ?_)
      exact Finset.inf_le
        (Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩)
    have hqmem : ∀ q : P, q ≠ p → a p ∈ q.1 := by
      intro q hqp
      change xS * b p ∈ q.1
      apply q.1.mul_mem_left xS
      exact hJpq q hqp (hbJ p)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨a p * r, ?_⟩
    funext q
    by_cases hqp : q = p
    · subst q
      change Ideal.Quotient.mk p.1 (a p * r) = a p • m p
      rw [← hr]
      change Ideal.Quotient.mk p.1 (a p * r) =
        Ideal.Quotient.mk p.1 (a p) * Ideal.Quotient.mk p.1 r
      simp [f]
    · have haq : Ideal.Quotient.mk q.1 (a p) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact hqmem q hqp
      change Ideal.Quotient.mk q.1 (a p * r) = a p • m q
      rw [show a p • m q = 0 by
        change Ideal.Quotient.mk q.1 (a p) * m q = 0
        rw [haq, zero_mul]]
      rw [map_mul, haq, zero_mul]
  have hxJ : ∃ k : ℕ, 0 < k ∧ xS ^ k ∈ J := by
    have hxrad : xS ∈ J.radical := by
      rw [hJrad]
      exact hxS
    obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff).mp hxrad
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    simpa [pow_succ, mul_comm] using J.mul_mem_right xS hn
  obtain ⟨k, hk, hxkJ⟩ := hxJ
  let I : Ideal S := Ideal.span ({xS ^ k} : Set S)
  let A := S ⧸ I
  let N : Submodule S M := I • (⊤ : Submodule S M)
  let B := M ⧸ N
  have hAfin : IsFiniteLength S A := by
    simpa [A, I] using hfin_pow k hk
  have hIann : I ≤ Module.annihilator S Q := by
    apply Ideal.span_le.mpr
    intro z hz
    obtain ⟨rfl⟩ := hz
    exact hJann hxkJ
  have hIdef : Formalization.Books.Algebra.Unit59.IsIdealOfDefinition S I := by
    have hpow : xS ^ k ∈ IsLocalRing.maximalIdeal S :=
      Ideal.pow_mem_of_mem _ hxS k hk
    have hpowmin : ∀ p ∈ (⊥ : Ideal S).minimalPrimes, xS ^ k ∉ p := by
      intro p hp hxp
      exact hminS p hp ((Ideal.IsMinimalPrime.isPrime hp).mem_of_pow_mem k hxp)
    have hqdim : ringKrullDim (S ⧸ I) = 0 := by
      have h := one_equation_dimension_eq_of_not_mem_minimalPrimes
        S (by infer_instance) (xS ^ k) hpow hpowmin
      rw [hdimS] at h
      apply ENat.WithBot.add_one_cancel.mp
      simpa [I, zero_add] using h.symm
    have hIle : I ≤ IsLocalRing.maximalIdeal S := by
      apply Ideal.span_le.mpr
      simpa [I] using hpow
    have hItop : I ≠ (⊤ : Ideal S) := by
      intro htop
      have h1 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
        apply hIle
        rw [htop]
        exact Set.mem_univ 1
      exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1
    let A' := S ⧸ I
    letI : Nontrivial A' := Ideal.Quotient.nontrivial_iff.mpr hItop
    letI : IsLocalRing A' :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    letI : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    letI : Ring.KrullDimLE 0 A' :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr (by
        simpa [A'] using hqdim)
    have hrad : (⊥ : Ideal A').radical = IsLocalRing.maximalIdeal A' :=
      Ring.KrullDimLE.radical_eq_maximalIdeal (⊥ : Ideal A') bot_ne_top
    unfold Formalization.Books.Algebra.Unit59.IsIdealOfDefinition
    calc
      I.radical = Ideal.comap (Ideal.Quotient.mk I)
          ((⊥ : Ideal A').radical) := by
        rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      _ = Ideal.comap (Ideal.Quotient.mk I)
          (IsLocalRing.maximalIdeal A') := by rw [hrad]
      _ = IsLocalRing.maximalIdeal S := IsLocalRing.maximalIdeal_comap _
  have hkillB : I • (⊤ : Submodule S B) = ⊥ := by
    have hmap : I • (⊤ : Submodule S B) =
        N.map (N.mkQ) := by
      rw [show I • (⊤ : Submodule S B) =
        (I • (⊤ : Submodule S M)).map N.mkQ by
          rw [Submodule.map_smul'', Submodule.map_top,
            LinearMap.range_eq_top.mpr N.mkQ_surjective]]
    rw [hmap]
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.comap_bot,
        Submodule.ker_mkQ]
    · exact bot_le
  have hBfin : IsFiniteLength S B :=
    Formalization.Books.Algebra.Unit59.finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition
      I hIdef ⟨1, by simpa [pow_one] using hkillB⟩
  let t : S := xS ^ k
  let uS : S →ₗ[S] S := LinearMap.mulLeft S t
  let uM : M →ₗ[S] M :=
    { toFun := fun m => t • m
      map_add' := by intro m n; simp
      map_smul' := by
        intro r m
        simp [smul_smul, mul_comm] }
  have hIrangeS : LinearMap.range uS = I := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      apply Ideal.mem_span_singleton'.mpr
      exact ⟨y, by simp [uS, t, mul_comm]⟩
    · intro hz
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (by simpa [I] using hz)
      refine ⟨y, ?_⟩
      simpa [uS, t, mul_comm] using hy
  have hIrangeM : LinearMap.range uM = N := by
    apply le_antisymm
    · rintro z ⟨m, rfl⟩
      exact Submodule.smul_mem_smul (by simpa [I, t]) Submodule.mem_top
    · refine Submodule.smul_le.mpr ?_
      intro r hr m hm
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (by simpa [I] using hr)
      refine ⟨y • m, ?_⟩
      change t • (y • m) = r • m
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun z : S => z • m) hy
  let q : M →ₗ[S] Q := (LinearMap.range f).mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hqexact : Function.Exact f q := LinearMap.exact_map_mkQ_range f
  have h1 : f.comp uS = uM.comp f := by
    apply LinearMap.ext
    intro z
    funext p
    change Ideal.Quotient.mk p.1 (t * z) =
      Ideal.Quotient.mk p.1 t * Ideal.Quotient.mk p.1 z
    simp
  have h2 : q.comp uM = (0 : Q →ₗ[S] Q).comp q := by
    apply LinearMap.ext
    intro m
    have htann : t ∈ Module.annihilator S Q := hIann (by simpa [I, t])
    rw [Module.mem_annihilator] at htann
    change q (t • m) = 0
    rw [q.map_smul]
    exact htann (q m)
  have huM : Function.Injective uM := by
    intro m n hmn
    funext p
    letI : p.1.IsPrime := Ideal.IsMinimalPrime.isPrime p.2
    have htp : Ideal.Quotient.mk p.1 t ≠ 0 := by
      intro hzero
      apply hminS p.1 p.2
      rw [Ideal.Quotient.eq_zero_iff_mem] at hzero
      exact (Ideal.IsMinimalPrime.isPrime p.2).mem_of_pow_mem k (by simpa [t] using hzero)
    have hmul := congrFun hmn p
    change t • m p = t • n p at hmul
    have hmul' : Ideal.Quotient.mk p.1 t * m p =
        Ideal.Quotient.mk p.1 t * n p := by
      change Ideal.Quotient.mk p.1 t * m p =
        Ideal.Quotient.mk p.1 t * n p at hmul
      exact hmul
    exact (mul_eq_mul_left_iff.mp hmul').resolve_right htp
  have hπ1 : Function.Exact uS I.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, hIrangeS]
  have hπ2 : Function.Exact uM N.mkQ := by
    apply LinearMap.exact_iff.mpr
    rw [Submodule.ker_mkQ, hIrangeM]
  have hIker : I ≤ LinearMap.ker (N.mkQ.comp f) := by
    intro z hz
    rw [LinearMap.mem_ker]
    change N.mkQ (f z) = 0
    rw [N.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hfz : f z = z • f 1 := by simpa using f.map_smul z (1 : S)
    rw [hfz]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  let G : A →ₗ[S] B := I.liftQ (N.mkQ.comp f) hIker
  have hG : G.comp I.mkQ = N.mkQ.comp f := by
    rw [Submodule.liftQ_mkQ]
  let δ : Q →ₗ[S] A :=
    SnakeLemma.δ uS uM (0 : Q →ₗ[S] Q) f q hqexact
      f q hqexact h1 h2 (Function.surjInv hq) (Function.comp_surjInv hq)
      (Function.invFun f) (Function.invFun_comp hf)
      (LinearMap.id : Q →ₗ[S] Q) (by
        rw [LinearMap.exact_iff]
        ext z
        simp) I.mkQ hπ1
  have hsnake : Function.Exact
      δ G := by
    apply SnakeLemma.exact_δ_left uS uM (0 : Q →ₗ[S] Q) f q hqexact
      f q hqexact h1 h2 (Function.surjInv hq) (Function.comp_surjInv hq)
      (Function.invFun f) (Function.invFun_comp hf)
      (LinearMap.id : Q →ₗ[S] Q) (by
        rw [LinearMap.exact_iff]
        simp) I.mkQ hπ1 N.mkQ hπ2 G
    simpa [G] using hG
    exact Submodule.mkQ_surjective _
  have hzero_uM : Function.Exact (0 : S →ₗ[S] M) uM := by
    rw [LinearMap.exact_iff, LinearMap.ker_eq_bot.mpr huM]
    simp
  have hδexact : Function.Exact (0 : S →ₗ[S] Q) δ := by
    apply SnakeLemma.exact_δ_right uS uM (0 : Q →ₗ[S] Q) f q hqexact
      f q hqexact h1 h2 (Function.surjInv hq) (Function.comp_surjInv hq)
      (Function.invFun f) (Function.invFun_comp hf)
      (0 : S →ₗ[S] M) hzero_uM (LinearMap.id : Q →ₗ[S] Q) (by
        rw [LinearMap.exact_iff]
        ext z
        simp) I.mkQ hπ1 (0 : S →ₗ[S] Q) (by simp)
      (by intro z w h; exact h)
  have hδinj : Function.Injective δ := by
    apply LinearMap.ker_eq_bot.mp
    simpa using LinearMap.exact_iff.mp hδexact
  let Gcod : A →ₗ[S] LinearMap.range G :=
    G.codRestrict (LinearMap.range G) (LinearMap.mem_range_self G)
  have hGcod : Function.Surjective Gcod := by
    intro y
    rcases y.property with ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩
  have hδGcod : Function.Exact δ Gcod := by
    rw [LinearMap.exact_iff, LinearMap.ker_codRestrict]
    exact LinearMap.exact_iff.mp hsnake
  have hAlen : Module.length S A =
      Module.length S Q + Module.length S (LinearMap.range G) :=
    Module.length_eq_add_of_exact δ Gcod hδinj hGcod hδGcod
  have hNker : N ≤ LinearMap.ker q := by
    refine Submodule.smul_le.mpr ?_
    intro z hz m hm
    rw [LinearMap.mem_ker]
    change q (z • m) = 0
    rw [q.map_smul]
    have hzann : z ∈ Module.annihilator S Q := hIann hz
    rw [Module.mem_annihilator] at hzann
    exact hzann (q m)
  let qbar : B →ₗ[S] Q := N.liftQ q hNker
  have hqbar : Function.Surjective qbar := by
    intro y
    obtain ⟨m, hm⟩ := hq y
    refine ⟨N.mkQ m, ?_⟩
    change q m = y
    exact hm
  have hGzero : qbar.comp G = 0 := by
    apply LinearMap.ext
    intro y
    refine Submodule.Quotient.induction_on (p := I) y ?_
    intro z
    change q (f z) = 0
    change Submodule.Quotient.mk (p := LinearMap.range f) (f z) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self f z
  have hcomp : qbar.comp (LinearMap.range G).subtype = 0 := by
    apply LinearMap.ext
    intro y
    rcases y.property with ⟨z, hz⟩
    change qbar (y : B) = 0
    rw [← hz]
    exact DFunLike.congr_fun hGzero z
  have hGBexact : Function.Exact (LinearMap.range G).subtype qbar := by
    apply LinearMap.exact_of_comp_of_mem_range hcomp
    intro y hy
    refine Submodule.Quotient.induction_on (p := N) y ?_ hy
    intro m hm
    have hqm : q m = 0 := by
      change q m = 0 at hm
      exact hm
    have hmrange : m ∈ LinearMap.range f := by
      rw [← LinearMap.exact_iff.mp hqexact]
      exact hqm
    obtain ⟨z, rfl⟩ := hmrange
    refine ⟨Gcod (I.mkQ z), ?_⟩
    change G (I.mkQ z) = N.mkQ (f z)
    exact DFunLike.congr_fun hG z
  have hBlen : Module.length S B =
      Module.length S (LinearMap.range G) + Module.length S Q :=
    Module.length_eq_add_of_exact (LinearMap.range G).subtype qbar
      (Submodule.subtype_injective _) hqbar hGBexact
  have hlenAB : Module.length S A = Module.length S B := by
    calc
      Module.length S A = Module.length S Q + Module.length S (LinearMap.range G) := hAlen
      _ = Module.length S (LinearMap.range G) + Module.length S Q := add_comm _ _
      _ = Module.length S B := hBlen.symm
  sorry

/-! ## Extending a parameter sequence -/

/-- A non-minimal-prime element can be completed to parameters, with the
other parameters chosen in any prescribed power of the maximal ideal. -/
theorem lemma_sopexists
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hd : 1 < d)
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, f ∉ p)
    (k : ℕ) :
    ∃ (g : Fin d → R) (i : Fin d),
      g i = f ∧
        (∀ j : Fin d, j ≠ i → g j ∈ (IsLocalRing.maximalIdeal R) ^ k) ∧
          IsSystemOfParameters R d g := by
  sorry

/-! ## Stability of parameter quotients -/

/-- In dimension two, a parameter pair and its sufficiently high-order
perturbations have the same quotient length. -/
theorem lemma_syspar
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 2)
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, f ∉ p) :
    ∃ (g : R) (N : ℕ),
      IsSystemOfParameters R 2 ![f, g] ∧
        ∀ h ∈ (IsLocalRing.maximalIdeal R) ^ N,
          IsSystemOfParameters R 2 ![f + h, g] ∧
            idealQuotientLength (Ideal.span (Set.range ![f, g])) =
              idealQuotientLength (Ideal.span (Set.range ![f + h, g])) := by
  sorry

/-! ## Reduced principal quotients in dimension two -/

/-- Finitely many distinct height-one primes in a two-dimensional normal local
domain contain a nonzero element generating a radical ideal. -/
theorem lemma_radical_element
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : Formalization.Books.Algebra.Unit37.IsNormalDomain R)
    (hdim : ringKrullDim R = 2)
    (r : ℕ) (p : Fin r → Ideal R)
    (hp : ∀ i, (p i).IsPrime ∧ (p i).height = 1)
    (hdistinct : ∀ ⦃i j : Fin r⦄, i ≠ j → p i ≠ p j) :
    ∃ f : R,
      f ≠ 0 ∧ (∀ i, f ∈ p i) ∧
        IsReduced (R ⧸ Ideal.span ({f} : Set R)) := by
  sorry

/-- A nonzero element in the maximal ideal divides a power of a reduced
principal element. -/
theorem lemma_divides_radical
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Formalization.Books.Algebra.Unit37.IsNormalDomain A)
    (hdim : ringKrullDim A = 2)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (ha0 : a ≠ 0) :
    ∃ c : A,
      IsReduced (A ⧸ Ideal.span ({c} : Set A)) ∧
        ∃ n : ℕ, a ∣ c ^ n := by
  sorry

/-! ## Multiplicity -/

/-- The multiplicity of a parameter ideal is bounded by its colength. -/
theorem lemma_multiplicity
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = d)
    (g : Fin d → R) (hg : IsSystemOfParameters R d g) :
    ∀ (e : ℕ) (P : Polynomial ℚ),
      Formalization.Books.Algebra.Unit59.IsEventuallyRationalPolynomial
          (Formalization.Books.Algebra.Unit59.idealCumulativeHilbertFunctionInteger
            (Ideal.span (Set.range g)) R) P →
        P.degree = d →
          P.leadingCoeff = (e : ℚ) / (Nat.factorial d : ℚ) →
            e ≤ idealQuotientLength (Ideal.span (Set.range g)) := by
  sorry

/-! ## Minimal primes in higher dimension -/

/-- The number of top-dimensional minimal primes is bounded by the length of
a parameter-ideal quotient. -/
theorem lemma_minprimespolyhigher
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = d)
    (g : Fin d → R) (hg : IsSystemOfParameters R d g) :
    Nat.card
        {p : Ideal R //
          p ∈ (⊥ : Ideal R).minimalPrimes ∧
            ringKrullDim (R ⧸ p) = d} ≤
      idealQuotientLength (Ideal.span (Set.range g)) := by
  sorry

/-! ## Stable parameter systems in higher dimension -/

/-- In any dimension, a parameter system beginning with a non-minimal-prime
element is stable under sufficiently high-order perturbations of that entry. -/
theorem lemma_sysparhigher
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = d)
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hmin : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, f ∉ p) :
    ∃ (g : Fin d → R) (i : Fin d) (N : ℕ),
      g i = f ∧
        IsSystemOfParameters R d g ∧
          ∀ h ∈ (IsLocalRing.maximalIdeal R) ^ N,
            IsSystemOfParameters R d (Function.update g i (f + h)) ∧
              idealQuotientLength (Ideal.span (Set.range g)) =
                idealQuotientLength
                  (Ideal.span (Set.range (Function.update g i (f + h)))) := by
  sorry

/-! ## The principal radical ideal theorem -/

/-- A nonzero radical ideal in a catenary Noetherian normal local domain
contains a nonzero element generating a radical ideal. -/
theorem proposition_propdimd
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : Formalization.Books.Algebra.Unit37.IsNormalDomain R)
    (hcat : Formalization.Books.Algebra.Unit105.IsCatenaryRing R)
    (J : Ideal R) (hJ : J.IsRadical) (hJ0 : J ≠ ⊥) :
    ∃ f : R,
      f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ Ideal.span ({f} : Set R)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit126
