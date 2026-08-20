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

private lemma mem_sup_span_singleton
    {S : Type*} [CommRing S] (p : Ideal S) (x z : S)
    (hz : z ∈ p ⊔ Ideal.span ({x} : Set S)) :
    ∃ y ∈ p, ∃ a : S, z = y + a * x := by
  obtain ⟨y, hy, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hz'
  exact ⟨y, hy, a, by simp [ha]⟩

private lemma mem_sup_span_pow
    {S : Type*} [CommRing S] (p : Ideal S) (x : S) (n : ℕ) (z : S)
    (hz : x * z ∈ p ⊔ Ideal.span ({x ^ (n + 1)} : Set S)) :
    ∃ y ∈ p, ∃ a : S, y + a * x ^ (n + 1) = x * z := by
  obtain ⟨y, hy, z', hz', hsum⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hz'
  exact ⟨y, hy, a, by
    calc
      y + a * x ^ (n + 1) = y + z' := by rw [ha]
      _ = x * z := hsum⟩

private lemma length_sup_pow_succ_toNat
    {S : Type*} [CommRing S] (p : Ideal S) (hp : p.IsPrime)
    (x : S) (hxnot : x ∉ p) (n : ℕ) (hn : 0 < n)
    (hfin : ∀ m : ℕ, 0 < m →
      IsFiniteLength S (S ⧸ (p ⊔ Ideal.span ({x ^ m} : Set S)))) :
    (Module.length S (S ⧸ (p ⊔ Ideal.span ({x ^ (n + 1)} : Set S)))).toNat =
      (Module.length S (S ⧸ (p ⊔ Ideal.span ({x ^ n} : Set S)))).toNat +
        (Module.length S (S ⧸ (p ⊔ Ideal.span ({x ^ 1} : Set S)))).toNat := by
  let K : ℕ → Ideal S := fun m =>
    p ⊔ Ideal.span ({x ^ m} : Set S)
  have hker : K n ≤ LinearMap.ker
      ((K (n + 1)).mkQ.comp (LinearMap.mulLeft S x)) := by
    intro z hz
    rw [LinearMap.mem_ker]
    change (K (n + 1)).mkQ (x * z) = 0
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    obtain ⟨y, hy, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
    dsimp [K]
    rw [mul_add]
    apply Submodule.add_mem_sup
    · exact p.mul_mem_left x hy
    · obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hz'
      change x * z' ∈ Ideal.span ({x ^ (n + 1)} : Set S)
      rw [← ha]
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
        (Ideal.span ({x ^ (n + 1)} : Set S)).mul_mem_left a
          (Ideal.subset_span (show x ^ (n + 1) ∈
            ({x ^ (n + 1)} : Set S) by simp))
  let f : S ⧸ K n →ₗ[S] S ⧸ K (n + 1) :=
    (K n).liftQ ((K (n + 1)).mkQ.comp (LinearMap.mulLeft S x)) hker
  have hle : K (n + 1) ≤ K 1 := by
    apply sup_le
    · exact le_sup_left
    · apply Ideal.span_le.mpr
      rintro z ⟨rfl⟩
      dsimp [K]
      apply Ideal.mem_sup_right
      exact Ideal.mem_span_singleton'.mpr ⟨x ^ n, by
        simp [pow_succ, mul_comm]⟩
  have hgker : K (n + 1) ≤ LinearMap.ker (K 1).mkQ := by
    simpa [Submodule.ker_mkQ] using hle
  let g : S ⧸ K (n + 1) →ₗ[S] S ⧸ K 1 :=
    (K (n + 1)).liftQ (K 1).mkQ hgker
  have hf (z : S) : f ((K n).mkQ z) =
      (K (n + 1)).mkQ (x * z) := by
    change (((K n).liftQ
      ((K (n + 1)).mkQ.comp (LinearMap.mulLeft S x)) hker).comp
        (K n).mkQ) z = _
    rw [Submodule.liftQ_mkQ]
    rfl
  have hg (z : S) : g ((K (n + 1)).mkQ z) = (K 1).mkQ z := by
    change (((K (n + 1)).liftQ (K 1).mkQ hgker).comp
      (K (n + 1)).mkQ) z = _
    rw [Submodule.liftQ_mkQ]
  have hex : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro y hy'
      refine Submodule.Quotient.induction_on (p := K (n + 1)) y ?_ hy'
      intro z hz
      rw [LinearMap.mem_ker] at hz
      have hz' : g ((K (n + 1)).mkQ z) = 0 := by
        simpa only [Submodule.mkQ_apply] using hz
      rw [hg] at hz'
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hz'
      have hzsup : z ∈ K 1 := hz'
      change z ∈ p ⊔ Ideal.span ({x ^ 1} : Set S) at hzsup
      obtain ⟨y', hy', a, ha⟩ := mem_sup_span_singleton p (x ^ 1) z hzsup
      refine ⟨(K n).mkQ a, ?_⟩
      rw [hf]
      rw [ha]
      have hyzero : (K (n + 1)).mkQ y' = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact Ideal.mem_sup_left hy'
      have hq : (K (n + 1)).mkQ (x * a) =
          (K (n + 1)).mkQ (y' + a * x) := by
        calc
          (K (n + 1)).mkQ (x * a) = (K (n + 1)).mkQ (a * x) := by
            rw [mul_comm]
          _ = 0 + (K (n + 1)).mkQ (a * x) := by rw [zero_add]
          _ = (K (n + 1)).mkQ (y' + a * x) := by
            rw [(K (n + 1)).mkQ.map_add, hyzero, zero_add]
      simpa only [Submodule.mkQ_apply, pow_one] using hq
    · intro y
      rintro ⟨z, rfl⟩
      refine Submodule.Quotient.induction_on (p := K n) z ?_
      intro a
      rw [LinearMap.mem_ker]
      change g (f ((K n).mkQ a)) = 0
      rw [hf, hg]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      apply Ideal.mem_sup_right
      simpa [pow_one, mul_comm] using
        (Ideal.mem_span_singleton'.mpr ⟨a, by simp [mul_comm]⟩ :
          a * x ∈ Ideal.span ({x} : Set S))
  have hf_inj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    ext y
    constructor
    · intro hy'
      refine Submodule.Quotient.induction_on (p := K n) y ?_ hy'
      intro z hz
      rw [LinearMap.mem_ker] at hz
      have hz' : f ((K n).mkQ z) = 0 := by simpa using hz
      rw [hf] at hz'
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hz'
      obtain ⟨y', hy', a, hsum⟩ := mem_sup_span_pow p x n z hz'
      have hxmem : x * (z - a * x ^ n) ∈ p := by
        rw [mul_sub, ← hsum]
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hy'
      have hdiff : z - a * x ^ n ∈ p :=
        (hp.mul_mem_left_iff hxnot).mp (by simpa [mul_comm] using hxmem)
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      change z ∈ K n
      rw [← sub_add_cancel z (a * x ^ n)]
      change z - a * x ^ n + a * x ^ n ∈
        p ⊔ Ideal.span ({x ^ n} : Set S)
      exact (p ⊔ Ideal.span ({x ^ n} : Set S)).add_mem
        (Ideal.mem_sup_left hdiff)
        (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩))
    · intro hy'
      rw [Submodule.mem_bot] at hy'
      rw [hy']
      simp
  have hgsurj : Function.Surjective g := by
    intro y
    refine Submodule.Quotient.induction_on (p := K 1) y ?_
    intro z
    exact ⟨(K (n + 1)).mkQ z, rfl⟩
  have hseq := Module.length_eq_add_of_exact f g hf_inj hgsurj hex
  have hnat := congrArg ENat.toNat hseq
  rw [ENat.toNat_add] at hnat
  · simpa [K] using hnat
  · exact Module.length_ne_top_iff.mpr (hfin n hn)
  · exact Module.length_ne_top_iff.mpr (hfin 1 one_pos)

private lemma quotient_length_toNat_le_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (x : R)
    (hfin : IsFiniteLength R (R ⧸ Ideal.span ({x} : Set R))) :
    (Module.length S (S ⧸ Ideal.span ({f x} : Set S))).toNat ≤
      (Module.length R (R ⧸ Ideal.span ({x} : Set R))).toNat := by
  letI : Module R (S ⧸ Ideal.span ({f x} : Set S)) :=
    Module.compHom (S ⧸ Ideal.span ({f x} : Set S)) f
  let v : R →ₗ[R] S ⧸ Ideal.span ({f x} : Set S) :=
    { toFun := fun z => Ideal.Quotient.mk (Ideal.span ({f x} : Set S)) (f z)
      map_add' := by
        intro a b
        change Ideal.Quotient.mk (Ideal.span ({f x} : Set S)) (f (a + b)) = _
        simp
      map_smul' := by
        intro a b
        change Ideal.Quotient.mk (Ideal.span ({f x} : Set S)) (f (a * b)) =
          Ideal.Quotient.mk (Ideal.span ({f x} : Set S)) (f a) *
            Ideal.Quotient.mk (Ideal.span ({f x} : Set S)) (f b)
        simp }
  have hvker : Ideal.span ({x} : Set R) ≤ LinearMap.ker v := by
    intro z hz
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk (Ideal.span ({f x} : Set S)) (f z) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hz
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨f a, ?_⟩
    rw [← ha]
    simp [map_mul, mul_comm]
  let q : R ⧸ Ideal.span ({x} : Set R) →ₗ[R]
      S ⧸ Ideal.span ({f x} : Set S) :=
    (Ideal.span ({x} : Set R)).liftQ v hvker
  have hq : Function.Surjective q := by
    intro y
    refine Submodule.Quotient.induction_on
      (p := Ideal.span ({f x} : Set S)) y ?_
    intro z
    obtain ⟨r, hr⟩ := hf z
    refine ⟨(Ideal.span ({x} : Set R)).mkQ r, ?_⟩
    change Ideal.Quotient.mk (Ideal.span ({f x} : Set S)) (f r) = _
    rw [hr]
    rfl
  have hlen := Module.length_le_of_surjective q hq
  have hlen' :
      @Module.length R (S ⧸ Ideal.span ({f x} : Set S)) _ _
        (Module.compHom (S ⧸ Ideal.span ({f x} : Set S)) f) ≤
        Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
    simpa [q] using hlen
  have hlenS : Module.length S (S ⧸ Ideal.span ({f x} : Set S)) ≤
      Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
    rw [← Formalization.Books.Algebra.Unit52.length_eq_of_surjective_ringHom f hf]
    exact hlen'
  exact ENat.toNat_le_toNat hlenS
    (Module.length_ne_top_iff.mpr hfin)

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
  have hfinR : IsFiniteLength R (R ⧸ Ideal.span ({x} : Set R)) := by
    have hqdim : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) = 0 := by
      have h := one_equation_dimension_eq_of_not_mem_minimalPrimes
        R hR x hx hmin
      rw [hdim] at h
      apply ENat.WithBot.add_one_cancel.mp
      simpa [zero_add] using h.symm
    let I : Ideal R := Ideal.span ({x} : Set R)
    have hItop : I ≠ (⊤ : Ideal R) := by
      intro htop
      have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        apply (show I ≤ IsLocalRing.maximalIdeal R from by
          apply Ideal.span_le.mpr
          simpa [I] using hx)
        rw [htop]
        exact Set.mem_univ 1
      exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1
    let Q' := R ⧸ I
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
    have hrad : (⊥ : Ideal Q').radical = IsLocalRing.maximalIdeal Q' :=
      Ring.KrullDimLE.radical_eq_maximalIdeal (⊥ : Ideal Q') bot_ne_top
    have hdef : Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R I := by
      unfold Formalization.Books.Algebra.Unit59.IsIdealOfDefinition
      calc
        I.radical = Ideal.comap (Ideal.Quotient.mk I)
            ((⊥ : Ideal Q').radical) := by
          rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        _ = Ideal.comap (Ideal.Quotient.mk I)
            (IsLocalRing.maximalIdeal Q') := by rw [hrad]
        _ = IsLocalRing.maximalIdeal R := IsLocalRing.maximalIdeal_comap _
    have hkill : I ^ 1 • (⊤ : Submodule R Q') = ⊥ := by
      simp only [pow_one]
      rw [Ideal.smul_top_eq_map]
      have hmapzero : I.map (algebraMap R Q') = ⊥ := by
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
  have hcomponent : ∀ p : P,
      k ≤ (Module.length S (S ⧸ (p.1 ⊔ I))).toNat := by
    intro p
    let K : ℕ → Ideal S := fun n =>
      p.1 ⊔ Ideal.span ({xS ^ n} : Set S)
    have hKle : ∀ n : ℕ, 0 < n → K n ≤ IsLocalRing.maximalIdeal S := by
      intro n hn
      apply sup_le
      · letI : p.1.IsPrime := Ideal.IsMinimalPrime.isPrime p.2
        exact IsLocalRing.le_maximalIdeal_of_isPrime p.1
      · apply Ideal.span_le.mpr
        simpa [K] using Ideal.pow_mem_of_mem _ hxS n hn
    have hfinK : ∀ n : ℕ, 0 < n →
        IsFiniteLength S (S ⧸ K n) := by
      intro n hn
      let v : S ⧸ Ideal.span ({xS ^ n} : Set S) →ₗ[S] S ⧸ K n :=
        (Ideal.span ({xS ^ n} : Set S)).liftQ
          (K n).mkQ (by
            intro z hz
            rw [Submodule.ker_mkQ]
            exact Ideal.mem_sup_right hz)
      have hv : Function.Surjective v := by
        intro y
        refine Submodule.Quotient.induction_on (p := K n) y ?_
        intro z
        exact ⟨(Ideal.span ({xS ^ n} : Set S)).mkQ z, rfl⟩
      exact IsFiniteLength.of_surjective (hfin_pow n hn) hv
    have hstep : ∀ n : ℕ, 0 < n →
        (Module.length S (S ⧸ K (n + 1))).toNat =
          (Module.length S (S ⧸ K n)).toNat +
            (Module.length S (S ⧸ K 1)).toNat := by
      intro n hn
      change (Module.length S
          (S ⧸ (p.1 ⊔ Ideal.span ({xS ^ (n + 1)} : Set S)))).toNat =
        (Module.length S
          (S ⧸ (p.1 ⊔ Ideal.span ({xS ^ n} : Set S)))).toNat +
          (Module.length S
            (S ⧸ (p.1 ⊔ Ideal.span ({xS ^ 1} : Set S)))).toNat
      apply length_sup_pow_succ_toNat
        (p := p.1) (Ideal.IsMinimalPrime.isPrime p.2) xS
          (hminS p.1 p.2) n hn
      intro m hm
      change IsFiniteLength S
        (S ⧸ (p.1 ⊔ Ideal.span ({xS ^ m} : Set S)))
      exact hfinK m hm
    have hKtop : K 1 ≠ (⊤ : Ideal S) := by
      intro htop
      have h1 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
        apply hKle 1 one_pos
        rw [htop]
        exact Set.mem_univ 1
      exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1
    letI : Nontrivial (S ⧸ K 1) := Ideal.Quotient.nontrivial_iff.mpr hKtop
    have hbase : 1 ≤ (Module.length S (S ⧸ K 1)).toNat := by
      have hpos : 0 < Module.length S (S ⧸ K 1) := Module.length_pos
      exact ENat.toNat_pos (ne_of_gt hpos)
        (Module.length_ne_top_iff.mpr (hfinK 1 one_pos))
    have hind : ∀ n : ℕ, 0 < n →
        n ≤ (Module.length S (S ⧸ K n)).toNat := by
      intro n hn
      induction n with
      | zero => simp at hn
      | succ n ih =>
          by_cases hn0 : n = 0
          · subst n
            simpa [K] using hbase
          · have hi := ih (Nat.pos_of_ne_zero hn0)
            rw [hstep n (Nat.pos_of_ne_zero hn0)]
            omega
    simpa [K, I] using hind k hk
  let cp0 : ∀ p : P, S ⧸ p.1 →ₗ[S] S ⧸ (p.1 ⊔ I) := fun p =>
    p.1.liftQ (p.1 ⊔ I).mkQ (by
      intro z hz
      rw [Submodule.ker_mkQ]
      exact Ideal.mem_sup_left hz)
  let cp : M →ₗ[S] (∀ p : P, S ⧸ (p.1 ⊔ I)) :=
    { toFun := fun m p => cp0 p (m p)
      map_add' := by
        intro m n
        funext p
        change cp0 p ((m + n) p) = cp0 p (m p) + cp0 p (n p)
        exact (cp0 p).map_add _ _
      map_smul' := by
        intro r m
        funext p
        change cp0 p (r • m p) = r • cp0 p (m p)
        exact (cp0 p).map_smul _ _ }
  have hNcp : N ≤ LinearMap.ker cp := by
    change I • (⊤ : Submodule S M) ≤ LinearMap.ker cp
    refine Submodule.smul_le.mpr ?_
    intro z hz m hm
    rw [LinearMap.mem_ker]
    funext p
    change cp0 p (z • m p) = 0
    refine Submodule.Quotient.induction_on (p := p.1) (m p) ?_
    intro y
    change Ideal.Quotient.mk (p.1 ⊔ I) (z * y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.mem_sup_right
    simpa [mul_comm] using I.mul_mem_left y hz
  let qcp : B →ₗ[S] (∀ p : P, S ⧸ (p.1 ⊔ I)) := N.liftQ cp hNcp
  have hcp : Function.Surjective cp := by
    intro y
    choose s hs using fun p : P =>
      (Ideal.Quotient.mk_surjective (I := p.1 ⊔ I) (y p))
    let z : M := fun p => p.1.mkQ (s p)
    refine ⟨z, ?_⟩
    funext p
    change cp0 p (p.1.mkQ (s p)) = y p
    dsimp [cp0]
    change (p.1 ⊔ I).mkQ (s p) = y p
    exact hs p
  have hqcp : Function.Surjective qcp := by
    intro y
    obtain ⟨m, hm⟩ := hcp y
    refine ⟨N.mkQ m, ?_⟩
    change cp m = y
    exact hm
  have hprodle :
      Module.length S (∀ p : P, S ⧸ (p.1 ⊔ I)) ≤ Module.length S B := by
    simpa [B] using Module.length_le_of_surjective qcp hqcp
  have hfinCp : ∀ p : P, IsFiniteLength S (S ⧸ (p.1 ⊔ I)) := by
    intro p
    let v : A →ₗ[S] S ⧸ (p.1 ⊔ I) :=
      I.liftQ (p.1 ⊔ I).mkQ (by
        intro z hz
        rw [Submodule.ker_mkQ]
        exact Ideal.mem_sup_right hz)
    have hv : Function.Surjective v := by
      intro y
      refine Submodule.Quotient.induction_on (p := p.1 ⊔ I) y ?_
      intro z
      exact ⟨I.mkQ z, rfl⟩
    exact IsFiniteLength.of_surjective hAfin hv
  have hprodnat :
      (Module.length S (∀ p : P, S ⧸ (p.1 ⊔ I))).toNat ≤
        (Module.length S A).toNat := by
    rw [hlenAB]
    exact ENat.toNat_le_toNat hprodle
      (Module.length_ne_top_iff.mpr hBfin)
  rw [Module.length_pi_of_fintype] at hprodnat
  have hsum : Nat.card P * k ≤
      ∑ p : P, (Module.length S (S ⧸ (p.1 ⊔ I))).toNat := by
    calc
      Nat.card P * k = ∑ p : P, k := by
        simp [Nat.card_eq_fintype_card]
      _ ≤ ∑ p : P, (Module.length S (S ⧸ (p.1 ⊔ I))).toNat := by
        exact Finset.sum_le_sum (fun p _ => hcomponent p)
  have hprodnat' :
      (∑ p : P, (Module.length S (S ⧸ (p.1 ⊔ I))).toNat) ≤
        (Module.length S A).toNat := by
    rw [ENat.toNat_sum] at hprodnat
    · exact hprodnat
    · intro p hp
      exact Module.length_ne_top_iff.mpr (hfinCp p)
  have hcardk : Nat.card P * k ≤ (Module.length S A).toNat :=
    hsum.trans hprodnat'
  have hAk : (Module.length S A).toNat =
      principalPowerQuotientLength xS k := by
    simp [A, I, principalPowerQuotientLength, idealQuotientLength,
      Formalization.Books.Algebra.Unit59.moduleLengthNat]
  have hcardk' : Nat.card P * k ≤
      k * principalPowerQuotientLength xS 1 := by
    calc
      Nat.card P * k ≤ principalPowerQuotientLength xS k := by
        simpa [hAk] using hcardk
      _ ≤ k * principalPowerQuotientLength xS 1 := hSbound.1 k
  have hcardS : Nat.card P ≤ principalPowerQuotientLength xS 1 := by
    apply Nat.le_of_mul_le_mul_right
    · simpa [Nat.mul_comm] using hcardk'
    · exact hk
  have hlenRSnat :
      (Module.length S (S ⧸ Ideal.span ({xS} : Set S))).toNat ≤
        (Module.length R (R ⧸ Ideal.span ({x} : Set R))).toNat := by
    simpa [xS] using quotient_length_toNat_le_of_surjective
      (Ideal.Quotient.mk (nilradical R)) Ideal.Quotient.mk_surjective x
      hfinR
  let fmin : P → {p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes} := fun q =>
    ⟨Ideal.comap (Ideal.Quotient.mk (nilradical R)) q.1, by
      rw [show (⊥ : Ideal R).minimalPrimes = (nilradical R).minimalPrimes by
        simpa [nilradical] using
          (Ideal.radical_minimalPrimes (I := (⊥ : Ideal R))).symm]
      rw [Ideal.minimalPrimes_eq_comap]
      exact ⟨q.1, by simpa [S] using q.2, rfl⟩⟩
  have hfmin_inj : Function.Injective fmin := by
    intro p q hpq
    apply Subtype.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (nilradical R))
      Ideal.Quotient.mk_surjective
    exact congrArg Subtype.val hpq
  have hfmin_surj : Function.Surjective fmin := by
    intro p
    have hp : p.1 ∈ (nilradical R).minimalPrimes := by
      have hbotmin :
          (⊥ : Ideal R).minimalPrimes = (nilradical R).minimalPrimes := by
        simpa [nilradical] using
          (Ideal.radical_minimalPrimes (I := (⊥ : Ideal R))).symm
      exact hbotmin ▸ p.2
    have hpimage : p.1 ∈
        Ideal.comap (Ideal.Quotient.mk (nilradical R)) ''
          (⊥ : Ideal S).minimalPrimes := by
      exact (congrArg (fun s : Set (Ideal R) => p.1 ∈ s)
        (Ideal.minimalPrimes_eq_comap (I := nilradical R))).mp hp
    obtain ⟨q, hq, hqp⟩ := hpimage
    refine ⟨⟨q, hq⟩, ?_⟩
    apply Subtype.ext
    exact hqp
  let eMin : P ≃ {p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes} :=
    Equiv.ofBijective fmin ⟨hfmin_inj, hfmin_surj⟩
  have hcardR : Nat.card P ≤ principalPowerQuotientLength x 1 := by
    calc
      Nat.card P ≤ principalPowerQuotientLength xS 1 := hcardS
      _ = (Module.length S (S ⧸ Ideal.span ({xS} : Set S))).toNat := by
        change (Module.length S
          (S ⧸ Ideal.span ({xS ^ 1} : Set S))).toNat =
          (Module.length S (S ⧸ Ideal.span ({xS} : Set S))).toNat
        rw [pow_one]
      _ ≤ (Module.length R (R ⧸ Ideal.span ({x} : Set R))).toNat := hlenRSnat
      _ = principalPowerQuotientLength x 1 := by
        change (Module.length R
          (R ⧸ Ideal.span ({x} : Set R))).toNat =
          (Module.length R (R ⧸ Ideal.span ({x ^ 1} : Set R))).toNat
        rw [pow_one]
  calc
    Nat.card {p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes} = Nat.card P :=
      (Nat.card_congr eMin).symm
    _ ≤ principalPowerQuotientLength x 1 := hcardR

/-! ## Extending a parameter sequence -/

/-- A non-minimal-prime element can be completed to parameters, with the
other parameters chosen in any prescribed power of the maximal ideal. -/
theorem lemma_sopexists
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = d) (hd : 1 < d)
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
  obtain ⟨v, i, hiv, hvi, hv⟩ :=
    lemma_sopexists R 2 hdim (by norm_num) f hf hmin 0
  have hstable :
      ∀ (g : R), IsSystemOfParameters R 2 ![f, g] →
        ∃ N, ∀ h ∈ (IsLocalRing.maximalIdeal R) ^ N,
          IsSystemOfParameters R 2 ![f + h, g] ∧
            idealQuotientLength (Ideal.span (Set.range ![f, g])) =
              idealQuotientLength (Ideal.span (Set.range ![f + h, g])) := by
    intro g hvg
    let I : Ideal R := Ideal.span (Set.range ![f, g])
    have hIdef : Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R I := by
      simpa [I] using hvg.2
    have hmuldef :
        Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R
          (IsLocalRing.maximalIdeal R * I) := by
      unfold Formalization.Books.Algebra.Unit59.IsIdealOfDefinition at hIdef ⊢
      rw [Ideal.radical_mul, hIdef,
        (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical]
      exact inf_idem _
    obtain ⟨N, hN⟩ :=
      Formalization.Books.Algebra.Unit59.exists_pow_maximalIdeal_le_of_isIdealOfDefinition
        (IsLocalRing.maximalIdeal R * I) hmuldef
    refine ⟨N, ?_⟩
    intro h hh
    have hmem : h ∈ IsLocalRing.maximalIdeal R * I := hN hh
    have hmem' : h ∈ IsLocalRing.maximalIdeal R • I := by exact hmem
    obtain ⟨a, ha, hsum⟩ :=
      (Submodule.mem_ideal_smul_span_iff_exists_sum
        (I := IsLocalRing.maximalIdeal R) (f := ![f, g]) h).mp hmem'
    rw [a.sum_fintype (fun i c => c • ![f, g] i) (by simp)] at hsum
    rw [Fin.sum_univ_two] at hsum
    have hsum' : a 0 * f + a 1 * g = h := by
      simpa [smul_eq_mul] using hsum
    have ha0 : a 0 ∈ IsLocalRing.maximalIdeal R := ha 0
    have ha1 : a 1 ∈ IsLocalRing.maximalIdeal R := ha 1
    let J : Ideal R := Ideal.span (Set.range ![f + h, g])
    have hfh : f + h ∈ J := by
      apply Ideal.subset_span
      exact ⟨0, by simp⟩
    have hgJ : g ∈ J := by
      apply Ideal.subset_span
      exact ⟨1, by simp⟩
    have hunit : IsUnit (1 + a 0) := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      intro hbad
      have hone : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        simpa using (IsLocalRing.maximalIdeal R).sub_mem hbad ha0
      exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) hone
    obtain ⟨u, hu⟩ := hunit
    have huf : (1 + a 0) * f ∈ J := by
      have hsub : (f + h) - a 1 * g ∈ J :=
        J.sub_mem hfh (J.mul_mem_left _ hgJ)
      convert hsub using 1
      rw [← hsum']
      ring
    have hfJ : f ∈ J := by
      have hmul := J.mul_mem_left (↑(u⁻¹) : R) huf
      simpa [← hu, mul_assoc] using hmul
    have hJleI : J ≤ I := by
      apply Ideal.span_le.mpr
      rintro z ⟨j, rfl⟩
      fin_cases j
      · apply I.add_mem
        · exact Ideal.subset_span (by exact ⟨0, by simp⟩)
        · exact (Ideal.mul_le_left (I := IsLocalRing.maximalIdeal R) (J := I)) hmem
      · exact Ideal.subset_span (by exact ⟨1, by simp⟩)
    have hIleJ : I ≤ J := by
      apply Ideal.span_le.mpr
      rintro z ⟨j, rfl⟩
      fin_cases j
      · exact hfJ
      · exact hgJ
    have hIJ : I = J := le_antisymm hIleJ hJleI
    have hnewmem : ∀ j : Fin 2, ![f + h, g] j ∈ IsLocalRing.maximalIdeal R := by
      intro j
      fin_cases j
      · have hmemM : h ∈ IsLocalRing.maximalIdeal R :=
          (Ideal.mul_le_right (I := IsLocalRing.maximalIdeal R) (J := I)) hmem
        simpa using (IsLocalRing.maximalIdeal R).add_mem hf hmemM
      · simpa using hvg.1 1
    refine ⟨⟨hnewmem, ?_⟩, ?_⟩
    · change Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R J
      rw [← hIJ]
      exact hIdef
    · change idealQuotientLength I = idealQuotientLength J
      rw [hIJ]
  fin_cases i
  · let g := v 1
    have hv' : v = ![f, g] := by
      funext j
      fin_cases j
      · simpa using hiv
      · rfl
    have hvg : IsSystemOfParameters R 2 ![f, g] := by
      rcases hv with ⟨hv_mem, hv_def⟩
      constructor
      · intro j
        fin_cases j
        · have ht : f ∈ IsLocalRing.maximalIdeal R := by
            rw [← hiv]
            exact hv_mem 0
          simpa using ht
        · simpa [g] using hv_mem (1 : Fin 2)
      · have hspan : Ideal.span (Set.range ![f, g]) =
            Ideal.span (Set.range v) := by rw [hv']
        rw [hspan]
        exact hv_def
    obtain ⟨N, hN⟩ := hstable g hvg
    exact ⟨g, N, hvg, hN⟩
  · let g := v 0
    have hv' : v = ![g, f] := by
      funext j
      fin_cases j
      · rfl
      · simpa using hiv
    have hvg : IsSystemOfParameters R 2 ![f, g] := by
      rcases hv with ⟨hv_mem, hv_def⟩
      constructor
      · intro j
        fin_cases j
        · have ht : f ∈ IsLocalRing.maximalIdeal R := by
            rw [← hiv]
            exact hv_mem 1
          simpa using ht
        · simpa [g] using hv_mem (0 : Fin 2)
      · have hrange : Set.range ![f, g] = Set.range ![g, f] := by
          ext z
          simp [or_comm]
        have hspan : Ideal.span (Set.range ![f, g]) =
            Ideal.span (Set.range v) := by
          rw [hrange, ← hv']
        rw [hspan]
        exact hv_def
    obtain ⟨N, hN⟩ := hstable g hvg
    exact ⟨g, N, hvg, hN⟩

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
  have hdpos : 0 < d := by
    by_contra hd0
    have hdzero : d = 0 := Nat.eq_zero_of_not_pos hd0
    have hR0 : Nontrivial R := by
      by_contra hR
      letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
      have hzero : (⊥ : WithBot ℕ∞) = 0 := by simpa [hdzero] using hdim
      exact WithBot.bot_ne_coe hzero
    letI : Nontrivial R := hR0
    letI : Ring.KrullDimLE 0 R :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr (by simpa [hdzero] using hdim)
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
    have hpmax : p.IsMaximal := (Ideal.IsMinimalPrime.isPrime hp).isMaximal'
    have hpeq : p = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal hpmax
    exact hmin p hp (hpeq ▸ hf)
  have hd_cases : d = 1 ∨ 1 < d := by omega
  have hvdata : ∃ (v : Fin d → R) (i : Fin d),
      v i = f ∧ (∀ j : Fin d, j ≠ i → v j ∈ (IsLocalRing.maximalIdeal R) ^ 0) ∧
        IsSystemOfParameters R d v := by
    rcases hd_cases with rfl | hd
    · let v : Fin 1 → R := ![f]
      have hR0 : Nontrivial R := by
        by_contra hR
        letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
        rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
        have hzero : (⊥ : WithBot ℕ∞) = (1 : WithBot ℕ∞) := by simpa using hdim
        exact WithBot.bot_ne_coe hzero
      letI : Nontrivial R := hR0
      have hv : IsSystemOfParameters R 1 v := by
        constructor
        · intro j
          fin_cases j
          exact hf
        · let I : Ideal R := Ideal.span ({f} : Set R)
          have hqdim : ringKrullDim (R ⧸ I) = 0 := by
            have h := one_equation_dimension_eq_of_not_mem_minimalPrimes
              R hR0 f hf hmin
            rw [show ringKrullDim R = 1 by simpa using hdim] at h
            have h' : ringKrullDim (R ⧸ I) + 1 =
                (0 : WithBot ℕ∞) + 1 := by
              rw [zero_add]
              simpa [I] using h.symm
            exact ENat.WithBot.add_one_cancel.mp h'
          have hItop : I ≠ (⊤ : Ideal R) := by
            intro htop
            have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
              apply (show I ≤ IsLocalRing.maximalIdeal R from by
                apply Ideal.span_le.mpr
                simpa [I] using hf)
              rw [htop]
              exact Set.mem_univ 1
            exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1
          let Q := R ⧸ I
          letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hItop
          letI : IsLocalRing Q :=
            IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
              Ideal.Quotient.mk_surjective
          letI : IsLocalHom (Ideal.Quotient.mk I) :=
            IsLocalHom.of_surjective (Ideal.Quotient.mk I)
              Ideal.Quotient.mk_surjective
          letI : Ring.KrullDimLE 0 Q :=
            (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr (by
              simpa [Q] using hqdim)
          have hrad : (⊥ : Ideal Q).radical = IsLocalRing.maximalIdeal Q :=
            Ring.KrullDimLE.radical_eq_maximalIdeal (⊥ : Ideal Q) bot_ne_top
          have hdef : Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R I := by
            unfold Formalization.Books.Algebra.Unit59.IsIdealOfDefinition
            calc
              I.radical = Ideal.comap (Ideal.Quotient.mk I)
                  ((⊥ : Ideal Q).radical) := by
                rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
              _ = Ideal.comap (Ideal.Quotient.mk I)
                  (IsLocalRing.maximalIdeal Q) := by rw [hrad]
              _ = IsLocalRing.maximalIdeal R := IsLocalRing.maximalIdeal_comap _
          simpa [v, I] using hdef
      exact ⟨v, 0, rfl, by intro j hj; fin_cases j; contradiction, hv⟩
    · exact lemma_sopexists R d hdim hd f hf hmin 0
  obtain ⟨v, i, hiv, hvi, hv⟩ := hvdata
  have hstable :
      ∀ (g : Fin d → R), IsSystemOfParameters R d g → g i = f →
        ∃ N, ∀ h ∈ (IsLocalRing.maximalIdeal R) ^ N,
          IsSystemOfParameters R d (Function.update g i (f + h)) ∧
            idealQuotientLength (Ideal.span (Set.range g)) =
              idealQuotientLength
                (Ideal.span (Set.range (Function.update g i (f + h)))) := by
    intro g hvg hgi
    let I : Ideal R := Ideal.span (Set.range g)
    have hIdef : Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R I := by
      simpa [I] using hvg.2
    have hmuldef :
        Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R
          (IsLocalRing.maximalIdeal R * I) := by
      unfold Formalization.Books.Algebra.Unit59.IsIdealOfDefinition at hIdef ⊢
      rw [Ideal.radical_mul, hIdef,
        (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical]
      exact inf_idem _
    obtain ⟨N, hN⟩ :=
      Formalization.Books.Algebra.Unit59.exists_pow_maximalIdeal_le_of_isIdealOfDefinition
        (IsLocalRing.maximalIdeal R * I) hmuldef
    refine ⟨N, ?_⟩
    intro h hh
    have hmem : h ∈ IsLocalRing.maximalIdeal R * I := hN hh
    have hmem' : h ∈ IsLocalRing.maximalIdeal R • I := by exact hmem
    obtain ⟨a, ha, hsum⟩ :=
      (Submodule.mem_ideal_smul_span_iff_exists_sum
        (I := IsLocalRing.maximalIdeal R) (f := g) h).mp hmem'
    rw [a.sum_fintype (fun j c => c • g j) (by simp)] at hsum
    have hsum' : (∑ j : Fin d, a j * g j) = h := by
      simpa [smul_eq_mul] using hsum
    let J : Ideal R :=
      Ideal.span (Set.range (Function.update g i (f + h)))
    have hnewmem : ∀ j : Fin d,
        Function.update g i (f + h) j ∈ IsLocalRing.maximalIdeal R := by
      intro j
      classical
      by_cases hji : j = i
      · subst j
        have hmemM : h ∈ IsLocalRing.maximalIdeal R := by
          exact (Ideal.mul_le_right (I := IsLocalRing.maximalIdeal R) (J := I)) hmem
        simpa [hgi] using (IsLocalRing.maximalIdeal R).add_mem (hvg.1 i) hmemM
      · simpa [hji] using hvg.1 j
    have hunit : IsUnit (1 + a i) := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      intro hbad
      have hone : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        simpa using (IsLocalRing.maximalIdeal R).sub_mem hbad (ha i)
      exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) hone
    obtain ⟨u, hu⟩ := hunit
    have hfi : f ∈ J := by
      have hsum_i :
          (1 + a i) * f + ∑ j ∈ (Finset.univ.erase i), a j * g j = f + h := by
        have hdecomp :
            (∑ j ∈ (Finset.univ.erase i), a j * g j) + a i * g i =
              ∑ j : Fin d, a j * g j := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        rw [← hgi, ← hsum', ← hdecomp]
        ring
      have hgen : f + h ∈ J := by
        exact Ideal.subset_span ⟨i, by simp [J]
          ⟩
      have hrest :
          (f + h) - ∑ j ∈ (Finset.univ.erase i), a j * g j ∈ J := by
        apply J.sub_mem hgen
        apply J.sum_mem
        intro j hj
        exact J.mul_mem_left _
          (Ideal.subset_span ⟨j, by simp [J, (Finset.mem_erase.mp hj).1]⟩)
      have hmul : (1 + a i) * f ∈ J := by
        rw [← hsum_i] at hrest
        convert hrest using 1 <;> ring
      have hmul' := J.mul_mem_left (↑(u⁻¹) : R) hmul
      simpa [← hu, mul_assoc] using hmul'
    have hJleI : J ≤ I := by
      apply Ideal.span_le.mpr
      rintro z ⟨j, rfl⟩
      classical
      by_cases hji : j = i
      · subst j
        have hmemnew : f + h ∈ I := by
          apply I.add_mem
          · rw [← hgi]
            exact Ideal.subset_span ⟨i, rfl⟩
          · exact (Ideal.mul_le_left (I := IsLocalRing.maximalIdeal R) (J := I)) hmem
        simpa [Function.update] using hmemnew
      · apply Ideal.subset_span
        exact ⟨j, by simp [hji]⟩
    have hIleJ : I ≤ J := by
      apply Ideal.span_le.mpr
      rintro z ⟨j, rfl⟩
      classical
      by_cases hji : j = i
      · subst j
        simpa [hgi] using hfi
      · apply Ideal.subset_span
        exact ⟨j, by simp [hji]⟩
    have hIJ : I = J := le_antisymm hIleJ hJleI
    refine ⟨⟨hnewmem, ?_⟩, ?_⟩
    · change Formalization.Books.Algebra.Unit59.IsIdealOfDefinition R J
      rw [← hIJ]
      exact hIdef
    · change idealQuotientLength I = idealQuotientLength J
      rw [hIJ]
  obtain ⟨N, hN⟩ := hstable v hv hiv
  exact ⟨v, i, N, hiv, hv, hN⟩

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
