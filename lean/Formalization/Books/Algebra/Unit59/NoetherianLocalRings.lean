import Formalization.Books.Algebra.Unit51.MoreNoetherianRings
import Formalization.Books.Algebra.Unit52.Length
import Formalization.Books.Algebra.Unit58.NoetherianGradedRings
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Operations

/-!
# Commutative Algebra, Chapter 59: Noetherian local rings

The source's Hilbert functions use the canonical `Module.length` and
submodule quotients.  Numerical-polynomial assertions are phrased using the
integer-valued interface from Chapter 58; the functions on `ℕ` are extended
by zero to `ℤ` only to match that interface.
-/

namespace Formalization.Books.Algebra.Unit59

open Formalization.Books.Algebra.Unit58
open scoped BigOperators

universe u v w

noncomputable section

/-! ## Powers and lengths -/

/- The quotient of successive powers of an ideal acting on a module. -/
abbrev idealPowerPiece
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : Type v :=
  let N : Submodule R M := I ^ n • (⊤ : Submodule R M)
  N ⧸ Submodule.comap N.subtype (I ^ (n + 1) • (⊤ : Submodule R M))

/- The quotient occurring in the cumulative Hilbert function. -/
abbrev idealPowerCumulativeQuotient
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : Type v :=
  M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))

/- Mathlib's length is extended-natural-valued; under the finite-length
   hypotheses in the source, this is its ordinary natural-number value. -/
def moduleLengthNat
    {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] : ℕ :=
  (Module.length R M).toNat

private theorem finiteLength_of_maximalIdeal_pow_smul_top_eq_bot
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : ∃ s : ℕ,
      (IsLocalRing.maximalIdeal R) ^ s • (⊤ : Submodule R M) = ⊥) :
    IsFiniteLength R M := by
  obtain ⟨s, hs⟩ := hM
  let K : Ideal R := (IsLocalRing.maximalIdeal R) ^ s
  have hkill : K • (⊤ : Submodule R M) = ⊥ := by
    simpa [K] using hs
  by_cases hK : K = ⊤
  · let : Subsingleton M := by
      constructor
      intro x y
      apply sub_eq_zero.mp
      have hx : x - y ∈ K • (⊤ : Submodule R M) := by
        rw [hK]
        simp
      rw [hkill] at hx
      simpa using hx
    exact IsFiniteLength.of_subsingleton
  · let S := R ⧸ K
    let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hK
    let : IsLocalRing S :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective
    let : IsNoetherianRing S :=
      isNoetherianRing_of_surjective R S (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective
    have hmap :
        (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk K) =
          IsLocalRing.maximalIdeal S :=
      IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective
    let : IsSemiprimaryRing S :=
      { isSemisimpleRing := by
          have hJac : Ring.jacobson S = IsLocalRing.maximalIdeal S :=
            IsLocalRing.ringJacobson_eq_maximalIdeal S
          let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal S)
          exact (Ideal.quotEquivOfEq hJac).symm.isSemisimpleRing
        isNilpotent := by
          rw [IsLocalRing.ringJacobson_eq_maximalIdeal S, ← hmap]
          refine ⟨s, ?_⟩
          rw [← Ideal.map_pow, Ideal.zero_eq_bot,
            Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] }
    have htors : Module.IsTorsionBySet R M K := by
      rw [Module.isTorsionBySet_iff_subset_annihilator]
      change K ≤ Module.annihilator R M
      rw [← Submodule.annihilator_top, Submodule.le_annihilator_iff]
      exact hkill
    let : Module S M := htors.module
    let : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
    have hfinS : IsNoetherian S M := inferInstance
    have hArtS : IsArtinian S M :=
      (IsSemiprimaryRing.isNoetherian_iff_isArtinian (R := S) (M := M)).mp hfinS
    have hArtR : IsArtinian R M :=
      (LinearMap.isArtinian_iff_of_bijective htors.semilinearMap
        Function.bijective_id).mpr hArtS
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hArtR⟩

/-! ## The maximal-ideal Hilbert functions -/

def hilbertFunction
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  moduleLengthNat (R := R)
    (M := idealPowerPiece (IsLocalRing.maximalIdeal R) M n)

def cumulativeHilbertFunction
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  moduleLengthNat (R := R)
    (M := idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M n)

theorem cumulativeHilbertFunction_eq_sum
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) :
    cumulativeHilbertFunction R M n =
      ∑ i ∈ Finset.range (n + 1), hilbertFunction R M i := by
  have hlength (P Q : Submodule R M) (hQP : Q ≤ P) :
      Module.length R (M ⧸ Q) =
        Module.length R (P ⧸ Submodule.comap P.subtype Q) +
          Module.length R (M ⧸ P) := by
    let K : Submodule R P := Submodule.comap P.subtype Q
    have hker : K = LinearMap.ker (Q.mkQ.comp P.subtype) := by
      ext x
      simp [K]
    let f : (P ⧸ K) →ₗ[R] (M ⧸ Q) :=
      K.liftQ (Q.mkQ.comp P.subtype) hker.le
    have hfker : LinearMap.ker f = ⊥ := by
      exact Submodule.ker_liftQ_eq_bot' K (Q.mkQ.comp P.subtype) hker
    have hf : Function.Injective f := LinearMap.ker_eq_bot.mp hfker
    let g : (M ⧸ Q) →ₗ[R] (M ⧸ P) :=
      Q.liftQ P.mkQ (by simpa [Submodule.ker_mkQ] using hQP)
    have hg : Function.Surjective g := by
      intro y
      refine Submodule.Quotient.induction_on (p := P) y ?_
      intro x
      exact ⟨Q.mkQ x, rfl⟩
    have hex : Function.Exact f g := by
      rw [LinearMap.exact_iff]
      simp [f, g, K, Submodule.range_liftQ, Submodule.ker_liftQ,
        LinearMap.range_comp]
    exact Module.length_eq_add_of_exact f g hf hg hex
  have hstep (k : ℕ) :
      Module.length R
          (idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M (k + 1)) =
        Module.length R
            (idealPowerPiece (IsLocalRing.maximalIdeal R) M (k + 1)) +
          Module.length R
            (idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M k) := by
    have hQP :
        (IsLocalRing.maximalIdeal R) ^ ((k + 1) + 1) • (⊤ : Submodule R M) ≤
          (IsLocalRing.maximalIdeal R) ^ (k + 1) • (⊤ : Submodule R M) := by
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)))
    simpa [idealPowerCumulativeQuotient, idealPowerPiece] using
      hlength
        ((IsLocalRing.maximalIdeal R) ^ (k + 1) • (⊤ : Submodule R M))
        ((IsLocalRing.maximalIdeal R) ^ ((k + 1) + 1) • (⊤ : Submodule R M)) hQP
  have hpiece_fin (k : ℕ) :
      IsFiniteLength R
        (idealPowerPiece (IsLocalRing.maximalIdeal R) M k) := by
    let P : Submodule R M := (IsLocalRing.maximalIdeal R) ^ k • (⊤ : Submodule R M)
    let Q : Submodule R M :=
      (IsLocalRing.maximalIdeal R) ^ (k + 1) • (⊤ : Submodule R M)
    let K : Submodule R P := Submodule.comap P.subtype Q
    change IsFiniteLength R (P ⧸ K)
    have hkill : IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P ⧸ K)) = ⊥ := by
      have hmap : IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P ⧸ K)) =
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)).map K.mkQ := by
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr K.mkQ_surjective]
      rw [hmap]
      apply le_antisymm
      · rw [Submodule.map_le_iff_le_comap, Submodule.comap_bot,
          Submodule.ker_mkQ]
        have hIP : IsLocalRing.maximalIdeal R • P ≤ Q := by
          simp [P, Q, pow_succ, Submodule.mul_smul, mul_comm]
        intro x hx
        exact hIP ((Submodule.mem_smul_top_iff _ P x).mp hx)
      · exact bot_le
    exact finiteLength_of_maximalIdeal_pow_smul_top_eq_bot
      ⟨1, by simpa only [pow_one] using hkill⟩
  have hcum_fin (k : ℕ) :
      IsFiniteLength R
        (idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M k) := by
    let Q : Submodule R M :=
      (IsLocalRing.maximalIdeal R) ^ (k + 1) • (⊤ : Submodule R M)
    change IsFiniteLength R (M ⧸ Q)
    have hkill :
        (IsLocalRing.maximalIdeal R) ^ (k + 1) • (⊤ : Submodule R (M ⧸ Q)) = ⊥ := by
      have hmap :
          (IsLocalRing.maximalIdeal R) ^ (k + 1) • (⊤ : Submodule R (M ⧸ Q)) =
            ((IsLocalRing.maximalIdeal R) ^ (k + 1) • (⊤ : Submodule R M)).map Q.mkQ := by
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr Q.mkQ_surjective]
      rw [hmap]
      apply le_antisymm
      · rw [Submodule.map_le_iff_le_comap, Submodule.comap_bot,
          Submodule.ker_mkQ]
      · exact bot_le
    exact finiteLength_of_maximalIdeal_pow_smul_top_eq_bot ⟨k + 1, hkill⟩
  have hbase : cumulativeHilbertFunction R M 0 = hilbertFunction R M 0 := by
    have hQP :
        (IsLocalRing.maximalIdeal R) ^ (0 + 1) • (⊤ : Submodule R M) ≤
          (IsLocalRing.maximalIdeal R) ^ 0 • (⊤ : Submodule R M) := by
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ 0))
    have h := hlength
      ((IsLocalRing.maximalIdeal R) ^ 0 • (⊤ : Submodule R M))
      ((IsLocalRing.maximalIdeal R) ^ (0 + 1) • (⊤ : Submodule R M)) hQP
    have hn := congrArg ENat.toNat h
    simpa [cumulativeHilbertFunction, hilbertFunction, moduleLengthNat,
      idealPowerCumulativeQuotient, idealPowerPiece, pow_zero] using hn
  have hnat_step (k : ℕ) :
      cumulativeHilbertFunction R M (k + 1) =
        hilbertFunction R M (k + 1) + cumulativeHilbertFunction R M k := by
    change (Module.length R
        (idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M (k + 1))).toNat =
      (Module.length R
        (idealPowerPiece (IsLocalRing.maximalIdeal R) M (k + 1))).toNat +
        (Module.length R
          (idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M k)).toNat
    rw [hstep k, ENat.toNat_add]
    · exact Module.length_ne_top_iff.mpr
        (hpiece_fin (k + 1))
    · exact Module.length_ne_top_iff.mpr
        (hcum_fin k)
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      calc
        cumulativeHilbertFunction R M (Nat.succ n) =
            hilbertFunction R M (n + 1) + cumulativeHilbertFunction R M n := by
              simpa [Nat.succ_eq_add_one] using hnat_step n
        _ = hilbertFunction R M (n + 1) +
              ∑ i ∈ Finset.range (n + 1), hilbertFunction R M i := by rw [ih]
        _ = ∑ i ∈ Finset.range (Nat.succ n + 1), hilbertFunction R M i := by
          simp only [Nat.succ_eq_add_one, Finset.sum_range_succ]
          ac_rfl

/-! ## Ideals of definition and their Hilbert functions -/

/-- An ideal whose radical is the maximal ideal of a local ring. -/
def IsIdealOfDefinition
    (R : Type u) [CommRing R] [IsLocalRing R] (I : Ideal R) : Prop :=
  I.radical = IsLocalRing.maximalIdeal R

theorem maximalIdeal_isIdealOfDefinition
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsIdealOfDefinition R (IsLocalRing.maximalIdeal R) := by
  unfold IsIdealOfDefinition
  exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical

theorem exists_pow_maximalIdeal_le_of_isIdealOfDefinition
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : IsIdealOfDefinition R I) :
    ∃ r : ℕ, (IsLocalRing.maximalIdeal R) ^ r ≤ I := by
  unfold IsIdealOfDefinition at hI
  have hrad : IsLocalRing.maximalIdeal R ≤ I.radical := by
    simp [hI]
  have hfg : (IsLocalRing.maximalIdeal R).FG :=
    Ideal.FG.of_isNoetherianRing _
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg

theorem finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (hM : ∃ r : ℕ, I ^ r • (⊤ : Submodule R M) = ⊥) :
    IsFiniteLength R M := by
  obtain ⟨r, hr⟩ := exists_pow_maximalIdeal_le_of_isIdealOfDefinition I hI
  obtain ⟨s, hs⟩ := hM
  have hmax :
      (IsLocalRing.maximalIdeal R) ^ (r * s) • (⊤ : Submodule R M) = ⊥ := by
    apply le_antisymm
    · have hpow :
          (IsLocalRing.maximalIdeal R) ^ (r * s) ≤ I ^ s := by
        simpa [pow_mul] using Ideal.pow_right_mono hr s
      exact (Submodule.smul_mono_left hpow).trans_eq hs
    · exact bot_le
  exact finiteLength_of_maximalIdeal_pow_smul_top_eq_bot ⟨r * s, hmax⟩

def idealHilbertFunction
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  moduleLengthNat (R := R) (M := idealPowerPiece I M n)

def idealCumulativeHilbertFunction
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  moduleLengthNat (R := R)
    (M := idealPowerCumulativeQuotient I M n)

theorem idealPowerPiece_isFiniteLength
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (n : ℕ) :
    IsFiniteLength R (idealPowerPiece I M n) := by
  let P : Submodule R M := I ^ n • (⊤ : Submodule R M)
  let Q : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let K : Submodule R P := Submodule.comap P.subtype Q
  change IsFiniteLength R (P ⧸ K)
  have hkill : I • (⊤ : Submodule R (P ⧸ K)) = ⊥ := by
    have hmap : I • (⊤ : Submodule R (P ⧸ K)) =
        (I • (⊤ : Submodule R P)).map K.mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr K.mkQ_surjective]
    rw [hmap]
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.comap_bot,
        Submodule.ker_mkQ]
      have hIP : I • P ≤ Q := by
        simp [P, Q, pow_succ, Submodule.mul_smul, mul_comm]
      intro x hx
      exact hIP ((Submodule.mem_smul_top_iff I P x).mp hx)
    · exact bot_le
  exact finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition I hI
    ⟨1, by simpa only [pow_one] using hkill⟩
/-
  let P : Submodule R M := I ^ n • (⊤ : Submodule R M)
  let Q : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let K : Submodule R P := Submodule.comap P.subtype Q
  change IsFiniteLength R (P ⧸ K)
  have hkill : I • (⊤ : Submodule R (P ⧸ K)) = ⊥ := by
    have hmap : I • (⊤ : Submodule R (P ⧸ K)) =
        (I • (⊤ : Submodule R P)).map K.mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr K.mkQ_surjective]
    rw [hmap]
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.comap_bot,
        Submodule.ker_mkQ]
      have hIP : I • P ≤ Q := by
        simpa [P, Q, pow_succ, Submodule.mul_smul, mul_comm]
      intro x hx
      exact hIP ((Submodule.mem_smul_top_iff I P x).mp hx)
    · exact bot_le
  exact finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition I hI
    ⟨1, hkill⟩

 -/
theorem idealPowerCumulativeQuotient_isFiniteLength
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (n : ℕ) :
    IsFiniteLength R (idealPowerCumulativeQuotient I M n) := by
  let Q : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  change IsFiniteLength R (M ⧸ Q)
  have hkill : I ^ (n + 1) • (⊤ : Submodule R (M ⧸ Q)) = ⊥ := by
    have hmap : I ^ (n + 1) • (⊤ : Submodule R (M ⧸ Q)) =
        (I ^ (n + 1) • (⊤ : Submodule R M)).map Q.mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr Q.mkQ_surjective]
    rw [hmap]
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.comap_bot,
        Submodule.ker_mkQ]
    · exact bot_le
  exact finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition I hI
    ⟨n + 1, hkill⟩
/-
  let Q : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  change IsFiniteLength R (M ⧸ Q)
  have hkill : I ^ (n + 1) • (⊤ : Submodule R (M ⧸ Q)) = ⊥ := by
    have hmap : I ^ (n + 1) • (⊤ : Submodule R (M ⧸ Q)) =
        (I ^ (n + 1) • (⊤ : Submodule R M)).map Q.mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr Q.mkQ_surjective]
    rw [hmap]
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.comap_bot,
        Submodule.ker_mkQ]
      exact le_rfl
    · exact bot_le
  exact finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition I hI
    ⟨n + 1, hkill⟩

 -/
theorem hilbertPowerPiece_isFiniteLength
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) :
    IsFiniteLength R
      (idealPowerPiece (IsLocalRing.maximalIdeal R) M n) := by
  exact idealPowerPiece_isFiniteLength (IsLocalRing.maximalIdeal R)
    (maximalIdeal_isIdealOfDefinition R) n

theorem hilbertPowerCumulativeQuotient_isFiniteLength
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) :
    IsFiniteLength R
      (idealPowerCumulativeQuotient (IsLocalRing.maximalIdeal R) M n) := by
  exact idealPowerCumulativeQuotient_isFiniteLength (IsLocalRing.maximalIdeal R)
    (maximalIdeal_isIdealOfDefinition R) n

theorem idealCumulativeHilbertFunction_eq_sum
    {R : Type u} {M : Type v} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (n : ℕ) :
    idealCumulativeHilbertFunction I M n =
      ∑ i ∈ Finset.range (n + 1), idealHilbertFunction I M i := by
  have hlength (P Q : Submodule R M) (hQP : Q ≤ P) :
      Module.length R (M ⧸ Q) =
        Module.length R (P ⧸ Submodule.comap P.subtype Q) +
          Module.length R (M ⧸ P) := by
    let K : Submodule R P := Submodule.comap P.subtype Q
    have hker : K = LinearMap.ker (Q.mkQ.comp P.subtype) := by
      ext x
      simp [K]
    let f : (P ⧸ K) →ₗ[R] (M ⧸ Q) :=
      K.liftQ (Q.mkQ.comp P.subtype) hker.le
    have hfker : LinearMap.ker f = ⊥ := by
      exact Submodule.ker_liftQ_eq_bot' K (Q.mkQ.comp P.subtype) hker
    have hf : Function.Injective f := LinearMap.ker_eq_bot.mp hfker
    let g : (M ⧸ Q) →ₗ[R] (M ⧸ P) :=
      Q.liftQ P.mkQ (by simpa [Submodule.ker_mkQ] using hQP)
    have hg : Function.Surjective g := by
      intro y
      refine Submodule.Quotient.induction_on (p := P) y ?_
      intro x
      exact ⟨Q.mkQ x, rfl⟩
    have hex : Function.Exact f g := by
      rw [LinearMap.exact_iff]
      simp [f, g, K, Submodule.range_liftQ, Submodule.ker_liftQ,
        LinearMap.range_comp]
    exact Module.length_eq_add_of_exact f g hf hg hex
  have hstep (k : ℕ) :
      Module.length R
          (idealPowerCumulativeQuotient I M (k + 1)) =
        Module.length R (idealPowerPiece I M (k + 1)) +
          Module.length R (idealPowerCumulativeQuotient I M k) := by
    have hQP :
        I ^ ((k + 1) + 1) • (⊤ : Submodule R M) ≤
          I ^ (k + 1) • (⊤ : Submodule R M) := by
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)))
    simpa [idealPowerCumulativeQuotient, idealPowerPiece] using
      hlength (I ^ (k + 1) • (⊤ : Submodule R M))
        (I ^ ((k + 1) + 1) • (⊤ : Submodule R M)) hQP
  have hpiece_fin (k : ℕ) : IsFiniteLength R (idealPowerPiece I M k) := by
    exact idealPowerPiece_isFiniteLength I hI k
  have hcum_fin (k : ℕ) :
      IsFiniteLength R (idealPowerCumulativeQuotient I M k) := by
    exact idealPowerCumulativeQuotient_isFiniteLength I hI k
  have hbase : idealCumulativeHilbertFunction I M 0 = idealHilbertFunction I M 0 := by
    have hQP :
        I ^ (0 + 1) • (⊤ : Submodule R M) ≤
          I ^ 0 • (⊤ : Submodule R M) := by
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ 0))
    have h := hlength (I ^ 0 • (⊤ : Submodule R M))
      (I ^ (0 + 1) • (⊤ : Submodule R M)) hQP
    have hn := congrArg ENat.toNat h
    simpa [idealCumulativeHilbertFunction, idealHilbertFunction,
      moduleLengthNat, idealPowerCumulativeQuotient, idealPowerPiece, pow_zero] using hn
  have hnat_step (k : ℕ) :
      idealCumulativeHilbertFunction I M (k + 1) =
        idealHilbertFunction I M (k + 1) +
          idealCumulativeHilbertFunction I M k := by
    change (Module.length R (idealPowerCumulativeQuotient I M (k + 1))).toNat =
      (Module.length R (idealPowerPiece I M (k + 1))).toNat +
        (Module.length R (idealPowerCumulativeQuotient I M k)).toNat
    rw [hstep k, ENat.toNat_add]
    · exact Module.length_ne_top_iff.mpr (hpiece_fin (k + 1))
    · exact Module.length_ne_top_iff.mpr (hcum_fin k)
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      calc
        idealCumulativeHilbertFunction I M (Nat.succ n) =
            idealHilbertFunction I M (n + 1) +
              idealCumulativeHilbertFunction I M n := by
              simpa [Nat.succ_eq_add_one] using hnat_step n
        _ = idealHilbertFunction I M (n + 1) +
              ∑ i ∈ Finset.range (n + 1), idealHilbertFunction I M i := by rw [ih]
        _ = ∑ i ∈ Finset.range (Nat.succ n + 1), idealHilbertFunction I M i := by
          simp only [Nat.succ_eq_add_one, Finset.sum_range_succ]
          ac_rfl

/- The numerical-polynomial API is indexed by `ℤ`, whereas the source only
   defines these functions for nonnegative integers. -/
def natFunctionToInteger (f : ℕ → ℕ) (n : ℤ) : ℤ :=
  if 0 ≤ n then (f n.toNat : ℤ) else 0

def hilbertFunctionInteger
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℤ → ℤ :=
  natFunctionToInteger (hilbertFunction R M)

def cumulativeHilbertFunctionInteger
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℤ → ℤ :=
  natFunctionToInteger (cumulativeHilbertFunction R M)

def idealHilbertFunctionInteger
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : ℤ → ℤ :=
  natFunctionToInteger (idealHilbertFunction I M)

def idealCumulativeHilbertFunctionInteger
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : ℤ → ℤ :=
  natFunctionToInteger (idealCumulativeHilbertFunction I M)

/-! ## Comparison of finite-colength modules -/

/-- A submodule has finite colength when its quotient has finite length. -/
def Submodule.HasFiniteColength
    {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] (N : Submodule R M) : Prop :=
  IsFiniteLength R (M ⧸ N)

private theorem exists_maximalIdeal_pow_smul_top_eq_bot_of_finiteLength
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (hfin : IsFiniteLength R M) :
    ∃ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R M) = ⊥ := by
  let I : Ideal R := IsLocalRing.maximalIdeal R
  induction hfin with
  | of_subsingleton =>
      refine ⟨0, ?_⟩
      ext x
      simp [show x = 0 from Subsingleton.elim x 0]
  | @of_simple_quotient M _ _ N _ _ ih =>
      obtain ⟨n, hn⟩ := ih
      have hmax : (Module.annihilator R (M ⧸ N)).IsMaximal :=
        IsSimpleModule.annihilator_isMaximal
      have hquot' : (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule R (M ⧸ N)) = ⊥ := by
        rw [← IsLocalRing.eq_maximalIdeal hmax, ← Submodule.annihilator_top,
          ← Submodule.le_annihilator_iff]
      have hquot : I • (⊤ : Submodule R (M ⧸ N)) = ⊥ := by
        simpa [I] using hquot'
      have hIN : I • (⊤ : Submodule R M) ≤ N := by
        rw [← N.ker_mkQ]
        apply LinearMap.le_ker_iff_map.mpr
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr N.mkQ_surjective]
        exact hquot
      have hn' : I ^ n • N = ⊥ := by
        have h := congrArg (fun P : Submodule R N => P.map N.subtype) hn
        simpa only [Submodule.map_smul'', Submodule.map_subtype_top,
          Submodule.map_bot] using h
      refine ⟨n + 1, le_antisymm ?_ bot_le⟩
      rw [pow_succ, Submodule.mul_smul]
      exact (smul_mono_right (I ^ n) hIN).trans_eq hn'

theorem cumulative_hilbert_compare_of_finite_colength
    {R : Type u} {M' M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (f : M' →ₗ[R] M) (hf : Function.Injective f)
    (hquot : IsFiniteLength R (M ⧸ LinearMap.range f)) :
    ∃ c₁ c₂ : ℕ, ∀ n ≥ c₂,
      c₁ + idealCumulativeHilbertFunction I M' (n - c₂) ≤
          idealCumulativeHilbertFunction I M n ∧
        idealCumulativeHilbertFunction I M n ≤
          c₁ + idealCumulativeHilbertFunction I M' n := by
  /-
  prior attempt:
  let L : Submodule R M := LinearMap.range f
  have hfL_surj : Function.Surjective
      (f.codRestrict L (fun x => LinearMap.mem_range_self f x)) := by
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨c, hc_pos, hc⟩ := Formalization.Books.Algebra.Unit51.artin_rees I L
  obtain ⟨s, hs⟩ :=
    exists_maximalIdeal_pow_smul_top_eq_bot_of_finiteLength hquot
  have hIlemax : I ≤ IsLocalRing.maximalIdeal R := by
    rw [← hI]
    exact Ideal.le_radical
  have hkill : I ^ s • (⊤ : Submodule R (M ⧸ L)) = ⊥ := by
    apply le_antisymm
    · exact (Submodule.smul_mono_left (Ideal.pow_right_mono hIlemax s)).trans_eq hs
    · exact bot_le
  let c₂ : ℕ := c - 1
  let c₁ : ℕ := moduleLengthNat (R := R) (M := M ⧸ L)
  have hupper (n : ℕ) :
      idealCumulativeHilbertFunction I M n ≤
        c₁ + idealCumulativeHilbertFunction I M' n := by
    let P : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
    let P' : Submodule R M' := I ^ (n + 1) • (⊤ : Submodule R M')
    have hPmap : P' ≤ Submodule.comap f P := by
      change I ^ (n + 1) • (⊤ : Submodule R M') ≤
        Submodule.comap f (I ^ (n + 1) • (⊤ : Submodule R M))
      refine Submodule.smul_le.mpr ?_
      intro r hr x hx
      change f (r • x) ∈ I ^ (n + 1) • (⊤ : Submodule R M)
      rw [map_smul]
      exact Submodule.smul_mem_smul hr (Submodule.mem_top)
    have hPker : P' ≤ LinearMap.ker (P.mkQ.comp f) := by
      simpa [P, P', LinearMap.ker_comp, Submodule.ker_mkQ] using hPmap
    let fbar : (M' ⧸ P') →ₗ[R] (M ⧸ P) := P'.liftQ (P.mkQ.comp f) hPker
    let A : Submodule R (M ⧸ P) := LinearMap.range fbar
    let fA : (M' ⧸ P') →ₗ[R] A :=
      fbar.codRestrict A (fun x => LinearMap.mem_range_self fbar x)
    have hfA : Function.Surjective fA := by
      intro y
      rcases y.property with ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
    have hA : Module.length R A ≤ Module.length R (M' ⧸ P') :=
      Module.length_le_of_surjective fA hfA
    have hLker : L ≤ LinearMap.ker (A.mkQ.comp P.mkQ) := by
      intro x hx
      rcases hx with ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨P'.mkQ y, rfl⟩
    let qbar : (M ⧸ L) →ₗ[R] ((M ⧸ P) ⧸ A) :=
      L.liftQ (A.mkQ.comp P.mkQ) hLker
    have hqbar : Function.Surjective qbar := by
      intro y
      refine Submodule.Quotient.induction_on (p := L) y ?_
      intro x
      refine ⟨P.mkQ x, ?_⟩
      rfl
    have hres : Module.length R ((M ⧸ P) ⧸ A) ≤ Module.length R (M ⧸ L) :=
      Module.length_le_of_surjective qbar hqbar
    have hlen : Module.length R (M ⧸ P) =
        Module.length R A + Module.length R ((M ⧸ P) ⧸ A) :=
      Module.length_eq_add_of_exact A.subtype (M ⧸ P).mkQ
        (Submodule.subtype_injective A) P.mkQ_surjective
        (LinearMap.exact_subtype_mkQ A)
    have hP'fin : IsFiniteLength R (M' ⧸ P') := by
      exact idealPowerCumulativeQuotient_isFiniteLength I hI n
    have hAfin : IsFiniteLength R A :=
      IsFiniteLength.of_surjective hP'fin hfA
    have hresfin : IsFiniteLength R ((M ⧸ P) ⧸ A) :=
      IsFiniteLength.of_surjective hquot hqbar
    have hnat : (Module.length R (M ⧸ P)).toNat ≤
        (Module.length R (M' ⧸ P')).toNat +
          (Module.length R (M ⧸ L)).toNat := by
      have hlen' := congrArg ENat.toNat hlen
      rw [ENat.toNat_add, ENat.toNat_add] at hlen'
      · rw [hlen']
        exact Nat.add_le_add
          (ENat.toNat_le_toNat hA (Module.length_ne_top_iff.mpr hAfin))
          (ENat.toNat_le_toNat hres (Module.length_ne_top_iff.mpr hresfin))
      · exact Module.length_ne_top_iff.mpr hAfin
      · exact Module.length_ne_top_iff.mpr hresfin
      · exact Module.length_ne_top_iff.mpr hP'fin
      · exact Module.length_ne_top_iff.mpr hquot
    simpa [c₁, idealCumulativeHilbertFunction, moduleLengthNat,
      idealPowerCumulativeQuotient, P, P', Nat.add_comm] using hnat
  have hlower (n : ℕ) (hn : n ≥ c₂) :
      c₁ + idealCumulativeHilbertFunction I M' (n - c₂) ≤
        idealCumulativeHilbertFunction I M n := by
    have hn' : c ≤ n + 1 := by
      dsimp [c₂] at hn
      omega
    have har := hc (n + 1) hn'
    have hkill_n : I ^ (n + 1) • (⊤ : Submodule R (M ⧸ L)) = ⊥ := by
      apply le_antisymm
      · exact (Submodule.smul_mono_left
          (Ideal.pow_le_pow_right hn')).trans_eq hkill
      · exact bot_le
    let P : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
    let K : Submodule R L := Submodule.comap L.subtype P
    let P' : Submodule R M' := I ^ (n - c₂) • (⊤ : Submodule R M')
    let B : Submodule R L := I ^ (n - c₂) • (⊤ : Submodule R L)
    have hP_le_L : P ≤ L := by
      rw [← L.ker_mkQ]
      apply LinearMap.le_ker_iff_map.mpr
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr L.mkQ_surjective]
      exact hkill_n
    have hKB : K ≤ B := by
      intro x hx
      have hxM : (x : M) ∈ P ⊓ L := ⟨hx, x.property⟩
      rw [har] at hxM
      have hxB : (x : M) ∈
          I ^ (n + 1 - c) • (L : Submodule R M) :=
        (Submodule.smul_mono_right (I ^ (n + 1 - c)) inf_le_right) hxM
      have hshift : n + 1 - c = n - c₂ := by
        dsimp [c₂]
        omega
      have hxB' : (x : M) ∈ I ^ (n - c₂) • (L : Submodule R M) := by
        simpa [hshift] using hxB
      have hmapB : B.map L.subtype = I ^ (n - c₂) • (L : Submodule R M) := by
        rw [Submodule.map_smul'', Submodule.map_subtype_top]
      have : (x : M) ∈ B.map L.subtype := hmapB.symm ▸ hxB'
      rcases this with ⟨y, hy, hxy⟩
      exact Subtype.ext hxy.symm
    let u : (L ⧸ K) →ₗ[R] (M ⧸ P) :=
      K.liftQ (P.mkQ.comp L.subtype) (by
        have hker : K = LinearMap.ker (P.mkQ.comp L.subtype) := by
          ext x
          simp [K]
        exact hker.le)
    have hu : Function.Injective u := by
      apply LinearMap.ker_eq_bot.mp
      exact Submodule.ker_liftQ_eq_bot' K (P.mkQ.comp L.subtype) (by
        have hker : K = LinearMap.ker (P.mkQ.comp L.subtype) := by
          ext x
          simp [K]
        exact hker)
    let v : (M ⧸ P) →ₗ[R] (M ⧸ L) :=
      P.liftQ L.mkQ (by simpa [Submodule.ker_mkQ] using hP_le_L)
    have hv : Function.Surjective v := by
      intro y
      refine Submodule.Quotient.induction_on (p := L) y ?_
      intro x
      exact ⟨P.mkQ x, rfl⟩
    have huv : Function.Exact u v := by
      rw [LinearMap.exact_iff]
      simp [u, v, K, Submodule.range_liftQ, Submodule.ker_liftQ,
        LinearMap.range_comp]
    have hlen : Module.length R (M ⧸ P) =
        Module.length R (L ⧸ K) + Module.length R (M ⧸ L) :=
      Module.length_eq_add_of_exact u v hu hv huv
    let fL : M' →ₗ[R] L :=
      f.codRestrict L (fun x => LinearMap.mem_range_self f x)
    have hfL : Function.Bijective fL := by
      refine ⟨?_, hfL_surj⟩
      intro x y hxy
      apply hf
      exact Subtype.ext hxy
    have hPmapB : P' ≤ LinearMap.ker (B.mkQ.comp fL) := by
      have hmap : P'.map fL = B := by
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr hfL.2]
      intro x hx
      rw [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero]
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    let fbar : (M' ⧸ P') →ₗ[R] (L ⧸ B) :=
      P'.liftQ (B.mkQ.comp fL) hPmapB
    have hfbar_surj : Function.Surjective fbar := by
      intro y
      refine Submodule.Quotient.induction_on (p := B) y ?_
      intro x
      rcases hfL.2 x with ⟨y, rfl⟩
      exact ⟨P'.mkQ y, rfl⟩
    have hfbar_inj : Function.Injective fbar := by
      intro x y hxy
      refine Submodule.Quotient.induction_on (p := P') x ?_ y hxy
      intro x
      refine Submodule.Quotient.induction_on (p := P') y ?_
      intro y hxy
      have hxy' : B.mkQ (fL x) = B.mkQ (fL y) := by
        simpa [fbar] using hxy
      have hmem : fL (x - y) ∈ B := by
        have := Submodule.Quotient.eq.mp hxy'
        simpa [map_sub] using this
      have hmap : P'.map fL = B := by
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr hfL.2]
      rw [← hmap] at hmem
      rcases hmem with ⟨z, hz, hzy⟩
      have hzxy : z = x - y := by
        apply hf
        exact Subtype.ext hzy
      apply Submodule.Quotient.eq.mpr
      rw [← hzxy]
      exact hz
    have hlen_fbar : Module.length R (M' ⧸ P') = Module.length R (L ⧸ B) :=
      (LinearEquiv.ofBijective fbar ⟨hfbar_inj, hfbar_surj⟩).length_eq
    let qB : (L ⧸ K) →ₗ[R] (L ⧸ B) :=
      K.liftQ B.mkQ (by simpa [Submodule.ker_mkQ] using hKB)
    have hqB : Function.Surjective qB := by
      intro y
      refine Submodule.Quotient.induction_on (p := B) y ?_
      intro x
      exact ⟨K.mkQ x, rfl⟩
    have hlenB : Module.length R (L ⧸ B) ≤ Module.length R (L ⧸ K) :=
      Module.length_le_of_surjective qB hqB
    have hlenM' : Module.length R (M' ⧸ P') ≤ Module.length R (L ⧸ K) := by
      rw [hlen_fbar]
      exact hlenB
    have hM'fin : IsFiniteLength R (M' ⧸ P') := by
      exact idealPowerCumulativeQuotient_isFiniteLength I hI (n - c₂)
    have hKfin : IsFiniteLength R (L ⧸ K) := by
      exact IsFiniteLength.of_injective
        (idealPowerCumulativeQuotient_isFiniteLength I hI n) hu
    have hnat : (Module.length R (M' ⧸ P')).toNat +
        (Module.length R (M ⧸ L)).toNat ≤
          (Module.length R (M ⧸ P)).toNat := by
      have hlen' := congrArg ENat.toNat hlen
      rw [ENat.toNat_add] at hlen'
      · rw [← hlen']
        exact Nat.add_le_add
          (ENat.toNat_le_toNat hlenM' (Module.length_ne_top_iff.mpr hKfin)) le_rfl
      · exact Module.length_ne_top_iff.mpr hKfin
      · exact Module.length_ne_top_iff.mpr hquot
      · exact Module.length_ne_top_iff.mpr hM'fin
    simpa [c₁, idealCumulativeHilbertFunction, moduleLengthNat,
      idealPowerCumulativeQuotient, P, P', Nat.add_comm] using hnat
  refine ⟨c₁, c₂, ?_⟩
  intro n hn
  exact ⟨hlower n hn, by simpa [Nat.add_comm] using hupper n⟩
  -/
  sorry

theorem hilbert_functions_of_short_exact
    {R : Type u} {M' M M'' : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    ∃ N : Submodule R M', ∃ l c : ℕ,
      Submodule.HasFiniteColength N ∧
        l = moduleLengthNat (R := R) (M := M' ⧸ N) ∧
        (∀ n ≥ c,
          idealCumulativeHilbertFunction I M n =
              idealCumulativeHilbertFunction I M'' n +
                idealCumulativeHilbertFunction I N (n - c) + l) ∧
        (∀ n ≥ c,
          idealHilbertFunction I M n =
              idealHilbertFunction I M'' n +
                idealHilbertFunction I N (n - c)) := by
  sorry

theorem hilbert_cumulative_change_of_ideal
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I I' : Ideal R)
    (hI : IsIdealOfDefinition R I) (hI' : IsIdealOfDefinition R I') :
    ∃ a : ℕ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      idealCumulativeHilbertFunction I M n ≤
        idealCumulativeHilbertFunction I' M (a * n) := by
  obtain ⟨r, hr⟩ := exists_pow_maximalIdeal_le_of_isIdealOfDefinition I hI
  have hI'lemax : I' ≤ IsLocalRing.maximalIdeal R := by
    rw [← hI']
    exact Ideal.le_radical
  let a : ℕ := 2 * r + 1
  have ha : 0 < a := by
    dsimp [a]
    omega
  have hpow : I' ^ a ≤ I ^ 2 := by
    have hpow_max : (IsLocalRing.maximalIdeal R) ^ (2 * r + 1) ≤ I ^ 2 := by
      calc
        (IsLocalRing.maximalIdeal R) ^ (2 * r + 1) ≤
            (IsLocalRing.maximalIdeal R) ^ (2 * r) :=
          Ideal.pow_le_pow_right (Nat.le_succ (2 * r))
        _ = ((IsLocalRing.maximalIdeal R) ^ r) ^ 2 := by
          rw [← pow_mul, Nat.mul_comm]
        _ ≤ I ^ 2 := Ideal.pow_right_mono hr 2
    exact (Ideal.pow_right_mono hI'lemax a).trans hpow_max
  refine ⟨a, ha, ?_⟩
  intro n hn
  have hpow_n : I' ^ (a * n + 1) ≤ I ^ (n + 1) := by
    calc
      I' ^ (a * n + 1) ≤ I' ^ (a * n) :=
        Ideal.pow_le_pow_right (Nat.le_succ (a * n))
      _ = (I' ^ a) ^ n := by
        rw [pow_mul]
      _ ≤ (I ^ 2) ^ n := Ideal.pow_right_mono hpow n
      _ = I ^ (2 * n) := by rw [pow_mul]
      _ ≤ I ^ (n + 1) := by
        apply Ideal.pow_le_pow_right
        omega
  let Q : Submodule R M := I' ^ (a * n + 1) • (⊤ : Submodule R M)
  let P : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  have hQP : Q ≤ P := by
    exact Submodule.smul_mono_left hpow_n
  let q : (M ⧸ Q) →ₗ[R] (M ⧸ P) :=
    Q.liftQ P.mkQ (by simpa [Submodule.ker_mkQ] using hQP)
  have hq : Function.Surjective q := by
    intro y
    refine Submodule.Quotient.induction_on (p := P) y ?_
    intro x
    exact ⟨Q.mkQ x, rfl⟩
  have hlen : Module.length R (M ⧸ P) ≤ Module.length R (M ⧸ Q) :=
    Module.length_le_of_surjective q hq
  have hQfin : IsFiniteLength R (M ⧸ Q) := by
    change IsFiniteLength R (idealPowerCumulativeQuotient I' M (a * n))
    exact idealPowerCumulativeQuotient_isFiniteLength I' hI' (a * n)
  exact ENat.toNat_le_toNat hlen (Module.length_ne_top_iff.mpr hQfin)

/-! ## Numerical polynomials and the Hilbert polynomial -/

theorem ideal_hilbert_functions_are_numerical
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : IsIdealOfDefinition R I) :
    IsNumericalPolynomial (idealHilbertFunctionInteger I M) ∧
      IsNumericalPolynomial (idealCumulativeHilbertFunctionInteger I M) := by
  sorry

theorem hilbert_functions_are_numerical
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    IsNumericalPolynomial (hilbertFunctionInteger R M) ∧
      IsNumericalPolynomial (cumulativeHilbertFunctionInteger R M) := by
  change IsNumericalPolynomial
      (idealHilbertFunctionInteger (IsLocalRing.maximalIdeal R) M) ∧
    IsNumericalPolynomial
      (idealCumulativeHilbertFunctionInteger (IsLocalRing.maximalIdeal R) M)
  exact ideal_hilbert_functions_are_numerical
    (IsLocalRing.maximalIdeal R) (maximalIdeal_isIdealOfDefinition R)

def IsEventuallyRationalPolynomial (f : ℤ → ℤ) (P : Polynomial ℚ) : Prop :=
  ∀ᶠ n : ℤ in Filter.atTop, P.eval (n : ℚ) = (f n : ℚ)

theorem exists_eventually_rational_polynomial_of_isNumericalPolynomial
    (f : ℤ → ℤ) (hf : IsNumericalPolynomial f) :
    ∃ P : Polynomial ℚ, IsEventuallyRationalPolynomial f P := by
  rcases hf with ⟨r, a, ha⟩
  let P : Polynomial ℚ :=
    ∑ i ∈ Finset.range (r + 1), (a i : ℚ) • Polynomial.preHilbertPoly ℚ i i
  refine ⟨P, ?_⟩
  filter_upwards [ha, Filter.Ici_mem_atTop (r : ℤ)] with n hn hnr
  have hnr_int : (r : ℤ) ≤ n := hnr
  have hn0 : 0 ≤ n := by omega
  have hn_toNat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have hn_cast : (n : ℚ) = (n.toNat : ℚ) := by exact_mod_cast hn_toNat.symm
  have hnr' : r ≤ n.toNat := by
    have hnr_toNat : (r : ℤ) ≤ (n.toNat : ℤ) := by
      rw [hn_toNat]
      exact hnr_int
    exact_mod_cast hnr_toNat
  calc
    P.eval (n : ℚ) =
        ∑ i ∈ Finset.range (r + 1),
          (a i : ℚ) * (Polynomial.preHilbertPoly ℚ i i).eval (n : ℚ) := by
      simp [P, Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul]
    _ = ∑ i ∈ Finset.range (r + 1),
          (a i : ℚ) * (n.toNat.choose i : ℚ) := by
      rw [hn_cast]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_le : i ≤ n.toNat :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hnr'
      have hchoose :=
        Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) i hi_le
      rw [hchoose]
      simp [Nat.sub_add_cancel hi_le]
    _ = ((∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i : ℤ) : ℚ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [integerBinomial, hn0, mul_comm]
    _ = (f n : ℚ) := by rw [hn]

noncomputable def eventuallyRationalPolynomial (f : ℤ → ℤ) : Polynomial ℚ :=
  by
    classical
    exact if h : ∃ P : Polynomial ℚ, IsEventuallyRationalPolynomial f P then
      Classical.choose h
    else 0

def numericalPolynomialDegree (f : ℤ → ℤ) : WithBot ℕ :=
  (eventuallyRationalPolynomial f).degree

theorem eventuallyRationalPolynomial_spec
    (f : ℤ → ℤ) (hf : IsNumericalPolynomial f) :
    IsEventuallyRationalPolynomial f (eventuallyRationalPolynomial f) := by
  classical
  rw [eventuallyRationalPolynomial]
  split_ifs with h
  · exact Classical.choose_spec h
  · exact False.elim (h (exists_eventually_rational_polynomial_of_isNumericalPolynomial f hf))

noncomputable def hilbertPolynomial
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Polynomial ℚ :=
  eventuallyRationalPolynomial (hilbertFunctionInteger R M)

theorem hilbertPolynomial_spec
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∀ᶠ n : ℕ in Filter.atTop,
      (hilbertPolynomial R M).eval (n : ℚ) =
        (hilbertFunction R M n : ℚ) := by
  sorry

theorem hilbertPolynomial_unique
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (P : Polynomial ℚ)
    (hP : ∀ᶠ n : ℕ in Filter.atTop,
      P.eval (n : ℚ) = (hilbertFunction R M n : ℚ)) :
    P = hilbertPolynomial R M := by
  sorry

theorem ideal_hilbert_function_degree_independent
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I I' : Ideal R)
    (hI : IsIdealOfDefinition R I) (hI' : IsIdealOfDefinition R I') :
    numericalPolynomialDegree (idealHilbertFunctionInteger I M) =
        numericalPolynomialDegree (idealHilbertFunctionInteger I' M) ∧
      numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M) =
        numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I' M) := by
  sorry

/-- The dimension invariant `d(M)` from the source. -/
def d
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] : WithBot ℕ :=
  by
    classical
    exact if Nontrivial M then
      numericalPolynomialDegree (cumulativeHilbertFunctionInteger R M)
    else ⊥

theorem d_eq_hilbertPolynomial_degree_add_one
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : ∀ n : ℕ,
      (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R M) ≠ ⊥) :
    d R M = (hilbertPolynomial R M).degree + 1 := by
  sorry

/-! ## Finite-colength differences -/

theorem cumulative_hilbert_difference_of_finite_colength
    {R : Type u} {M' M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (f : M' →ₗ[R] M) (hf : Function.Injective f)
    (hquot : IsFiniteLength R (M ⧸ LinearMap.range f))
    (hM : ¬ IsFiniteLength R M) :
    let Δ := fun n : ℤ =>
      idealCumulativeHilbertFunctionInteger I M n -
        idealCumulativeHilbertFunctionInteger I M' n
    IsNumericalPolynomial Δ ∧
      numericalPolynomialDegree Δ <
        numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M) ∧
      numericalPolynomialDegree Δ <
        numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M') := by
  sorry

/-! ## Exact sequences and degrees -/

theorem hilbert_short_exact_degree_statements
    {R : Type u} {M' M M'' : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (I : Ideal R) (hI : IsIdealOfDefinition R I)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    (¬ IsFiniteLength R M' →
        let Δ := fun n : ℤ =>
          idealCumulativeHilbertFunctionInteger I M n -
            idealCumulativeHilbertFunctionInteger I M'' n -
            idealCumulativeHilbertFunctionInteger I M' n
        IsNumericalPolynomial Δ ∧
          numericalPolynomialDegree Δ <
            numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M')) ∧
      max
          (numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M'))
          (numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M'')) =
        numericalPolynomialDegree (idealCumulativeHilbertFunctionInteger I M) ∧
      max (d R M') (d R M'') = d R M := by
  sorry

end

end Formalization.Books.Algebra.Unit59
