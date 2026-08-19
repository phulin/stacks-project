import Formalization.Books.Algebra.Unit05.FiniteModules
import Formalization.Books.Algebra.Unit40.SupportsAndAnnihilators
import Formalization.Books.Algebra.Unit60.Dimension
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 62: Support and dimension of modules

The source's prime filtration is represented by the earlier chapter's
`FiniteCyclicFiltration`, refined with the assertion that every cyclic factor
is a prime quotient and with the resulting strictness of the filtration.
Support and its dimension use Mathlib's canonical `Module.support` and
`Module.supportDim`.
-/

namespace Formalization.Books.Algebra.Unit62

open Formalization.Books.Algebra.Unit05
open Formalization.Books.Algebra.Unit59
open Set

universe u v

noncomputable section

/-! ## Prime filtrations -/

/- A prime filtration keeps the cyclic-filtration data from Chapter 5 and
   records precisely the extra properties used in this chapter. -/
structure PrimeFiltration
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] where
  cyclic : FiniteCyclicFiltration R M
  ideal_isPrime : ∀ i : Fin cyclic.length, (cyclic.ideal i).IsPrime
  strict_step : ∀ i : Fin cyclic.length,
    cyclic.stage (Fin.castSucc i) < cyclic.stage (Fin.succ i)

theorem exists_primeFiltration
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] :
    Nonempty (PrimeFiltration R M) := by
  classical
  obtain ⟨s, hs_zero, hs_top⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  have hquot (i : Fin s.length) :
      ∃ p : PrimeSpectrum R,
        Nonempty
          (((s (Fin.succ i)) ⧸
            (s (Fin.castSucc i)).submoduleOf (s (Fin.succ i))) ≃ₗ[R]
            (R ⧸ p.asIdeal)) :=
    (s.step i).2
  choose p hp using hquot
  have hstrict (i : Fin s.length) :
      s (Fin.castSucc i) < s (Fin.succ i) := by
    have hle : s (Fin.castSucc i) ≤ s (Fin.succ i) := (s.step i).1
    apply lt_of_le_of_ne hle
    intro heq
    have hba : s (Fin.succ i) ≤ s (Fin.castSucc i) := by
      rw [heq]
    have htop :
        (s (Fin.castSucc i)).submoduleOf (s (Fin.succ i)) = ⊤ := by
      exact Submodule.submoduleOf_eq_top.mpr hba
    have hsub :
        Subsingleton
          (s (Fin.succ i) ⧸
            (s (Fin.castSucc i)).submoduleOf (s (Fin.succ i))) := by
      rw [Submodule.Quotient.subsingleton_iff, htop]
    letI : Subsingleton
        (s (Fin.succ i) ⧸
          (s (Fin.castSucc i)).submoduleOf (s (Fin.succ i))) := hsub
    let e := Classical.choice (hp i)
    have hzero : (1 : R ⧸ (p i).asIdeal) = 0 := by
      rw [← e.apply_symm_apply (1 : R ⧸ (p i).asIdeal)]
      rw [show e.symm (1 : R ⧸ (p i).asIdeal) = 0 by
        exact Subsingleton.elim _ _]
      exact map_zero e
    have hone : (1 : R ⧸ (p i).asIdeal) ≠ 0 := by
      letI : Nontrivial (R ⧸ (p i).asIdeal) :=
        Ideal.Quotient.nontrivial_iff.mpr (p i).isPrime.ne_top
      exact one_ne_zero
    exact hone hzero
  let I : FiniteCyclicFiltration R M :=
    { length := s.length
      stage := s
      ideal := fun i => (p i).asIdeal
      zero := by simpa [RelSeries.head] using hs_zero
      top := by simpa [RelSeries.last] using hs_top
      step := fun i => (s.step i).1
      finite := fun _ => inferInstance
      quotient := fun i => hp i }
  exact ⟨{ cyclic := I, ideal_isPrime := fun i => (p i).isPrime, strict_step := hstrict }⟩

/-! ## Support of a prime filtration -/

theorem support_eq_iUnion_zeroLocus_of_primeFiltration
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (F : PrimeFiltration R M) :
    (Module.support R M =
      ⋃ i : Fin F.cyclic.length,
        PrimeSpectrum.zeroLocus ((F.cyclic.ideal i : Ideal R) : Set R)) ∧
      (∀ i : Fin F.cyclic.length,
        (⟨F.cyclic.ideal i, F.ideal_isPrime i⟩ : PrimeSpectrum R) ∈
          Module.support R M) := by
  classical
  let n := F.cyclic.length
  let emb (k : Fin (n + 1)) (i : Fin k) : Fin n :=
    ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩
  have hfactor (i : Fin n) :
      Module.support R
          (F.cyclic.stage (Fin.succ i) ⧸
            (F.cyclic.stage (Fin.castSucc i)).submoduleOf
              (F.cyclic.stage (Fin.succ i))) =
        PrimeSpectrum.zeroLocus ((F.cyclic.ideal i : Ideal R) : Set R) := by
    obtain ⟨e⟩ := F.cyclic.quotient i
    change Module.support R
        (F.cyclic.stage (Fin.succ i) ⧸
          Submodule.comap (F.cyclic.stage (Fin.succ i)).subtype
            (F.cyclic.stage (Fin.castSucc i))) = _
    rw [e.support_eq, Module.support_eq_zeroLocus]
    simp [Submodule.annihilator_quotient]
  have hprefix (k : Fin (n + 1)) :
      Module.support R (F.cyclic.stage k) =
        ⋃ i : Fin k,
          PrimeSpectrum.zeroLocus
            ((F.cyclic.ideal (emb k i) : Ideal R) : Set R) := by
    induction k using Fin.induction with
    | zero =>
        rw [F.cyclic.zero]
        simp [Module.support_eq_empty]
    | succ i hi =>
        let A := F.cyclic.stage (Fin.castSucc i)
        let B := F.cyclic.stage (Fin.succ i)
        let P := A.submoduleOf B
        let e : P ≃ₗ[R] A := Submodule.submoduleOfEquivOfLe
          (F.cyclic.step i)
        let f : A →ₗ[R] B := P.subtype.comp e.symm.toLinearMap
        let g : B →ₗ[R] (B ⧸ P) := P.mkQ
        have hf : Function.Injective f := by
          exact P.subtype_injective.comp e.symm.injective
        have hg : Function.Surjective g := P.mkQ_surjective
        have hex : Function.Exact f g := by
          change Function.Exact (P.subtype.comp e.symm.toLinearMap) P.mkQ
          exact (LinearEquiv.precomp_exact_iff_exact).2
            (LinearMap.exact_subtype_mkQ P)
        have hsup : Module.support R B =
            Module.support R (B ⧸ P) ∪ Module.support R A := by
          exact Formalization.Books.Algebra.Unit40.support_short_exact
            f g hex hf hg
        rw [hsup, hfactor i, hi]
        ext x
        constructor
        · intro hx
          rcases hx with hx | hx
          · refine Set.mem_iUnion.mpr ⟨Fin.last i.val, ?_⟩
            simpa [emb] using hx
          · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
            refine Set.mem_iUnion.mpr ⟨Fin.castSucc j, ?_⟩
            simpa [emb] using hj
        · intro hx
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
          rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
          · right
            refine Set.mem_iUnion.mpr ⟨j, ?_⟩
            simpa [emb] using hj
          · left
            simpa [emb] using hj
  have hmain : Module.support R M =
      ⋃ i : Fin n,
        PrimeSpectrum.zeroLocus ((F.cyclic.ideal i : Ideal R) : Set R) := by
    calc
      Module.support R M = Module.support R (⊤ : Submodule R M) :=
        (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M).support_eq.symm
      _ = Module.support R (F.cyclic.stage (Fin.last n)) := by
        rw [F.cyclic.top]
      _ = ⋃ i : Fin (Fin.last n),
          PrimeSpectrum.zeroLocus
            ((F.cyclic.ideal (emb (Fin.last n) i) : Ideal R) : Set R) :=
        hprefix (Fin.last n)
      _ = ⋃ i : Fin n,
          PrimeSpectrum.zeroLocus ((F.cyclic.ideal i : Ideal R) : Set R) := by
        rfl
  refine ⟨hmain, ?_⟩
  intro i
  let A := F.cyclic.stage (Fin.castSucc i)
  let B := F.cyclic.stage (Fin.succ i)
  let P := A.submoduleOf B
  let g : B →ₗ[R] (B ⧸ P) := P.mkQ
  have hg : Function.Surjective g := P.mkQ_surjective
  obtain ⟨e⟩ := F.cyclic.quotient i
  have hi : (⟨F.cyclic.ideal i, F.ideal_isPrime i⟩ : PrimeSpectrum R) ∈
      Module.support R (B ⧸ P) := by
    change (⟨F.cyclic.ideal i, F.ideal_isPrime i⟩ : PrimeSpectrum R) ∈
      Module.support R
        (F.cyclic.stage (Fin.succ i) ⧸
          Submodule.comap (F.cyclic.stage (Fin.succ i)).subtype
            (F.cyclic.stage (Fin.castSucc i)))
    rw [e.support_eq, Module.support_eq_zeroLocus]
    rw [PrimeSpectrum.mem_zeroLocus]
    simpa [Submodule.annihilator_quotient] using
      (show ∀ r : R, r ∈ F.cyclic.ideal i → r ∈ F.cyclic.ideal i from
        fun _ h => h)
  have hi' : (⟨F.cyclic.ideal i, F.ideal_isPrime i⟩ : PrimeSpectrum R) ∈
      Module.support R B := Module.support_subset_of_surjective g hg hi
  exact Module.support_subset_of_injective B.subtype B.subtype_injective hi'

theorem support_eq_singleton_closedPoint_iff_finiteLength
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    Module.support R M = {IsLocalRing.closedPoint R} ↔
      IsFiniteLength R M := by
  constructor
  · intro hsupp
    have hzero :
        PrimeSpectrum.zeroLocus (Module.annihilator R M : Set R) =
          PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R) := by
      rw [← Module.support_eq_zeroLocus, hsupp,
        PrimeSpectrum.zeroLocus_eq_singleton]
      simp [IsLocalRing.closedPoint]
    have hrad : (Module.annihilator R M).radical = IsLocalRing.maximalIdeal R :=
      (PrimeSpectrum.zeroLocus_eq_iff).mp hzero |>.trans
        (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical
    exact finiteLength_of_pow_smul_top_eq_bot_of_isIdealOfDefinition
      (Module.annihilator R M) hrad ⟨1, by
        rw [pow_one, ← Submodule.le_annihilator_iff]
        simpa only [Submodule.annihilator_top] using
          (le_refl (Module.annihilator R M))⟩
  · intro hfin
    have hpow :
        ∃ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n •
          (⊤ : Submodule R M) = ⊥ := by
      induction hfin with
      | of_subsingleton =>
          refine ⟨0, ?_⟩
          ext x
          simp [show x = 0 from Subsingleton.elim x 0]
      | @of_simple_quotient M _ _ N _ _ ih =>
          obtain ⟨n, hn⟩ := ih
          have hmax :
              (Module.annihilator R (M ⧸ N)).IsMaximal :=
            IsSimpleModule.annihilator_isMaximal
          have hquot' :
              IsLocalRing.maximalIdeal R •
                (⊤ : Submodule R (M ⧸ N)) = ⊥ := by
            rw [← IsLocalRing.eq_maximalIdeal hmax,
              ← Submodule.annihilator_top, ← Submodule.le_annihilator_iff]
          have hIN :
              IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≤ N := by
            rw [← N.ker_mkQ]
            apply LinearMap.le_ker_iff_map.mpr
            rw [Submodule.map_smul'', Submodule.map_top,
              LinearMap.range_eq_top.mpr N.mkQ_surjective]
            exact hquot'
          have hn' :
              (IsLocalRing.maximalIdeal R) ^ n • N = ⊥ := by
            have h := congrArg (fun P : Submodule R N => P.map N.subtype) hn
            simpa only [Submodule.map_smul'', Submodule.map_subtype_top,
              Submodule.map_bot] using h
          refine ⟨n + 1, le_antisymm ?_ bot_le⟩
          rw [pow_succ, Submodule.mul_smul]
          exact (smul_mono_right ((IsLocalRing.maximalIdeal R) ^ n) hIN).trans_eq hn'
    have hsubset : Module.support R M ⊆ {IsLocalRing.closedPoint R} := by
      intro p hp
      have hann : Module.annihilator R M ≤ p.asIdeal :=
        Module.annihilator_le_of_mem_support hp
      have hpow_le :
          (IsLocalRing.maximalIdeal R) ^ (Classical.choose hpow) ≤
            Module.annihilator R M := by
        rw [← Submodule.annihilator_top, Submodule.le_annihilator_iff]
        exact Classical.choose_spec hpow
      have hmaxle : IsLocalRing.maximalIdeal R ≤ p.asIdeal := by
        intro x hx
        apply p.isPrime.mem_of_pow_mem (Classical.choose hpow)
        exact hann (hpow_le (Ideal.pow_mem_pow hx (Classical.choose hpow)))
      have hpeq : p.asIdeal = IsLocalRing.maximalIdeal R := by
        exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
          p.isPrime.ne_top hmaxle).symm
      apply PrimeSpectrum.ext
      exact hpeq
    apply Set.Subset.antisymm hsubset
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact IsLocalRing.closedPoint_mem_support R M

theorem exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) :
    (∃ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥) ↔
      Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  constructor
  · rintro ⟨n, hn⟩ p hp
    rw [PrimeSpectrum.mem_zeroLocus]
    intro x hx
    have hxann : x ^ n ∈ Module.annihilator R M := by
      rw [Module.mem_annihilator]
      intro m
      have hm : x ^ n • m ∈ I ^ n • (⊤ : Submodule R M) :=
        Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) Submodule.mem_top
      rw [hn] at hm
      simpa using hm
    exact p.isPrime.mem_of_pow_mem (r := x) n
      ((Module.annihilator_le_of_mem_support hp) hxann)
  · intro hsubset
    have hzero :
        PrimeSpectrum.zeroLocus (Module.annihilator R M : Set R) ⊆
          PrimeSpectrum.zeroLocus (I : Set R) := by
      rw [← Module.support_eq_zeroLocus]
      exact hsubset
    have hle : I ≤ (Module.annihilator R M).radical :=
      (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hzero
    obtain ⟨n, hn⟩ :=
      Ideal.exists_pow_le_of_le_radical_of_fg hle (Ideal.FG.of_isNoetherianRing I)
    refine ⟨n, ?_⟩
    apply le_antisymm
    · calc
        I ^ n • (⊤ : Submodule R M) ≤
            Module.annihilator R M • (⊤ : Submodule R M) :=
          Submodule.smul_mono_left hn
        _ = ⊥ := by
          rw [← Submodule.le_annihilator_iff]
          simpa only [Submodule.annihilator_top] using
            (le_refl (Module.annihilator R M))
    · exact bot_le

/-! ## Minimal primes and localized length -/

theorem minimal_prime_set_and_occurrences
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (F : PrimeFiltration R M) :
    ({p : PrimeSpectrum R |
        Minimal
          (fun q : Ideal R =>
            q ∈ Set.range (fun i : Fin F.cyclic.length => F.cyclic.ideal i))
          p.asIdeal} =
      {p : PrimeSpectrum R |
        Minimal (fun q : PrimeSpectrum R => q ∈ Module.support R M) p}) ∧
      (∀ p : PrimeSpectrum R,
        Minimal
            (fun q : Ideal R =>
              q ∈ Set.range (fun i : Fin F.cyclic.length => F.cyclic.ideal i))
            p.asIdeal →
          (Nat.card
              {i : Fin F.cyclic.length // F.cyclic.ideal i = p.asIdeal} : ℕ∞) =
            Module.length (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M)) := by
  sorry

/-! ## Dimension -/

/- `d` from Chapter 59 is `WithBot ℕ`, whereas Mathlib's support dimension is
   `WithBot ℕ∞`; the displayed equality uses the canonical embedding of the
   finite natural-valued invariant into extended naturals. -/
theorem d_eq_supportDim
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    WithBot.map (fun n : ℕ => (n : ℕ∞))
        (Formalization.Books.Algebra.Unit59.d R M) =
      Module.supportDim R M := by
  sorry

theorem supportDim_eq_max_of_short_exact
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [IsNoetherianRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    max (Module.supportDim R M') (Module.supportDim R M'') =
      Module.supportDim R M := by
  sorry

end

end Formalization.Books.Algebra.Unit62
