import Formalization.Books.Algebra.Unit05.FiniteModules
import Formalization.Books.Algebra.Unit40.SupportsAndAnnihilators
import Formalization.Books.Algebra.Unit60.Dimension
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Ideal

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

universe u v w

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

private theorem krullDim_union_eq_max_of_mono
    {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : ∀ ⦃x y : α⦄, x ≤ y → x ∈ s → y ∈ s)
    (ht : ∀ ⦃x y : α⦄, x ≤ y → x ∈ t → y ∈ t) :
    Order.krullDim (s ∪ t : Set α) = max (Order.krullDim s) (Order.krullDim t) := by
  apply le_antisymm
  · unfold Order.krullDim
    refine iSup_le fun p => ?_
    rcases p.head.property with hp | hp
    · let q : LTSeries s :=
        LTSeries.mk p.length (fun i =>
          ⟨p i, hs (p.head_le i) hp⟩) (by
            intro i j hij
            exact p.strictMono hij)
      calc
        ((p.length : ℕ∞) : WithBot ℕ∞) = ((q.length : ℕ∞) : WithBot ℕ∞) := by rfl
        _ ≤ Order.krullDim s := Order.LTSeries.length_le_krullDim q
        _ ≤ max (Order.krullDim s) (Order.krullDim t) := le_max_left _ _
    · let q : LTSeries t :=
        LTSeries.mk p.length (fun i =>
          ⟨p i, ht (p.head_le i) hp⟩) (by
            intro i j hij
            exact p.strictMono hij)
      calc
        ((p.length : ℕ∞) : WithBot ℕ∞) = ((q.length : ℕ∞) : WithBot ℕ∞) := by rfl
        _ ≤ Order.krullDim t := Order.LTSeries.length_le_krullDim q
        _ ≤ max (Order.krullDim s) (Order.krullDim t) := le_max_right _ _
  · exact max_le
      (Order.krullDim_le_of_strictMono
        (fun x : s => (⟨x.1, Or.inl x.2⟩ : (s ∪ t : Set α)))
        (by intro x y h; exact h))
      (Order.krullDim_le_of_strictMono
        (fun x : t => (⟨x.1, Or.inr x.2⟩ : (s ∪ t : Set α)))
        (by intro x y h; exact h))

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
  have hsupport := support_eq_iUnion_zeroLocus_of_primeFiltration F
  constructor
  · apply Set.ext
    intro p
    constructor
    · intro hp
      change Minimal
        (fun q : Ideal R =>
          q ∈ Set.range (fun i : Fin F.cyclic.length => F.cyclic.ideal i))
        p.asIdeal at hp
      have hpmem : p.asIdeal ∈
          Set.range (fun i : Fin F.cyclic.length => F.cyclic.ideal i) := hp.1
      obtain ⟨i, hi⟩ := hpmem
      have hqmem := hsupport.2 i
      have hpeq : p.asIdeal = F.cyclic.ideal i := hi.symm
      have hpsupp : p ∈ Module.support R M := by
        have heq :
            (⟨F.cyclic.ideal i, F.ideal_isPrime i⟩ : PrimeSpectrum R) = p := by
          apply PrimeSpectrum.ext
          exact hpeq.symm
        rw [← heq]
        exact hqmem
      refine ⟨hpsupp, ?_⟩
      intro q hq hqle
      rw [hsupport.1] at hq
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
      have hIq : F.cyclic.ideal j ≤ q.asIdeal := by
        rw [PrimeSpectrum.mem_zeroLocus] at hj
        exact hj
      have hpIq : p.asIdeal ≤ F.cyclic.ideal j :=
        hp.2 ⟨j, rfl⟩ (hIq.trans hqle)
      exact hpIq.trans hIq
    · intro hp
      change Minimal (fun q : PrimeSpectrum R => q ∈ Module.support R M) p at hp
      have hpsupp : p ∈ Module.support R M := hp.1
      rw [hsupport.1] at hpsupp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpsupp
      have hIp : F.cyclic.ideal i ≤ p.asIdeal := by
        rw [PrimeSpectrum.mem_zeroLocus] at hi
        exact hi
      have hqmem := hsupport.2 i
      have hqle :
          (⟨F.cyclic.ideal i, F.ideal_isPrime i⟩ : PrimeSpectrum R) ≤ p := hIp
      have hpq := hp.2 hqmem hqle
      have hpI : p.asIdeal ≤ F.cyclic.ideal i := hpq
      have hEq : p.asIdeal = F.cyclic.ideal i := le_antisymm hpI hIp
      change Minimal
        (fun q : Ideal R =>
          q ∈ Set.range (fun i : Fin F.cyclic.length => F.cyclic.ideal i))
        p.asIdeal
      refine ⟨⟨i, hEq.symm⟩, ?_⟩
      intro I hI hIpI
      obtain ⟨j, rfl⟩ := hI
      have hqmem := hsupport.2 j
      have hqle :
          (⟨F.cyclic.ideal j, F.ideal_isPrime j⟩ : PrimeSpectrum R) ≤ p := hIpI
      have hpq := hp.2 hqmem hqle
      exact hpq
  · intro p hp
    classical
    let S := Localization.AtPrime p.asIdeal
    have hfactor_length (i : Fin F.cyclic.length) :
        Module.length S
            (LocalizedModule.AtPrime p.asIdeal
              (F.cyclic.stage (Fin.succ i) ⧸
                Submodule.comap (F.cyclic.stage (Fin.succ i)).subtype
                  (F.cyclic.stage (Fin.castSucc i)))) =
          if F.cyclic.ideal i = p.asIdeal then 1 else 0 := by
      obtain ⟨e⟩ := F.cyclic.quotient i
      let e' := LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap
      have he' : Function.Bijective e' := ⟨
        LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
      let eloc : LocalizedModule.AtPrime p.asIdeal
            (F.cyclic.stage (Fin.succ i) ⧸
              Submodule.comap (F.cyclic.stage (Fin.succ i)).subtype
                (F.cyclic.stage (Fin.castSucc i))) ≃ₗ[S]
            LocalizedModule.AtPrime p.asIdeal (R ⧸ F.cyclic.ideal i) :=
        LinearEquiv.ofBijective e' he'
      by_cases hi : F.cyclic.ideal i = p.asIdeal
      · let e₀ : LocalizedModule.AtPrime p.asIdeal (R ⧸ p.asIdeal) ≃ₗ[S]
            S ⧸ p.asIdeal.map (algebraMap R S) := by
          rw [← Ideal.localized'_eq_map (S := S)
            (p := p.asIdeal.primeCompl) p.asIdeal]
          exact (localizedQuotientEquiv p.asIdeal.primeCompl
            (p.asIdeal : Submodule R R)).symm
        let _ : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) := by
          apply (isSimpleModule_iff_quot_maximal).2
          exact ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
        have hmap : p.asIdeal.map (algebraMap R S) = IsLocalRing.maximalIdeal S :=
          IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal S
        have e₀' : LocalizedModule.AtPrime p.asIdeal (R ⧸ F.cyclic.ideal i) ≃ₗ[S]
            S ⧸ p.asIdeal.map (algebraMap R S) := by
          rw [hi]
          exact e₀
        calc
          Module.length S
              (LocalizedModule.AtPrime p.asIdeal
                (F.cyclic.stage (Fin.succ i) ⧸
                  Submodule.comap (F.cyclic.stage (Fin.succ i)).subtype
                    (F.cyclic.stage (Fin.castSucc i)))) =
              Module.length S
                (LocalizedModule.AtPrime p.asIdeal (R ⧸ F.cyclic.ideal i)) :=
            eloc.length_eq
          _ = Module.length S (S ⧸ p.asIdeal.map (algebraMap R S)) := by
            exact e₀'.length_eq
          _ = Module.length S (S ⧸ IsLocalRing.maximalIdeal S) := by rw [hmap]
          _ = 1 := Module.length_eq_one _ _
          _ = if F.cyclic.ideal i = p.asIdeal then 1 else 0 := by simp [hi]
      · have hnotle : ¬ F.cyclic.ideal i ≤ p.asIdeal := by
          intro hle
          have hle' : p.asIdeal ≤ F.cyclic.ideal i :=
            hp.2 ⟨i, rfl⟩ hle
          exact hi (le_antisymm hle hle')
        have hnotle' : ¬ (F.cyclic.ideal i : Set R) ⊆ (p.asIdeal : Set R) := by
          intro hle
          exact hnotle hle
        obtain ⟨x, hxI, hxp⟩ := Set.not_subset.mp hnotle'
        have hxS : x ∈ p.asIdeal.primeCompl :=
          Ideal.mem_primeCompl_iff.mpr hxp
        let _ : Subsingleton (LocalizedModule.AtPrime p.asIdeal
            (R ⧸ F.cyclic.ideal i)) := by
          rw [LocalizedModule.subsingleton_iff]
          intro z
          refine ⟨x, hxS, ?_⟩
          refine Submodule.Quotient.induction_on
            (p := (F.cyclic.ideal i : Submodule R R)) z ?_
          intro y
          rw [← Submodule.Quotient.mk_smul]
          change Submodule.Quotient.mk (x • y) = Submodule.Quotient.mk (0 : R)
          apply (Submodule.Quotient.eq
            (p := (F.cyclic.ideal i : Submodule R R))).2
          simpa [smul_eq_mul, mul_comm] using
            F.cyclic.ideal i |>.mul_mem_left y hxI
        calc
          Module.length S
              (LocalizedModule.AtPrime p.asIdeal
                (F.cyclic.stage (Fin.succ i) ⧸
                  Submodule.comap (F.cyclic.stage (Fin.succ i)).subtype
                    (F.cyclic.stage (Fin.castSucc i)))) =
              Module.length S
                (LocalizedModule.AtPrime p.asIdeal (R ⧸ F.cyclic.ideal i)) :=
            eloc.length_eq
          _ = 0 := Module.length_eq_zero
          _ = if F.cyclic.ideal i = p.asIdeal then 1 else 0 := by simp [hi]
    have hstep (i : Fin F.cyclic.length) :
        Module.length S (LocalizedModule.AtPrime p.asIdeal
            (F.cyclic.stage (Fin.succ i))) =
          Module.length S (LocalizedModule.AtPrime p.asIdeal
            (F.cyclic.stage (Fin.castSucc i))) +
            Module.length S (LocalizedModule.AtPrime p.asIdeal
              (F.cyclic.stage (Fin.succ i) ⧸
                Submodule.comap (F.cyclic.stage (Fin.succ i)).subtype
                  (F.cyclic.stage (Fin.castSucc i)))) := by
      let N := Submodule.comap (F.cyclic.stage (Fin.succ i)).subtype
        (F.cyclic.stage (Fin.castSucc i))
      let f := LocalizedModule.map p.asIdeal.primeCompl
        (Submodule.inclusion (F.cyclic.step i))
      let g := LocalizedModule.map p.asIdeal.primeCompl N.mkQ
      have hf : Function.Injective f := by
        exact LocalizedModule.map_injective p.asIdeal.primeCompl _
          (Submodule.inclusion_injective _)
      have hg : Function.Surjective g := by
        exact LocalizedModule.map_surjective p.asIdeal.primeCompl _
          (Submodule.mkQ_surjective N)
      have hex0 : Function.Exact (Submodule.inclusion (F.cyclic.step i)) N.mkQ := by
        rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
      have hex : Function.Exact f g := by
        simpa [f, g, LocalizedModule.map, IsLocalizedModule.mapExtendScalars,
          LinearMap.extendScalarsOfIsLocalizationEquiv,
          LinearMap.extendScalarsOfIsLocalization] using
          (LocalizedModule.map_exact p.asIdeal.primeCompl
            (Submodule.inclusion (F.cyclic.step i)) N.mkQ hex0)
      exact Module.length_eq_add_of_exact f g hf hg hex
    let a : Fin F.cyclic.length → ℕ∞ := fun i =>
      if F.cyclic.ideal i = p.asIdeal then 1 else 0
    let emb (k : Fin (F.cyclic.length + 1)) (i : Fin k) : Fin F.cyclic.length :=
      ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩
    have hprefix (k : Fin (F.cyclic.length + 1)) :
        Module.length S (LocalizedModule.AtPrime p.asIdeal (F.cyclic.stage k)) =
          ∑ i : Fin k, a (emb k i) := by
      induction k using Fin.induction with
      | zero =>
          rw [F.cyclic.zero, Module.length_eq_zero]
          symm
          apply Finset.sum_eq_zero
          intro i hi
          exact Fin.elim0 i
      | succ i hi =>
          rw [hstep i, hfactor_length i, hi]
          change
            (∑ j : Fin i.val, a (emb i.castSucc j)) +
                (if F.cyclic.ideal i = p.asIdeal then 1 else 0) =
              ∑ j : Fin (i.val + 1), a (emb (Fin.succ i) j)
          calc
            (∑ j : Fin i.val, a (emb i.castSucc j)) +
                  (if F.cyclic.ideal i = p.asIdeal then 1 else 0) =
                (∑ j : Fin i.val,
                    a (emb (Fin.succ i) (Fin.castSucc j))) +
                  a (emb (Fin.succ i) (Fin.last i.val)) := by
              apply congrArg₂ (fun x y => x + y)
              · apply Finset.sum_congr rfl
                intro j hj
                simp [emb]
              · simp [emb, a]
            _ = ∑ j : Fin (i.val + 1), a (emb (Fin.succ i) j) :=
              (Fin.sum_univ_castSucc
                (fun j : Fin (i.val + 1) => a (emb (Fin.succ i) j))).symm
    let etop' := LocalizedModule.map p.asIdeal.primeCompl
      (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M).toLinearMap
    have hetop' : Function.Bijective etop' := ⟨
      LocalizedModule.map_injective p.asIdeal.primeCompl _
        (Submodule.topEquiv.injective),
      LocalizedModule.map_surjective p.asIdeal.primeCompl _
        (Submodule.topEquiv.surjective)⟩
    let etop : LocalizedModule.AtPrime p.asIdeal (⊤ : Submodule R M) ≃ₗ[S]
        LocalizedModule.AtPrime p.asIdeal M := LinearEquiv.ofBijective etop' hetop'
    have hlast :
        Module.length S (LocalizedModule.AtPrime p.asIdeal M) =
          ∑ i : Fin F.cyclic.length, a i := by
      rw [← etop.length_eq]
      have htop : F.cyclic.stage (Fin.last F.cyclic.length) = ⊤ := F.cyclic.top
      have h := hprefix (Fin.last F.cyclic.length)
      rw [htop] at h
      simpa [emb, a] using h
    have hcard :
        (Nat.card {i : Fin F.cyclic.length // F.cyclic.ideal i = p.asIdeal} : ℕ∞) =
          ∑ i : Fin F.cyclic.length, a i := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      symm
      simp [a]
    rw [hcard, ← hlast]

/-! ## Dimension -/

private theorem d_eq_of_linearEquiv
    {R : Type u} {N : Type v} {N' : Type w} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [AddCommGroup N'] [Module R N'] [Module.Finite R N']
    (e : N ≃ₗ[R] N') :
    Formalization.Books.Algebra.Unit59.d R N =
      Formalization.Books.Algebra.Unit59.d R N' := by
  have hcum :
      Formalization.Books.Algebra.Unit59.cumulativeHilbertFunction R N =
        Formalization.Books.Algebra.Unit59.cumulativeHilbertFunction R N' := by
    funext n
    let P : Submodule R N :=
      (IsLocalRing.maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R N)
    let Q : Submodule R N' :=
      (IsLocalRing.maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R N')
    have hPQ : P.map e.toLinearMap = Q := by
      dsimp [P, Q]
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr e.surjective]
    let eQ : (N ⧸ P) ≃ₗ[R] (N' ⧸ Q) :=
      Submodule.Quotient.equiv P Q e hPQ
    change
      (Module.length R (N ⧸ P)).toNat =
        (Module.length R (N' ⧸ Q)).toNat
    exact congrArg ENat.toNat eQ.length_eq
  have hcumInteger :
      Formalization.Books.Algebra.Unit59.cumulativeHilbertFunctionInteger
          R N =
        Formalization.Books.Algebra.Unit59.cumulativeHilbertFunctionInteger
          R N' := by
    funext n
    simp [Formalization.Books.Algebra.Unit59.cumulativeHilbertFunctionInteger,
      Formalization.Books.Algebra.Unit59.natFunctionToInteger, hcum]
  by_cases hN : Nontrivial N
  · have hnot : ¬ Subsingleton N' := by
      intro hsub
      exact (not_nontrivial_iff_subsingleton.mpr
        (show Subsingleton N from
          ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩)) hN
    have hN' : Nontrivial N' := not_subsingleton_iff_nontrivial.mp hnot
    simp only [Formalization.Books.Algebra.Unit59.d, if_pos hN, if_pos hN',
      hcumInteger]
  · have hsub : Subsingleton N := not_nontrivial_iff_subsingleton.mp hN
    have hsub' : Subsingleton N' := ⟨fun x y =>
      e.symm.injective (Subsingleton.elim _ _)⟩
    have hN' : ¬ Nontrivial N' :=
      not_nontrivial_iff_subsingleton.mpr hsub'
    simp only [Formalization.Books.Algebra.Unit59.d, if_neg hN, if_neg hN']

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
  let F := Classical.choice (exists_primeFiltration (R := R) (M := M))
  have hd_quotient (I : Ideal R) (hI : I.IsPrime) :
      WithBot.map (fun n : ℕ => (n : ℕ∞))
          (Formalization.Books.Algebra.Unit59.d R (R ⧸ I)) =
        ringKrullDim (R ⧸ I) := by
    have : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hI.ne_top
    let hlocalhom : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk I) := hlocalhom
    have hmaxmap :
        (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) =
          IsLocalRing.maximalIdeal (R ⧸ I) := by
      rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk I)]
      exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective _
    have hlength_cum (n : ℕ) :
        Module.length R
            (Formalization.Books.Algebra.Unit59.idealPowerCumulativeQuotient
              (IsLocalRing.maximalIdeal R) (R ⧸ I) n) =
          Module.length (R ⧸ I)
            (Formalization.Books.Algebra.Unit59.idealPowerCumulativeQuotient
              (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I) n) := by
      let P : Submodule (R ⧸ I) (R ⧸ I) :=
        (IsLocalRing.maximalIdeal (R ⧸ I)) ^ (n + 1) •
          (⊤ : Submodule (R ⧸ I) (R ⧸ I))
      let P' : Submodule R (R ⧸ I) :=
        (IsLocalRing.maximalIdeal R) ^ (n + 1) •
          (⊤ : Submodule R (R ⧸ I))
      have hpowmap :
          ((IsLocalRing.maximalIdeal R) ^ (n + 1)).map
              (Ideal.Quotient.mk I) =
            (IsLocalRing.maximalIdeal (R ⧸ I)) ^ (n + 1) := by
        rw [Ideal.map_pow, hmaxmap]
      have hP : P = (IsLocalRing.maximalIdeal (R ⧸ I) ^ (n + 1) :
          Submodule (R ⧸ I) (R ⧸ I)) := by
        dsimp [P]
        calc
          (IsLocalRing.maximalIdeal (R ⧸ I)) ^ (n + 1) •
                (⊤ : Submodule (R ⧸ I) (R ⧸ I)) =
              (((IsLocalRing.maximalIdeal (R ⧸ I)) ^ (n + 1)).map
                (algebraMap (R ⧸ I) (R ⧸ I))).restrictScalars (R ⧸ I) :=
            Ideal.smul_top_eq_map _
          _ = (IsLocalRing.maximalIdeal (R ⧸ I) ^ (n + 1) :
              Submodule (R ⧸ I) (R ⧸ I)) := by simp
      have hP' : P' =
          (((IsLocalRing.maximalIdeal R) ^ (n + 1)).map
            (Ideal.Quotient.mk I)).restrictScalars R := by
        dsimp [P']
        exact Ideal.smul_top_eq_map _
      have hsub : P' = P.restrictScalars R := by
        rw [hP', hP, hpowmap]
      let e : ((R ⧸ I) ⧸ P') ≃ₗ[R] (R ⧸ I) ⧸ P := by
        rw [hsub]
        exact (Submodule.Quotient.restrictScalarsEquiv (R ⧸ I) P).restrictScalars R
      calc
        Module.length R
            (Formalization.Books.Algebra.Unit59.idealPowerCumulativeQuotient
              (IsLocalRing.maximalIdeal R) (R ⧸ I) n) =
            Module.length R ((R ⧸ I) ⧸ P') := rfl
        _ = Module.length R ((R ⧸ I) ⧸ P) := e.length_eq
        _ = Module.length (R ⧸ I) ((R ⧸ I) ⧸ P) :=
          Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
        _ = Module.length (R ⧸ I)
            (Formalization.Books.Algebra.Unit59.idealPowerCumulativeQuotient
              (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I) n) := rfl
    have hcum :
        Formalization.Books.Algebra.Unit59.cumulativeHilbertFunction R (R ⧸ I) =
          Formalization.Books.Algebra.Unit59.cumulativeHilbertFunction
            (R ⧸ I) (R ⧸ I) := by
      funext n
      change
        (Module.length R
          (Formalization.Books.Algebra.Unit59.idealPowerCumulativeQuotient
            (IsLocalRing.maximalIdeal R) (R ⧸ I) n)).toNat =
          (Module.length (R ⧸ I)
            (Formalization.Books.Algebra.Unit59.idealPowerCumulativeQuotient
              (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I) n)).toNat
      rw [hlength_cum]
    have hcumInteger :
        Formalization.Books.Algebra.Unit59.cumulativeHilbertFunctionInteger
            R (R ⧸ I) =
          Formalization.Books.Algebra.Unit59.cumulativeHilbertFunctionInteger
            (R ⧸ I) (R ⧸ I) := by
      funext n
      simp [Formalization.Books.Algebra.Unit59.cumulativeHilbertFunctionInteger,
        Formalization.Books.Algebra.Unit59.natFunctionToInteger, hcum]
    have hd_base :
        Formalization.Books.Algebra.Unit59.d R (R ⧸ I) =
          Formalization.Books.Algebra.Unit59.d (R ⧸ I) (R ⧸ I) := by
      unfold Formalization.Books.Algebra.Unit59.d
      simp only [if_pos (inferInstance : Nontrivial (R ⧸ I)), hcumInteger]
    rw [hd_base]
    have hbot : ringKrullDim (R ⧸ I) ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim (R ⧸ I) ≠ ⊤ := ringKrullDim_ne_top
    cases hq : ringKrullDim (R ⧸ I) with
    | bot => exact (hbot hq).elim
    | coe q =>
        cases q with
        | top => exact (htop hq).elim
        | coe n =>
            have hiff :
                ringKrullDim (R ⧸ I) = n ↔
                  Formalization.Books.Algebra.Unit59.d (R ⧸ I) (R ⧸ I) = n :=
              (Formalization.Books.Algebra.Unit60.local_dimension_characterization
                (R ⧸ I) (inferInstance : Nontrivial (R ⧸ I)) n).out 0 1
            have hdim : ringKrullDim (R ⧸ I) = n := by
              rw [hq]
              rfl
            have hd :
                Formalization.Books.Algebra.Unit59.d (R ⧸ I) (R ⧸ I) = n :=
              hiff.mp hdim
            rw [hd]
            rfl
  have hstage (k : Fin (F.cyclic.length + 1)) :
      WithBot.map (fun n : ℕ => (n : ℕ∞))
          (Formalization.Books.Algebra.Unit59.d R (F.cyclic.stage k)) =
        Module.supportDim R (F.cyclic.stage k) := by
    induction k using Fin.induction with
    | zero =>
        have hsub : Subsingleton (F.cyclic.stage (0 : Fin (F.cyclic.length + 1))) := by
          rw [F.cyclic.zero]
          infer_instance
        have hn : ¬ Nontrivial (F.cyclic.stage (0 : Fin (F.cyclic.length + 1))) :=
          not_nontrivial_iff_subsingleton.mpr hsub
        have hdzero :
            Formalization.Books.Algebra.Unit59.d R
                (F.cyclic.stage (0 : Fin (F.cyclic.length + 1))) = ⊥ := by
          unfold Formalization.Books.Algebra.Unit59.d
          rw [if_neg hn]
        have hsbot :
            Module.supportDim R
                (F.cyclic.stage (0 : Fin (F.cyclic.length + 1))) = ⊥ :=
          @Module.supportDim_eq_bot_of_subsingleton R _
            (F.cyclic.stage (0 : Fin (F.cyclic.length + 1))) _ _ hsub
        rw [hdzero, hsbot]
        rfl
    | succ i hi =>
        let A := F.cyclic.stage (Fin.castSucc i)
        let B := F.cyclic.stage (Fin.succ i)
        let P := A.submoduleOf B
        let e : P ≃ₗ[R] A := Submodule.submoduleOfEquivOfLe
          (F.cyclic.step i)
        let f : A →ₗ[R] B := P.subtype.comp e.symm.toLinearMap
        let g₀ : B →ₗ[R] (B ⧸ P) := P.mkQ
        obtain ⟨q⟩ := F.cyclic.quotient i
        have q' : (B ⧸ P) ≃ₗ[R] (R ⧸ F.cyclic.ideal i) := by
          change (B ⧸ P) ≃ₗ[R] (R ⧸ F.cyclic.ideal i) at q
          exact q
        let g : B →ₗ[R] (R ⧸ F.cyclic.ideal i) :=
          q'.toLinearMap.comp g₀
        have hf : Function.Injective f := by
          exact P.subtype_injective.comp e.symm.injective
        have hg₀ : Function.Surjective g₀ := P.mkQ_surjective
        have hex₀ : Function.Exact f g₀ := by
          change Function.Exact (P.subtype.comp e.symm.toLinearMap) P.mkQ
          exact (LinearEquiv.precomp_exact_iff_exact).2
            (LinearMap.exact_subtype_mkQ P)
        have hg : Function.Surjective g := by
          exact q'.surjective.comp hg₀
        have hex : Function.Exact f g := by
          change Function.Exact f (q'.toLinearMap.comp g₀)
          exact (LinearEquiv.postcomp_exact_iff_exact).2 hex₀
        have hdstep :=
          (Formalization.Books.Algebra.Unit59.hilbert_short_exact_degree_statements
            (IsLocalRing.maximalIdeal R)
            (Formalization.Books.Algebra.Unit59.maximalIdeal_isIdealOfDefinition R)
            f g₀ hf hg₀ hex₀).2.2
        have hfactor :
            WithBot.map (fun n : ℕ => (n : ℕ∞))
                (Formalization.Books.Algebra.Unit59.d R
                  (B ⧸ P)) =
              Module.supportDim R (B ⧸ P) := by
          calc
            WithBot.map (fun n : ℕ => (n : ℕ∞))
                (Formalization.Books.Algebra.Unit59.d R
                  (B ⧸ P)) =
                WithBot.map (fun n : ℕ => (n : ℕ∞))
                  (Formalization.Books.Algebra.Unit59.d R
                    (R ⧸ F.cyclic.ideal i)) :=
              congrArg (WithBot.map (fun n : ℕ => (n : ℕ∞)))
                (d_eq_of_linearEquiv q')
            _ = Module.supportDim R (R ⧸ F.cyclic.ideal i) :=
              (hd_quotient _ (F.ideal_isPrime i)).trans
                (Module.supportDim_quotient_eq_ringKrullDim _).symm
            _ = Module.supportDim R (B ⧸ P) :=
              (Module.supportDim_eq_of_equiv q').symm
        have hsupport : Module.support R B =
            Module.support R (B ⧸ P) ∪ Module.support R A :=
          Formalization.Books.Algebra.Unit40.support_short_exact
            f g₀ hex₀ hf hg₀
        have hdimstep :
            max (Module.supportDim R A) (Module.supportDim R (B ⧸ P)) =
              Module.supportDim R B := by
          calc
            max (Module.supportDim R A) (Module.supportDim R (B ⧸ P)) =
                max (Module.supportDim R (B ⧸ P)) (Module.supportDim R A) :=
              max_comm _ _
            _ = Order.krullDim
                (Module.support R (B ⧸ P) ∪ Module.support R A :
                  Set (PrimeSpectrum R)) := by
              rw [Module.supportDim, Module.supportDim,
                krullDim_union_eq_max_of_mono]
              · intro p r hp hmem
                exact Module.mem_support_mono hp hmem
              · intro p r hp hmem
                exact Module.mem_support_mono hp hmem
            _ = Module.supportDim R B := by
              rw [← hsupport, Module.supportDim]
        have hmapstep :
            max
                (WithBot.map (fun n : ℕ => (n : ℕ∞))
                  (Formalization.Books.Algebra.Unit59.d R A))
                (WithBot.map (fun n : ℕ => (n : ℕ∞))
                  (Formalization.Books.Algebra.Unit59.d R
                    (B ⧸ P))) =
              WithBot.map (fun n : ℕ => (n : ℕ∞))
                (Formalization.Books.Algebra.Unit59.d R B) := by
          have map_max (a b : WithBot ℕ) :
              WithBot.map (fun n : ℕ => (n : ℕ∞)) (max a b) =
                max (WithBot.map (fun n : ℕ => (n : ℕ∞)) a)
                  (WithBot.map (fun n : ℕ => (n : ℕ∞)) b) := by
            cases a with
            | bot => cases b <;> simp [WithBot.map_coe]
            | coe a =>
                cases b with
                | bot => simp [WithBot.map_coe]
                | coe b =>
                    have hmaple :
                        WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑a : WithBot ℕ) ≤
                            WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑b : WithBot ℕ) ↔
                          (↑a : WithBot ℕ) ≤ (↑b : WithBot ℕ) :=
                      WithBot.map_le_iff _ (by
                        intro x y
                        exact WithTop.coe_le_coe)
                    by_cases h : (↑a : WithBot ℕ) ≤ (↑b : WithBot ℕ)
                    · have hm := hmaple.mpr h
                      have hleft :
                          max (↑a : WithBot ℕ) (↑b : WithBot ℕ) = (↑b : WithBot ℕ) :=
                        max_eq_right h
                      have hright :
                          max (WithBot.map (fun n : ℕ => (n : ℕ∞))
                            (↑a : WithBot ℕ))
                              (WithBot.map (fun n : ℕ => (n : ℕ∞))
                                (↑b : WithBot ℕ)) =
                            WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑b : WithBot ℕ) :=
                            max_eq_right hm
                      calc
                        WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (max (↑a : WithBot ℕ) (↑b : WithBot ℕ)) =
                            WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑b : WithBot ℕ) := congrArg _ hleft
                        _ = max (WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑a : WithBot ℕ))
                            (WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑b : WithBot ℕ)) := hright.symm
                    · have hm : ¬
                          WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑a : WithBot ℕ) ≤
                            WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑b : WithBot ℕ) := by
                        intro hm
                        exact h (hmaple.mp hm)
                      have hleft :
                          max (↑a : WithBot ℕ) (↑b : WithBot ℕ) = (↑a : WithBot ℕ) :=
                        max_eq_left (le_of_not_ge h)
                      have hright :
                          max (WithBot.map (fun n : ℕ => (n : ℕ∞))
                            (↑a : WithBot ℕ))
                              (WithBot.map (fun n : ℕ => (n : ℕ∞))
                                (↑b : WithBot ℕ)) =
                            WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑a : WithBot ℕ) :=
                            max_eq_left (le_of_not_ge hm)
                      calc
                        WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (max (↑a : WithBot ℕ) (↑b : WithBot ℕ)) =
                            WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑a : WithBot ℕ) := congrArg _ hleft
                        _ = max (WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑a : WithBot ℕ))
                            (WithBot.map (fun n : ℕ => (n : ℕ∞))
                              (↑b : WithBot ℕ)) := hright.symm
          rw [← map_max]
          exact congrArg
            (WithBot.map (fun n : ℕ => (n : ℕ∞))) hdstep
        calc
          WithBot.map (fun n : ℕ => (n : ℕ∞))
              (Formalization.Books.Algebra.Unit59.d R B) =
              max
                (WithBot.map (fun n : ℕ => (n : ℕ∞))
                  (Formalization.Books.Algebra.Unit59.d R A))
                (WithBot.map (fun n : ℕ => (n : ℕ∞))
                  (Formalization.Books.Algebra.Unit59.d R
                    (B ⧸ P))) := hmapstep.symm
          _ = max (Module.supportDim R A)
              (Module.supportDim R (B ⧸ P)) := by
            rw [hi, hfactor]
          _ = Module.supportDim R B := hdimstep
  let eTop : F.cyclic.stage (Fin.last F.cyclic.length) ≃ₗ[R] M := by
    rw [F.cyclic.top]
    exact Submodule.topEquiv
  calc
    WithBot.map (fun n : ℕ => (n : ℕ∞))
        (Formalization.Books.Algebra.Unit59.d R M) =
      WithBot.map (fun n : ℕ => (n : ℕ∞))
        (Formalization.Books.Algebra.Unit59.d R
          (F.cyclic.stage (Fin.last F.cyclic.length))) := by
        exact congrArg (WithBot.map (fun n : ℕ => (n : ℕ∞)))
          (d_eq_of_linearEquiv eTop).symm
    _ = Module.supportDim R (F.cyclic.stage (Fin.last F.cyclic.length)) :=
      hstage (Fin.last F.cyclic.length)
    _ = Module.supportDim R M := Module.supportDim_eq_of_equiv eTop

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
  have hsupport : Module.support R M =
      Module.support R M'' ∪ Module.support R M' :=
    Formalization.Books.Algebra.Unit40.support_short_exact f g hfg hf hg
  calc
    max (Module.supportDim R M') (Module.supportDim R M'') =
        max (Module.supportDim R M'') (Module.supportDim R M') := max_comm _ _
    _ = Order.krullDim
        (Module.support R M'' ∪ Module.support R M' : Set (PrimeSpectrum R)) := by
      rw [Module.supportDim, Module.supportDim, krullDim_union_eq_max_of_mono]
      · intro p q hp hmem
        exact Module.mem_support_mono hp hmem
      · intro p q hp hmem
        exact Module.mem_support_mono hp hmem
    _ = Module.supportDim R M := by rw [← hsupport, Module.supportDim]

end

end Formalization.Books.Algebra.Unit62
