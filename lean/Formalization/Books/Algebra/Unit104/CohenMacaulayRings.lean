import Formalization.Books.Algebra.Unit71.ExtGroups
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Commutative Algebra, Chapter 104: Cohen-Macaulay rings

This file records the definitions and theorem interfaces in the section
“Cohen-Macaulay rings”.  The Cohen-Macaulay module predicate and the
dimension, chain, regular-sequence, and resolution interfaces are reused
from earlier chapters.
-/

namespace Formalization.Books.Algebra.Unit104

open Formalization.Books.Algebra.Unit72

universe u

noncomputable section

/-! ## Local Cohen-Macaulay rings -/

/- The source definition: a local ring is Cohen-Macaulay when its regular
   module is Cohen-Macaulay. -/
def IsCohenMacaulayLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  Formalization.Books.Algebra.Unit103.IsCohenMacaulay R R

private theorem regular_mem_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {xs : List R} (hreg : RingTheory.Sequence.IsRegular R xs)
    {r : R} (hr : r ∈ xs) : r ∈ IsLocalRing.maximalIdeal R := by
  by_contra hrmax
  have hunit : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp hrmax
  have htop : Ideal.ofList xs = (⊤ : Ideal R) := by
    apply top_unique
    rw [← Ideal.span_singleton_eq_top.mpr hunit]
    exact Ideal.span_le.2 (fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Ideal.subset_span hr)
  apply hreg.top_ne_smul
  rw [htop]
  simp

/- The equivalent criterion stated immediately after the definition. -/
theorem isCohenMacaulayLocalRing_iff_exists_regularSequence
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsCohenMacaulayLocalRing R ↔
      ∃ xs : List R,
        (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
          RingTheory.Sequence.IsRegular R xs ∧
            ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) = 0 := by
  constructor
  · intro hcm
    obtain ⟨ys, hreg, hdepth⟩ :=
      regular_sequence_extend_to_localDepth ([] : List R)
        (RingTheory.Sequence.IsRegular.nil R R)
    simp only [List.nil_append] at hreg hdepth
    have hcm' : ((localDepth R R : ℕ∞) : WithBot ℕ∞) =
        Module.supportDim R R := hcm
    have hdimlen : ringKrullDim R =
        (((ys.length : ℕ∞) : WithBot ℕ∞)) := by
      calc
        ringKrullDim R = Module.supportDim R R :=
          (Module.supportDim_self_eq_ringKrullDim R).symm
        _ = ((localDepth R R : ℕ∞) : WithBot ℕ∞) := hcm'.symm
        _ = (((ys.length : ℕ∞) : WithBot ℕ∞)) := by rw [hdepth]
    have hqadd :=
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ys hreg
    have hqzero : ringKrullDim (R ⧸ (Ideal.ofList ys : Ideal R)) = 0 := by
      have hcancel :
          ringKrullDim (R ⧸ (Ideal.ofList ys : Ideal R)) +
              (((ys.length : ℕ∞) : WithBot ℕ∞)) =
            0 + (((ys.length : ℕ∞) : WithBot ℕ∞)) := by
        calc
          ringKrullDim (R ⧸ (Ideal.ofList ys : Ideal R)) +
                (((ys.length : ℕ∞) : WithBot ℕ∞)) =
              ringKrullDim R := hqadd
          _ = (((ys.length : ℕ∞) : WithBot ℕ∞)) := hdimlen
          _ = 0 + (((ys.length : ℕ∞) : WithBot ℕ∞)) := by simp
      cases hq : ringKrullDim (R ⧸ (Ideal.ofList ys : Ideal R)) with
      | bot => simp [hq] at hcancel
      | coe q =>
          have hcancel' : ((q : ℕ∞) : WithBot ℕ∞) +
              (((ys.length : ℕ∞) : WithBot ℕ∞)) =
              0 + (((ys.length : ℕ∞) : WithBot ℕ∞)) := by
            simpa [hq] using hcancel
          have hcancel'' : q + (ys.length : ℕ∞) =
              0 + (ys.length : ℕ∞) := by
            exact WithBot.coe_injective hcancel'
          have hq' : q = 0 := by
            exact ENat.add_right_injective_of_ne_top (n := ys.length)
              (by simp) (by simpa [add_comm] using hcancel'')
          simpa [hq] using hq'
    refine ⟨ys, ?_, hreg, hqzero⟩
    intro x hx
    exact regular_mem_maximalIdeal hreg hx
  · rintro ⟨xs, hmem, hreg, hq⟩
    have hdimlen : ringKrullDim R =
        (((xs.length : ℕ∞) : WithBot ℕ∞)) := by
      have hadd :=
        ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs hreg
      rw [hq] at hadd
      simpa using hadd.symm
    have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ :=
      smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) R
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
    have hlow : (xs.length : ℕ∞) ≤ localDepth R R := by
      unfold localDepth depth
      rw [dif_neg hmax]
      exact le_sSup ⟨xs, rfl, hmem, hreg⟩
    have hupp : localDepth R R ≤ (xs.length : ℕ∞) := by
      apply WithBot.coe_le_coe.mp
      rw [← hdimlen]
      calc
        ((localDepth R R : ℕ∞) : WithBot ℕ∞) ≤
            Module.supportDim R R := supportDim_ge_localDepth
        _ = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
    have hdepth : localDepth R R = (xs.length : ℕ∞) :=
      le_antisymm hupp hlow
    change ((localDepth R R : ℕ∞) : WithBot ℕ∞) =
      Module.supportDim R R
    rw [hdepth, Module.supportDim_self_eq_ringKrullDim]
    exact hdimlen.symm

/- The first part of lemma-reformulate-CM.  Addition in `WithBot ℕ∞` is the
   canonical dimension normalization used by the preceding chapter. -/
theorem regularSequence_iff_expected_quotient_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) :
    RingTheory.Sequence.IsRegular R xs ↔
      ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) +
          (((xs.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := by
  constructor
  · intro hreg
    exact ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs hreg
  · intro hEq
    obtain ⟨d, hd, _, _⟩ :=
      localDepth_eq_min_ext (R := R) (M := R)
    have hcm : Formalization.Books.Algebra.Unit103.IsCohenMacaulay R R := hR
    have hdim : Module.supportDim R R =
        (((d : ℕ∞) : WithBot ℕ∞)) := by
      calc
        Module.supportDim R R =
            ((localDepth R R : ℕ∞) : WithBot ℕ∞) := hcm.symm
        _ = (((d : ℕ∞) : WithBot ℕ∞)) := by rw [hd]
    have hEq' := hEq
    rw [← Module.supportDim_self_eq_ringKrullDim R, hdim] at hEq'
    have hEq'' :
        Module.supportDim R (R ⧸ (Ideal.ofList xs : Ideal R)) +
            (((xs.length : ℕ∞) : WithBot ℕ∞)) =
          (((d : ℕ∞) : WithBot ℕ∞)) := by
      simpa [Module.supportDim_quotient_eq_ringKrullDim] using hEq'
    have hqne :
        Module.supportDim R (R ⧸ (Ideal.ofList xs : Ideal R)) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hEq''
      simp at hEq''
    obtain ⟨q, hqeq⟩ :=
      WithBot.ne_bot_iff_exists.mp hqne
    have hEqNat :
        q + (xs.length : ℕ∞) = (d : ℕ∞) := by
      apply WithBot.coe_injective
      simpa [hqeq] using hEq''
    cases q with
    | top => simp at hEqNat
    | coe q =>
        have hEqNat' : q + xs.length = d := by
          exact_mod_cast hEqNat
        have hle : xs.length ≤ d := by omega
        have hq : q = d - xs.length := by omega
        let g : Fin xs.length → R := fun i => xs.get i
        have hlist : List.ofFn g = xs := by
          simpa only [g] using List.ofFn_get xs
        have hg : ∀ i, g i ∈ IsLocalRing.maximalIdeal R := by
          intro i
          exact hxs (g i) (by
            change xs.get i ∈ xs
            exact List.get_mem xs i)
        have hsub :
            (Ideal.ofList xs : Ideal R) • (⊤ : Submodule R R) =
              (Ideal.ofList xs : Submodule R R) := by
          simp
        have hquot :
            Module.supportDim R
                (Formalization.Books.Algebra.Unit103.quotientByList R
                  (List.ofFn g)) =
              (((d - xs.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
          change Module.supportDim R
            (R ⧸ (Ideal.ofList (List.ofFn g) • (⊤ : Submodule R R))) =
              (((d - xs.length : ℕ) : ℕ∞) : WithBot ℕ∞)
          rw [hlist]
          calc
            Module.supportDim R
                (R ⧸ (Ideal.ofList xs • (⊤ : Submodule R R))) =
                Module.supportDim R (R ⧸ (Ideal.ofList xs : Ideal R)) :=
              Module.supportDim_eq_of_equiv
                (Submodule.quotEquivOfEq _ _ hsub)
            _ = (((d - xs.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
              rw [← hqeq]
              simp [hq]
        have hres :=
          Formalization.Books.Algebra.Unit103.regularSequence_of_supportDim_quotient_eq
            d xs.length hcm g hle hdim hg hquot
        simpa only [hlist] using hres.1

/- The second part of lemma-reformulate-CM, namely that the sequence can be
   extended to maximal length and all its successive quotients are
   Cohen-Macaulay of the expected dimension. -/
def IsCohenMacaulayQuotientRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) : Prop :=
  ∃ hlocal : IsLocalRing (R ⧸ I),
    letI : IsLocalRing (R ⧸ I) := hlocal
    Formalization.Books.Algebra.Unit103.IsCohenMacaulay
      (R ⧸ I) (R ⧸ I)

private theorem localDepth_eq_of_linearEquiv
    {R M N : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) : localDepth R M = localDepth R N := by
  unfold localDepth
  have hmap :
      Submodule.map e.toLinearMap
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) =
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    simp
  have htop : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤ ↔
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have h' := congrArg (Submodule.map e.toLinearMap) h
      rw [hmap] at h'
      simpa using h'
    · intro h
      have h' : Submodule.map e.toLinearMap
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) =
            (⊤ : Submodule R N) := hmap.trans h
      simpa only [Submodule.map_eq_top_iff] using h'
  by_cases h : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤
  · have h' := htop.mp h
    simp only [depth, dif_pos h, dif_pos h']
  · have h' : IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) ≠ ⊤ := by
      intro hn
      exact h (htop.mpr hn)
    simp only [depth, dif_neg h, dif_neg h']
    congr 1
    ext n
    constructor
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, (e.isRegular_congr rs).mp hreg⟩
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, (e.isRegular_congr rs).mpr hreg⟩

private theorem isCohenMacaulay_of_linearEquiv
    {R M N : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N)
    (hM : Formalization.Books.Algebra.Unit103.IsCohenMacaulay R M) :
    Formalization.Books.Algebra.Unit103.IsCohenMacaulay R N := by
  unfold Formalization.Books.Algebra.Unit103.IsCohenMacaulay at hM ⊢
  calc
    ((localDepth R N : ℕ∞) : WithBot ℕ∞) =
        ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
          rw [localDepth_eq_of_linearEquiv e]
    _ = Module.supportDim R M := hM
    _ = Module.supportDim R N := Module.supportDim_eq_of_equiv e

private theorem isCohenMacaulay_of_module_eq
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] (P Q : Module R M) (hPQ : P = Q)
    (finiteP : @Module.Finite R M _ _ P)
    (finiteQ : @Module.Finite R M _ _ Q)
    (hP : @Formalization.Books.Algebra.Unit103.IsCohenMacaulay R M
      _ _ _ _ P finiteP) :
    @Formalization.Books.Algebra.Unit103.IsCohenMacaulay R M
      _ _ _ _ Q finiteQ := by
  cases hPQ
  exact hP

private theorem isCohenMacaulay_quotientByList
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Formalization.Books.Algebra.Unit103.IsCohenMacaulay R M) :
    ∀ xs : List R,
      RingTheory.Sequence.IsRegular M xs →
        (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) →
          Formalization.Books.Algebra.Unit103.IsCohenMacaulay R
            (Formalization.Books.Algebra.Unit103.quotientByList M xs) := by
  intro xs
  induction xs generalizing M with
  | nil =>
      intro _ _
      have hzero : Ideal.ofList ([] : List R) • (⊤ : Submodule R M) = ⊥ := by
        simp [Ideal.ofList]
      change Formalization.Books.Algebra.Unit103.IsCohenMacaulay R
        (M ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R M)))
      rw [hzero]
      exact isCohenMacaulay_of_linearEquiv
        (Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl).symm hM
  | cons x xs ih =>
      intro hreg hmem
      have hparts :=
        (RingTheory.Sequence.isRegular_cons_iff M x xs).mp hreg
      have hx : x ∈ IsLocalRing.maximalIdeal R := hmem x (by simp)
      have hQ : Formalization.Books.Algebra.Unit103.IsCohenMacaulay R
          (QuotSMulTop x M) :=
        (Formalization.Books.Algebra.Unit103.isCohenMacaulay_iff_of_isSMulRegular
          x hx hparts.1).mp hM
      have htailmem : ∀ r ∈ xs, r ∈ IsLocalRing.maximalIdeal R := by
        intro r hr
        exact hmem r (by simp [hr])
      have htail := ih (M := QuotSMulTop x M) hQ hparts.2 htailmem
      exact isCohenMacaulay_of_linearEquiv
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs).symm htail

private theorem isRegular_take
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    {xs : List R} (hreg : RingTheory.Sequence.IsRegular M xs) :
    ∀ n : ℕ, n ≤ xs.length →
      RingTheory.Sequence.IsRegular M (xs.take n) := by
  intro n hn
  refine { regular_mod_prev := ?_, top_ne_smul := ?_ }
  · intro i hi
    have hi_n : i < n := by
      simpa [List.length_take, hn] using hi
    have hi_xs : i < xs.length := lt_of_lt_of_le hi_n hn
    have htake : (xs.take n).take i = xs.take i := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hi_n)]
    rw [htake]
    rw [List.getElem_take]
    exact hreg.regular_mod_prev i hi_xs
  · intro heq
    apply hreg.top_ne_smul
    apply le_antisymm
    · calc
        (⊤ : Submodule R M) = Ideal.ofList (xs.take n) • ⊤ := heq
        _ ≤ Ideal.ofList xs • ⊤ := by
          apply Submodule.smul_mono_left
          apply Ideal.span_le.2
          intro r hr
          exact Ideal.subset_span (List.mem_of_mem_take hr)
    · simp

theorem regularSequence_extend_and_quotients_are_CohenMacaulay
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular R xs) :
    ∃ ys : List R,
      RingTheory.Sequence.IsRegular R (xs ++ ys) ∧
        (((xs ++ ys).length : ℕ∞) : WithBot ℕ∞) = ringKrullDim R ∧
          ∀ i : Fin xs.length,
            IsCohenMacaulayQuotientRing R
                (Ideal.ofList (xs.take (i.1 + 1))) ∧
              ringKrullDim
                  (R ⧸ (Ideal.ofList (xs.take (i.1 + 1)) : Ideal R)) +
                ((((i.1 + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) =
                ringKrullDim R := by
  obtain ⟨ys, hregall, hlen⟩ :=
    regular_sequence_extend_to_localDepth xs hreg
  have hdim : ((localDepth R R : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
    calc
      ((localDepth R R : ℕ∞) : WithBot ℕ∞) = Module.supportDim R R := hR
      _ = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
  have hlen' : (((xs ++ ys).length : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
    rw [← hlen]
    exact hdim
  refine ⟨ys, hregall, hlen', ?_⟩
  intro i
  let pref := xs.take (i.1 + 1)
  have hipref : i.1 + 1 ≤ xs.length := Nat.succ_le_of_lt i.isLt
  have hregpref : RingTheory.Sequence.IsRegular R pref := by
    exact isRegular_take hreg (i.1 + 1) hipref
  have hmempref : ∀ x ∈ pref, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    exact hxs x (List.mem_of_mem_take hx)
  have hCMpref := isCohenMacaulay_quotientByList hR pref hregpref hmempref
  have hsub :
      (Ideal.ofList pref : Ideal R) • (⊤ : Submodule R R) =
        (Ideal.ofList pref : Submodule R R) := by simp
  have hIne : (Ideal.ofList pref : Submodule R R) ≠ ⊤ := by
    intro htop
    apply hregpref.top_ne_smul
    calc
      (⊤ : Submodule R R) = Ideal.ofList pref := htop.symm
      _ = Ideal.ofList pref • (⊤ : Submodule R R) := hsub.symm
  let _ : Nontrivial (R ⧸ (Ideal.ofList pref : Ideal R)) :=
    Submodule.Quotient.nontrivial_iff.mpr hIne
  have hlocal : IsLocalRing (R ⧸ (Ideal.ofList pref : Ideal R)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.ofList pref))
      Ideal.Quotient.mk_surjective
  refine ⟨⟨hlocal, ?_⟩, ?_⟩
  · let : IsLocalRing (R ⧸ (Ideal.ofList pref : Ideal R)) := hlocal
    let moduleR : Module R (R ⧸ (Ideal.ofList pref : Ideal R)) := inferInstance
    have hmodule :
        Module.compHom (R ⧸ (Ideal.ofList pref : Ideal R))
            (Ideal.Quotient.mk (Ideal.ofList pref)) = moduleR := by
      apply Module.ext'
      intro r z
      induction z using Submodule.Quotient.induction_on with
      | _ z => rfl
    have hCMmodule :
        Formalization.Books.Algebra.Unit103.IsCohenMacaulay R
          (R ⧸ (Ideal.ofList pref : Ideal R)) := by
      exact isCohenMacaulay_of_linearEquiv
        (Submodule.quotEquivOfEq _ _ hsub) hCMpref
    have finiteComp :
        @Module.Finite R (R ⧸ (Ideal.ofList pref : Ideal R)) _ _
          (Module.compHom (R ⧸ (Ideal.ofList pref : Ideal R))
            (Ideal.Quotient.mk (Ideal.ofList pref))) := by
      exact Formalization.Books.Algebra.Unit103.moduleFinite_of_surjective_ringHom
        (Ideal.Quotient.mk (Ideal.ofList pref)) Ideal.Quotient.mk_surjective
    have hCMmoduleComp := isCohenMacaulay_of_module_eq moduleR
      (Module.compHom (R ⧸ (Ideal.ofList pref : Ideal R))
        (Ideal.Quotient.mk (Ideal.ofList pref))) hmodule.symm
      (inferInstance : @Module.Finite R (R ⧸ (Ideal.ofList pref : Ideal R)) _ _ moduleR)
      finiteComp hCMmodule
    apply (Formalization.Books.Algebra.Unit103.isCohenMacaulay_iff_of_surjective_localRingHom
      (Ideal.Quotient.mk (Ideal.ofList pref)) Ideal.Quotient.mk_surjective).2
    simpa only [pref] using hCMmoduleComp
  · simpa [pref] using
      (regularSequence_iff_expected_quotient_dimension R hR pref hmempref).mp hregpref

/-! ## Prime chains and localization -/

theorem maximalPrimeChain_length_eq_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R)
    (C : Formalization.Books.Algebra.Unit60.PrimeIdealChain R)
    (hC : Formalization.Books.Algebra.Unit103.IsMaximalPrimeChain C) :
    (((C.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := by
  exact Formalization.Books.Algebra.Unit103.maximalPrimeChain_length_eq_ringKrullDim
    (M := R) hR
    (by
      rw [Module.support_eq_zeroLocus, Module.annihilator_eq_bot.mpr inferInstance]
      simp)
    C hC

theorem dimension_eq_localization_add_quotient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (p : PrimeSpectrum R) :
    ringKrullDim R =
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        ringKrullDim (R ⧸ p.asIdeal) := by
  exact Formalization.Books.Algebra.Unit103.ringKrullDim_eq_localization_add_quotientDim
    (M := R) hR
    (by
      rw [Module.support_eq_zeroLocus, Module.annihilator_eq_bot.mpr inferInstance]
      simp)
    p

theorem isCohenMacaulayLocalRing_localization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (p : PrimeSpectrum R) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal) := by
  simpa [IsCohenMacaulayLocalRing] using
    Formalization.Books.Algebra.Unit103.isCohenMacaulay_localize (M := R) hR p

/- The global definition is the source's condition on all local rings. -/
def IsCohenMacaulayRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal)

theorem isCohenMacaulayRing_mPolynomial
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayRing R) (n : ℕ) :
    IsCohenMacaulayRing (MvPolynomial (Fin n) R) := by
  sorry

/-! ## Dimension shift and maximal Cohen-Macaulay resolutions -/

theorem dimension_shift_in_exact_sequence
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K M : Type u) [AddCommGroup K] [Module R K] [Module.Finite R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : IsCohenMacaulayLocalRing R) (d n : ℕ)
    (hdim : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)))
    (f : K →ₗ[R] (Fin n → R))
    (g : (Fin n → R) →ₗ[R] M)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Subsingleton M ∨
      (((localDepth R K : ℕ∞) : WithBot ℕ∞) >
          ((localDepth R M : ℕ∞) : WithBot ℕ∞)) ∨
        ((((localDepth R K : ℕ∞) : WithBot ℕ∞) =
            ((localDepth R M : ℕ∞) : WithBot ℕ∞)) ∧
          ((localDepth R M : ℕ∞) : WithBot ℕ∞) =
            (((d : ℕ∞) : WithBot ℕ∞))) := by
  sorry

/- A source-facing predicate for a finite initial segment of a finite-free
   resolution whose last displayed kernel is maximal Cohen-Macaulay. -/
def HasMCMFiniteFreeResolutionPrefix
    (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ) : Prop :=
  ∃ F : Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M),
    (∀ i : Fin n,
        Module.Free R (F.complex.X i) ∧
          Module.Finite R (F.complex.X i)) ∧
      ∃ hK : Module.Finite R (F.complex.X n),
        letI : Module.Finite R (F.complex.X n) := hK
        Formalization.Books.Algebra.Unit103.IsMaximalCohenMacaulay
            R (F.complex.X n) ∧
          (n = 0 → Function.Bijective F.augmentation.hom) ∧
            (0 < n → Function.Injective (F.complex.d n (n - 1)).hom)

theorem exists_mcm_finite_free_resolution_prefix
    (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : IsCohenMacaulayLocalRing R) (d e : ℕ)
    (hdim : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)))
    (hdepth : localDepth R M = (e : ℕ∞)) :
    ∃ n : ℕ, n + e = d ∧ HasMCMFiniteFreeResolutionPrefix R M n := by
  sorry

/-! ## Regular sequences from a local map -/

theorem exists_regularSequence_of_localRingHom
    (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (hB : IsCohenMacaulayLocalRing B)
    (hmax : IsLocalRing.maximalIdeal B =
      Ideal.radical (Ideal.map φ (IsLocalRing.maximalIdeal A))) :
    ∃ xs : List A,
      (((xs.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim B ∧
        RingTheory.Sequence.IsRegular B (xs.map φ) := by
  sorry

end

end Formalization.Books.Algebra.Unit104
