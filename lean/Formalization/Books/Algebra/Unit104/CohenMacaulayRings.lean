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
open CategoryTheory
open scoped TensorProduct

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
  let P := MvPolynomial (Fin n) R
  have hmodule :
      Formalization.Books.Algebra.Unit103.IsCohenMacaulayModule R R := by
    intro p
    change Formalization.Books.Algebra.Unit103.IsCohenMacaulay
      (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal R)
    change Formalization.Books.Algebra.Unit103.IsCohenMacaulay
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)
    exact hR p
  have hpoly :=
    Formalization.Books.Algebra.Unit103.isCohenMacaulayModule_polynomialModuleExtension
      (R := R) (M := R) hmodule n
  intro q
  let e : (P ⊗[R] R) ≃ₗ[P] P := TensorProduct.AlgebraTensorModule.rid R P P
  let e' :
      LocalizedModule q.asIdeal.primeCompl (P ⊗[R] R) ≃ₗ[Localization.AtPrime q.asIdeal]
        LocalizedModule q.asIdeal.primeCompl P :=
    LinearEquiv.ofBijective
      (LocalizedModule.map q.asIdeal.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective q.asIdeal.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective q.asIdeal.primeCompl e.toLinearMap e.surjective⟩
  exact isCohenMacaulay_of_linearEquiv e' (hpoly q)

private theorem localDepth_fin_succ_ge
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (k : ℕ) :
    localDepth R (Fin k.succ → R) ≥ localDepth R R := by
  induction k with
  | zero =>
      exact le_of_eq (localDepth_eq_of_linearEquiv
        (LinearEquiv.piUnique R (fun _ : Fin 1 => R))).symm
  | succ k ih =>
      let e : (R × (Fin k.succ → R)) ≃ₗ[R] (Fin k.succ.succ → R) :=
        Fin.consLinearEquiv R (fun _ : Fin k.succ.succ => R)
      let f := e.toLinearMap.comp (LinearMap.inl R R (Fin k.succ → R))
      let g := (LinearMap.snd R R (Fin k.succ → R)).comp e.symm.toLinearMap
      have hf : Function.Injective f :=
        e.injective.comp LinearMap.inl_injective
      have hfg : Function.Exact f g :=
        (LinearEquiv.conj_exact_iff_exact
          (LinearMap.inl R R (Fin k.succ → R))
          (LinearMap.snd R R (Fin k.succ → R)) e).2 Function.Exact.inl_snd
      have hsnd : Function.Surjective
          (LinearMap.snd R R (Fin k.succ → R)) := LinearMap.snd_surjective
      have hg : Function.Surjective g :=
        hsnd.comp e.symm.surjective
      have hseq := localDepth_shortExact f g hf hfg hg
      simpa [ih] using hseq.1

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
  classical
  by_cases hMsub : Subsingleton M
  · exact Or.inl hMsub
  have hMnon : Nontrivial M := by
    by_contra h
    exact hMsub (not_nontrivial_iff_subsingleton.mp h)
  let : Nontrivial M := hMnon
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hsub : Subsingleton M := by
      have hzero : Subsingleton (Fin 0 → R) := by
        constructor
        intro x y
        funext i
        exact Fin.elim0 i
      constructor
      intro x y
      obtain ⟨x', rfl⟩ := hg x
      obtain ⟨y', rfl⟩ := hg y
      exact congrArg g (hzero.elim x' y')
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hMnon
  have hPnon : Nontrivial (Fin n → R) := Function.Surjective.nontrivial hg
  have hRnon : Nontrivial R := by
    by_contra h
    let : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    exact (not_nontrivial_iff_subsingleton.mpr
      (inferInstance : Subsingleton (Fin n → R))) hPnon
  let : Nontrivial R := hRnon
  have hRdepth : localDepth R R = (d : ℕ∞) := by
    apply WithBot.coe_injective
    calc
      ((localDepth R R : ℕ∞) : WithBot ℕ∞) =
          Module.supportDim R R := hR
      _ = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
      _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
  have hmaxM : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hMtop : localDepth R M < ⊤ :=
    depth_lt_top_of_noetherian (IsLocalRing.maximalIdeal R) M hmaxM
  have hMdepthle : localDepth R M ≤ (d : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    calc
      ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R M :=
        supportDim_ge_localDepth
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
      _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
  have hfree : localDepth R (Fin n → R) ≥ localDepth R R := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact localDepth_fin_succ_ge k
  have hPdepthle : localDepth R (Fin n → R) ≤ (d : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    calc
      ((localDepth R (Fin n → R) : ℕ∞) : WithBot ℕ∞) ≤
          Module.supportDim R (Fin n → R) := supportDim_ge_localDepth
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R (Fin n → R)
      _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
  have hPdepth : localDepth R (Fin n → R) = (d : ℕ∞) := by
    apply le_antisymm hPdepthle
    simpa [hRdepth] using hfree
  by_cases hKsub : Subsingleton K
  · let : Subsingleton K := hKsub
    have hKtop : localDepth R K = ⊤ :=
      depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal R) K
    refine Or.inr (Or.inl ?_)
    rw [hKtop]
    exact WithBot.coe_lt_coe.mpr hMtop
  have hKnon : Nontrivial K := by
    by_contra h
    exact hKsub (not_nontrivial_iff_subsingleton.mp h)
  let : Nontrivial K := hKnon
  have hseq := localDepth_shortExact f g hf hfg hg
  have hKineq : min (localDepth R (Fin n → R))
      (localDepth R M + 1) ≤ localDepth R K := hseq.2.2
  by_cases hgt : localDepth R M < localDepth R K
  · exact Or.inr (Or.inl (WithBot.coe_lt_coe.mpr hgt))
  have hKle : localDepth R K ≤ localDepth R M := le_of_not_gt hgt
  by_cases hbd : localDepth R M < (d : ℕ∞)
  · have hM1d : localDepth R M + 1 ≤ (d : ℕ∞) :=
      (ENat.add_one_le_iff hMtop.ne).mpr hbd
    have hM1P : localDepth R M + 1 ≤ localDepth R (Fin n → R) := by
      exact hM1d.trans (by simp [hPdepth])
    have hM1K : localDepth R M + 1 ≤ localDepth R K := by
      rw [min_eq_right hM1P] at hKineq
      exact hKineq
    have hMK : localDepth R M < localDepth R K :=
      (ENat.add_one_le_iff hMtop.ne).mp hM1K
    exact (not_lt_of_ge hKle hMK).elim
  have hdb : (d : ℕ∞) ≤ localDepth R M := le_of_not_gt hbd
  have hM_eq : localDepth R M = (d : ℕ∞) :=
    le_antisymm hMdepthle hdb
  have hK_eq : localDepth R K = (d : ℕ∞) := by
    apply le_antisymm
    · exact hKle.trans_eq hM_eq
    · rw [hPdepth, hM_eq, min_eq_left (by simp)] at hKineq
      exact hKineq
  exact Or.inr (Or.inr (by
    simp [hK_eq, hM_eq]))

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

private noncomputable def identityResolution
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M) := by
  let C : Formalization.Books.Algebra.Unit71.ModuleChainComplex R :=
    { X := fun i => if i = 0 then ModuleCat.of R M else
          ModuleCat.of R (Fin 0 → R)
      d := fun _ _ => 0
      shape := by intro i j hij; rfl
      d_comp_d' := by intro i j k hij hjk; simp }
  let a : C.X 0 ⟶ ModuleCat.of R M := CategoryTheory.eqToHom (by simp [C])
  have ha : CategoryTheory.CategoryStruct.comp (C.d 1 0) a = 0 := by simp [C, a]
  refine { complex := C, augmentation := a, augmentation_condition := ha, exact_zero := ?_, exact_succ := ?_, augmentation_epi := ?_ }
  · apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact (0 : (Fin 0 → R) →ₗ[R] M) LinearMap.id
    intro x
    constructor
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      exact ⟨0, by simp [hx0]⟩
    · rintro ⟨y, hy⟩
      have hy0 : y = 0 := Subsingleton.elim _ _
      rw [hy0] at hy
      simpa using hy.symm
  · intro n
    by_cases hn : n = 0
    · subst n
      dsimp [C]
      apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      change Function.Exact (0 : (Fin 0 → R) →ₗ[R] (Fin 0 → R))
        (0 : (Fin 0 → R) →ₗ[R] M)
      intro x
      constructor <;> intro hx
      · exact ⟨0, Subsingleton.elim _ _⟩
      · rfl
    · cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
        simp [C]
        apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        change Function.Exact (0 : (Fin 0 → R) →ₗ[R] (Fin 0 → R))
          (0 : (Fin 0 → R) →ₗ[R] (Fin 0 → R))
        intro x
        constructor <;> intro hx
        · exact ⟨0, Subsingleton.elim _ _⟩
        · exact Subsingleton.elim _ _
  · exact (ModuleCat.epi_iff_surjective a).mpr (by
      intro y
      exact ⟨y, by simp [a]⟩)

private theorem localDepth_finiteFree_eq
    {R P : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [Module.Free R P]
    [Module.Finite R P] [Nontrivial P] (d : ℕ)
    (hR : IsCohenMacaulayLocalRing R)
    (hdim : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞))) :
    localDepth R P = (d : ℕ∞) := by
  let ι := Module.Free.ChooseBasisIndex R P
  let _ : Fintype ι := Fintype.ofFinite ι
  let b₀ : Module.Basis ι R P := Module.Free.chooseBasis R P
  let b : Module.Basis (Fin (Fintype.card ι)) R P :=
    b₀.reindex (Fintype.equivFin ι)
  let e : (Fin (Fintype.card ι) → R) ≃ₗ[R] P := b.equivFun.symm
  have hPfun : Nontrivial (Fin (Fintype.card ι) → R) :=
    Function.Surjective.nontrivial e.surjective
  have hn : Fintype.card ι ≠ 0 := by
    intro hn
    have hsub : Subsingleton (Fin (Fintype.card ι) → R) := by
      rw [hn]
      infer_instance
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hPfun
  have hRdepth : localDepth R R = (d : ℕ∞) := by
    apply WithBot.coe_injective
    calc
      ((localDepth R R : ℕ∞) : WithBot ℕ∞) = Module.supportDim R R := hR
      _ = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
      _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
  have hfree : localDepth R (Fin (Fintype.card ι) → R) ≥ localDepth R R := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hk]
    exact localDepth_fin_succ_ge k
  have hPdepthle : localDepth R (Fin (Fintype.card ι) → R) ≤ (d : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    calc
      ((localDepth R (Fin (Fintype.card ι) → R) : ℕ∞) : WithBot ℕ∞) ≤
          Module.supportDim R (Fin (Fintype.card ι) → R) :=
        supportDim_ge_localDepth
      _ ≤ ringKrullDim R :=
        Module.supportDim_le_ringKrullDim R (Fin (Fintype.card ι) → R)
      _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
  have hPdepth : localDepth R (Fin (Fintype.card ι) → R) = (d : ℕ∞) := by
    apply le_antisymm hPdepthle
    simpa [hRdepth] using hfree
  calc
    localDepth R P = localDepth R (Fin (Fintype.card ι) → R) :=
      (localDepth_eq_of_linearEquiv e).symm
    _ = (d : ℕ∞) := hPdepth

private theorem localDepth_kernel_eq_succ_of_lt
    {R K P M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup K] [Module R K] [Module.Finite R K] [Nontrivial K]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Nontrivial P]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (f : K →ₗ[R] P) (g : P →ₗ[R] M)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (d e : ℕ)
    (hP : localDepth R P = (d : ℕ∞))
    (hM : localDepth R M = (e : ℕ∞))
    (hed : (e : ℕ∞) < (d : ℕ∞))
    (_hKtop : localDepth R K < ⊤) :
    localDepth R K = ((e + 1 : ℕ) : ℕ∞) := by
  have hseq := localDepth_shortExact f g hf hfg hg
  have hde : (e : ℕ∞) + 1 ≤ (d : ℕ∞) := by
    exact (ENat.add_one_le_iff (by simp)).mpr hed
  have hlow : (e : ℕ∞) + 1 ≤ localDepth R K := by
    rw [hP, hM, min_eq_right hde] at hseq
    exact hseq.2.2
  have hsub : localDepth R K - 1 ≤ (e : ℕ∞) := by
    by_contra h
    have hlt : (e : ℕ∞) < localDepth R K - 1 := lt_of_not_ge h
    have hltmin : (e : ℕ∞) < min (d : ℕ∞) (localDepth R K - 1) :=
      (lt_min_iff.mpr ⟨hed, hlt⟩)
    rw [hP, hM] at hseq
    exact (not_lt_of_ge hseq.2.1) hltmin
  have hKone : (1 : ℕ∞) ≤ localDepth R K := by
    exact le_trans (by simp) hlow
  have hupp : localDepth R K ≤ (e : ℕ∞) + 1 := by
    calc
      localDepth R K = (localDepth R K - 1) + 1 := by
        rw [tsub_add_cancel_of_le hKone]
      _ ≤ (e : ℕ∞) + 1 := by
        simpa [add_comm] using add_le_add_right hsub 1
  exact le_antisymm hupp hlow

private noncomputable def prependResolution
    {R K P M : Type u} [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    (ι : ModuleCat.of R K ⟶ ModuleCat.of R P)
    (g : ModuleCat.of R P ⟶ ModuleCat.of R M)
    (hcomp : ι ≫ g = 0)
    (hS : (CategoryTheory.ShortComplex.mk ι g hcomp).ShortExact)
    (G : Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R K)) :
    Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M) := by
  let X : ℕ → ModuleCat R := fun i => match i with
    | 0 => ModuleCat.of R P
    | i + 1 => G.complex.X i
  let d : ∀ i j, X i ⟶ X j := fun i j => match i, j with
    | 0, 0 => 0
    | 0, j + 1 => 0
    | 1, 0 => G.augmentation ≫ ι
    | i + 2, 0 => 0
    | i + 1, j + 1 => G.complex.d i j
  let C : Formalization.Books.Algebra.Unit71.ModuleChainComplex R :=
    { X := X
      d := d
      shape := by
        intro i j hij
        cases i with
        | zero =>
          cases j <;> rfl
        | succ i =>
          cases j with
          | zero =>
            cases i with
            | zero => exact (hij rfl).elim
            | succ i => rfl
          | succ j =>
            cases i with
            | zero =>
              simp [d]
            | succ i =>
              change G.complex.d (i + 1) j = 0
              apply G.complex.shape
              intro h
              apply hij
              simp only [ComplexShape.down_Rel] at h ⊢
              omega
      d_comp_d' := by
        intro i j k hij hjk
        cases i <;> cases j <;> cases k <;>
          simp [d, G.complex.d_comp_d,
            Nat.add_assoc, ComplexShape.down_Rel] at *
        all_goals
          subst_vars
          simp
          simpa [Category.assoc] using
            congrArg (fun q => q ≫ ι) G.augmentation_condition }
  have hGepi : Function.Surjective G.augmentation.hom :=
    (ModuleCat.epi_iff_surjective G.augmentation).mp G.augmentation_epi
  have hSexact : Function.Exact ι.hom g.hom :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      hS.exact
  have hGexact : Function.Exact
      (G.complex.d 1 0).hom G.augmentation.hom :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      G.exact_zero
  have hCexact_zero :
      Function.Exact (C.d 1 0).hom g.hom := by
    apply LinearMap.exact_iff.mpr
    apply le_antisymm
    · intro x hx
      have hxι : x ∈ LinearMap.range ι.hom := by
        rw [← LinearMap.exact_iff.mp hSexact]
        exact hx
      obtain ⟨y, rfl⟩ := hxι
      obtain ⟨z, hz⟩ := hGepi y
      refine ⟨z, ?_⟩
      change ι.hom (G.augmentation.hom z) = ι.hom y
      exact congrArg (fun z => ι.hom z) hz
    · rw [LinearMap.range_le_ker_iff]
      ext x
      change g.hom (ι.hom (G.augmentation.hom x)) = 0
      simpa [Category.assoc] using
        congrArg (fun q => q.hom (G.augmentation.hom x)) hcomp
  have hCexact_succ : ∀ n : ℕ,
      Function.Exact (C.d (n + 2) (n + 1)).hom (C.d (n + 1) n).hom := by
    intro n
    cases n with
    | zero =>
        have hinj : Function.Injective ι.hom :=
          (ModuleCat.mono_iff_injective ι).mp hS.mono_f
        have h := (Function.Injective.comp_exact_iff_exact
          (f := (G.complex.d 1 0).hom) (g := G.augmentation.hom)
          (i := ι.hom) hinj).mpr hGexact
        change Function.Exact (G.complex.d 1 0).hom
          (ι.hom.comp G.augmentation.hom)
        exact h
    | succ n =>
        have h :=
          (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
            (G.exact_succ n)
        simpa [C, d, X] using h
  have hzero : C.d 1 0 ≫ g = 0 := by
    calc
      C.d 1 0 ≫ g = (G.augmentation ≫ ι) ≫ g := by simp [C, d]
      _ = G.augmentation ≫ (ι ≫ g) := by simp [Category.assoc]
      _ = 0 := by simp [hcomp]
  exact
    { complex := C
      augmentation := g
      augmentation_condition := hzero
      exact_zero :=
        (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
          hCexact_zero
      exact_succ := fun n =>
        (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
          (hCexact_succ n)
      augmentation_epi := hS.epi_g }

private noncomputable def tailResolution
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (F : Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M)) :
    Formalization.Books.Algebra.Unit71.Resolution R
      (CategoryTheory.Limits.kernel F.augmentation) := by
  let K := CategoryTheory.Limits.kernel F.augmentation
  let p : F.complex.X 1 ⟶ K :=
    CategoryTheory.Limits.kernel.lift F.augmentation (F.complex.d 1 0)
      F.augmentation_condition
  let C : Formalization.Books.Algebra.Unit71.ModuleChainComplex R :=
    { X := fun i => F.complex.X (i + 1)
      d := fun i j => F.complex.d (i + 1) (j + 1)
      shape := by
        intro i j hij
        apply F.complex.shape
        simp only [ComplexShape.down_Rel] at hij ⊢
        omega
      d_comp_d' := by
        intro i j k hij hjk
        apply F.complex.d_comp_d'
        · simp only [ComplexShape.down_Rel] at hij ⊢
          omega
        · simp only [ComplexShape.down_Rel] at hjk ⊢
          omega }
  have hpι : p ≫ CategoryTheory.Limits.kernel.ι F.augmentation =
      F.complex.d 1 0 := by
    exact CategoryTheory.Limits.kernel.lift_ι _ _ _
  have hpzero : F.complex.d 2 1 ≫ p = 0 := by
    apply (CategoryTheory.cancel_mono
      (CategoryTheory.Limits.kernel.ι F.augmentation)).1
    simp [hpι, F.complex.d_comp_d]
  have htail_exact : Function.Exact
      (F.complex.d 2 1).hom p.hom := by
    apply LinearMap.exact_iff.mpr
    apply le_antisymm
    · intro x hx
      have hx0 : p.hom x = 0 := (LinearMap.mem_ker).1 hx
      have hx' : (F.complex.d 1 0).hom x = 0 := by
        have h := congrArg (fun q => q.hom x) hpι
        simpa [hx0] using h.symm
      have hFexact : Function.Exact
          (F.complex.d 2 1).hom (F.complex.d 1 0).hom :=
        (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
          (F.exact_succ 0)
      have hxrange : x ∈ LinearMap.range (F.complex.d 2 1).hom := by
        rw [← (LinearMap.exact_iff.mp hFexact)]
        exact hx'
      exact hxrange
    · rw [LinearMap.range_le_ker_iff]
      ext y
      simpa using congrArg (fun q => q.hom y) hpzero
  have htail_zero : C.d 1 0 ≫ p = 0 := by
    exact hpzero
  have htail_exact_zero :
      (CategoryTheory.ShortComplex.mk (C.d 1 0) p htail_zero).Exact := by
    exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      htail_exact
  have htail_exact_succ : ∀ k : ℕ,
      (CategoryTheory.ShortComplex.mk (C.d (k + 2) (k + 1))
        (C.d (k + 1) k) (C.d_comp_d (k + 2) (k + 1) k)).Exact := by
    intro k
    simpa [C] using F.exact_succ (k + 1)
  have htail_epi : Epi p := by
    exact (CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift _).mp
      F.exact_zero
  exact
    { complex := C
      augmentation := p
      augmentation_condition := htail_zero
      exact_zero := htail_exact_zero
      exact_succ := htail_exact_succ
      augmentation_epi := htail_epi }

private theorem exists_mcm_finite_free_resolution_prefix_aux
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N]
    [Nontrivial (N : Type u)] (d k e : ℕ)
    (F : Formalization.Books.Algebra.Unit71.Resolution R N)
    (hterms : ∀ i,
      Module.Free R (F.complex.X i) ∧ Module.Finite R (F.complex.X i))
    (hR : IsCohenMacaulayLocalRing R)
    (hdim : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)))
    (hdepth : localDepth R (N : Type u) = (e : ℕ∞))
    (heq : k + e = d) :
    ∃ n : ℕ, n + e = d ∧
      Formalization.Books.Algebra.Unit104.HasMCMFiniteFreeResolutionPrefix R
        (N : Type u) n := by
  induction k generalizing e N with
  | zero =>
      have hed : e = d := by omega
      refine ⟨0, by omega, ?_⟩
      refine ⟨identityResolution R (N : Type u), ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · have hfinite0 : Module.Finite R
          ((identityResolution R (N : Type u)).complex.X 0 : Type u) := by
          change Module.Finite R (N : Type u)
          infer_instance
        refine ⟨hfinite0, ?_, ?_, ?_⟩
        · unfold Formalization.Books.Algebra.Unit103.IsMaximalCohenMacaulay
          change ((localDepth R (N : Type u) : ℕ∞) : WithBot ℕ∞) = ringKrullDim R
          rw [hdepth, hed, hdim]
        · intro _
          change Function.Bijective
            (LinearMap.id : (N : Type u) →ₗ[R] (N : Type u))
          constructor
          · intro x y hxy
            simpa using hxy
          · intro x
            exact ⟨x, rfl⟩
        · intro h
          omega
  | succ k ih =>
      let : Module.Finite R (F.complex.X 0 : Type u) := (hterms 0).2
      let : Module.Free R (F.complex.X 0 : Type u) := (hterms 0).1
      have hPnon : Nontrivial (F.complex.X 0 : Type u) := by
        exact Function.Surjective.nontrivial
          ((ModuleCat.epi_iff_surjective F.augmentation).mp F.augmentation_epi)
      let : Nontrivial (F.complex.X 0 : Type u) := hPnon
      let K := CategoryTheory.Limits.kernel F.augmentation
      let : IsNoetherian R (F.complex.X 0 : Type u) :=
        isNoetherian_of_isNoetherianRing_of_finite R _
      let : Module.Finite R (K : Type u) := by
        apply Module.Finite.of_injective (R := R) (S := R)
          (M := (K : Type u)) (N := (F.complex.X 0 : Type u))
          (CategoryTheory.Limits.kernel.ι F.augmentation).hom
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      have hKsub : ¬Nontrivial (K : Type u) → False := by
        intro hK
        let : Subsingleton (K : Type u) :=
          not_nontrivial_iff_subsingleton.mp hK
        have hKzero : CategoryTheory.Limits.IsZero K :=
          ModuleCat.isZero_iff_subsingleton.mpr inferInstance
        let : Mono F.augmentation :=
          CategoryTheory.Preadditive.mono_of_isZero_kernel F.augmentation hKzero
        let : Epi F.augmentation := F.augmentation_epi
        let : IsIso F.augmentation :=
          CategoryTheory.isIso_of_mono_of_epi F.augmentation
        let ePM : (F.complex.X 0 : Type u) ≃ₗ[R] (N : Type u) :=
          (CategoryTheory.asIso F.augmentation).toLinearEquiv
        have hPM : localDepth R (F.complex.X 0 : Type u) =
            localDepth R (N : Type u) :=
          localDepth_eq_of_linearEquiv ePM
        have hPdepth : localDepth R (F.complex.X 0 : Type u) = (d : ℕ∞) :=
          localDepth_finiteFree_eq d hR hdim
        have hde : (d : ℕ∞) = (e : ℕ∞) := by
          simpa [hPdepth, hdepth] using hPM
        have hedNat : e < d := by omega
        have hed : (e : ℕ∞) < (d : ℕ∞) := by exact_mod_cast hedNat
        exact (ne_of_gt hed) hde
      have hKnon : Nontrivial (K : Type u) := by
        by_contra hK
        exact hKsub hK
      let : Nontrivial (K : Type u) := hKnon
      let S := CategoryTheory.ShortComplex.mk
        (CategoryTheory.Limits.kernel.ι F.augmentation) F.augmentation
        (CategoryTheory.Limits.kernel.condition F.augmentation)
      let : Epi F.augmentation := F.augmentation_epi
      have hS : S.ShortExact := by
        dsimp [S]
        refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
        apply CategoryTheory.ShortComplex.exact_of_f_is_kernel
        exact CategoryTheory.Limits.kernelIsKernel F.augmentation
      have hPdepth : localDepth R (F.complex.X 0 : Type u) = (d : ℕ∞) :=
        localDepth_finiteFree_eq d hR hdim
      have hedNat : e < d := by omega
      have hed : (e : ℕ∞) < (d : ℕ∞) := by exact_mod_cast hedNat
      have hKmax : IsLocalRing.maximalIdeal R •
          (⊤ : Submodule R (K : Type u)) ≠ ⊤ :=
        smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R)
          (K : Type u) (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
      have hKtop : localDepth R (K : Type u) < ⊤ :=
        depth_lt_top_of_noetherian (IsLocalRing.maximalIdeal R) (K : Type u) hKmax
      have hKdepth : localDepth R (K : Type u) = ((e + 1 : ℕ) : ℕ∞) :=
        localDepth_kernel_eq_succ_of_lt
          (CategoryTheory.Limits.kernel.ι F.augmentation).hom
          F.augmentation.hom
          ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
          ((CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
            hS.exact)
          ((ModuleCat.epi_iff_surjective F.augmentation).mp F.augmentation_epi)
          d e hPdepth hdepth hed hKtop
      let G := tailResolution F
      have hGterms : ∀ i,
          Module.Free R (G.complex.X i) ∧ Module.Finite R (G.complex.X i) := by
        intro i
        change Module.Free R (F.complex.X (i + 1)) ∧
          Module.Finite R (F.complex.X (i + 1))
        exact hterms (i + 1)
      obtain ⟨n, hn, hprefix⟩ := ih (N := K) (e := e + 1)
        G hGterms hKdepth (by omega)
      rcases hprefix with ⟨G', hG'terms, ⟨hterm, hcm, hzero, hinj⟩⟩
      let : Module.Finite R (G'.complex.X n) := hterm
      let H := prependResolution
        (CategoryTheory.Limits.kernel.ι F.augmentation) F.augmentation
        (CategoryTheory.Limits.kernel.condition F.augmentation) hS G'
      refine ⟨n + 1, by omega, ⟨H, ?_, ?_⟩⟩
      · intro i
        rcases i with ⟨i, hi⟩
        by_cases hi0 : i = 0
        · subst i
          change Module.Free R (F.complex.X 0) ∧
            Module.Finite R (F.complex.X 0)
          exact hterms 0
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
          have hj : j < n := by omega
          change Module.Free R (G'.complex.X j) ∧
            Module.Finite R (G'.complex.X j)
          exact hG'terms ⟨j, hj⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · change Module.Finite R (G'.complex.X n)
          exact hterm
        · change Formalization.Books.Algebra.Unit103.IsMaximalCohenMacaulay
            R (G'.complex.X n)
          exact hcm
        · intro h
          omega
        · intro h
          cases n with
          | zero =>
              have hι : Function.Injective
                  (CategoryTheory.Limits.kernel.ι F.augmentation).hom :=
                (ModuleCat.mono_iff_injective _).mp hS.mono_f
              have hGinj := (hzero rfl).1
              have hcomp : Function.Injective
                  ((CategoryTheory.Limits.kernel.ι F.augmentation).hom.comp
                    G'.augmentation.hom) := hι.comp hGinj
              change Function.Injective
                ((CategoryTheory.Limits.kernel.ι F.augmentation).hom.comp
                  G'.augmentation.hom)
              exact hcomp
          | succ n =>
              change Function.Injective (G'.complex.d (n + 1) n).hom
              exact hinj (by omega)

theorem exists_mcm_finite_free_resolution_prefix
    (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : IsCohenMacaulayLocalRing R) (d e : ℕ)
    (hdim : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)))
    (hdepth : localDepth R M = (e : ℕ∞)) :
    ∃ n : ℕ, n + e = d ∧ HasMCMFiniteFreeResolutionPrefix R M n := by
  classical
  have hRnon : Nontrivial R := by
    by_contra h
    let : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    have hbot : ringKrullDim R = (⊥ : WithBot ℕ∞) :=
      ringKrullDim_eq_bot_of_subsingleton
    rw [hbot] at hdim
    simp at hdim
  let : Nontrivial R := hRnon
  have hMnon : Nontrivial M := by
    by_contra h
    let : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
    have htop : localDepth R M = ⊤ :=
      depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal R) M
    have : (e : ℕ∞) = ⊤ := by simpa [hdepth] using htop.symm
    simp at this
  let : Nontrivial M := hMnon
  have hdepthle : localDepth R M ≤ (d : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    calc
      ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R M :=
        supportDim_ge_localDepth
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
      _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
  have hed : e ≤ d := by
    have hcast : (e : ℕ∞) ≤ (d : ℕ∞) := by simpa [hdepth] using hdepthle
    exact_mod_cast hcast
  obtain ⟨F⟩ := Formalization.Books.Algebra.Unit71.exists_finite_free_resolution
    (ModuleCat.of R M)
  let G := F.resolution.resolution
  have hterms : ∀ i,
      Module.Free R (G.complex.X i) ∧ Module.Finite R (G.complex.X i) := by
    intro i
    exact ⟨F.resolution.free i, F.finite i⟩
  exact exists_mcm_finite_free_resolution_prefix_aux
    (N := ModuleCat.of R M) d (d - e) e G hterms hR hdim hdepth
      (Nat.sub_add_cancel hed)

/-! ## Regular sequences from a local map -/

private theorem exists_regular_image_of_no_associated_max
    {A B M : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (φ : A →+* B) [IsLocalHom φ]
    (hmax : IsLocalRing.maximalIdeal B =
      (Ideal.map φ (IsLocalRing.maximalIdeal A)).radical)
    (hnot : ∀ q : PrimeSpectrum B,
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes B M →
        ¬ IsLocalRing.maximalIdeal B ≤ q.asIdeal) :
    ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
      IsSMulRegular M (φ a) := by
  classical
  let s : Set (Ideal A) :=
    (fun q : PrimeSpectrum B => q.asIdeal.comap φ) ''
      Formalization.Books.Algebra.Unit63.associatedPrimes B M
  have hs : s.Finite := by
    exact (Formalization.Books.Algebra.Unit63.finite_ass (R := B) (M := M)).image _
  have hsp : ∀ J ∈ s, J ≠ (⊤ : Ideal A) → J ≠ (⊤ : Ideal A) → J.IsPrime := by
    rintro J ⟨q, hq, rfl⟩ _ _
    exact q.isPrime.comap φ
  have hnotall : ¬ (IsLocalRing.maximalIdeal A : Set A) ⊆
      ⋃ J ∈ s, (J : Set A) := by
    intro hsub
    obtain ⟨J, hJs, hAJ⟩ :=
      (Ideal.subset_union_prime_finite hs (⊤ : Ideal A) (⊤ : Ideal A) hsp).mp hsub
    obtain ⟨q, hq, hqJ⟩ := hJs
    have hmap : Ideal.map φ (IsLocalRing.maximalIdeal A) ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [hqJ] using hAJ
    have hrad : (Ideal.map φ (IsLocalRing.maximalIdeal A)).radical ≤ q.asIdeal :=
      (q.isPrime.radical_le_iff).2 hmap
    apply hnot q hq
    rw [hmax]
    exact hrad
  obtain ⟨a, ha, ha_not⟩ := Set.not_subset.mp hnotall
  refine ⟨a, ha, ?_⟩
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro m hma
  by_contra hm
  have hunion :
      (⋃ J ∈ s, (J : Set A)) =
        {x : A | ∃ z : M, z ≠ 0 ∧ φ x • z = 0} := by
    have hBunion :
        (⋃ J ∈ (fun q : PrimeSpectrum B => q.asIdeal) ''
            Formalization.Books.Algebra.Unit63.associatedPrimes B M,
            (J : Set B)) =
          {x : B | ∃ z : M, z ≠ 0 ∧ x • z = 0} := by
      rw [← Formalization.Books.Algebra.Unit63.iUnion_associatedPrimes_eq_module_zeroDivisors
        (R := B) (M := M)]
      ext x
      simp
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨J, hJs, hxJ⟩
      obtain ⟨q, hq, rfl⟩ := hJs
      have hxq : φ x ∈ q.asIdeal := hxJ
      have hxunion : φ x ∈
          ⋃ J ∈ (fun q : PrimeSpectrum B => q.asIdeal) ''
            Formalization.Books.Algebra.Unit63.associatedPrimes B M,
            (J : Set B) := by
        exact Set.mem_iUnion_of_mem q.asIdeal
          (Set.mem_iUnion_of_mem ⟨q, hq, rfl⟩ hxq)
      rw [hBunion] at hxunion
      exact hxunion
    · intro hx
      have hxunion : φ x ∈
          ⋃ J ∈ (fun q : PrimeSpectrum B => q.asIdeal) ''
            Formalization.Books.Algebra.Unit63.associatedPrimes B M,
            (J : Set B) := by
        rw [hBunion]
        exact hx
      obtain ⟨J, hxJ⟩ := Set.mem_iUnion.mp hxunion
      obtain ⟨hJs, hxq⟩ := Set.mem_iUnion.mp hxJ
      obtain ⟨q, hq, rfl⟩ := hJs
      exact ⟨q.asIdeal.comap φ, ⟨q, hq, rfl⟩, hxq⟩
  apply ha_not
  rw [hunion]
  exact ⟨m, hm, hma⟩

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
  classical
  have aux : ∀ c : ℕ, ∀ (M : Type u) [AddCommGroup M] [Module B M]
      [Module.Finite B M] [Nontrivial M],
      Formalization.Books.Algebra.Unit103.IsCohenMacaulay B M →
      Module.supportDim B M = (((c : ℕ∞) : WithBot ℕ∞)) →
      ∃ xs : List A,
        xs.length = c ∧ RingTheory.Sequence.IsRegular M (xs.map φ) := by
    intro c
    induction c with
    | zero =>
        intro M _ _ _ _ hM hdimM
        exact ⟨[], by simp, RingTheory.Sequence.IsRegular.nil B M⟩
    | succ c ih =>
        intro M _ _ _ _ hM hdimM
        have hMnon : Nontrivial M := inferInstance
        have hdepth : localDepth B M = (c.succ : ℕ∞) := by
          apply WithBot.coe_injective
          calc
            ((localDepth B M : ℕ∞) : WithBot ℕ∞) = Module.supportDim B M := hM
            _ = (((c.succ : ℕ∞) : WithBot ℕ∞)) := by simpa using hdimM
        have hreg_exists : ∃ x : B, x ∈ IsLocalRing.maximalIdeal B ∧
            IsSMulRegular M x := by
          by_contra h
          have hzero : localDepth B M = 0 := by
            change depth (IsLocalRing.maximalIdeal B) M = 0
            apply (depth_eq_zero_iff (IsLocalRing.maximalIdeal B) M).2
            refine ⟨hMnon, ?_⟩
            simpa [not_exists] using h
          simp [hdepth] at hzero
        have hnot : ∀ q : PrimeSpectrum B,
            q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes B M →
              ¬ IsLocalRing.maximalIdeal B ≤ q.asIdeal :=
          (Formalization.Books.Algebra.Unit63.ideal_contains_regular_iff
            (R := B) (M := M) (IsLocalRing.maximalIdeal B) le_rfl).mp hreg_exists
        obtain ⟨a, ha, hreg⟩ :=
          exists_regular_image_of_no_associated_max φ hmax hnot
        have haB : φ a ∈ IsLocalRing.maximalIdeal B :=
          (IsLocalRing.map_maximalIdeal_le φ) (Ideal.mem_map_of_mem φ ha)
        let Q := QuotSMulTop (φ a) M
        have hQnon : Nontrivial Q :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal M haB
        let : Nontrivial Q := hQnon
        have hQcm : Formalization.Books.Algebra.Unit103.IsCohenMacaulay B Q :=
          (Formalization.Books.Algebra.Unit103.isCohenMacaulay_iff_of_isSMulRegular
            (R := B) (M := M) (φ a) haB hreg).mp hM
        have hdrop : Module.supportDim B Q + 1 = Module.supportDim B M :=
          Module.supportDim_quotSMulTop_succ_eq_supportDim hreg haB
        have hQdim : Module.supportDim B Q =
            (((c : ℕ∞) : WithBot ℕ∞)) := by
          cases hq : Module.supportDim B Q with
          | bot =>
              exact ((Module.supportDim_ne_bot_iff_nontrivial B Q).mpr hQnon hq).elim
          | coe q =>
              have hqtop : q ≠ ⊤ := by
                intro htop
                have hEqTop := hdrop
                rw [hq, hdimM, htop] at hEqTop
                have htopEq : (⊤ : ℕ∞) = c := by
                  apply WithBot.coe_injective
                  simpa using hEqTop
                exact ENat.top_ne_natCast c htopEq
              have hEq : q + 1 = (c.succ : ℕ∞) := by
                have hEq' := hdrop
                rw [hq, hdimM] at hEq'
                apply WithBot.coe_injective
                simpa [Nat.succ_eq_add_one] using hEq'
              have hqeq : q = (c : ℕ∞) := by
                exact ENat.add_right_injective_of_ne_top (n := 1)
                  (by simp) (by simpa [add_comm] using hEq)
              simp [hqeq]
        obtain ⟨ys, hyslen, hysreg⟩ := ih Q hQcm hQdim
        refine ⟨a :: ys, ?_, ?_⟩
        · simp [hyslen]
        · simpa using RingTheory.Sequence.IsRegular.cons hreg hysreg
  have hmaxB : IsLocalRing.maximalIdeal B • (⊤ : Submodule B B) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal B) B
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal B))
  have hdepthtop : localDepth B B < ⊤ :=
    depth_lt_top_of_noetherian (IsLocalRing.maximalIdeal B) B hmaxB
  have hringtop : ringKrullDim B < ⊤ := by
    calc
      ringKrullDim B = Module.supportDim B B :=
        (Module.supportDim_self_eq_ringKrullDim B).symm
      _ = ((localDepth B B : ℕ∞) : WithBot ℕ∞) := hB.symm
      _ < ⊤ := WithBot.coe_lt_coe.mpr hdepthtop
  have hnonneg : (0 : WithBot ℕ∞) ≤ ringKrullDim B :=
    ringKrullDim_nonneg_of_nontrivial
  cases hd : ringKrullDim B with
  | bot =>
      exfalso
      rw [hd] at hnonneg
      simp at hnonneg
  | coe q =>
      have hqtop : q ≠ ⊤ := by
        intro hq
        rw [hd, hq] at hringtop
        simp at hringtop
      let d := q.toNat
      have hdim : ringKrullDim B =
          (((d : ℕ∞) : WithBot ℕ∞)) := by
        calc
          ringKrullDim B = ((q : ℕ∞) : WithBot ℕ∞) := hd
          _ = (((d : ℕ∞) : WithBot ℕ∞)) := by
            symm
            exact congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞))
              (ENat.natCast_toNat hqtop)
      have hdimB : Module.supportDim B B =
          (((d : ℕ∞) : WithBot ℕ∞)) := by
        rw [Module.supportDim_self_eq_ringKrullDim B, hdim]
      obtain ⟨xs, hxslen, hxsreg⟩ := aux d B hB hdimB
      refine ⟨xs, ?_, hxsreg⟩
      rw [hxslen]
      exact congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞))
        (ENat.natCast_toNat hqtop)

end

end Formalization.Books.Algebra.Unit104
