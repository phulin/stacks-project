import Formalization.Books.Algebra.Unit71.ExtGroups
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Commutative Algebra, Chapter 104: Cohen-Macaulay rings

The ring conditions in this chapter reuse Chapter 103's canonical
Cohen-Macaulay module predicates.  Prime chains, dimensions, regular
sequences, and free resolutions likewise use the interfaces established in
the preceding chapters.
-/

namespace Formalization.Books.Algebra.Unit104

open Formalization.Books.Algebra.Unit72
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u

noncomputable section

/-! ## Local and global Cohen-Macaulay rings -/

/- A local Cohen-Macaulay ring is the regular module viewed through the
   canonical module predicate from Chapter 103. -/
def IsCohenMacaulayLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  Formalization.Books.Algebra.Unit103.IsCohenMacaulay R R

/-! The source's equivalent existence criterion for a maximal regular
sequence is recorded before the later regular-sequence characterization. -/
theorem isCohenMacaulayLocalRing_iff_exists_regularSequence
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsCohenMacaulayLocalRing R ↔
    ∃ xs : List R,
        (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
          RingTheory.Sequence.IsRegular R xs ∧
            ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) = 0 := by
  constructor
  · intro hCM
    obtain ⟨ys, hreg, hlen⟩ :=
      regular_sequence_extend_to_localDepth (R := R) (M := R) []
        (@RingTheory.Sequence.IsRegular.nil R R _ _ _ inferInstance)
    have hlen' : localDepth R R = (ys.length : ℕ∞) := by
      simpa using hlen
    have hdimlen :
        (((ys.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := by
      calc
        (((ys.length : ℕ∞) : WithBot ℕ∞)) =
            (((localDepth R R : ℕ∞) : WithBot ℕ∞)) := by rw [hlen']
        _ = Module.supportDim R R := by
          exact hCM
        _ = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
    have hmem : ∀ x ∈ ys, x ∈ IsLocalRing.maximalIdeal R := by
      intro x hx
      by_contra hxmax
      have hxunit : IsUnit x := IsLocalRing.notMem_maximalIdeal.mp hxmax
      have hxideal : x ∈ Ideal.ofList ys := by
        exact Ideal.subset_span hx
      have htop : Ideal.ofList ys = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ hxideal hxunit
      have htop' : (⊤ : Submodule R R) =
          Ideal.ofList ys • (⊤ : Submodule R R) := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, htop]
      exact hreg.top_ne_smul htop'
    have hqeq :
        ringKrullDim (R ⧸ (Ideal.ofList ys : Ideal R)) +
            (((ys.length : ℕ∞) : WithBot ℕ∞)) =
          (((ys.length : ℕ∞) : WithBot ℕ∞)) := by
      calc
        ringKrullDim (R ⧸ (Ideal.ofList ys : Ideal R)) +
              (((ys.length : ℕ∞) : WithBot ℕ∞)) =
            ringKrullDim R :=
          ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ys
            (by simpa using hreg)
        _ = (((ys.length : ℕ∞) : WithBot ℕ∞)) := hdimlen.symm
    cases hqdim : ringKrullDim (R ⧸ (Ideal.ofList ys : Ideal R)) with
    | bot =>
        simp [hqdim] at hqeq
    | coe q =>
        have hqeq' : q + (ys.length : ℕ∞) = (ys.length : ℕ∞) := by
          apply WithBot.coe_injective
          simpa [hqdim] using hqeq
        have hq0 : q = 0 := by
          apply (WithTop.add_right_inj (by simp :
            (ys.length : ℕ∞) ≠ ⊤)).mp
          calc
            q + (ys.length : ℕ∞) = (ys.length : ℕ∞) := hqeq'
            _ = 0 + (ys.length : ℕ∞) := by simp
        have hq : ringKrullDim (R ⧸ (Ideal.ofList ys : Ideal R)) = 0 := by
          rw [hqdim, hq0]
          rfl
        exact ⟨ys, hmem, (by simpa using hreg), hq⟩
  · rintro ⟨xs, hxs, hreg, hq⟩
    have hdepth : (xs.length : ℕ∞) ≤ localDepth R R := by
      rw [localDepth, depth]
      split_ifs with htop
      · exact False.elim
          ((smul_top_ne_top_of_le_ring_jacobson
            (IsLocalRing.maximalIdeal R) R
            (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))) htop)
      · apply le_sSup
        exact ⟨xs, rfl, hxs, hreg⟩
    have hdimlen :
        (((xs.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := by
      simpa [hq] using
        (ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs hreg)
    have hlenbot :
        (((xs.length : ℕ∞) : WithBot ℕ∞)) ≤
          (((localDepth R R : ℕ∞) : WithBot ℕ∞)) := by
      exact_mod_cast hdepth
    have hdim_support :
        (((xs.length : ℕ∞) : WithBot ℕ∞)) = Module.supportDim R R := by
      calc
        (((xs.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := hdimlen
        _ = Module.supportDim R R :=
          (Module.supportDim_self_eq_ringKrullDim R).symm
    have hlocal :
        (((localDepth R R : ℕ∞) : WithBot ℕ∞)) =
          Module.supportDim R R := by
      apply le_antisymm (supportDim_ge_localDepth (R := R) (M := R))
      calc
        Module.supportDim R R = (((xs.length : ℕ∞) : WithBot ℕ∞)) :=
          hdim_support.symm
        _ ≤ (((localDepth R R : ℕ∞) : WithBot ℕ∞)) := hlenbot
    exact hlocal

/- The two assertions in the source's reformulation lemma are separated into
   a dimension characterization and the extension/quotient package. -/
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
  · intro hdim
    let d : ℕ := (LTSeries.longestOf (PrimeSpectrum R)).length
    have hd : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)) := by
      change Order.krullDim (PrimeSpectrum R) = _
      rw [Order.krullDim_eq_length_of_finiteDimensionalOrder]
      simp [d]
    have hqbot :
        ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) ≠ ⊥ := by
      intro hbot
      rw [hbot, hd] at hdim
      simp at hdim
    have hqnonneg :
        (0 : WithBot ℕ∞) ≤
          ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) := by
      cases hq : ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) with
      | bot =>
          exact False.elim (hqbot hq)
      | coe q =>
          exact WithBot.coe_le_coe.mpr (by simp)
    have hc_cast :
        (((xs.length : ℕ∞) : WithBot ℕ∞)) ≤
          (((d : ℕ∞) : WithBot ℕ∞)) := by
      calc
        (((xs.length : ℕ∞) : ℕ∞) : WithBot ℕ∞)
            = 0 + (((xs.length : ℕ∞) : WithBot ℕ∞)) := by simp
        _ ≤ ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) +
              (((xs.length : ℕ∞) : WithBot ℕ∞)) := by
          simpa [add_comm] using
            (add_le_add_right hqnonneg
              (((xs.length : ℕ∞) : WithBot ℕ∞)))
        _ = (((d : ℕ∞) : WithBot ℕ∞)) := by
          simpa [hd] using hdim
    have hc : xs.length ≤ d := by
      exact_mod_cast hc_cast
    let g : Fin xs.length → R := fun i => xs.get i
    have hlist : List.ofFn g = xs := by
      simpa only [g] using (List.ofFn_get xs)
    have hg : ∀ i, g i ∈ IsLocalRing.maximalIdeal R := by
      intro i
      simpa only [g] using hxs _ (List.get_mem xs i)
    have hMdim : Module.supportDim R R = (((d : ℕ∞) : WithBot ℕ∞)) := by
      rw [Module.supportDim_self_eq_ringKrullDim R, hd]
    cases hq : ringKrullDim (R ⧸ (Ideal.ofList xs : Ideal R)) with
    | bot =>
        exact False.elim (hqbot hq)
    | coe q =>
        have hqtop : q ≠ ⊤ := by
          intro htop
          rw [hq, hd] at hdim
          rw [htop] at hdim
          have hdim' :
              (⊤ : ℕ∞) + (xs.length : ℕ∞) = (d : ℕ∞) := by
            exact WithBot.coe_injective hdim
          have htopd : (⊤ : ℕ∞) = (d : ℕ∞) := by
            simpa only [top_add] using hdim'
          exact (WithTop.coe_ne_top : (d : ℕ∞) ≠ ⊤) htopd.symm
        let qn : ℕ := ENat.lift q
          (WithTop.lt_top_iff_ne_top.mpr hqtop)
        have hqcast : (qn : ℕ∞) = q := by
          exact ENat.natCast_lift q
            (WithTop.lt_top_iff_ne_top.mpr hqtop)
        have hqnat : qn + xs.length = d := by
          rw [hq, hd] at hdim
          rw [← hqcast] at hdim
          exact_mod_cast hdim
        have hqnat_sub : qn = d - xs.length := by
          exact Nat.eq_sub_of_add_eq hqnat
        have hsub :
            Ideal.ofList xs • (⊤ : Submodule R R) =
              (Ideal.ofList xs : Submodule R R) := by
          rw [Ideal.smul_eq_mul, Ideal.mul_top]
        have hquot : Module.supportDim R
            (Formalization.Books.Algebra.Unit103.quotientByList R
              (List.ofFn g)) =
              (((d - xs.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
          rw [hlist]
          change Module.supportDim R
            (R ⧸ (Ideal.ofList xs • (⊤ : Submodule R R))) = _
          rw [hsub, Module.supportDim_quotient_eq_ringKrullDim, hq]
          rw [← hqcast, hqnat_sub]
        have hres :=
          Formalization.Books.Algebra.Unit103.regularSequence_of_supportDim_quotient_eq
            d xs.length hR g hc hMdim hg hquot
        simpa only [hlist] using hres.1

/- Quotients by ideals in a local ring are again local, but Mathlib does not
   install that fact as an unconditional typeclass for an arbitrary ideal.
   This small wrapper exposes exactly the local Cohen-Macaulay assertion needed
   for the successive quotients below. -/
def IsCohenMacaulayQuotientRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) : Prop :=
  ∃ hlocal : IsLocalRing (R ⧸ I),
    letI : IsLocalRing (R ⧸ I) := hlocal
    Formalization.Books.Algebra.Unit103.IsCohenMacaulay
      (R ⧸ I) (R ⧸ I)

private theorem isCohenMacaulay_linearEquiv
    {R M N : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    Formalization.Books.Algebra.Unit103.IsCohenMacaulay R M ↔
      Formalization.Books.Algebra.Unit103.IsCohenMacaulay R N := by
  have hdepth : localDepth R M = localDepth R N := by
    unfold localDepth
    rw [depth_eq_sSup_weaklyRegular, depth_eq_sSup_weaklyRegular]
    congr 1
    ext n
    constructor
    · rintro ⟨rs, rfl, hmem, hreg⟩
      refine ⟨rs, rfl, hmem, ?_⟩
      exact (e.toAddEquiv.isWeaklyRegular_congr
        (List.forall₂_same.mpr fun r _ x => e.map_smul r x)).mp hreg
    · rintro ⟨rs, rfl, hmem, hreg⟩
      refine ⟨rs, rfl, hmem, ?_⟩
      exact (e.symm.toAddEquiv.isWeaklyRegular_congr
        (List.forall₂_same.mpr fun r _ x => e.symm.map_smul r x)).mp hreg
  unfold Formalization.Books.Algebra.Unit103.IsCohenMacaulay
  rw [hdepth, Module.supportDim_eq_of_equiv e]

private theorem isCohenMacaulay_quotientByList
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Formalization.Books.Algebra.Unit103.IsCohenMacaulay R M)
    (xs : List R) (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M xs) :
    Formalization.Books.Algebra.Unit103.IsCohenMacaulay R
      (M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M))) := by
  induction xs generalizing M with
  | nil =>
      apply (isCohenMacaulay_linearEquiv
        (Submodule.quotEquivOfEqBot
          (Ideal.ofList ([] : List R) • (⊤ : Submodule R M)) (by simp))).mpr
      exact hM
  | cons r rs ih =>
      obtain ⟨hr, hrest⟩ :=
        (RingTheory.Sequence.isRegular_cons_iff M r rs).mp hreg
      have hM' :=
        (Formalization.Books.Algebra.Unit103.isCohenMacaulay_iff_of_isSMulRegular
          r (hxs r (by simp)) hr).mp hM
      have htail := ih (M := QuotSMulTop r M) hM'
        (fun x hx => hxs x (by simp [hx])) hrest
      apply (isCohenMacaulay_linearEquiv
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs)).mpr
      exact htail

private theorem isRegular_prefix
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    ∀ (xs ys : List R), RingTheory.Sequence.IsRegular M (xs ++ ys) →
      RingTheory.Sequence.IsRegular M xs := by
  intro xs
  induction xs generalizing M with
  | nil =>
      intro ys hreg
      exact @RingTheory.Sequence.IsRegular.nil R M _ _ _ hreg.nontrivial
  | cons x xs ih =>
      intro ys hreg
      obtain ⟨hx, hrest⟩ :=
        (RingTheory.Sequence.isRegular_cons_iff M x (xs ++ ys)).mp hreg
      exact (RingTheory.Sequence.isRegular_cons_iff M x xs).mpr
        ⟨hx, ih (M := QuotSMulTop x M) ys hrest⟩

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
  have hlen' : localDepth R R = ((xs ++ ys).length : ℕ∞) := by
    simpa using hlen
  have hdimlen :
      (((xs ++ ys).length : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
    calc
      (((xs ++ ys).length : ℕ∞) : WithBot ℕ∞) =
          (((localDepth R R : ℕ∞) : WithBot ℕ∞)) := by rw [hlen']
      _ = Module.supportDim R R := by exact hR
      _ = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
  refine ⟨ys, hregall, hdimlen, ?_⟩
  intro i
  let k : ℕ := i.1 + 1
  have hk : k ≤ xs.length := by
    dsimp [k]
    exact Nat.succ_le_iff.mpr i.isLt
  have hfull : xs.take k ++ (xs.drop k ++ ys) = xs ++ ys := by
    rw [← List.append_assoc, List.take_append_drop]
  have hpreg : RingTheory.Sequence.IsRegular R (xs.take k) := by
    exact isRegular_prefix (xs.take k) (xs.drop k ++ ys) (hfull ▸ hregall)
  have hlen_take : (xs.take k).length = k := List.length_take_of_le hk
  have hdim :
      ringKrullDim (R ⧸ (Ideal.ofList (xs.take k) : Ideal R)) +
          (((k : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := by
    simpa [hlen_take] using
      (ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
        (xs.take k) hpreg)
  have hcm : IsCohenMacaulayQuotientRing R (Ideal.ofList (xs.take k)) := by
    let I : Ideal R := Ideal.ofList (xs.take k)
    have hI_le : I ≤ IsLocalRing.maximalIdeal R := by
      exact Ideal.span_le.2 (fun x hx =>
        hxs x (List.mem_of_mem_take hx))
    have hI_ne_top : I ≠ ⊤ := by
      intro hI
      apply (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      exact le_antisymm le_top (hI ▸ hI_le)
    have hnontrivial : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
    let hlocal : IsLocalRing (R ⧸ I) :=
      letI : Nontrivial (R ⧸ I) := hnontrivial
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    refine ⟨hlocal, ?_⟩
    have hCMmod := isCohenMacaulay_quotientByList hR (xs.take k)
      (fun x hx => hxs x (List.mem_of_mem_take hx)) hpreg
    have hsub : I • (⊤ : Submodule R R) = (I : Submodule R R) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [hsub] at hCMmod
    exact
      letI : IsLocalRing (R ⧸ I) := hlocal
      let hiff :=
        Formalization.Books.Algebra.Unit103.isCohenMacaulay_iff_of_surjective_localRingHom
          (R := R) (S := R ⧸ I) (N := R ⧸ I)
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      hiff.2 hCMmod
  refine ⟨?_, ?_⟩
  · simpa [k, hlen_take] using hcm
  · simpa [k, hlen_take] using hdim

/- A maximal prime chain is the canonical `LTSeries` chain from Chapter 60;
   `IsMaximalPrimeChain` is the endpoint/intermediate-prime predicate from
   Chapter 103. -/
theorem maximalPrimeChain_length_eq_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R)
    (C : Formalization.Books.Algebra.Unit60.PrimeIdealChain R)
    (hC : Formalization.Books.Algebra.Unit103.IsMaximalPrimeChain C) :
    (((C.length : ℕ∞) : WithBot ℕ∞)) = ringKrullDim R := by
  apply Formalization.Books.Algebra.Unit103.maximalPrimeChain_length_eq_ringKrullDim
    (M := R) (hM := hR) ?_ C hC
  ext p
  rw [Module.mem_support_iff]
  constructor
  · intro _
    trivial
  · intro _
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    rcases (LocalizedModule.subsingleton_iff.mp hs) (1 : R) with ⟨s, hs, hzero⟩
    have hz : s = 0 := by
      simp only [smul_eq_mul, mul_one] at hzero
      exact hzero
    apply hs
    rw [hz]
    exact Ideal.zero_mem _

theorem dimension_eq_localization_add_quotient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (p : PrimeSpectrum R) :
    ringKrullDim R =
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        ringKrullDim (R ⧸ p.asIdeal) := by
  apply Formalization.Books.Algebra.Unit103.ringKrullDim_eq_localization_add_quotientDim
    (M := R) hR ?_ p
  ext q
  rw [Module.mem_support_iff]
  constructor
  · intro _
    trivial
  · intro _
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    rcases (LocalizedModule.subsingleton_iff.mp hs) (1 : R) with ⟨s, hs, hzero⟩
    have hz : s = 0 := by
      simp only [smul_eq_mul, mul_one] at hzero
      exact hzero
    apply hs
    rw [hz]
    exact Ideal.zero_mem _

theorem isCohenMacaulayLocalRing_localization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (p : PrimeSpectrum R) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal) := by
  exact Formalization.Books.Algebra.Unit103.isCohenMacaulay_localize hR p

/- A global Cohen-Macaulay ring is one whose local rings at all primes are
   Cohen-Macaulay. -/
def IsCohenMacaulayRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal)

theorem isCohenMacaulayRing_mPolynomial
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayRing R) (n : ℕ) :
    IsCohenMacaulayRing (MvPolynomial (Fin n) R) := by
  unfold IsCohenMacaulayRing
  intro q
  have hpoly :=
    Formalization.Books.Algebra.Unit103.isCohenMacaulayModule_polynomialModuleExtension
      (R := R) (M := R) hR n q
  let e₀ :
      (MvPolynomial (Fin n) R ⊗[R] R) ≃ₗ[MvPolynomial (Fin n) R]
        MvPolynomial (Fin n) R :=
    TensorProduct.AlgebraTensorModule.rid R (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin n) R)
  let e₁ :
      LocalizedModule.AtPrime q.asIdeal
          (MvPolynomial (Fin n) R ⊗[R] R) ≃ₗ[MvPolynomial (Fin n) R]
        LocalizedModule.AtPrime q.asIdeal (MvPolynomial (Fin n) R) :=
    LinearEquiv.ofBijective
      (IsLocalizedModule.map q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl
          (MvPolynomial (Fin n) R ⊗[R] R))
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl
          (MvPolynomial (Fin n) R)) e₀.toLinearMap)
      ⟨IsLocalizedModule.map_injective q.asIdeal.primeCompl
          (f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl
            (MvPolynomial (Fin n) R ⊗[R] R))
          (g := LocalizedModule.mkLinearMap q.asIdeal.primeCompl
            (MvPolynomial (Fin n) R)) e₀.toLinearMap e₀.injective,
        IsLocalizedModule.map_surjective q.asIdeal.primeCompl
          (f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl
            (MvPolynomial (Fin n) R ⊗[R] R))
          (g := LocalizedModule.mkLinearMap q.asIdeal.primeCompl
            (MvPolynomial (Fin n) R)) e₀.toLinearMap e₀.surjective⟩
  let e₂ :
      LocalizedModule.AtPrime q.asIdeal
          (MvPolynomial (Fin n) R ⊗[R] R) ≃ₗ[Localization.AtPrime q.asIdeal]
        LocalizedModule.AtPrime q.asIdeal (MvPolynomial (Fin n) R) :=
    e₁.extendScalarsOfIsLocalization q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal)
  exact (isCohenMacaulay_linearEquiv e₂).mp hpoly

private theorem localDepth_eq_of_linearEquiv
    {R M N : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    localDepth R M = localDepth R N := by
  unfold localDepth
  rw [depth_eq_sSup_weaklyRegular, depth_eq_sSup_weaklyRegular]
  congr 1
  ext n
  constructor
  · rintro ⟨rs, rfl, hmem, hreg⟩
    refine ⟨rs, rfl, hmem, ?_⟩
    exact (e.toAddEquiv.isWeaklyRegular_congr
      (List.forall₂_same.mpr fun r _ x => e.map_smul r x)).mp hreg
  · rintro ⟨rs, rfl, hmem, hreg⟩
    refine ⟨rs, rfl, hmem, ?_⟩
    exact (e.symm.toAddEquiv.isWeaklyRegular_congr
      (List.forall₂_same.mpr fun r _ x => e.symm.map_smul r x)).mp hreg

/-! ## Dimension shift and MCM resolutions -/

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
  have hRdim :
      ((localDepth R R : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
    exact hR.trans (Module.supportDim_self_eq_ringKrullDim R)
  have hfree : ∀ k : ℕ, localDepth R (Fin k.succ → R) = localDepth R R := by
    intro k
    induction k with
    | zero =>
        exact localDepth_eq_of_linearEquiv
          (LinearEquiv.piUnique R (fun _ : Fin 1 => R))
    | succ k ih =>
        let e : (R × (Fin k.succ → R)) ≃ₗ[R] (Fin k.succ.succ → R) :=
          Fin.consLinearEquiv R (fun _ : Fin k.succ.succ => R)
        let f₀ := e.toLinearMap.comp (LinearMap.inl R R (Fin k.succ → R))
        let g₀ := (LinearMap.snd R R (Fin k.succ → R)).comp e.symm.toLinearMap
        have hf₀ : Function.Injective f₀ := by
          have hinj : Function.Injective
              (LinearMap.inl R R (Fin k.succ → R)) := LinearMap.inl_injective
          exact e.injective.comp hinj
        have hfg₀ : Function.Exact f₀ g₀ := by
          exact (LinearEquiv.conj_exact_iff_exact
            (LinearMap.inl R R (Fin k.succ → R))
            (LinearMap.snd R R (Fin k.succ → R)) e).2
            Function.Exact.inl_snd
        have hg₀ : Function.Surjective g₀ := by
          have hsurj : Function.Surjective
              (LinearMap.snd R R (Fin k.succ → R)) := LinearMap.snd_surjective
          exact hsurj.comp e.symm.surjective
        have hseq := localDepth_shortExact f₀ g₀ hf₀ hfg₀ hg₀
        have hge :
            localDepth R (Fin k.succ.succ → R) ≥ localDepth R R := by
          simpa [ih] using hseq.1
        have hle :
            ((localDepth R (Fin k.succ.succ → R) : ℕ∞) : WithBot ℕ∞) ≤
              ((localDepth R R : ℕ∞) : WithBot ℕ∞) := by
          calc
            ((localDepth R (Fin k.succ.succ → R) : ℕ∞) : WithBot ℕ∞) ≤
                Module.supportDim R (Fin k.succ.succ → R) :=
              supportDim_ge_localDepth
            _ ≤ ringKrullDim R :=
              Module.supportDim_le_ringKrullDim R (Fin k.succ.succ → R)
            _ = ((localDepth R R : ℕ∞) : WithBot ℕ∞) := hRdim.symm
        exact le_antisymm (WithBot.coe_le_coe.mp hle) hge
  by_cases hMsub : Subsingleton M
  · exact Or.inl hMsub
  · have hMnontr : Nontrivial M := not_subsingleton_iff_nontrivial.mp hMsub
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      have hFsub : Subsingleton (Fin n → R) := by
        rw [hn0]
        infer_instance
      apply hMsub
      constructor
      intro x y
      obtain ⟨x', hx'⟩ := hg x
      obtain ⟨y', hy'⟩ := hg y
      calc
        x = g x' := hx'.symm
        _ = g y' := congrArg g (hFsub.elim x' y')
        _ = y := hy'
    have hFnontr : Nontrivial (Fin n → R) := by
      apply not_subsingleton_iff_nontrivial.mp
      intro hsub
      have hzero := congrFun
        (hsub.elim (0 : Fin n → R) (fun _ => 1)) ⟨0, hn⟩
      exact zero_ne_one hzero
    have hn1 : 1 ≤ n := hn
    have hfree_n : localDepth R (Fin n → R) = localDepth R R := by
      have h := hfree (n - 1)
      change localDepth R (Fin (n - 1 + 1) → R) = localDepth R R at h
      rw [Nat.sub_add_cancel hn1] at h
      exact h
    have hfree_raw : localDepth R (Fin n → R) = (d : ℕ∞) := by
      apply WithBot.coe_injective
      calc
        ((localDepth R (Fin n → R) : ℕ∞) : WithBot ℕ∞) =
            ((localDepth R R : ℕ∞) : WithBot ℕ∞) := congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hfree_n
        _ = ringKrullDim R := hRdim
        _ = ((d : ℕ∞) : WithBot ℕ∞) := hdim
    have hMle_raw : localDepth R M ≤ (d : ℕ∞) := by
      apply WithBot.coe_le_coe.mp
      calc
        ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R M :=
          @supportDim_ge_localDepth R M _ _ _ _ _ _ hMnontr
        _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
        _ = ((d : ℕ∞) : WithBot ℕ∞) := hdim
    by_cases hKsub : Subsingleton K
    · have hKdepth : localDepth R K = ⊤ := by
        exact @depth_eq_top_of_subsingleton R _ (IsLocalRing.maximalIdeal R) K
          _ _ _ hKsub
      have hMdepth : localDepth R M < ⊤ := by
        apply @depth_lt_top_of_noetherian R _ (IsLocalRing.maximalIdeal R) M
          _ _ _ _ hMnontr
        exact @smul_top_ne_top_of_le_ring_jacobson R _
          (IsLocalRing.maximalIdeal R) M _ _ _ hMnontr
          (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
      exact Or.inr (Or.inl (by
        rw [hKdepth]
        exact WithBot.coe_lt_coe.mpr hMdepth))
    · have hKnontr : Nontrivial K := not_subsingleton_iff_nontrivial.mp hKsub
      have hseq := @localDepth_shortExact R K (Fin n → R) M
        _ _ _ _ _ _ hKnontr _ _ _ hFnontr _ _ _ hMnontr
        f g hf hfg hg
      rcases lt_or_ge (localDepth R M) (localDepth R K) with hMK | hKM
      · exact Or.inr (Or.inl (WithBot.coe_lt_coe.mpr hMK))
      · have hKM' : localDepth R K ≤ localDepth R M := hKM
        have hFM : localDepth R M ≤ localDepth R (Fin n → R) := by
          rw [hfree_raw]
          exact hMle_raw
        have hKF : localDepth R K ≤ localDepth R (Fin n → R) := by
          have := hseq.1
          simpa [min_eq_left hKM'] using this
        have hFK : localDepth R (Fin n → R) ≤ localDepth R K := by
          by_contra hFK'
          have hKF' : localDepth R K < localDepth R (Fin n → R) :=
            lt_of_not_ge hFK'
          have hFtop : localDepth R (Fin n → R) < ⊤ := by
            rw [hfree_raw]
            exact WithTop.coe_lt_top d
          have hMtop : localDepth R M < ⊤ := lt_of_le_of_lt hFM hFtop
          have hKM1 : localDepth R K < localDepth R M + 1 := by
            exact (ENat.lt_add_one_iff (n := localDepth R M)
              (m := localDepth R K) (ne_of_lt hMtop)).2 hKM'
          have hmin : localDepth R K <
              min (localDepth R (Fin n → R)) (localDepth R M + 1) :=
            lt_min hKF' hKM1
          exact (not_lt_of_ge hseq.2.2) hmin
        have hK_eq_F : localDepth R K = localDepth R (Fin n → R) :=
          le_antisymm hKF hFK
        have hF_eq_M : localDepth R (Fin n → R) = localDepth R M := by
          apply le_antisymm
          · simpa [hK_eq_F] using hKM'
          · exact hFM
        have hK_eq_M : localDepth R K = localDepth R M := hK_eq_F.trans hF_eq_M
        have hM_eq_d : localDepth R M = (d : ℕ∞) := hF_eq_M.symm.trans hfree_raw
        exact Or.inr (Or.inr ⟨
          congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hK_eq_M,
          congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hM_eq_d⟩)

/- A finite prefix of the canonical exact resolution of `M`.  The terms
   indexed below `n` are the finite free modules F_0,...,F_(n-1), while the
   term in degree n is the maximal Cohen-Macaulay left kernel K.  The
   resolution interface supplies exactness at all displayed free terms; the
   explicit injectivity condition supplies exactness at K. -/
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

private noncomputable def mcmPrefixComplex
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    (P : Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M))
    (n : ℕ) (hn : 0 < n) (K : ModuleCat R)
    (ι : K ⟶ P.complex.X (n - 1))
    (hι : ∀ j, (ComplexShape.down ℕ).Rel (n - 1) j →
      ι ≫ P.complex.d (n - 1) j = 0) :
    Formalization.Books.Algebra.Unit71.ModuleChainComplex R := by
  have hnsub : n - 1 < n := by omega
  let X : ℕ → ModuleCat R := fun i =>
    if i < n then P.complex.X i else if i = n then K else
      ModuleCat.of R (Fin 0 → R)
  let d : ∀ i j, X i ⟶ X j := fun i j => by
    by_cases hi : i = n
    · by_cases hj : j = n - 1
      · subst i
        subst j
        exact eqToHom (by simp [X, hn]) ≫ ι ≫
          eqToHom (by simp [X, hnsub])
      · exact 0
    · by_cases hil : i < n
      · by_cases hjlt : j < n
        · exact eqToHom (by simp [X, hi, hil]) ≫ P.complex.d i j ≫
            eqToHom (by simp [X, hjlt])
        · exact 0
      · exact 0
  exact HomologicalComplex.mk X d (by
    intro i j hrel
    by_cases hi : i = n
    · by_cases hj : j = n - 1
      · exfalso
        apply hrel
        simp only [ComplexShape.down_Rel]
        omega
      · simp [d, hi, hj]
    · by_cases hil : i < n
      · by_cases hjlt : j < n
        · simp [d, hi, hil, hjlt]
          rw [P.complex.shape i j]
          exact hrel
        · simp [d, hi, hil, hjlt]
      · simp [d, hi, hil]) (by
    intro i j k hij hjk
    have hij' : i = j + 1 := by
      have h := (by simpa only [ComplexShape.down_Rel] using hij)
      exact h.symm
    have hjk' : j = k + 1 := by
      have h := (by simpa only [ComplexShape.down_Rel] using hjk)
      exact h.symm
    by_cases hi : i = n
    · have hj : j = n - 1 := by omega
      have hjlt : j < n := by omega
      have hjk_n : k + 1 = n - 1 := by omega
      have hk1lt : k + 1 < n := by omega
      have hk1ne : k + 1 ≠ n := by omega
      have hik : k + 1 + 1 = n := by omega
      have hnsubadd : n - 1 + 1 = n := by omega
      have hjne : n - 1 ≠ n := by omega
      subst i
      subst j
      subst n
      have hklt0 : k < k + 1 + 1 := by omega
      have hι' : ι ≫ P.complex.d (k + 1) k = 0 := by
        simpa [Nat.add_sub_cancel, ComplexShape.down_Rel] using
          hι k (by simp [ComplexShape.down_Rel])
      simp [d, hklt0]
      rw [← Category.assoc, hι']
      simp
    · by_cases hj : j = n
      · have hnext : i = n + 1 := by omega
        have hil : ¬ i < n := by omega
        have hkn : k + 1 = n := by omega
        have hik : k + 1 + 1 = n + 1 := by omega
        simp [d, hij', hjk', hj, hnext, hi, hil, hkn, hik]
      · by_cases hk : k = n
        · have hjnext : j = n + 1 := by omega
          have hjlt : ¬ j < n := by omega
          have hnext : i = n + 2 := by omega
          have hkn : k + 1 = n + 1 := by omega
          have hjk_next : k + 1 + 1 = n + 2 := by omega
          simp [d, hij', hjk', hj, hk, hjnext, hnext, hjlt, hkn, hjk_next]
        · by_cases hil : i < n
          · have hjlt : j < n := by omega
            have hklt : k < n := by omega
            simp only [d, dif_pos hij', dif_neg hi, dif_pos hil,
              dif_pos hjk', dif_neg hj, dif_pos hjlt, dif_pos hklt, X]
            apply eq_of_heq
            simpa [Category.assoc] using
              (show P.complex.d i j ≫ P.complex.d j k =
                  (0 : P.complex.X i ⟶ P.complex.X k) from
                P.complex.d_comp_d i j k)
          · have hi_not : ¬ k + 1 + 1 = n := by omega
            have hi_lt : ¬ k + 1 + 1 < n := by omega
            have hj_not : ¬ k + 1 = n := by omega
            have hj_lt : ¬ k + 1 < n := by omega
            simp [d, hij', hjk', hi, hil, hi_not, hi_lt, hj_not, hj_lt])

private theorem exists_regularSequence_of_localRingHom_aux
    (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (hB : IsCohenMacaulayLocalRing B)
    (hmax : IsLocalRing.maximalIdeal B =
      Ideal.radical (Ideal.map φ (IsLocalRing.maximalIdeal A)))
    (d : ℕ) (hdim : ringKrullDim B = (((d : ℕ∞) : WithBot ℕ∞))) :
    ∃ xs : List A,
      xs.length = d ∧ RingTheory.Sequence.IsRegular B (xs.map φ) := by
  induction d generalizing A B with
  | zero =>
      refine ⟨[], by simp, ?_⟩
      exact RingTheory.Sequence.IsRegular.nil B B
  | succ d ih =>
      let mins : Set (Ideal B) := (Module.annihilator B B).minimalPrimes
      have hmins : mins.Finite := by
        exact Ideal.finite_minimalPrimes_of_isNoetherianRing B (Module.annihilator B B)
      have hnot : ¬ ((IsLocalRing.maximalIdeal A : Set A) ⊆
          ⋃ p ∈ mins, (p.comap φ : Set A)) := by
        intro hsub
        obtain ⟨p, hp, hle⟩ :=
          (Ideal.subset_union_prime_finite (f := fun p : Ideal B => p.comap φ)
            hmins (⊤ : Ideal B) (⊤ : Ideal B)
            (fun p hp _ _ => hp.isPrime.comap φ) (I := IsLocalRing.maximalIdeal A)).mp hsub
        have hmap : Ideal.map φ (IsLocalRing.maximalIdeal A) ≤ p :=
          (Ideal.map_le_iff_le_comap).2 hle
        have hrad : IsLocalRing.maximalIdeal B ≤ p := by
          rw [hmax]
          exact hp.isPrime.radical_le_iff.mpr hmap
        have hpeq : IsLocalRing.maximalIdeal B = p := by
          exact (IsLocalRing.maximalIdeal.isMaximal B).eq_of_le hp.isPrime.ne_top hrad
        have hp' : p ∈ _root_.associatedPrimes B B := by
          apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B
          simpa [mins] using hp
        have himage :=
          (Formalization.Books.Algebra.Unit63.associatedPrimes_toIdeal_eq_mathlib
            (R := B) (M := B)).symm ▸ hp'
        obtain ⟨q, hq, hqp⟩ := himage
        have hq' : q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes B B := hq
        have hdimq :=
          Formalization.Books.Algebra.Unit103.associatedPrime_is_minimal_support_of_isCohenMacaulay
            hB q hq'
        have hpmax : p.IsMaximal := hpeq ▸ (IsLocalRing.maximalIdeal.isMaximal B)
        have hzero : ringKrullDim (B ⧸ p) = 0 :=
          ringKrullDim_eq_zero_of_isField
            ((Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mp hpmax)
        have hzero' : ringKrullDim (B ⧸ q.asIdeal) = 0 := by
          have hqp' : q.asIdeal = p := hqp
          rw [hqp']
          exact hzero
        have hdimzero : Module.supportDim B B = 0 := hdimq.1.symm.trans hzero'
        have hdimB : Module.supportDim B B = ringKrullDim B :=
          Module.supportDim_self_eq_ringKrullDim B
        have hdimzero' : ringKrullDim B = 0 := hdimB.symm.trans hdimzero
        rw [hdim] at hdimzero'
        have hzeroE : (d : ℕ∞) + 1 = 0 := by
          apply WithBot.coe_injective
          simpa using hdimzero'
        have hpos : (0 : ℕ∞) < (d : ℕ∞) + 1 := by positivity
        rw [hzeroE] at hpos
        exact (lt_irrefl _ hpos).elim
      obtain ⟨a, ha, hamin⟩ := Set.not_subset.mp hnot
      let y : B := φ a
      have hy : y ∈ IsLocalRing.maximalIdeal B := by
        exact map_nonunit φ a ha
      have hynot : ∀ p ∈ mins, y ∉ p := by
        intro p hp hpy
        exact hamin (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, by simpa [y] using hpy⟩⟩)
      let g : Fin 1 → B := fun _ => y
      have hBdim : Module.supportDim B B =
          (((Nat.succ d : ℕ∞) : WithBot ℕ∞)) := by
        rw [Module.supportDim_self_eq_ringKrullDim B, hdim]
      have hquotdim : Module.supportDim B (QuotSMulTop y B) + 1 =
          (((Nat.succ d : ℕ∞) : WithBot ℕ∞)) := by
        simpa [hBdim] using
          (Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
            (R := B) (M := B) (x := y) (by simpa [mins] using hynot) hy)
      have hquot : Module.supportDim B
          (Formalization.Books.Algebra.Unit103.quotientByList B (List.ofFn g)) =
          (((d : ℕ∞) : WithBot ℕ∞)) := by
        have hq : Module.supportDim B (QuotSMulTop y B) =
            (((d : ℕ∞) : WithBot ℕ∞)) := by
          cases hX : Module.supportDim B (QuotSMulTop y B) with
          | bot =>
              have hbad : (⊥ : WithBot ℕ∞) =
                  (((d : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) := by
                simpa [hX] using hquotdim
              exact (WithBot.bot_ne_coe hbad).elim
          | coe X =>
              have hXeq : X + 1 = (d : ℕ∞) + 1 := by
                apply WithBot.coe_injective
                simpa [hX, Nat.cast_add] using hquotdim
              have hXd : X = (d : ℕ∞) :=
                (WithTop.add_right_inj (by simp : (1 : ℕ∞) ≠ ⊤)).mp hXeq
              simp [hXd]
        have hlist : List.ofFn g = [y] := by simp [g]
        rw [hlist]
        change Module.supportDim B
          (B ⧸ (Ideal.ofList [y] • (⊤ : Submodule B B))) = _
        rw [show Ideal.ofList [y] = Ideal.span ({y} : Set B) by simp,
          Submodule.ideal_span_singleton_smul]
        exact hq
      have hyreg : RingTheory.Sequence.IsRegular B [y] := by
        have hreg := Formalization.Books.Algebra.Unit103.regularSequence_of_supportDim_quotient_eq
          (Nat.succ d) 1 hB g (by simp) hBdim (by intro i; simpa [g] using hy)
            hquot
        simpa [g] using hreg.1
      let I : Ideal B := Ideal.span ({y} : Set B)
      have hI_le : I ≤ IsLocalRing.maximalIdeal B := by
        exact Ideal.span_le.2 (by simpa [I] using hy)
      have hI_ne_top : I ≠ ⊤ := by
        intro hI'
        exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top
          (top_unique (hI' ▸ hI_le))
      let B' : Type u := B ⧸ I
      let q : B →+* B' := Ideal.Quotient.mk I
      let φ' : A →+* B' := q.comp φ
      have hsub : Ideal.span ({y} : Set B) • (⊤ : Submodule B B) =
          (I : Submodule B B) := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      let hlocal : IsLocalRing B' :=
        letI : Nontrivial B' := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
        IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
      letI : IsLocalRing B' := hlocal
      letI : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
      letI : IsLocalHom φ' := RingHom.isLocalHom_comp q φ
      have hB' : IsCohenMacaulayLocalRing B' := by
        letI : IsLocalRing B' := hlocal
        have hCMmod :=
          (Formalization.Books.Algebra.Unit103.isCohenMacaulay_iff_of_isSMulRegular
            y hy ((RingTheory.Sequence.isRegular_cons_iff B y []).mp hyreg).1).mp hB
        have hCMmod' : Formalization.Books.Algebra.Unit103.IsCohenMacaulay B
            (B ⧸ (Ideal.span ({y} : Set B) • (⊤ : Submodule B B))) := by
          rw [Submodule.ideal_span_singleton_smul]
          exact hCMmod
        rw [hsub] at hCMmod'
        exact
          (Formalization.Books.Algebra.Unit103.isCohenMacaulay_iff_of_surjective_localRingHom
            (R := B) (S := B') (N := B') q Ideal.Quotient.mk_surjective).2 hCMmod'
      have hmax' : IsLocalRing.maximalIdeal B' =
          Ideal.radical (Ideal.map φ' (IsLocalRing.maximalIdeal A)) := by
        letI : IsLocalRing B' := hlocal
        apply le_antisymm
        · rw [← Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective
              (IsLocalRing.maximalIdeal B'),
            IsLocalRing.maximalIdeal_comap q]
          rw [hmax]
          calc
            Ideal.map q (Ideal.radical (Ideal.map φ (IsLocalRing.maximalIdeal A))) ≤
                Ideal.radical (Ideal.map q (Ideal.map φ (IsLocalRing.maximalIdeal A))) :=
              Ideal.map_radical_le q
            _ = Ideal.radical (Ideal.map φ' (IsLocalRing.maximalIdeal A)) := by
              simp [φ', Ideal.map_map]
        · have hradical : (IsLocalRing.maximalIdeal B' : Ideal B').IsRadical :=
            (IsLocalRing.maximalIdeal.isMaximal B').isPrime.isRadical
          apply hradical.radical_le_iff.mpr
          exact (Ideal.map_le_iff_le_comap).2 (by
            intro a ha
            exact map_nonunit φ' a ha)
      have hdim' : ringKrullDim B' = (((d : ℕ∞) : WithBot ℕ∞)) := by
        letI : IsLocalRing B' := hlocal
        have hdimq := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular [y] hyreg
        have hIeq : Ideal.ofList [y] = I := by simp [I]
        have hdimq' : ringKrullDim B' + 1 = ringKrullDim B := by
          change ringKrullDim (B ⧸ I) + 1 = ringKrullDim B
          rw [← hIeq]
          exact hdimq
        cases hX : ringKrullDim B' with
        | bot =>
            have hbad : (⊥ : WithBot ℕ∞) =
                (((Nat.succ d : ℕ∞) : WithBot ℕ∞)) := by
              simpa [hX] using hdimq'.trans hdim
            exact (WithBot.bot_ne_coe hbad).elim
        | coe X =>
            have hXeq : X + 1 = (d : ℕ∞) + 1 := by
              apply WithBot.coe_injective
              simpa [hX, Nat.cast_add] using hdimq'.trans hdim
            have hXd : X = (d : ℕ∞) :=
              (WithTop.add_right_inj (by simp : (1 : ℕ∞) ≠ ⊤)).mp hXeq
            simp [hXd]
      obtain ⟨xs, hxslen, hxsreg⟩ := ih A B' φ' hB' hmax' hdim'
      refine ⟨a :: xs, by simp [hxslen], ?_⟩
      let e : (QuotSMulTop y B) ≃ₐ[B] B' :=
        Ideal.quotientEquivAlgOfEq B (by
          rw [← Submodule.ideal_span_singleton_smul]
          exact hsub)
      have hfor : List.Forall₂
          (fun (r : B) (s : B') => ∀ x, e (r • x) = s • e x)
          (xs.map φ) (xs.map φ') := by
        clear hxslen hxsreg
        induction xs with
        | nil => exact List.Forall₂.nil
        | cons a xs ih =>
            refine List.Forall₂.cons ?_ ih
            intro x
            simpa [B', Algebra.smul_def, Ideal.Quotient.algebraMap_eq, φ', q,
              RingHom.coe_comp, Function.comp_apply] using
              e.toLinearEquiv.map_smul (φ a) x
      apply (RingTheory.Sequence.isRegular_cons_iff B y (xs.map φ)).2
      exact ⟨((RingTheory.Sequence.isRegular_cons_iff B y []).mp hyreg).1,
        (e.toAddEquiv.isRegular_congr hfor).mpr hxsreg⟩

private noncomputable def mcmPrefixResolution_of_kernel
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    (P : Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M))
    (n : ℕ) (hn2 : 1 < n) (K : ModuleCat R)
    (ι : K ⟶ P.complex.X (n - 1))
    (hι : ∀ j, (ComplexShape.down ℕ).Rel (n - 1) j →
      ι ≫ P.complex.d (n - 1) j = 0)
    (hcomp : ι ≫ P.complex.d (n - 1) (n - 2) = 0)
    (hker : IsLimit (KernelFork.ofι ι hcomp)) :
    Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M) := by
  let C := mcmPrefixComplex P n (by omega) K ι hι
  have h₀ : C.X 0 = P.complex.X 0 := by
    have hnpos : 0 < n := by omega
    dsimp [C, mcmPrefixComplex]
    simp [hnpos]
  let aug : C.X 0 ⟶ ModuleCat.of R M :=
    eqToHom h₀ ≫ P.augmentation
  have eqToHom_eq_id {X : ModuleCat.{u} R} (p : X = X) :
      eqToHom p = 𝟙 X := by
    have hp : p = rfl := Subsingleton.elim _ _
    rw [hp]
    simp
  refine {
    complex := C
    augmentation := aug
    augmentation_condition := ?_
    exact_zero := ?_
    exact_succ := ?_
    augmentation_epi := ?_ }
  · have hn0 : 0 ≠ n := by omega
    have hn1 : 1 ≠ n := by omega
    have hn1lt : 1 < n := by omega
    have hn0lt : 0 < n := by omega
    have hnsublt : n - 1 < n := by omega
    have h1 : C.X 1 = P.complex.X 1 := by
      simp [C, mcmPrefixComplex, hn1lt, hn1]
    have hd : C.d 1 0 ≫ eqToHom h₀ = eqToHom h1 ≫ P.complex.d 1 0 := by
      dsimp [C, mcmPrefixComplex] at h₀ h1 ⊢
      apply eq_of_heq
      subst_vars
      simp only [dif_neg hn1, dif_pos hn1lt, dif_pos hn0lt,
        eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
        comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
      simp [eqToHom_eq_id, hn0lt, hn1lt, hn0, hn1,
        Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp, Category.comp_id, proof_irrel_heq]
    have h : eqToHom h1 ≫ (P.complex.d 1 0 ≫ P.augmentation) = 0 := by
      rw [P.augmentation_condition]
      simp
    dsimp [aug]
    rw [← Category.assoc, hd]
    exact h
  · let S := ShortComplex.mk (C.d 1 0) aug (by
        have hn1lt : 1 < n := by omega
        have hn0lt : 0 < n := by omega
        have hn1 : 1 ≠ n := by omega
        have h1 : C.X 1 = P.complex.X 1 := by
          simp [C, mcmPrefixComplex, hn1lt, hn1]
        have hd : C.d 1 0 ≫ eqToHom h₀ = eqToHom h1 ≫ P.complex.d 1 0 := by
          dsimp [C, mcmPrefixComplex] at h₀ h1 ⊢
          apply eq_of_heq
          subst_vars
          simp only [dif_neg hn1, dif_pos hn1lt, dif_pos hn0lt,
            eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
            comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
          simp [eqToHom_eq_id, hn0lt, hn1lt, hn1,
            Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.id_comp, Category.comp_id, proof_irrel_heq]
        have h : eqToHom h1 ≫ (P.complex.d 1 0 ≫ P.augmentation) = 0 := by
          rw [P.augmentation_condition]
          simp
        dsimp [aug]
        rw [← Category.assoc, hd]
        exact h)
    let T := ShortComplex.mk (P.complex.d 1 0) P.augmentation
      P.augmentation_condition
    let e₁ : S.X₁ ≅ T.X₁ := eqToIso (by
      have hn1lt : 1 < n := by omega
      have hn1 : 1 ≠ n := by omega
      simp [S, T, C, mcmPrefixComplex, hn2, hn1lt, hn1])
    let e₂ : S.X₂ ≅ T.X₂ := eqToIso (by
      have hn0lt : 0 < n := by omega
      have hn0 : 0 ≠ n := by omega
      simp [S, T, C, mcmPrefixComplex, hn2, hn0lt, hn0])
    let e₃ : S.X₃ ≅ T.X₃ := Iso.refl _
    have hST : S ≅ T := ShortComplex.isoMk e₁ e₂ e₃ (by
      dsimp [S, T, e₁, e₂]
      apply eq_of_heq
      subst_vars
      simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
        comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
      dsimp [C, mcmPrefixComplex]
      have hn1 : 1 ≠ n := by omega
      have hn1lt : 1 < n := by omega
      have hn0lt : 0 < n := by omega
      simp only [dif_neg hn1, dif_pos hn1lt, dif_pos hn0lt,
        eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
        comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
      simp) (by
      dsimp [S, T, e₂, e₃]
      apply eq_of_heq
      subst_vars
      simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
        comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
      simp [aug])
    exact ShortComplex.exact_of_iso hST.symm (P.exact_zero)
  · intro i
    by_cases hi : i + 1 = n - 1
    · have hi' : i = n - 2 := by omega
      have hi2 : i + 2 = n := by omega
      have hi1 : i + 1 = n - 1 := by omega
      have hnsub : n - 2 + 2 = n := by omega
      have hnsub1 : n - 2 + 1 = n - 1 := by omega
      let S := ShortComplex.mk (C.d (i + 2) (i + 1))
        (C.d (i + 1) i) (C.d_comp_d (i + 2) (i + 1) i)
      let T := ShortComplex.mk ι (P.complex.d (n - 1) (n - 2)) hcomp
      let e₁ : S.X₁ ≅ T.X₁ := eqToIso (by
        simp [S, T, C, mcmPrefixComplex, hi2, hn2])
      let e₂ : S.X₂ ≅ T.X₂ := eqToIso (by
        have hnpos : 0 < n := by omega
        have hnsublt : n - 1 < n := by omega
        simp [S, T, C, mcmPrefixComplex, hi1, hnsub, hnsublt, hnpos, hn2])
      let e₃ : S.X₃ ≅ T.X₃ := eqToIso (by
        have hnsub2lt : n - 2 < n := by omega
        simp [S, T, C, mcmPrefixComplex, hi', hnsub2lt, hn2])
      have hST : S ≅ T := ShortComplex.isoMk e₁ e₂ e₃ (by
        dsimp [S, T, e₁, e₂]
        apply eq_of_heq
        subst_vars
        simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
          comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
        dsimp [C, mcmPrefixComplex]
        simp only [if_true, dif_pos rfl, eqToHom_comp_heq_iff,
          heq_eqToHom_comp_iff, comp_eqToHom_heq_iff,
          heq_comp_eqToHom_iff]
        rfl) (by
        dsimp [S, T, e₂, e₃]
        apply eq_of_heq
        subst_vars
        simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
        comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
        dsimp [C, mcmPrefixComplex]
        have hne : i + 1 ≠ i + 2 := by omega
        have hlt1 : i + 1 < i + 2 := by omega
        have hlt0 : i < i + 2 := by omega
        simp only [Nat.add_sub_cancel_left, dif_neg hne, dif_pos hlt1, dif_pos hlt0,
          eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
          comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
        have hsub : i + 2 - 2 = i := hi'.symm
        rw [hsub]
        )
      exact ShortComplex.exact_of_iso hST.symm
        (ShortComplex.exact_of_f_is_kernel T hker)
    · by_cases hi' : i + 1 = n
      · let S := ShortComplex.mk (C.d (i + 2) (i + 1))
          (C.d (i + 1) i) (C.d_comp_d (i + 2) (i + 1) i)
        have hgt : n < i + 2 := by omega
        have hzero : IsZero (C.X (i + 2)) := by
          have hX : C.X (i + 2) = ModuleCat.of R (Fin 0 → R) := by
            have hne : i + 2 ≠ n := by omega
            have hlt : ¬ i + 2 < n := by omega
            simp [C, mcmPrefixComplex, hne, hlt, hgt]
          rw [hX]
          apply ModuleCat.isZero_of_subsingleton
        have hi0 : i = n - 1 := by omega
        subst i
        have hnsub : n - 1 + 1 = n := by omega
        have hnlt : n - 1 < n := by omega
        have hnn : n - 1 ≠ n := by omega
        have hnotlt : ¬ n - 1 + 1 < n := by omega
        let Z : ModuleCat R := ModuleCat.of R (Fin 0 → R)
        let T := ShortComplex.mk (0 : Z ⟶ K) ι (by simp)
        let e₁ : S.X₁ ≅ T.X₁ := eqToIso (by
          have hne : n - 1 + 2 ≠ n := by omega
          have hlt : ¬ n - 1 + 2 < n := by omega
          have hgt' : n < n - 1 + 2 := by omega
          simp [S, T, Z, C, mcmPrefixComplex, hne, hlt, hgt', hn2])
        let e₂ : S.X₂ ≅ T.X₂ := eqToIso (by
          simp [S, T, C, mcmPrefixComplex, hnsub, hnlt, hnotlt, hn2])
        let e₃ : S.X₃ ≅ T.X₃ := eqToIso (by
          simp [S, T, C, mcmPrefixComplex, hnlt, hnn, hn2])
        have hST : S ≅ T := ShortComplex.isoMk e₁ e₂ e₃ (by
          dsimp [S, T, e₁, e₂]
          apply eq_of_heq
          subst_vars
          simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
            comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
          dsimp [C, mcmPrefixComplex]
          have hne : n - 1 + 2 ≠ n := by omega
          have hlt : ¬ n - 1 + 2 < n := by omega
          simp only [dif_neg hne, dif_neg hlt, if_neg hne, if_neg hlt]
          have zero_heq {X X' Y Y' : ModuleCat R} (hX : X = X') (hY : Y = Y') :
              (0 : X ⟶ Y) ≍ (0 : X' ⟶ Y') := by
            subst hX
            subst hY
            rfl
          apply zero_heq
          · dsimp
            simp [Z, hlt, hne]
          · dsimp
            simp [hnotlt, hnsub]) (by
          dsimp [S, T, e₂, e₃]
          apply eq_of_heq
          subst_vars
          simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
            comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
          dsimp [C, mcmPrefixComplex]
          simp only [dif_pos hnsub, dif_pos rfl, dif_pos hnlt, dif_neg hnn,
            eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
            comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
          simp [eqToHom_eq_id, hnlt, hnn,
            Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.id_comp, Category.comp_id, proof_irrel_heq])
        have hmonoι : Mono ι := mono_of_isLimit_fork hker
        have hTZ : IsZero T.X₁ := by
          dsimp [T, Z]
          apply ModuleCat.isZero_of_subsingleton
        have hTexact : T.Exact := (T.exact_iff_mono (hTZ.eq_zero_of_src _)).2 hmonoι
        simpa [S] using ShortComplex.exact_of_iso hST.symm hTexact
      · by_cases hil : i + 1 < n - 1
        · have hi2 : i + 2 < n := by omega
          have hi1 : i + 1 < n := by omega
          have hi0 : i < n := by omega
          have hi2n : i + 2 ≠ n := by omega
          have hi1n : i + 1 ≠ n := by omega
          have hi0n : i ≠ n := by omega
          let S := ShortComplex.mk (C.d (i + 2) (i + 1))
            (C.d (i + 1) i) (C.d_comp_d (i + 2) (i + 1) i)
          let T := ShortComplex.mk (P.complex.d (i + 2) (i + 1))
            (P.complex.d (i + 1) i) (P.complex.d_comp_d (i + 2) (i + 1) i)
          let e₁ : S.X₁ ≅ T.X₁ := eqToIso (by
            simp [S, T, C, mcmPrefixComplex, hi2, hi2n, hn2])
          let e₂ : S.X₂ ≅ T.X₂ := eqToIso (by
            simp [S, T, C, mcmPrefixComplex, hi1, hi1n, hn2])
          let e₃ : S.X₃ ≅ T.X₃ := eqToIso (by
            simp [S, T, C, mcmPrefixComplex, hi0, hi0n, hn2])
          have hST : S ≅ T := ShortComplex.isoMk e₁ e₂ e₃ (by
            dsimp [S, T, e₁, e₂]
            apply eq_of_heq
            subst_vars
            simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
              comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
            dsimp [C, mcmPrefixComplex]
            simp only [dif_neg hi2n, dif_pos hi2, dif_neg hi1n, dif_pos hi1,
              dif_neg hi0n, dif_pos hi0, eqToHom_comp_heq_iff,
              heq_eqToHom_comp_iff, comp_eqToHom_heq_iff,
              heq_comp_eqToHom_iff]
            rfl) (by
            dsimp [S, T, e₂, e₃]
            apply eq_of_heq
            subst_vars
            simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
              comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
            dsimp [C, mcmPrefixComplex]
            simp only [dif_neg hi1n, dif_pos hi1, dif_neg hi0n, dif_pos hi0,
              eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
              comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
            rfl)
          exact ShortComplex.exact_of_iso hST.symm (P.exact_succ i)
        · have hgt : n < i + 1 := by omega
          have hzero : IsZero (C.X (i + 1)) := by
            have hX : C.X (i + 1) = ModuleCat.of R (Fin 0 → R) := by
              have hne : i + 1 ≠ n := by omega
              have hlt : ¬ i + 1 < n := by omega
              simp [C, mcmPrefixComplex, hne, hlt, hgt]
            rw [hX]
            apply ModuleCat.isZero_of_subsingleton
          apply ShortComplex.exact_of_isZero_X₂
          exact hzero
  · let e₀ : C.X 0 ≅ P.complex.X 0 := eqToIso (by
      have hnpos : 0 < n := by omega
      dsimp [C, mcmPrefixComplex]
      simp [hnpos])
    have haug : aug = e₀.hom ≫ P.augmentation := by
      dsimp [aug, e₀]
    rw [haug]
    letI : Epi P.augmentation := P.augmentation_epi
    infer_instance

theorem exists_mcm_finite_free_resolution_prefix
    (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : IsCohenMacaulayLocalRing R) (d e : ℕ)
    (hdim : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)))
    (hdepth : localDepth R M = (e : ℕ∞)) :
    ∃ n : ℕ, n + e = d ∧ HasMCMFiniteFreeResolutionPrefix R M n := by
  classical
  have hMnontr : Nontrivial M := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    have htop : localDepth R M = ⊤ := by
      exact @depth_eq_top_of_subsingleton R _ (IsLocalRing.maximalIdeal R) M
        _ _ _ hsub
    rw [hdepth] at htop
    exact (WithTop.coe_ne_top : (e : ℕ∞) ≠ ⊤) htop
  have hdepth_le : localDepth R M ≤ (d : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    calc
      ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R M :=
        @supportDim_ge_localDepth R M _ _ _ _ _ _ hMnontr
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
      _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
  have he_le : e ≤ d := by
    exact_mod_cast (show (e : ℕ∞) ≤ (d : ℕ∞) by simpa [hdepth] using hdepth_le)
  let n : ℕ := d - e
  have hne : n + e = d := by
    dsimp [n]
    exact Nat.sub_add_cancel he_le
  refine ⟨n, hne, ?_⟩
  by_cases hn : n = 0
  · simp only [hn] at *
    have hed : e = d := by omega
    have hMCM : Formalization.Books.Algebra.Unit103.IsMaximalCohenMacaulay R M := by
      unfold Formalization.Books.Algebra.Unit103.IsMaximalCohenMacaulay
      rw [hdepth, hed, hdim]
    let X : ℕ → ModuleCat R := fun i =>
      match i with
      | 0 => ModuleCat.of R M
      | _ => ModuleCat.of R (Fin 0 → R)
    let dz : ∀ i j, X i ⟶ X j := fun _ _ => 0
    let C : Formalization.Books.Algebra.Unit71.ModuleChainComplex R :=
      HomologicalComplex.mk X dz (by intros; simp [dz]) (by intros; simp [dz])
    let F : Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M) :=
      { complex := C
        augmentation := 𝟙 _
        augmentation_condition := by simp [C, dz]
        exact_zero := by
          apply ModuleCat.shortComplex_exact
          simp [C, dz]
          intro y
          constructor
          · intro hy
            refine ⟨0, ?_⟩
            simpa using hy.symm
          · rintro ⟨x, hx⟩
            simpa using hx.symm
        exact_succ := by
          intro j
          apply ShortComplex.exact_of_isZero_X₂
          change IsZero (C.X (j + 1))
          rw [show C.X (j + 1) = ModuleCat.of R (Fin 0 → R) by
            simp [C, X]]
          apply ModuleCat.isZero_of_subsingleton
        augmentation_epi := by infer_instance }
    refine ⟨F, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · refine ⟨inferInstance, hMCM, ?_, ?_⟩
      · intro _
        exact Function.bijective_id
      · intro h
        omega
  · let Pff := Classical.choice
      (Formalization.Books.Algebra.Unit71.exists_finite_free_resolution
        (ModuleCat.of R M))
    let P := Pff.resolution.resolution
    have hPfinite : ∀ j, Module.Finite R (P.complex.X j) := by
      intro j
      exact Pff.finite j
    have hPfree : ∀ j, Module.Free R (P.complex.X j) := by
      intro j
      exact Pff.resolution.free j
    have kernel_finite {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
        [Module.Finite R X] :
          Module.Finite R ((CategoryTheory.Limits.kernel f : ModuleCat.{u} R) : Type u) := by
      let _ : IsNoetherian R (X : Type u) :=
        isNoetherian_of_isNoetherianRing_of_finite R _
      apply Module.Finite.of_injective (R := R) (S := R)
        (M := ((CategoryTheory.Limits.kernel f : ModuleCat.{u} R) : Type u))
        (N := (X : Type u))
        (kernel.ι f).hom
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    have hRdim :
        ((localDepth R R : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
      exact hR.trans (Module.supportDim_self_eq_ringKrullDim R)
    have hfree_fin : ∀ k : ℕ, localDepth R (Fin k.succ → R) = localDepth R R := by
      intro k
      induction k with
      | zero =>
          exact localDepth_eq_of_linearEquiv
            (LinearEquiv.piUnique R (fun _ : Fin 1 => R))
      | succ k ih =>
          let e : (R × (Fin k.succ → R)) ≃ₗ[R] (Fin k.succ.succ → R) :=
            Fin.consLinearEquiv R (fun _ : Fin k.succ.succ => R)
          let f₀ := e.toLinearMap.comp (LinearMap.inl R R (Fin k.succ → R))
          let g₀ := (LinearMap.snd R R (Fin k.succ → R)).comp e.symm.toLinearMap
          have hf₀ : Function.Injective f₀ := by
            have hinj : Function.Injective
                (LinearMap.inl R R (Fin k.succ → R)) := LinearMap.inl_injective
            exact e.injective.comp hinj
          have hfg₀ : Function.Exact f₀ g₀ := by
            exact (LinearEquiv.conj_exact_iff_exact
              (LinearMap.inl R R (Fin k.succ → R))
              (LinearMap.snd R R (Fin k.succ → R)) e).2
              Function.Exact.inl_snd
          have hg₀ : Function.Surjective g₀ := by
            have hsurj : Function.Surjective
                (LinearMap.snd R R (Fin k.succ → R)) := LinearMap.snd_surjective
            exact hsurj.comp e.symm.surjective
          have hseq := localDepth_shortExact f₀ g₀ hf₀ hfg₀ hg₀
          have hge :
              localDepth R (Fin k.succ.succ → R) ≥ localDepth R R := by
            simpa [ih] using hseq.1
          have hle :
              ((localDepth R (Fin k.succ.succ → R) : ℕ∞) : WithBot ℕ∞) ≤
                ((localDepth R R : ℕ∞) : WithBot ℕ∞) := by
            calc
              ((localDepth R (Fin k.succ.succ → R) : ℕ∞) : WithBot ℕ∞) ≤
                  Module.supportDim R (Fin k.succ.succ → R) :=
                supportDim_ge_localDepth
              _ ≤ ringKrullDim R :=
                Module.supportDim_le_ringKrullDim R (Fin k.succ.succ → R)
              _ = ((localDepth R R : ℕ∞) : WithBot ℕ∞) := hRdim.symm
          exact le_antisymm (WithBot.coe_le_coe.mp hle) hge
    have hfree_depth {X : Type u} [AddCommGroup X] [Module R X]
        [Module.Free R X] [Module.Finite R X] (hX : Nontrivial X) :
        localDepth R X = localDepth R R := by
      letI : Nontrivial X := hX
      let ι := Module.Free.ChooseBasisIndex R X
      letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype R X
      let b := Module.Free.chooseBasis R X
      let e := b.equivFun.trans
        (LinearEquiv.funCongrLeft R R (Fintype.equivFin ι).symm)
      have hι : 0 < Fintype.card ι :=
        Fintype.card_pos_iff.mpr inferInstance
      have hcard : Fintype.card ι - 1 + 1 = Fintype.card ι := by omega
      calc
        localDepth R X = localDepth R (Fin (Fintype.card ι) → R) :=
          localDepth_eq_of_linearEquiv e
        _ = localDepth R R := by
          have hf := hfree_fin (Fintype.card ι - 1)
          rw [← hcard]
          simpa only [Nat.succ_eq_add_one] using hf
    let K : ℕ → ModuleCat R := fun j =>
      if hj : j = 0 then ModuleCat.of R M
      else if hj1 : j = 1 then kernel P.augmentation
      else kernel (P.complex.d (j - 1) (j - 2))
    have hK_one : K 1 = kernel P.augmentation := by simp [K]
    have hK_generic (j : ℕ) (hj : j ≠ 0) (hj1 : j ≠ 1) :
        K j = kernel (P.complex.d (j - 1) (j - 2)) := by
      simp [K, hj, hj1]
    have hK_next (j : ℕ) (hj : j ≠ 0) :
        K (j + 1) = kernel (P.complex.d j (j - 1)) := by
      have hj1 : j + 1 ≠ 1 := by omega
      have hjsub : j + 1 - 2 = j - 1 := by omega
      simp [K, hj, hj1]
      rw [hjsub]
    let κ : ∀ j, K (j + 1) ⟶ P.complex.X j := fun j => by
      by_cases hj : j = 0
      · subst j
        exact eqToHom hK_one ≫ kernel.ι P.augmentation
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hK := hK_next j hj
        exact eqToHom hK ≫ kernel.ι (P.complex.d j (j - 1))
    let ell : ∀ j, P.complex.X j ⟶ K j := fun j => by
      by_cases hj : j = 0
      · subst j
        simpa [K] using P.augmentation
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        by_cases hj1 : j = 1
        · subst j
          exact kernel.lift P.augmentation (P.complex.d 1 0)
              (by simpa using P.augmentation_condition) ≫ eqToHom hK_one.symm
        · have hK := hK_generic j hj hj1
          exact kernel.lift (P.complex.d (j - 1) (j - 2))
              (P.complex.d j (j - 1)) (by simp) ≫ eqToHom hK.symm
    have hKfinite : ∀ j, Module.Finite R (K j) := by
      intro j
      by_cases hj : j = 0
      · subst j
        simpa [K] using (inferInstance : Module.Finite R M)
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        by_cases hj1 : j = 1
        · subst j
          apply kernel_finite
        · have hK : K j = kernel (P.complex.d (j - 1) (j - 2)) := by
            simp [K, hj, hjpos, hj1]
          rw [hK]
          apply kernel_finite
    
    have hRdepth : localDepth R R = (d : ℕ∞) := by
      apply WithBot.coe_injective
      calc
        ((localDepth R R : ℕ∞) : WithBot ℕ∞) = ringKrullDim R :=
          hR.trans (Module.supportDim_self_eq_ringKrullDim R)
        _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
    have hKdepth_le : ∀ j, Nontrivial (K j) → localDepth R (K j) ≤ (d : ℕ∞) := by
      intro j hNj
      letI : Module.Finite R (K j) := hKfinite j
      apply WithBot.coe_le_coe.mp
      calc
        ((localDepth R (K j) : ℕ∞) : WithBot ℕ∞) ≤
            Module.supportDim R (K j) :=
          @supportDim_ge_localDepth R (K j) _ _ _ _ _ _ hNj
        _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R (K j)
        _ = (((d : ℕ∞) : WithBot ℕ∞)) := hdim
    have hκmono : ∀ j, Function.Injective (κ j).hom := by
      intro j
      by_cases hj : j = 0
      · subst j
        apply (ModuleCat.mono_iff_injective _).mp
        simpa [κ, K] using
          (inferInstance : Mono (kernel.ι P.augmentation))
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hK := hK_next j hj
        apply (ModuleCat.mono_iff_injective _).mp
        simpa [κ, hj, hK] using
          (inferInstance : Mono
            (eqToHom hK ≫ kernel.ι (P.complex.d j (j - 1))))
    have hellexact : ∀ j, Function.Exact (κ j).hom (ell j).hom := by
      intro j x
      constructor
      · intro hx
        by_cases hj : j = 0
        · subst j
          have hx0 : P.augmentation.hom x = 0 := by simpa [ell, K] using hx
          let z := (ModuleCat.kernelIsoKer P.augmentation).inv.hom ⟨x, hx0⟩
          have hzι : (kernel.ι P.augmentation).hom z = x := by
            dsimp [z]
            change ((ModuleCat.kernelIsoKer P.augmentation).inv ≫
              kernel.ι P.augmentation).hom ⟨x, hx0⟩ = x
            rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
            rfl
          have hK := hK_one
          refine ⟨(eqToHom hK.symm).hom z, ?_⟩
          simpa [κ, K, hzι]
        · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
          by_cases hj1 : j = 1
          · subst j
            have hK := hK_one
            have hK' := hK_next 1 (by omega)
            have hx' := congrArg
              (fun z => (kernel.ι P.augmentation).hom ((eqToHom hK).hom z)) hx
            have hx0 : (P.complex.d 1 0).hom x = 0 := by
              simpa [ell, hK] using hx'
            let z := (ModuleCat.kernelIsoKer (P.complex.d 1 0)).inv.hom ⟨x, hx0⟩
            have hzι : (kernel.ι (P.complex.d 1 0)).hom z = x := by
              dsimp [z]
              change ((ModuleCat.kernelIsoKer (P.complex.d 1 0)).inv ≫
                kernel.ι (P.complex.d 1 0)).hom ⟨x, hx0⟩ = x
              rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
              rfl
            refine ⟨(eqToHom hK'.symm).hom z, ?_⟩
            simp [κ, hK', hzι]
          · have hK := hK_generic j hj hj1
            have hK' := hK_next j hj
            have hx' := congrArg
              (fun z =>
                (kernel.ι (P.complex.d (j - 1) (j - 2))).hom
                  ((eqToHom hK).hom z)) hx
            have hell :
                (eqToHom hK).hom ((ell j).hom x) =
                  (kernel.lift (P.complex.d (j - 1) (j - 2))
                    (P.complex.d j (j - 1)) (by simp)).hom x := by
              rw [← ConcreteCategory.comp_apply]
              simp [ell, hK, hj, hj1, Category.assoc, eqToHom_trans,
                eqToHom_refl, proof_irrel_heq]
            have hx0 : (P.complex.d j (j - 1)).hom x = 0 := by
              rw [hell] at hx'
              simpa using hx'
            let z := (ModuleCat.kernelIsoKer (P.complex.d j (j - 1))).inv.hom
              ⟨x, hx0⟩
            have hzι : (kernel.ι (P.complex.d j (j - 1))).hom z = x := by
              dsimp [z]
              change ((ModuleCat.kernelIsoKer (P.complex.d j (j - 1))).inv ≫
                kernel.ι (P.complex.d j (j - 1))).hom ⟨x, hx0⟩ = x
              rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
              rfl
            refine ⟨(eqToHom hK'.symm).hom z, ?_⟩
            subst_vars
            have hκeq : κ j = eqToHom hK' ≫ kernel.ι (P.complex.d j (j - 1)) := by
              dsimp [κ]
              simp [hj, hK', proof_irrel_heq]
            rw [hκeq]
            change (eqToHom hK' ≫ kernel.ι (P.complex.d j (j - 1))).hom
              ((eqToHom hK'.symm).hom z) = x
            simp [hzι]
      · rintro ⟨y, rfl⟩
        have hcomp : κ j ≫ ell j = 0 := by
          by_cases hj : j = 0
          · subst j
            simp [κ, ell, K]
          · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
            by_cases hj1 : j = 1
            · subst j
              have hK := hK_one
              have hK' := hK_next 1 (by omega)
              rw [← cancel_mono (kernel.ι P.augmentation)]
              simp [κ, ell, K, hK, hK', Category.assoc]
            · have hK := hK_generic j hj hj1
              have hK' := hK_next j hj
              rw [← cancel_mono (eqToHom hK ≫
                kernel.ι (P.complex.d (j - 1) (j - 2)))]
              simp [κ, ell, hK, hK', hj, hj1, Category.assoc]
        exact congrArg (fun f => f.hom y) hcomp
    have hellsurj : ∀ j, Function.Surjective (ell j).hom := by
      intro j
      by_cases hj : j = 0
      · subst j
        exact (ModuleCat.epi_iff_surjective _).mp P.augmentation_epi
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        by_cases hj1 : j = 1
        · subst j
          have hK := hK_one
          intro y
          let y' := (eqToHom hK).hom y
          let z := (kernel.ι P.augmentation).hom y'
          have hz : P.augmentation.hom z = 0 := by simp [z]
          have hex : Function.Exact (P.complex.d 1 0).hom P.augmentation.hom :=
            (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
              P.exact_zero
          obtain ⟨x, hx⟩ := (hex z).1 hz
          refine ⟨x, ?_⟩
          apply (ModuleCat.mono_iff_injective _).mp
            (inferInstance : Mono (eqToHom hK ≫ kernel.ι P.augmentation))
          simpa [ell, hK, y', z] using hx
        · have hK := hK_generic j hj hj1
          intro y
          let y' := (eqToHom hK).hom y
          let z := (kernel.ι (P.complex.d (j - 1) (j - 2))).hom y'
          have hz : (P.complex.d (j - 1) (j - 2)).hom z = 0 := by
            simp [z]
          have hj2 : 2 ≤ j := by omega
          have hh :=
            (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
              (P.exact_succ (j - 2))
          have hex : Function.Exact
              (P.complex.d j (j - 1)).hom
              (P.complex.d (j - 1) (j - 2)).hom := by
            have h₁ : j - 2 + 2 = j := by omega
            have h₂ : j - 2 + 1 = j - 1 := by omega
            rw [h₁, h₂] at hh
            exact hh
          obtain ⟨x, hx⟩ := (hex z).1 hz
          refine ⟨x, ?_⟩
          apply (ModuleCat.mono_iff_injective _).mp
            (inferInstance : Mono
              (eqToHom hK ≫ kernel.ι (P.complex.d (j - 1) (j - 2))))
          have hell :
              (eqToHom hK).hom ((ell j).hom x) =
                (kernel.lift (P.complex.d (j - 1) (j - 2))
                  (P.complex.d j (j - 1)) (by simp)).hom x := by
              rw [← ConcreteCategory.comp_apply]
              subst_vars
              simp [ell, hK, hj, hj1, Category.assoc, eqToHom_trans,
              eqToHom_refl, proof_irrel_heq]
          change (kernel.ι (P.complex.d (j - 1) (j - 2))).hom
              ((eqToHom hK).hom ((ell j).hom x)) =
            (kernel.ι (P.complex.d (j - 1) (j - 2))).hom
              ((eqToHom hK).hom y)
          rw [hell]
          simpa [y', z] using hx
    have hPnontr_of_K (j : ℕ) (hKj : Nontrivial (K j)) :
        Nontrivial (P.complex.X j) := by
      apply not_subsingleton_iff_nontrivial.mp
      intro hsub
      apply (not_subsingleton_iff_nontrivial.mpr hKj)
      constructor
      intro x y
      obtain ⟨x', hx'⟩ := hellsurj j x
      obtain ⟨y', hy'⟩ := hellsurj j y
      calc
        x = (ell j).hom x' := hx'.symm
        _ = (ell j).hom y' := congrArg (ell j).hom (hsub.elim x' y')
        _ = y := hy'
    have hPdepth_of_K (j : ℕ) (hKj : Nontrivial (K j)) :
        localDepth R (P.complex.X j) = (d : ℕ∞) := by
      letI : Module.Finite R (P.complex.X j) := hPfinite j
      exact (hfree_depth (hPnontr_of_K j hKj)).trans hRdepth
    have hKnext_nontr (j : ℕ) (hNj : Nontrivial (K j))
        (hlt : localDepth R (K j) < (d : ℕ∞)) :
        Nontrivial (K (j + 1)) := by
      by_contra hnsub
      let hsub : Subsingleton (K (j + 1)) :=
        not_nontrivial_iff_subsingleton.mp hnsub
      letI : Subsingleton (K (j + 1)) := hsub
      letI : Module.Finite R (K j) := hKfinite j
      letI : Module.Finite R (K (j + 1)) := hKfinite (j + 1)
      have hellinj : Function.Injective (ell j).hom := by
        intro x y hxy
        have hzero : (ell j).hom (x - y) = 0 := by
          rw [map_sub, hxy]
          simp
        obtain ⟨z, hz⟩ := (hellexact j (x - y)).1 hzero
        have hz0 : z = 0 := Subsingleton.elim _ _
        have hxy0 : x - y = 0 := by
          simpa [hz0] using hz.symm
        exact sub_eq_zero.mp hxy0
      have hellbij : Function.Bijective (ell j).hom :=
        ⟨hellinj, hellsurj j⟩
      let eK : P.complex.X j ≃ₗ[R] K j :=
        LinearEquiv.ofBijective (ell j).hom hellbij
      have hdeptheq : localDepth R (P.complex.X j) = localDepth R (K j) :=
        localDepth_eq_of_linearEquiv eK
      have hKd : localDepth R (K j) = (d : ℕ∞) := by
        exact hdeptheq.symm.trans (hPdepth_of_K j hNj)
      exact (not_lt_of_ge (le_of_eq hKd)) hlt
    have hKdepth : ∀ j, j ≤ n →
        Nontrivial (K j) ∧
          localDepth R (K j) = min (e + j : ℕ∞) (d : ℕ∞) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base =>
          refine ⟨hMnontr, ?_⟩
          change localDepth R M = min (e : ℕ∞) (d : ℕ∞)
          rw [hdepth]
          exact min_eq_left (by exact_mod_cast he_le)
      | succ j hj ih =>
          have hjlt : j < n := by omega
          have hej : e + j < d := by omega
          have hej' : (e + j : ℕ∞) < (d : ℕ∞) := by exact_mod_cast hej
          have hKjlt : localDepth R (K j) < (d : ℕ∞) := by
            rw [ih.2, min_eq_left (le_of_lt hej')]
            exact hej'
          have hnext : Nontrivial (K (j + 1)) :=
            hKnext_nontr j ih.1 hKjlt
          letI : Module.Finite R (K j) := hKfinite j
          letI : Module.Finite R (K (j + 1)) := hKfinite (j + 1)
          letI : Nontrivial (K j) := ih.1
          letI : Nontrivial (K (j + 1)) := hnext
          letI : Module.Finite R (P.complex.X j) := hPfinite j
          letI : Nontrivial (P.complex.X j) := hPnontr_of_K j ih.1
          have hs := localDepth_shortExact (R := R)
            (κ j).hom (ell j).hom (hκmono j) (hellexact j) (hellsurj j)
          have hlow : (e + (j + 1) : ℕ∞) ≤ localDepth R (K (j + 1)) := by
            have hmin : min (d : ℕ∞) (localDepth R (K j) + 1) =
                (e + (j + 1) : ℕ∞) := by
              rw [ih.2, min_eq_right]
              · simp [Nat.cast_add]
              · exact_mod_cast (show e + j + 1 ≤ d by omega)
            rw [hPdepth_of_K j ih.1, hmin] at hs
            exact hs.2.2
          have hupp : localDepth R (K (j + 1)) ≤ (d : ℕ∞) :=
            hKdepth_le (j + 1) hnext
          refine ⟨hnext, ?_⟩
          rw [min_eq_left]
          · exact le_antisymm hupp hlow
          · exact_mod_cast (show e + (j + 1) ≤ d by omega)
    have hKn : Nontrivial (K n) := (hKdepth n le_rfl).1
    have hKn_depth : localDepth R (K n) = (d : ℕ∞) := by
      rw [(hKdepth n le_rfl).2, min_eq_right]
      exact_mod_cast (show d ≤ e + n by omega)
    let hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hn1 : n = 1
    · subst n
      let C := mcmPrefixComplex P 1 (by omega) (K 1) (κ 0) (by
        intro j hj
        simp only [ComplexShape.down_Rel] at hj
        omega)
      let F : Formalization.Books.Algebra.Unit71.Resolution
          R (ModuleCat.of R M) :=
        { complex := C
          augmentation := P.augmentation
          augmentation_condition := by
            simpa [C, mcmPrefixComplex] using (hellexact 0).linearMap_comp_eq_zero
          exact_zero := by
            apply ModuleCat.shortComplex_exact
            simpa [C, mcmPrefixComplex] using hellexact 0
          exact_succ := by
            intro j
            apply ShortComplex.exact_of_isZero_X₂
            have hX : C.X (j + 2) = ModuleCat.of R (Fin 0 → R) := by
              simp [C, mcmPrefixComplex, hnpos]
            rw [hX]
            apply ModuleCat.isZero_of_subsingleton
          augmentation_epi := P.augmentation_epi }
      refine ⟨F, ?_, ?_⟩
      · intro i
        have hi : i.1 < 1 := i.isLt
        have hi0 : i.1 = 0 := by omega
        subst i
        exact ⟨hPfree 0, hPfinite 0⟩
      · letI : Module.Finite R (K 1) := hKfinite 1
        refine ⟨hKfinite 1, ?_, ?_, ?_⟩
        · simpa [Formalization.Books.Algebra.Unit103.IsMaximalCohenMacaulay,
            hKn_depth]
        · intro h
          exact Function.bijective_id
        · intro h
          simpa [C, mcmPrefixComplex] using hκmono 0
    · have hn2 : 1 < n := by omega
      have hι : ∀ j, (ComplexShape.down ℕ).Rel (n - 1) j →
          κ (n - 1) ≫ P.complex.d (n - 1) j = 0 := by
        intro j hj
        have hj' : j = n - 2 := by
          simpa only [ComplexShape.down_Rel] using hj
        subst j
        simp [κ, K, hn2]
      have hcomp : κ (n - 1) ≫ P.complex.d (n - 1) (n - 2) = 0 := by
        simp [κ, K, hn2]
      have hker : IsLimit (KernelFork.ofι (κ (n - 1)) hcomp) := by
        have hK' : K n = kernel (P.complex.d (n - 1) (n - 2)) := by
          simp [K, hn2]
        simpa [κ, hK'] using
          (kernelIsKernel (P.complex.d (n - 1) (n - 2)))
      let F := mcmPrefixResolution_of_kernel P n hn2 (K n) (κ (n - 1)) hι hcomp hker
      refine ⟨F, ?_, ?_⟩
      · intro i
        have hi : i.1 < n := i.isLt
        have hfreei : Module.Free R (F.complex.X i) := by
          simpa [F, mcmPrefixResolution_of_kernel, mcmPrefixComplex, hi]
            using hPfree i
        have hfinitei : Module.Finite R (F.complex.X i) := by
          simpa [F, mcmPrefixResolution_of_kernel, mcmPrefixComplex, hi]
            using hPfinite i
        exact ⟨hfreei, hfinitei⟩
      · letI : Module.Finite R (K n) := hKfinite n
        refine ⟨hKfinite n, ?_, ?_, ?_⟩
        · simpa [Formalization.Books.Algebra.Unit103.IsMaximalCohenMacaulay,
            hKn_depth]
        · intro h
          omega
        · intro h
          simpa [F, mcmPrefixResolution_of_kernel, mcmPrefixComplex] using
            hκmono (n - 1)

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
  let d : ℕ := (LTSeries.longestOf (PrimeSpectrum B)).length
  have hdim : ringKrullDim B = (((d : ℕ∞) : WithBot ℕ∞)) := by
    change Order.krullDim (PrimeSpectrum B) = _
    rw [Order.krullDim_eq_length_of_finiteDimensionalOrder]
    simp [d]
  obtain ⟨xs, hxslen, hxsreg⟩ :=
    exists_regularSequence_of_localRingHom_aux A B φ hB hmax d hdim
  refine ⟨xs, ?_, hxsreg⟩
  simpa [hxslen] using hdim.symm

end

/-
#check CategoryTheory.eqToHom_naturality
#check CategoryTheory.eqToHom_map
#check HomologicalComplex.eqToHom_comp_d
#check ShortComplex.exact_of_isZero_X₁
#check ShortComplex.exact_of_mono
#check ShortComplex.exact_of_epi
#check ShortComplex.exact_zero
#check ShortComplex.
#check ModuleCat.shortComplex_exact
#check ModuleCat.shortComplexOfCompEqZero
-/

end Formalization.Books.Algebra.Unit104
