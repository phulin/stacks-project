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
  sorry

theorem isCohenMacaulayLocalRing_localization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsCohenMacaulayLocalRing R) (p : PrimeSpectrum R) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p.asIdeal) := by
  sorry

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
  sorry

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
  sorry

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
