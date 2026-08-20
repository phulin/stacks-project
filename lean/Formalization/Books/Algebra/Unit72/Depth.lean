import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit63.AssociatedPrimes
import Formalization.Books.Algebra.Unit68.RegularSequences
import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Commutative Algebra, Chapter 72: Depth

The source defines depth as a supremum of lengths of regular sequences.  The
value is represented by `ℕ∞`, so the convention that the zero module has
infinite depth and the possibility of an unbounded supremum are both visible
in the interface.  Regular and weakly regular sequences, associated primes,
support dimension, localization, finite ring maps, and Ext are the canonical
interfaces from Mathlib and earlier chapters.
-/

namespace Formalization.Books.Algebra.Unit72

open Set
open scoped Pointwise

universe u v w

noncomputable section

/-! ## Definition and immediate consequences -/

/-- The `I`-depth of a finite `R`-module, with `⊤` standing for `∞`.

The membership conditions on the list record that the regular sequence lies
in `I`; `RingTheory.Sequence.IsRegular` supplies the successive
nonzerodivisor conditions and the nonzero final quotient convention. -/
noncomputable def depth
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : ℕ∞ :=
  if _ : I • (⊤ : Submodule R M) = ⊤ then
    ⊤
  else
    sSup {n : ℕ∞ | ∃ rs : List R,
      n = (rs.length : ℕ∞) ∧
        (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs}

/-- Depth at the maximal ideal of a local ring. -/
abbrev localDepth
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : ℕ∞ :=
  depth (IsLocalRing.maximalIdeal R) M

/-- The zero-module convention for depth. -/
theorem depth_eq_top_of_subsingleton
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M] :
    depth I M = ⊤ := by
  simp [depth, Subsingleton.elim (I • (⊤ : Submodule R M)) (⊤ : Submodule R M)]

/-- If the ideal is the whole ring, every finite module has infinite depth. -/
theorem depth_top_ideal
    {R : Type u} (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    depth (⊤ : Ideal R) M = ⊤ := by
  simp [depth]

/-- Nakayama's consequence used in the source's explanation of the definition. -/
theorem smul_top_ne_top_of_le_ring_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    I • (⊤ : Submodule R M) ≠ ⊤ := by
  intro htop
  have htopbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I (⊤ : Submodule R M)
      Module.Finite.fg_top htop.symm.le hI
  have hsub : Subsingleton M := by
    constructor
    intro x y
    have hx : x ∈ (⊥ : Submodule R M) := htopbot ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule R M) := htopbot ▸ Submodule.mem_top
    have hx0 : x = 0 := by simpa using hx
    have hy0 : y = 0 := by simpa using hy
    exact hx0.trans hy0.symm
  exact (not_nontrivial_iff_subsingleton.mpr hsub) (inferInstance : Nontrivial M)

/-- A module has `I`-depth zero exactly when it is nonzero and `I` contains
no module nonzerodivisor. -/
theorem depth_eq_zero_iff
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    depth I M = 0 ↔
      Nontrivial M ∧ ¬ ∃ f : R, f ∈ I ∧ IsSMulRegular M f := by
  classical
  by_cases htop : I • (⊤ : Submodule R M) = ⊤
  · simp only [depth, dif_pos htop]
    constructor
    · intro hzero
      exact (ENat.top_ne_zero hzero).elim
    · rintro ⟨_, hno⟩
      obtain ⟨f, hf, hfm⟩ :=
        Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
          (⊤ : Submodule R M) Module.Finite.fg_top htop.symm.le
      have hg : 1 - f ∈ I := by
        simpa only [neg_sub] using I.neg_mem hf
      have hreg : IsSMulRegular M (1 - f) := by
        intro x y hxy
        simpa [sub_smul, hfm] using hxy
      exact (hno ⟨1 - f, hg, hreg⟩).elim
  · simp only [depth, dif_neg htop]
    rw [ENat.sSup_eq_zero]
    constructor
    · intro hzero
      have hnontr : Nontrivial M := by
        by_contra h
        have hsub : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
        have heq : I • (⊤ : Submodule R M) = ⊤ := by
          apply le_antisymm le_top
          intro x hx
          have hx0 : x = 0 := hsub.elim x 0
          rw [hx0]
          exact (I • (⊤ : Submodule R M)).zero_mem
        exact htop heq
      refine ⟨hnontr, ?_⟩
      rintro ⟨f, hf, hreg⟩
      have hspan : Ideal.span ({f} : Set R) ≤ I :=
        (Ideal.span_singleton_le_iff_mem (I := I)).mpr hf
      have hfle' : Ideal.span ({f} : Set R) • (⊤ : Submodule R M) ≤
          I • (⊤ : Submodule R M) := Submodule.smul_mono_left hspan
      have hfle : f • (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) := by
        simpa only [Submodule.ideal_span_singleton_smul] using hfle'
      have hfne : f • (⊤ : Submodule R M) ≠ ⊤ := by
        intro hftop
        apply htop
        have htop_le : (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) := by
          calc
            (⊤ : Submodule R M) = f • (⊤ : Submodule R M) := hftop.symm
            _ ≤ I • (⊤ : Submodule R M) := hfle
        exact top_unique htop_le
      have hq : Nontrivial (QuotSMulTop f M) :=
        Submodule.Quotient.nontrivial_iff.mpr hfne
      have hseq : RingTheory.Sequence.IsRegular M [f] :=
        RingTheory.Sequence.IsRegular.cons hreg
          (RingTheory.Sequence.IsRegular.nil R (QuotSMulTop f M))
      have hmem : (1 : ℕ∞) ∈ {n : ℕ∞ | ∃ rs : List R,
          n = (rs.length : ℕ∞) ∧
            (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs} := by
        exact ⟨[f], by simp, by simp [hf], hseq⟩
      have hone := hzero 1 hmem
      exact one_ne_zero hone
    · rintro ⟨hnontr, hno⟩ a ha
      rcases ha with ⟨rs, hlen, hmem, hreg⟩
      cases rs with
      | nil => simpa using hlen
      | cons f rs =>
          have hparts :=
            (RingTheory.Sequence.isRegular_cons_iff M f rs).mp hreg
          have hregf : IsSMulRegular M f := hparts.1
          exact (hno ⟨f, hmem f (by simp), hregf⟩).elim

/-! ## Basic properties -/

/-- Depth can be computed using weakly regular sequences, including the case
where the ideal acts surjectively on the module. -/
theorem depth_eq_sSup_weaklyRegular
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    depth I M =
      sSup {n : ℕ∞ | ∃ rs : List R,
        n = (rs.length : ℕ∞) ∧
          (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsWeaklyRegular M rs} := by
  classical
  by_cases htop : I • (⊤ : Submodule R M) = ⊤
  · simp only [depth, dif_pos htop]
    symm
    apply (sSup_eq_top ..).mpr
    intro n hn
    cases n with
    | top => exact (lt_irrefl _ hn).elim
    | coe n =>
        obtain ⟨f, hf, hfm⟩ :=
          Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
            (⊤ : Submodule R M) Module.Finite.fg_top htop.symm.le
        have ha : 1 - f ∈ I := by
          simpa only [neg_sub] using I.neg_mem hf
        have hreg : IsSMulRegular M (1 - f) := by
          intro x y hxy
          simpa [sub_smul, hfm] using hxy
        have htop_a : (1 - f) • (⊤ : Submodule R M) = ⊤ := by
          apply le_antisymm le_top
          intro x hx
          exact (Submodule.mem_smul_pointwise_iff_exists x (1 - f)
            (⊤ : Submodule R M)).mpr ⟨x, Submodule.mem_top, by
              simp [sub_smul, hfm]⟩
        have hsub : Subsingleton (QuotSMulTop (1 - f) M) := by
          apply not_nontrivial_iff_subsingleton.mp
          intro hnon
          exact (Submodule.Quotient.nontrivial_iff.mp hnon) htop_a
        have hweak_subsingleton : ∀ {N : Type v} [AddCommGroup N]
            [Module R N] [Subsingleton N] (rs : List R),
            RingTheory.Sequence.IsWeaklyRegular N rs := by
          intro N _ _ _ rs
          induction rs generalizing N with
          | nil => exact RingTheory.Sequence.IsWeaklyRegular.nil R N
          | cons r rs ih =>
              apply (RingTheory.Sequence.isWeaklyRegular_cons_iff N r rs).mpr
              refine ⟨?_, ?_⟩
              · intro x y _
                exact Subsingleton.elim _ _
              · let : Subsingleton (QuotSMulTop r N) := by
                  constructor
                  intro x y
                  exact Subsingleton.elim _ _
                exact ih
        have hweak : ∀ k : ℕ,
            RingTheory.Sequence.IsWeaklyRegular M
              ((1 - f) :: List.replicate k 0) := by
          intro k
          rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
          exact ⟨hreg, by simpa using hweak_subsingleton (List.replicate k 0)⟩
        refine ⟨((n + 1 : ℕ) : ℕ∞), ?_, by
          exact_mod_cast Nat.lt_succ_self n⟩
        refine ⟨(1 - f) :: List.replicate n 0, by
          simp [List.length_replicate], ?_, hweak n⟩
        intro r hr
        simp only [List.mem_cons, List.mem_replicate] at hr
        rcases hr with rfl | ⟨_, rfl⟩
        · exact ha
        · exact I.zero_mem
  · simp only [depth, dif_neg htop]
    congr 1
    ext n
    constructor
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, hreg.toIsWeaklyRegular⟩
    · rintro ⟨rs, hlen, hmem, hweak⟩
      have hspan : Ideal.ofList rs ≤ I := Ideal.span_le.mpr hmem
      have hsmul : Ideal.ofList rs • (⊤ : Submodule R M) ≤
          I • (⊤ : Submodule R M) := Submodule.smul_mono_left hspan
      have hne : (⊤ : Submodule R M) ≠
          Ideal.ofList rs • (⊤ : Submodule R M) := by
        intro heq
        apply htop
        apply top_unique
        calc
          (⊤ : Submodule R M) = Ideal.ofList rs • (⊤ : Submodule R M) := heq
          _ ≤ I • (⊤ : Submodule R M) := hsmul
      exact ⟨rs, hlen, hmem, ⟨hweak, hne⟩⟩

/-- Over a Noetherian local ring, support dimension bounds depth. -/
theorem supportDim_ge_localDepth
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R M := by
  have htop : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
      (by exact IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  unfold localDepth depth
  rw [dif_neg htop]
  cases hdim : Module.supportDim R M with
  | bot =>
      exact (Module.supportDim_ne_bot_of_nontrivial R M hdim).elim
  | coe d =>
      apply WithBot.coe_le_coe.mpr
      apply sSup_le
      intro n hn
      rcases hn with ⟨rs, hlen, hmem, hreg⟩
      have hlebot : (n : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
        rw [hlen]
        calc
          ((rs.length : ℕ∞) : WithBot ℕ∞) =
              (0 : WithBot ℕ∞) + ((rs.length : ℕ∞) : WithBot ℕ∞) := by simp
          _ ≤ Module.supportDim R
                (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) +
                ((rs.length : ℕ∞) : WithBot ℕ∞) := by
            let : Nontrivial (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) :=
              hreg.quot_ofList_smul_nontrivial ⊤
            have hqne : Module.supportDim R
                (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ≠ ⊥ :=
              Module.supportDim_ne_bot_of_nontrivial R _
            have hqzero : (0 : WithBot ℕ∞) ≤ Module.supportDim R
                (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) := by
              cases hq : Module.supportDim R
                  (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) with
              | bot => exact (hqne hq).elim
              | coe q => simp
            exact add_le_add_left hqzero
              ((rs.length : ℕ∞) : WithBot ℕ∞)
          _ = Module.supportDim R M :=
            Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
          _ = (d : WithBot ℕ∞) := hdim
      exact WithBot.coe_le_coe.mp hlebot

/-- A nonzero finite module over a Noetherian ring has finite `I`-depth when
`I` does not generate the whole module. -/
theorem depth_lt_top_of_noetherian
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    depth I M < ⊤ := by
  unfold depth
  rw [dif_neg hIM]
  let Q := M ⧸ (I • (⊤ : Submodule R M))
  let : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hIM
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := Q)
  change p ∈ Module.support R (M ⧸ (I • (⊤ : Submodule R M))) at hp
  rw [Module.support_quotient] at hp
  have hpM : p ∈ Module.support R M := hp.1
  have hpI : I ≤ p.asIdeal := by
    exact hp.2
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal M
  let : Nontrivial N := Module.mem_support_iff.mp hpM
  cases hdimS : ringKrullDim S with
  | bot =>
      have hle : Module.supportDim S N ≤ (⊥ : WithBot ℕ∞) := by
        rw [← hdimS]
        exact Module.supportDim_le_ringKrullDim S N
      exact (Module.supportDim_ne_bot_of_nontrivial S N
        (bot_unique hle)).elim
  | coe d =>
      have hdlt : d < (⊤ : ℕ∞) := by
        rw [lt_top_iff_ne_top]
        intro hd
        have hdimtop : ringKrullDim S = ⊤ := by
          rw [hdimS, hd]
          simp
        exact (ne_of_lt (ringKrullDim_lt_top (R := S))) hdimtop
      apply lt_of_le_of_lt (sSup_le ?_) hdlt
      intro n hn
      rcases hn with ⟨rs, hlen, hmem, hreg⟩
      have hregp : RingTheory.Sequence.IsRegular N
          (rs.map (algebraMap R S)) :=
        hreg.toIsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem
          (S := S) (p := p.asIdeal)
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
          (by
            intro r hr
            exact hpI (hmem r hr))
      have hdimreg := Module.supportDim_add_length_eq_supportDim_of_isRegular
        (rs.map (algebraMap R S)) hregp
      have hqnon : Nontrivial
          (N ⧸ (Ideal.ofList (rs.map (algebraMap R S)) •
            (⊤ : Submodule S N))) := hregp.quot_ofList_smul_nontrivial ⊤
      have hqne : Module.supportDim S
          (N ⧸ (Ideal.ofList (rs.map (algebraMap R S)) •
            (⊤ : Submodule S N))) ≠ ⊥ := by
        let := hqnon
        exact Module.supportDim_ne_bot_of_nontrivial S _
      have hqzero : (0 : WithBot ℕ∞) ≤ Module.supportDim S
          (N ⧸ (Ideal.ofList (rs.map (algebraMap R S)) •
            (⊤ : Submodule S N))) := by
        cases hq : Module.supportDim S
            (N ⧸ (Ideal.ofList (rs.map (algebraMap R S)) •
              (⊤ : Submodule S N))) with
        | bot => exact (hqne hq).elim
        | coe q => simp
      have hlenbot : ((rs.length : ℕ∞) : WithBot ℕ∞) ≤
          Module.supportDim S N := by
        calc
          ((rs.length : ℕ∞) : WithBot ℕ∞) =
              (0 : WithBot ℕ∞) + ((rs.length : ℕ∞) : WithBot ℕ∞) := by simp
          _ ≤ Module.supportDim S
                (N ⧸ (Ideal.ofList (rs.map (algebraMap R S)) •
                  (⊤ : Submodule S N))) +
                ((rs.length : ℕ∞) : WithBot ℕ∞) := by
            exact add_le_add_left hqzero _
          _ = Module.supportDim S N := by
            simpa [List.length_map] using hdimreg
      have hlenle : (rs.length : ℕ∞) ≤ d := by
        apply WithBot.coe_le_coe.mp
        calc
          ((rs.length : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim S N := hlenbot
          _ ≤ ringKrullDim S := Module.supportDim_le_ringKrullDim S N
          _ = (d : WithBot ℕ∞) := hdimS
      simpa [hlen] using hlenle

/-! ## Ext characterization -/

/-- The Ext groups used to detect local depth, together with the literal
"smallest integer" condition from the source.  The displayed long exact
Ext segment in the source is the canonical `extCovariantSequence` and its
exactness theorem from Chapter 71. -/
theorem localDepth_eq_min_ext
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∃ i : ℕ,
      localDepth R M = (i : ℕ∞) ∧
        Nontrivial
          (Formalization.Books.Algebra.Unit71.ExtGroup
            (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
            (ModuleCat.of R M) i) ∧
        ∀ j : ℕ, j < i →
          ¬ Nontrivial
            (Formalization.Books.Algebra.Unit71.ExtGroup
              (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
              (ModuleCat.of R M) j) := by
  classical
  have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hsmul : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
    lt_of_le_of_ne le_top hmax
  have hdepthtop : localDepth R M < ⊤ :=
    depth_lt_top_of_noetherian (IsLocalRing.maximalIdeal R) M hmax
  have hdepth_mem : localDepth R M ∈ {n : ℕ∞ | ∃ rs : List R,
      n = (rs.length : ℕ∞) ∧
        (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
          RingTheory.Sequence.IsRegular M rs} := by
    let : Nonempty {n : ℕ∞ | ∃ rs : List R,
        n = (rs.length : ℕ∞) ∧
          (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
            RingTheory.Sequence.IsRegular M rs} :=
      ⟨⟨0, ⟨[], by simp, by simp,
        RingTheory.Sequence.IsRegular.nil R M⟩⟩⟩
    unfold localDepth depth
    rw [dif_neg hmax]
    apply ENat.sSup_mem_of_nonempty_of_lt_top
    simpa [localDepth, depth, hmax] using hdepthtop
  rcases hdepth_mem with ⟨rs, hlen, hmem, hreg⟩
  have hK_support : Module.support R (R ⧸ IsLocalRing.maximalIdeal R) =
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hvanish : ∀ j : ℕ, j < rs.length →
      Subsingleton
        (Formalization.Books.Algebra.Unit71.ExtGroup
          (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
          (ModuleCat.of R M) j) :=
    fun j hj => ModuleCat.subsingleton_ext_of_exists_isRegular
      (IsLocalRing.maximalIdeal R)
      (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
      (by rw [hK_support])
      (ModuleCat.of R M) hsmul rs hmem hreg j hj
  have hnot : ¬ Subsingleton
      (Formalization.Books.Algebra.Unit71.ExtGroup
        (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
        (ModuleCat.of R M) rs.length) := by
    intro hsub
    have h_ext : ∀ j < rs.length + 1, Subsingleton
        (Formalization.Books.Algebra.Unit71.ExtGroup
          (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
          (ModuleCat.of R M) j) := by
      intro j hj
      have hjle : j ≤ rs.length := Nat.le_of_lt_succ hj
      rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
      · exact hvanish j hjlt
      · subst j
        exact hsub
    obtain ⟨ys, hyslen, hysmem, hysreg⟩ :=
      ModuleCat.exists_isRegular_of_exists_subsingleton_ext
        (IsLocalRing.maximalIdeal R) (rs.length + 1)
        (ModuleCat.of R M) hsmul
        (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
        hK_support h_ext
    have hle : (ys.length : ℕ∞) ≤ localDepth R M := by
      unfold localDepth depth
      rw [dif_neg hmax]
      exact le_sSup ⟨ys, rfl, hysmem, hysreg⟩
    have hle' : (ys.length : ℕ∞) ≤ (rs.length : ℕ∞) := by
      simpa [hlen] using hle
    have hleNat : ys.length ≤ rs.length := by
      exact_mod_cast hle'
    have hcontra : rs.length + 1 ≤ rs.length := by
      rw [hyslen] at hleNat
      exact hleNat
    exact (Nat.not_succ_le_self rs.length) hcontra
  refine ⟨rs.length, hlen, not_subsingleton_iff_nontrivial.mp hnot, ?_⟩
  intro j hj
  exact not_nontrivial_iff_subsingleton.mpr (hvanish j hj)

/-! ## Depth in a short exact sequence -/

/-- The three standard depth inequalities for a short exact sequence of
nonzero finite modules over a local Noetherian ring.  The displayed Ext
sequence is likewise supplied by Chapter 71's generic long exact sequence;
the scalar short exact sequence used in the proof is Mathlib's canonical
`IsSMulRegular.smulShortComplex_shortExact`. -/
theorem localDepth_shortExact
    {R N₁ N₂ N₃ : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [Nontrivial N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂] [Nontrivial N₂]
    [AddCommGroup N₃] [Module R N₃] [Module.Finite R N₃] [Nontrivial N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    localDepth R N₂ ≥ min (localDepth R N₁) (localDepth R N₃) ∧
      localDepth R N₃ ≥ min (localDepth R N₂) (localDepth R N₁ - 1) ∧
      localDepth R N₁ ≥ min (localDepth R N₂) (localDepth R N₃ + 1) := by
  classical
  let K := ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)
  let S := CategoryTheory.ShortComplex.moduleCatMk f g hfg.linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
  obtain ⟨i₁, hi₁, h₁, h₁'⟩ := localDepth_eq_min_ext (R := R) (M := N₁)
  obtain ⟨i₂, hi₂, h₂, h₂'⟩ := localDepth_eq_min_ext (R := R) (M := N₂)
  obtain ⟨i₃, hi₃, h₃, h₃'⟩ := localDepth_eq_min_ext (R := R) (M := N₃)
  have hzero_of_not_nontrivial {G : Type u} [AddCommGroup G]
      (hG : ¬ Nontrivial G) : ∀ z : G, z = 0 := by
    have hsub : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG
    intro z
    exact @Subsingleton.elim G hsub z 0
  have exists_ne_zero_of_nontrivial {G : Type u} [AddCommGroup G]
      (hG : Nontrivial G) : ∃ z : G, z ≠ 0 := by
    rcases hG.exists_pair_ne with ⟨a, b, hab⟩
    by_cases ha : a = 0
    · refine ⟨b, ?_⟩
      intro hb
      apply hab
      simp [ha, hb]
    · exact ⟨a, ha⟩
  have h₁i (i : ℕ) (hi : i < i₁) :
      ¬ Nontrivial
        (Formalization.Books.Algebra.Unit71.ExtGroup K (ModuleCat.of R N₁) i) :=
    h₁' i hi
  have h₂i (i : ℕ) (hi : i < i₂) :
      ¬ Nontrivial
        (Formalization.Books.Algebra.Unit71.ExtGroup K (ModuleCat.of R N₂) i) :=
    h₂' i hi
  have h₃i (i : ℕ) (hi : i < i₃) :
      ¬ Nontrivial
        (Formalization.Books.Algebra.Unit71.ExtGroup K (ModuleCat.of R N₃) i) :=
    h₃' i hi
  have h₁eq : localDepth R N₁ = (i₁ : ℕ∞) := hi₁
  have h₂eq : localDepth R N₂ = (i₂ : ℕ∞) := hi₂
  have h₃eq : localDepth R N₃ = (i₃ : ℕ∞) := hi₃
  constructor
  · by_contra h
    have hlt : localDepth R N₂ < min (localDepth R N₁) (localDepth R N₃) :=
      lt_of_not_ge h
    have hlt₁ : i₂ < i₁ := by
      have hlt' : (i₂ : ℕ∞) < (i₁ : ℕ∞) := by
        simpa [h₂eq, h₁eq] using
          hlt.trans_le (min_le_left (localDepth R N₁) (localDepth R N₃))
      exact_mod_cast hlt'
    have hlt₃ : i₂ < i₃ := by
      have hlt' : (i₂ : ℕ∞) < (i₃ : ℕ∞) := by
        simpa [h₂eq, h₃eq] using
          hlt.trans_le (min_le_right (localDepth R N₁) (localDepth R N₃))
      exact_mod_cast hlt'
    have hN₁sub : Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
        K (ModuleCat.of R N₁) i₂) :=
      not_nontrivial_iff_subsingleton.mp (h₁i i₂ hlt₁)
    have hN₃sub : Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
        K (ModuleCat.of R N₃) i₂) :=
      not_nontrivial_iff_subsingleton.mp (h₃i i₂ hlt₃)
    have hX₃sub : Subsingleton (CategoryTheory.Abelian.Ext K S.X₃ i₂) := by
      change Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
        K (ModuleCat.of R N₃) i₂)
      exact hN₃sub
    have hX₂non : Nontrivial (CategoryTheory.Abelian.Ext K S.X₂ i₂) := by
      change Nontrivial (Formalization.Books.Algebra.Unit71.ExtGroup
        K (ModuleCat.of R N₂) i₂)
      exact h₂
    obtain ⟨z, hz⟩ : ∃ z : CategoryTheory.Abelian.Ext K S.X₂ i₂, z ≠ 0 :=
      exists_ne_zero_of_nontrivial hX₂non
    have hzmap : z.comp (CategoryTheory.Abelian.Ext.mk₀ S.g)
        (Nat.add_zero i₂) = 0 := by
      exact @Subsingleton.elim _ hX₃sub _ _
    obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₂
      K hS z hzmap
    have hyzero : y = 0 := hzero_of_not_nontrivial (h₁i i₂ hlt₁) y
    apply hz
    simpa [hyzero] using hy.symm
  constructor
  · by_contra h
    have hlt : localDepth R N₃ < min (localDepth R N₂) (localDepth R N₁ - 1) :=
      lt_of_not_ge h
    have hlt₂ : i₃ < i₂ := by
      have hlt' : (i₃ : ℕ∞) < (i₂ : ℕ∞) := by
        simpa [h₃eq, h₂eq] using
          hlt.trans_le (min_le_left (localDepth R N₂) (localDepth R N₁ - 1))
      exact_mod_cast hlt'
    have hlt₁sub : i₃ < i₁ - 1 := by
      have hlt' : (i₃ : ℕ∞) < (i₁ : ℕ∞) - 1 := by
        simpa [h₃eq, h₁eq] using
          hlt.trans_le (min_le_right (localDepth R N₂) (localDepth R N₁ - 1))
      exact_mod_cast hlt'
    have hlt₁ : i₃ + 1 < i₁ := by omega
    have hN₂sub : Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
        K (ModuleCat.of R N₂) i₃) :=
      not_nontrivial_iff_subsingleton.mp (h₂i i₃ hlt₂)
    have hN₁sub : Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
        K (ModuleCat.of R N₁) (i₃ + 1)) :=
      not_nontrivial_iff_subsingleton.mp (h₁i (i₃ + 1) hlt₁)
    have hX₃non : Nontrivial (CategoryTheory.Abelian.Ext K S.X₃ i₃) := by
      change Nontrivial (Formalization.Books.Algebra.Unit71.ExtGroup
        K (ModuleCat.of R N₃) i₃)
      exact h₃
    have hX₁sub : Subsingleton (CategoryTheory.Abelian.Ext K S.X₁ (i₃ + 1)) := by
      change Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
        K (ModuleCat.of R N₁) (i₃ + 1))
      exact hN₁sub
    obtain ⟨z, hz⟩ : ∃ z : CategoryTheory.Abelian.Ext K S.X₃ i₃, z ≠ 0 :=
      exists_ne_zero_of_nontrivial hX₃non
    have hzmap : z.comp hS.extClass rfl = 0 :=
      @Subsingleton.elim _ hX₁sub _ _
    obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₃
      K hS z rfl hzmap
    have hyzero : y = 0 := hzero_of_not_nontrivial (h₂i i₃ hlt₂) y
    apply hz
    simpa [hyzero] using hy.symm
  · by_contra h
    have hlt : localDepth R N₁ < min (localDepth R N₂) (localDepth R N₃ + 1) :=
      lt_of_not_ge h
    have hlt₂ : i₁ < i₂ := by
      have hlt' : (i₁ : ℕ∞) < (i₂ : ℕ∞) := by
        simpa [h₁eq, h₂eq] using
          hlt.trans_le (min_le_left (localDepth R N₂) (localDepth R N₃ + 1))
      exact_mod_cast hlt'
    have hle₃ : i₁ ≤ i₃ := by
      have hlt' : (i₁ : ℕ∞) < (i₃ : ℕ∞) + 1 := by
        simpa [h₁eq, h₃eq] using
          hlt.trans_le (min_le_right (localDepth R N₂) (localDepth R N₃ + 1))
      have hle' : (i₁ : ℕ∞) ≤ (i₃ : ℕ∞) :=
        ENat.natCast_lt_add_one_iff.mp hlt'
      exact_mod_cast hle'
    cases i₁ with
    | zero =>
        have hN₂sub : Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
            K (ModuleCat.of R N₂) 0) :=
          not_nontrivial_iff_subsingleton.mp (h₂i 0 hlt₂)
        have hX₂sub : Subsingleton (CategoryTheory.Abelian.Ext K S.X₂ 0) := by
          change Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
            K (ModuleCat.of R N₂) 0)
          exact hN₂sub
        have hX₁non : Nontrivial (CategoryTheory.Abelian.Ext K S.X₁ 0) := by
          change Nontrivial (Formalization.Books.Algebra.Unit71.ExtGroup
            K (ModuleCat.of R N₁) 0)
          exact h₁
        obtain ⟨z, hz⟩ : ∃ z : CategoryTheory.Abelian.Ext K S.X₁ 0, z ≠ 0 :=
          exists_ne_zero_of_nontrivial hX₁non
        have hzmap :
            (CategoryTheory.Abelian.Ext.mk₀ S.f).postcomp K (Nat.add_zero 0) z = 0 :=
          @Subsingleton.elim _ hX₂sub _ _
        apply hz
        apply Formalization.Books.Algebra.Unit71.ext_covariant_initial_injective
          S hS K
        simpa using hzmap
    | succ n =>
        have hn₃ : n < i₃ := by omega
        have hN₂sub : Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
            K (ModuleCat.of R N₂) (n + 1)) :=
          not_nontrivial_iff_subsingleton.mp (h₂i (n + 1) hlt₂)
        have hN₃sub : Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
            K (ModuleCat.of R N₃) n) :=
          not_nontrivial_iff_subsingleton.mp (h₃i n hn₃)
        have hX₂sub : Subsingleton (CategoryTheory.Abelian.Ext K S.X₂ (n + 1)) := by
          change Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
            K (ModuleCat.of R N₂) (n + 1))
          exact hN₂sub
        have hX₃sub : Subsingleton (CategoryTheory.Abelian.Ext K S.X₃ n) := by
          change Subsingleton (Formalization.Books.Algebra.Unit71.ExtGroup
            K (ModuleCat.of R N₃) n)
          exact hN₃sub
        have hX₁non : Nontrivial (CategoryTheory.Abelian.Ext K S.X₁ (n + 1)) := by
          change Nontrivial (Formalization.Books.Algebra.Unit71.ExtGroup
            K (ModuleCat.of R N₁) (n + 1))
          exact h₁
        obtain ⟨z, hz⟩ :
            ∃ z : CategoryTheory.Abelian.Ext K S.X₁ (n + 1), z ≠ 0 :=
          exists_ne_zero_of_nontrivial hX₁non
        have hzmap : z.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) rfl = 0 :=
          @Subsingleton.elim _ hX₂sub _ _
        obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁
          K hS z hzmap rfl
        have hyzero : y = 0 := hzero_of_not_nontrivial (h₃i n hn₃) y
        apply hz
        simpa [hyzero] using hy.symm

private theorem depth_congr
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) (I : Ideal R) :
    depth I M = depth I N := by
  classical
  have hmap :
      Submodule.map e.toLinearMap (I • (⊤ : Submodule R M)) =
        I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    simp
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔
      I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have h' := congrArg (Submodule.map e.toLinearMap) h
      rw [hmap] at h'
      simpa using h'
    · intro h
      have h' : Submodule.map e.toLinearMap (I • (⊤ : Submodule R M)) =
          (⊤ : Submodule R N) := hmap.trans h
      simpa only [Submodule.map_eq_top_iff] using h'
  by_cases h : I • (⊤ : Submodule R M) = ⊤
  · have h' := htop.mp h
    simp only [depth, dif_pos h, dif_pos h']
  · have h' : I • (⊤ : Submodule R N) ≠ ⊤ := by
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

private theorem localDepth_eq_min_ext_universe
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] [Small.{v} R] :
    ∃ i : ℕ,
      localDepth R M = (i : ℕ∞) ∧
        Nontrivial
          (CategoryTheory.Abelian.Ext
            (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)))
            (ModuleCat.of R M) i) ∧
        ∀ j : ℕ, j < i →
          ¬ Nontrivial
            (CategoryTheory.Abelian.Ext
              (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)))
              (ModuleCat.of R M) j) := by
  classical
  have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hsmul : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
    lt_of_le_of_ne le_top hmax
  have hdepthtop : localDepth R M < ⊤ :=
    depth_lt_top_of_noetherian (IsLocalRing.maximalIdeal R) M hmax
  have hdepth_mem : localDepth R M ∈ {n : ℕ∞ | ∃ rs : List R,
      n = (rs.length : ℕ∞) ∧
        (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
          RingTheory.Sequence.IsRegular M rs} := by
    let : Nonempty {n : ℕ∞ | ∃ rs : List R,
        n = (rs.length : ℕ∞) ∧
          (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
            RingTheory.Sequence.IsRegular M rs} :=
      ⟨⟨0, ⟨[], by simp, by simp,
        RingTheory.Sequence.IsRegular.nil R M⟩⟩⟩
    unfold localDepth depth
    rw [dif_neg hmax]
    apply ENat.sSup_mem_of_nonempty_of_lt_top
    simpa [localDepth, depth, hmax] using hdepthtop
  rcases hdepth_mem with ⟨rs, hlen, hmem, hreg⟩
  have hK_support : Module.support R
      (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)) =
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient]
  have hvanish : ∀ j : ℕ, j < rs.length →
      Subsingleton
        (CategoryTheory.Abelian.Ext
          (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)))
          (ModuleCat.of R M) j) :=
    fun j hj => ModuleCat.subsingleton_ext_of_exists_isRegular
      (IsLocalRing.maximalIdeal R)
      (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)))
      (by rw [hK_support])
      (ModuleCat.of R M) hsmul rs hmem hreg j hj
  have hnot : ¬ Subsingleton
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)))
        (ModuleCat.of R M) rs.length) := by
    intro hsub
    have h_ext : ∀ j < rs.length + 1, Subsingleton
        (CategoryTheory.Abelian.Ext
          (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)))
          (ModuleCat.of R M) j) := by
      intro j hj
      have hjle : j ≤ rs.length := Nat.le_of_lt_succ hj
      rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
      · exact hvanish j hjlt
      · subst j
        exact hsub
    obtain ⟨ys, hyslen, hysmem, hysreg⟩ :=
      ModuleCat.exists_isRegular_of_exists_subsingleton_ext
        (IsLocalRing.maximalIdeal R) (rs.length + 1)
        (ModuleCat.of R M) hsmul
        (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)))
        hK_support h_ext
    have hle : (ys.length : ℕ∞) ≤ localDepth R M := by
      unfold localDepth depth
      rw [dif_neg hmax]
      exact le_sSup ⟨ys, rfl, hysmem, hysreg⟩
    have hle' : (ys.length : ℕ∞) ≤ (rs.length : ℕ∞) := by
      simpa [hlen] using hle
    have hleNat : ys.length ≤ rs.length := by
      exact_mod_cast hle'
    have hcontra : rs.length + 1 ≤ rs.length := by
      rw [hyslen] at hleNat
      exact hleNat
    exact (Nat.not_succ_le_self rs.length) hcontra
  refine ⟨rs.length, hlen, not_subsingleton_iff_nontrivial.mp hnot, ?_⟩
  intro j hj
  exact not_nontrivial_iff_subsingleton.mpr (hvanish j hj)

private theorem localDepth_quotient_ge_sub_one
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] [Small.{v} R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M x) :
    localDepth R (QuotSMulTop x M) ≥ localDepth R M - 1 := by
  have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hspan : Ideal.span ({x} : Set R) ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem (I := IsLocalRing.maximalIdeal R)).mpr hx
  have hspan_smul : Ideal.span ({x} : Set R) • (⊤ : Submodule R M) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) :=
    Submodule.smul_mono_left hspan
  have hne : x • (⊤ : Submodule R M) ≠ ⊤ := by
    intro heq
    apply hmax
    apply top_unique
    calc
      (⊤ : Submodule R M) = x • (⊤ : Submodule R M) := heq.symm
      _ = Ideal.span ({x} : Set R) • (⊤ : Submodule R M) := by
        rw [Submodule.ideal_span_singleton_smul]
      _ ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := hspan_smul
  have hQinst : Nontrivial (QuotSMulTop x M) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  have exists_ne_zero_of_nontrivial {G : Type v} [AddCommGroup G]
      (hG : Nontrivial G) : ∃ z : G, z ≠ 0 := by
    rcases hG.exists_pair_ne with ⟨a, b, hab⟩
    by_cases ha : a = 0
    · refine ⟨b, ?_⟩
      intro hb
      apply hab
      simp [ha, hb]
    · exact ⟨a, ha⟩
  let S := (ModuleCat.of R M).smulShortComplex x
  have hS : S.ShortExact := hreg.smulShortComplex_shortExact
  let K := ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R))
  obtain ⟨iM, hiM, hM, hM'⟩ :=
    localDepth_eq_min_ext_universe (R := R) (M := M)
  obtain ⟨iQ, hiQ, hQ, hQ'⟩ :=
    @localDepth_eq_min_ext_universe R (QuotSMulTop x M) _ _ _ _ _ _ hQinst _
  by_contra h
  have hlt : localDepth R (QuotSMulTop x M) < localDepth R M - 1 :=
    lt_of_not_ge h
  have hlt' : (iQ : ℕ∞) < (iM : ℕ∞) - 1 := by
    simpa [hiQ, hiM] using hlt
  have hlt₁sub : iQ < iM - 1 := by
    exact_mod_cast hlt'
  have hlt₁ : iQ + 1 < iM := by omega
  have hM₁sub : Subsingleton (CategoryTheory.Abelian.Ext K (ModuleCat.of R M)
      (iQ + 1)) :=
    not_nontrivial_iff_subsingleton.mp (hM' (iQ + 1) hlt₁)
  have hM₂sub : Subsingleton (CategoryTheory.Abelian.Ext K (ModuleCat.of R M) iQ) :=
    not_nontrivial_iff_subsingleton.mp (hM' iQ (by omega))
  have hQnon : Nontrivial (CategoryTheory.Abelian.Ext K
      (ModuleCat.of R (QuotSMulTop x M)) iQ) := hQ
  have hX₁sub : Subsingleton (CategoryTheory.Abelian.Ext K S.X₁ (iQ + 1)) := by
    change Subsingleton (CategoryTheory.Abelian.Ext K (ModuleCat.of R M)
      (iQ + 1))
    exact hM₁sub
  have hX₂sub : Subsingleton (CategoryTheory.Abelian.Ext K S.X₂ iQ) := by
    change Subsingleton (CategoryTheory.Abelian.Ext K (ModuleCat.of R M) iQ)
    exact hM₂sub
  have hX₃non : Nontrivial (CategoryTheory.Abelian.Ext K S.X₃ iQ) := by
    change Nontrivial (CategoryTheory.Abelian.Ext K
      (ModuleCat.of R (QuotSMulTop x M)) iQ)
    exact hQnon
  obtain ⟨z, hz⟩ : ∃ z : CategoryTheory.Abelian.Ext K S.X₃ iQ, z ≠ 0 :=
    exists_ne_zero_of_nontrivial hX₃non
  have hzmap : z.comp hS.extClass rfl = 0 :=
    @Subsingleton.elim _ hX₁sub _ _
  obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₃
    K hS z rfl hzmap
  have hyzero : y = 0 := @Subsingleton.elim _ hX₂sub _ _
  apply hz
  simpa [hyzero] using hy.symm

/-! ## Regular elements and depth drops -/

/-- A nonzerodivisor in the maximal ideal lowers local depth by one. -/
theorem localDepth_drops_by_one
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M x) :
    localDepth R (QuotSMulTop x M) = localDepth R M - 1 := by
  have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hspan : Ideal.span ({x} : Set R) ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem (I := IsLocalRing.maximalIdeal R)).mpr hx
  have hspan_smul : Ideal.span ({x} : Set R) • (⊤ : Submodule R M) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) :=
    Submodule.smul_mono_left hspan
  have hne : x • (⊤ : Submodule R M) ≠ ⊤ := by
    intro heq
    apply hmax
    apply top_unique
    calc
      (⊤ : Submodule R M) = x • (⊤ : Submodule R M) := heq.symm
      _ = Ideal.span ({x} : Set R) • (⊤ : Submodule R M) := by
        rw [Submodule.ideal_span_singleton_smul]
      _ ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := hspan_smul
  have hQinst : Nontrivial (QuotSMulTop x M) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  let eM : ULift.{u} M ≃ₗ[R] M := ULift.moduleEquiv
  have hregLift : IsSMulRegular (ULift.{u} M) x := by
    intro a b hab
    apply eM.injective
    apply hreg
    simpa using congrArg eM hab
  have hlowerLift := localDepth_quotient_ge_sub_one
    (R := R) (M := ULift.{u} M) x hx hregLift
  have hmapx :
      Submodule.map eM.toLinearMap (x • (⊤ : Submodule R (ULift.{u} M))) =
        x • (⊤ : Submodule R M) := by
    rw [← Submodule.ideal_span_singleton_smul,
      ← Submodule.ideal_span_singleton_smul, Submodule.map_smul'',
      Submodule.map_top]
    simp
  let eQ : QuotSMulTop x (ULift.{u} M) ≃ₗ[R]
      ULift.{u} (QuotSMulTop x M) :=
    (Submodule.Quotient.equiv
      (x • (⊤ : Submodule R (ULift.{u} M)))
      (x • (⊤ : Submodule R M)) eM hmapx).trans
      (ULift.moduleEquiv (R := R) (M := QuotSMulTop x M)).symm
  have hdepthM : localDepth R (ULift.{u} M) = localDepth R M :=
    depth_congr eM (IsLocalRing.maximalIdeal R)
  have hdepthQLift :
      localDepth R (QuotSMulTop x (ULift.{u} M)) =
        localDepth R (ULift.{u} (QuotSMulTop x M)) :=
    depth_congr eQ (IsLocalRing.maximalIdeal R)
  have hdepthQ : localDepth R (ULift.{u} (QuotSMulTop x M)) =
      localDepth R (QuotSMulTop x M) :=
    depth_congr (ULift.moduleEquiv (R := R) (M := QuotSMulTop x M))
      (IsLocalRing.maximalIdeal R)
  have hlower : localDepth R (QuotSMulTop x M) ≥ localDepth R M - 1 := by
    calc
      localDepth R (QuotSMulTop x M) =
          localDepth R (ULift.{u} (QuotSMulTop x M)) := hdepthQ.symm
      _ = localDepth R (QuotSMulTop x (ULift.{u} M)) := hdepthQLift.symm
      _ ≥ localDepth R (ULift.{u} M) - 1 := hlowerLift
      _ = localDepth R M - 1 := by rw [hdepthM]
  have hmaxQ : IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R)
      (QuotSMulTop x M)
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hdepthtopQ : localDepth R (QuotSMulTop x M) < ⊤ :=
    @depth_lt_top_of_noetherian R _ (IsLocalRing.maximalIdeal R)
      (QuotSMulTop x M) _ _ _ _ hQinst hmaxQ
  have hdepth_memQ : localDepth R (QuotSMulTop x M) ∈
      {n : ℕ∞ | ∃ rs : List R,
        n = (rs.length : ℕ∞) ∧
          (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
            RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs} := by
    let : Nonempty {n : ℕ∞ | ∃ rs : List R,
        n = (rs.length : ℕ∞) ∧
          (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
            RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs} :=
      ⟨⟨0, ⟨[], by simp, by simp,
        RingTheory.Sequence.IsRegular.nil R (QuotSMulTop x M)⟩⟩⟩
    unfold localDepth depth
    rw [dif_neg hmaxQ]
    apply ENat.sSup_mem_of_nonempty_of_lt_top
    simpa [localDepth, depth, hmaxQ] using hdepthtopQ
  rcases hdepth_memQ with ⟨rs, hrs, hrs_mem, hrs_reg⟩
  have hrs_cons : RingTheory.Sequence.IsRegular M (x :: rs) :=
    RingTheory.Sequence.IsRegular.cons hreg hrs_reg
  have hcons_mem : ∀ r ∈ x :: rs, r ∈ IsLocalRing.maximalIdeal R := by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hx
    · exact hrs_mem r hr
  have hupper : localDepth R (QuotSMulTop x M) + 1 ≤ localDepth R M := by
    have hle : ((x :: rs).length : ℕ∞) ≤ localDepth R M := by
      unfold localDepth depth
      rw [dif_neg hmax]
      exact le_sSup ⟨x :: rs, rfl, hcons_mem, hrs_cons⟩
    simpa [hrs, List.length_cons, Nat.cast_add] using hle
  apply le_antisymm
  · exact ENat.le_sub_of_add_le_right ENat.one_ne_top hupper
  · exact hlower

/-!
Proof roadmap for the consumer
`Unit103/CohenMacaulayModules.lean:isCohenMacaulay_iff_of_isSMulRegular`:

* For each implication, derive `Nontrivial` for the module known to be
  Cohen--Macaulay using `Module.supportDim_ne_bot_iff_nontrivial`; after
  unfolding `IsCohenMacaulay`, its support dimension is a coerced `ℕ∞` and
  hence is not `⊥`.  In the reverse implication, pull nontriviality back from
  `QuotSMulTop x M` along `Submodule.mkQ_surjective`.
* Instantiate `localDepth_drops_by_one` with `R : Type u` and `M : Type v`.
  Combine that equality with
  `Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hx` from
  `Mathlib/RingTheory/KrullDimension/Regular.lean`.
* Rewrite the Cohen--Macaulay equality on the known side.  The two successor
  equalities identify the other depth and support dimension: eliminate the
  impossible `⊥` case using nontriviality, then cancel `+ 1` after reducing
  the remaining values to coerced `ℕ∞` terms.
-/

private theorem exists_regular_extension_to_localDepth
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∀ xs : List R, RingTheory.Sequence.IsRegular M xs →
      ∃ ys : List R,
        RingTheory.Sequence.IsRegular M (xs ++ ys) ∧
          localDepth R M = ((xs ++ ys).length : ℕ∞) := by
  intro xs
  induction xs generalizing M with
  | nil =>
      intro _
      have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
        smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
          (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
      have hdepthtop : localDepth R M < ⊤ :=
        depth_lt_top_of_noetherian (IsLocalRing.maximalIdeal R) M hmax
      have hdepth_mem : localDepth R M ∈
          {n : ℕ∞ | ∃ rs : List R,
            n = (rs.length : ℕ∞) ∧
              (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
                RingTheory.Sequence.IsRegular M rs} := by
        let : Nonempty {n : ℕ∞ | ∃ rs : List R,
            n = (rs.length : ℕ∞) ∧
              (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
                RingTheory.Sequence.IsRegular M rs} :=
          ⟨⟨0, ⟨[], by simp, by simp,
            RingTheory.Sequence.IsRegular.nil R M⟩⟩⟩
        unfold localDepth depth
        rw [dif_neg hmax]
        apply ENat.sSup_mem_of_nonempty_of_lt_top
        simpa [localDepth, depth, hmax] using hdepthtop
      rcases hdepth_mem with ⟨rs, hrs, _, hrs_reg⟩
      exact ⟨rs, by simpa using hrs_reg, hrs⟩
  | cons x xs ih =>
      intro hxs
      have hparts :=
        (RingTheory.Sequence.isRegular_cons_iff M x xs).mp hxs
      let Q := QuotSMulTop x M
      have hQ : Nontrivial Q := hparts.2.nontrivial
      obtain ⟨ys, hys_reg, hys_depth⟩ := @ih Q _ _ _ hQ hparts.2
      have hx : x ∈ IsLocalRing.maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hxunit
        have htop : x • (⊤ : Submodule R M) = ⊤ := by
          apply le_antisymm le_top
          intro z hz
          apply (Submodule.mem_smul_pointwise_iff_exists z x
            (⊤ : Submodule R M)).mpr
          obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hxunit
          exact ⟨y • z, Submodule.mem_top, by rw [smul_smul, hy, one_smul]⟩
        exact (Submodule.Quotient.nontrivial_iff.mp hparts.2.nontrivial) htop
      have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
        smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
          (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
      have hone : (1 : ℕ∞) ≤ localDepth R M := by
        unfold localDepth depth
        rw [dif_neg hmax]
        apply le_sSup
        refine ⟨[x], by simp, ?_, ?_⟩
        · intro r hr
          rcases List.mem_singleton.mp hr with rfl
          exact hx
        · exact RingTheory.Sequence.IsRegular.cons hparts.1
            (@RingTheory.Sequence.IsRegular.nil R Q _ _ _ hQ)
      have hdrop : localDepth R Q = localDepth R M - 1 :=
        localDepth_drops_by_one (R := R) (M := M) x hx hparts.1
      have hdepth : localDepth R M = localDepth R Q + 1 := by
        calc
          localDepth R M = (localDepth R M - 1) + 1 :=
            (tsub_add_cancel_of_le hone).symm
          _ = localDepth R Q + 1 := by rw [hdrop]
      refine ⟨ys, ?_, ?_⟩
      · simpa [List.cons_append] using
          (RingTheory.Sequence.IsRegular.cons hparts.1 hys_reg)
      · rw [hdepth, hys_depth]
        simp [List.cons_append, List.length_append, Nat.cast_add, add_assoc]

/-- Every regular sequence can be extended to one of maximal local depth. -/
theorem regular_sequence_extend_to_localDepth
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∀ xs : List R, RingTheory.Sequence.IsRegular M xs →
      ∃ ys : List R,
          RingTheory.Sequence.IsRegular M (xs ++ ys) ∧
          localDepth R M = ((xs ++ ys).length : ℕ∞) := by
  exact exists_regular_extension_to_localDepth

/-! ## Associated primes and localization -/

/-- An associated prime survives in a suitable power quotient after adjoining
an element and taking a minimal prime. -/
private lemma associated_subset_of_injective
    {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (hg : Function.Injective g) :
    Formalization.Books.Algebra.Unit63.associatedPrimes R M ⊆
      Formalization.Books.Algebra.Unit63.associatedPrimes R N := by
  intro p hp
  change ∃ m, (⊥ : Submodule R N).colon ({m} : Set N) = p.asIdeal
  change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
  obtain ⟨m, hm⟩ := hp
  refine ⟨g m, ?_⟩
  ext r
  rw [Submodule.mem_colon_singleton, ← hm, Submodule.mem_colon_singleton]
  change r • g m = 0 ↔ r • m = 0
  rw [← g.map_smul, map_eq_zero_iff g hg]

theorem associatedPrime_inherit_minimal_prime
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (p q : PrimeSpectrum R)
    (hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M)
    (hq : q.asIdeal ∈ (p.asIdeal ⊔ Ideal.span ({x} : Set R)).minimalPrimes) :
    ∃ n : ℕ, 1 ≤ n ∧
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R
        (QuotSMulTop (x ^ n) M) := by
  classical
  change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
  obtain ⟨m, hm⟩ := hp
  let N : Submodule R M := Submodule.span R ({m} : Set M)
  let I : Ideal R := Ideal.span ({x} : Set R)
  obtain ⟨c, hcpos, hc⟩ := Formalization.Books.Algebra.Unit51.artin_rees I N
  let n : ℕ := c + 1
  have hn : 1 ≤ n := by
    dsimp [n]
    omega
  have hpow : I ^ n • (⊤ : Submodule R M) = (x ^ n) • (⊤ : Submodule R M) := by
    rw [show I = Ideal.span ({x} : Set R) from rfl,
      Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  have hinter :
      ((x ^ n) • (⊤ : Submodule R M)) ⊓ N ≤ x • N := by
    calc
      ((x ^ n) • (⊤ : Submodule R M)) ⊓ N =
          (I ^ n • (⊤ : Submodule R M)) ⊓ N := by rw [hpow]
      _ = I ^ (n - c) • (I ^ c • (⊤ : Submodule R M) ⊓ N) :=
        hc n (by omega)
      _ ≤ I • N := by
        have hpow_one : n - c = 1 := by omega
        rw [hpow_one, pow_one, show I = Ideal.span ({x} : Set R) from rfl,
          Submodule.ideal_span_singleton_smul]
        calc
          x • (Ideal.span ({x} : Set R) ^ c •
              (⊤ : Submodule R M) ⊓ N) ≤ x • N :=
            smul_mono_right x
              (inf_le_right :
                (Ideal.span ({x} : Set R) ^ c •
                  (⊤ : Submodule R M) ⊓ N) ≤ N)
          _ = Ideal.span ({x} : Set R) • N := by
            rw [Submodule.ideal_span_singleton_smul]
      _ = x • N := by
        rw [show I = Ideal.span ({x} : Set R) from rfl,
          Submodule.ideal_span_singleton_smul]
  let K : Submodule R M := (x ^ n) • (⊤ : Submodule R M)
  let Q := QuotSMulTop (x ^ n) M
  let u : Q := Submodule.mkQ K m
  have hu_ann (r : R) : r • u = 0 → r ∈ q.asIdeal := by
    intro hru
    have hrK : r • m ∈ K := by
      apply (Submodule.Quotient.mk_eq_zero K).mp
      change (Submodule.mkQ K) (r • m) = 0
      rw [(Submodule.mkQ K).map_smul, hru]
    have hrN : r • m ∈ N := by
      exact N.smul_mem r (Submodule.mem_span_singleton_self m)
    have hrxN : r • m ∈ x • N := hinter ⟨hrK, hrN⟩
    obtain ⟨y, hy, hxy⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists (r • m) x N).mp hrxN
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hy
    have hrs : r - x * s ∈ p.asIdeal := by
      have hmem : r - x * s ∈ (⊥ : Submodule R M).colon ({m} : Set M) := by
        rw [Submodule.mem_colon_singleton]
        change (r - x * s) • m = 0
        have hrel : r • m = x • (s • m) := by
          rw [← hxy, hs]
        rw [sub_smul, hrel, smul_smul]
        simp
      rw [hm] at hmem
      exact hmem
    have hbaseq : p.asIdeal ⊔ I ≤ q.asIdeal := hq.1.2
    have hpeq : p.asIdeal ≤ q.asIdeal := le_sup_left.trans hbaseq
    have hxq : x ∈ q.asIdeal := by
      apply hbaseq
      exact (le_sup_right : I ≤ p.asIdeal ⊔ I)
        (Ideal.mem_span_singleton_self x)
    have hxs : x * s ∈ q.asIdeal := by
      simpa [mul_comm] using q.asIdeal.mul_mem_left s hxq
    rw [← sub_add_cancel r (x * s)]
    exact add_mem (hpeq hrs) hxs
  let B : Submodule R Q := Submodule.span R ({u} : Set Q)
  have hpanB : p.asIdeal ≤ Module.annihilator R B := by
    intro a ha
    change a ∈ B.annihilator
    rw [Submodule.mem_annihilator_span_singleton]
    apply (Submodule.Quotient.mk_eq_zero K).mpr
    change a • m ∈ K
    have ham : a • m = 0 := by
      have hmem : a ∈ (⊥ : Submodule R M).colon ({m} : Set M) := by
        rw [hm]
        exact ha
      exact (Submodule.mem_colon_singleton.mp hmem)
    rw [ham]
    exact K.zero_mem
  have hqB : q ∈ Module.support R B := by
    rw [Module.mem_support_iff']
    refine ⟨⟨u, Submodule.mem_span_singleton_self u⟩, ?_⟩
    intro r hr hzero
    apply hr
    exact hu_ann r (by simpa using congrArg Subtype.val hzero)
  have hqminB :
      Minimal (fun r : PrimeSpectrum R => r ∈ Module.support R B) q := by
    refine ⟨hqB, ?_⟩
    intro r hr hrq
    have hrannB : Module.annihilator R B ≤ r.asIdeal :=
      Module.annihilator_le_of_mem_support hr
    have hrQ : r ∈ Module.support R Q :=
      Module.support_subset_of_injective B.subtype B.subtype_injective hr
    have hrannQ : Module.annihilator R Q ≤ r.asIdeal :=
      Module.annihilator_le_of_mem_support hrQ
    have hrpow : x ^ n ∈ r.asIdeal :=
      hrannQ (QuotSMulTop.mem_annihilator M (x ^ n))
    have hxr : x ∈ r.asIdeal := r.isPrime.mem_of_pow_mem n hrpow
    have hpr : p.asIdeal ≤ r.asIdeal := hpanB.trans hrannB
    have hIr : I ≤ r.asIdeal := by
      exact Ideal.span_le.mpr (by
        intro a ha
        obtain rfl := Set.mem_singleton_iff.mp ha
        exact hxr)
    exact hq.2 ⟨r.isPrime, sup_le hpr hIr⟩ hrq
  have hqassB :
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R B :=
    Formalization.Books.Algebra.Unit63.ass_of_minimal_support q hqB hqminB
  have hqassQ :
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R Q :=
    associated_subset_of_injective B.subtype B.subtype_injective hqassB
  exact ⟨n, hn, hqassQ⟩

/-- The dimension of the quotient by a point of the support is bounded by
the support dimension. -/
theorem dim_quotient_le_supportDim_of_mem_support
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) :
    ringKrullDim (R ⧸ p.asIdeal) ≤ Module.supportDim R M := by
  have hann : Module.annihilator R M ≤ p.asIdeal :=
    Module.annihilator_le_of_mem_support hp
  let f : (R ⧸ Module.annihilator R M) →+* (R ⧸ p.asIdeal) :=
    Ideal.Quotient.lift (Module.annihilator R M)
      (Ideal.Quotient.mk p.asIdeal) (by
        intro r hr
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hann hr))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk (Module.annihilator R M) r, by simp [f]⟩
  calc
    ringKrullDim (R ⧸ p.asIdeal) ≤
        ringKrullDim (R ⧸ Module.annihilator R M) :=
      ringKrullDim_le_of_surjective f hf
    _ = Module.supportDim R M :=
      (Module.supportDim_eq_ringKrullDim_quotient_annihilator R M).symm

/-- The dimension of the quotient by an associated prime is bounded by the
support dimension. -/
theorem dim_of_associatedPrime_le_supportDim
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R)
    (hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) :
    ringKrullDim (R ⧸ p.asIdeal) ≤ Module.supportDim R M :=
  dim_quotient_le_supportDim_of_mem_support p
    (Formalization.Books.Algebra.Unit63.ass_subset_support hp)

/-- Every associated prime gives a quotient whose dimension bounds local
depth. -/
theorem localDepth_le_dim_of_associatedPrime
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (p : PrimeSpectrum R)
    (hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) :
      ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (R ⧸ p.asIdeal) := by
  classical
  have aux : ∀ n : ℕ, ∀ (M : Type v) [AddCommGroup M] [Module R M]
      [Module.Finite R M] (p : PrimeSpectrum R),
      localDepth R M = (n : ℕ∞) →
      p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M →
      ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤
        ringKrullDim (R ⧸ p.asIdeal) := by
    intro n
    induction n with
    | zero =>
        intro M _ _ _ p hdepth hp
        let : Nontrivial (R ⧸ p.asIdeal) :=
          Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
        rw [hdepth]
        exact ringKrullDim_nonneg_of_nontrivial
    | succ n ih =>
        intro M _ _ _ p hdepth hp
        have hp' := hp
        change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
        obtain ⟨m, hm⟩ := hp
        have hMnontr : Nontrivial M := by
          by_contra h
          have hsub : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
          let : Subsingleton M := hsub
          have hptop : p.asIdeal = ⊤ := by
            rw [← hm]
            ext r
            constructor
            · intro _
              simp
            · intro _
              rw [Submodule.mem_colon_singleton]
              exact Subsingleton.elim (r • m : M) (0 : M)
          exact p.isPrime.ne_top hptop
        have hreg_exists : ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧
            IsSMulRegular M x := by
          by_contra h
          have hzero : localDepth R M = 0 := by
            apply (depth_eq_zero_iff (IsLocalRing.maximalIdeal R) M).2
            refine ⟨hMnontr, ?_⟩
            simpa [not_exists] using h
          have hne : (n.succ : ℕ∞) ≠ 0 := by simp
          exact hne (hdepth.symm.trans hzero)
        obtain ⟨x, hx, hreg⟩ := hreg_exists
        have hxp : x ∉ p.asIdeal := by
          intro hxp
          have hxm : x • m = 0 := by
            change x • m ∈ (⊥ : Submodule R M)
            rw [← Submodule.mem_colon_singleton, hm]
            exact hxp
          have hmzero : m = 0 := by
            exact hreg (by simpa only [smul_zero] using hxm)
          subst hmzero
          have hptop : p.asIdeal = ⊤ := by
            rw [← hm]
            simp
          exact p.isPrime.ne_top hptop
        have hIlemax : p.asIdeal ⊔ Ideal.span ({x} : Set R) ≤
            IsLocalRing.maximalIdeal R := by
          refine sup_le (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) ?_
          exact Ideal.span_le.mpr fun y hy => by
            obtain rfl := Set.mem_singleton_iff.mp hy
            exact hx
        have hIne : p.asIdeal ⊔ Ideal.span ({x} : Set R) ≠ ⊤ := by
          intro htop
          have : (⊤ : Ideal R) ≤ IsLocalRing.maximalIdeal R := htop ▸ hIlemax
          exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_unique this)
        obtain ⟨qI, hqI⟩ := Ideal.nonempty_minimalPrimes hIne
        let q : PrimeSpectrum R := ⟨qI, hqI.isPrime⟩
        have hqmin : q.asIdeal ∈
            (p.asIdeal ⊔ Ideal.span ({x} : Set R)).minimalPrimes := hqI
        obtain ⟨k, hk, hqass⟩ := associatedPrime_inherit_minimal_prime
          (R := R) (M := M) x hx p q hp' hqmin
        have hxk : x ^ k ∈ IsLocalRing.maximalIdeal R := by
          exact Ideal.pow_mem_of_mem (I := IsLocalRing.maximalIdeal R) hx k hk
        have hregk : IsSMulRegular M (x ^ k) := by
          have hpow : ∀ j : ℕ, IsSMulRegular M (x ^ j) := by
            intro j
            induction j with
            | zero =>
                intro a b hab
                simpa using hab
            | succ j ihj =>
                intro a b hab
                apply ihj
                apply hreg
                simpa [pow_succ, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hab
          exact hpow k
        let Q := QuotSMulTop (x ^ k) M
        have hQdepth : localDepth R Q = (n : ℕ∞) := by
          have hdrop : localDepth R Q = localDepth R M - 1 :=
            localDepth_drops_by_one (R := R) (M := M) (x ^ k) hxk hregk
          rw [hdrop, hdepth]
          exact (ENat.natCast_sub (n + 1) 1).symm
        have hIH : ((localDepth R Q : ℕ∞) : WithBot ℕ∞) ≤
            ringKrullDim (R ⧸ q.asIdeal) := by
          exact ih Q q hQdepth hqass
        let : Nontrivial (R ⧸ p.asIdeal) :=
          Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
        let : IsLocalRing (R ⧸ p.asIdeal) :=
          IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal)
            Ideal.Quotient.mk_surjective
        let : IsLocalHom (Ideal.Quotient.mk p.asIdeal) :=
          IsLocalHom.of_surjective (Ideal.Quotient.mk p.asIdeal)
            Ideal.Quotient.mk_surjective
        have hbarmax : Ideal.Quotient.mk p.asIdeal x ∈
            IsLocalRing.maximalIdeal (R ⧸ p.asIdeal) := by
          change x ∈ (IsLocalRing.maximalIdeal (R ⧸ p.asIdeal)).comap
            (Ideal.Quotient.mk p.asIdeal)
          rw [IsLocalRing.maximalIdeal_comap]
          exact hx
        have hbarreg : Ideal.Quotient.mk p.asIdeal x ∈
            nonZeroDivisors (R ⧸ p.asIdeal) := by
          rw [mem_nonZeroDivisors_iff_ne_zero]
          exact (Ideal.Quotient.eq_zero_iff_mem).not.mpr hxp
        have hdim : ringKrullDim (R ⧸ p.asIdeal) =
            ringKrullDim ((R ⧸ p.asIdeal) ⧸
              Ideal.span ({Ideal.Quotient.mk p.asIdeal x} : Set (R ⧸ p.asIdeal))) + 1 :=
          Formalization.Books.Algebra.Unit60.one_equation_dimension_eq_of_nonzerodivisor
            (R ⧸ p.asIdeal) inferInstance (Ideal.Quotient.mk p.asIdeal x)
            hbarmax hbarreg
        have hpq : p.asIdeal ≤ q.asIdeal :=
          le_trans le_sup_left hqI.le
        let f : (R ⧸ p.asIdeal) →+* (R ⧸ q.asIdeal) :=
          Ideal.Quotient.lift p.asIdeal (Ideal.Quotient.mk q.asIdeal) (by
            intro a ha
            exact Ideal.Quotient.eq_zero_iff_mem.mpr
              (hqI.le ((show p.asIdeal ≤
                p.asIdeal ⊔ Ideal.span ({x} : Set R) from le_sup_left) ha)))
        have hfker : Ideal.span
            ({Ideal.Quotient.mk p.asIdeal x} : Set (R ⧸ p.asIdeal)) ≤ RingHom.ker f := by
          apply Ideal.span_le.mpr
          intro y hy
          obtain rfl := Set.mem_singleton_iff.mp hy
          change f (Ideal.Quotient.mk p.asIdeal x) = 0
          rw [Ideal.Quotient.lift_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr
            (hqI.le ((show Ideal.span ({x} : Set R) ≤
              p.asIdeal ⊔ Ideal.span ({x} : Set R) from le_sup_right)
              (Ideal.subset_span rfl)))
        let g := Ideal.Quotient.lift
          (Ideal.span ({Ideal.Quotient.mk p.asIdeal x} : Set (R ⧸ p.asIdeal))) f hfker
        have hfsurj : Function.Surjective f := by
          intro z
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
          exact ⟨Ideal.Quotient.mk p.asIdeal a, by simp [f]⟩
        have hgsurj : Function.Surjective g :=
          Ideal.Quotient.lift_surjective_of_surjective
            (I := Ideal.span
              ({Ideal.Quotient.mk p.asIdeal x} : Set (R ⧸ p.asIdeal)))
            (f := f) (fun a ha => hfker ha) hfsurj
        have hdimq : ringKrullDim (R ⧸ q.asIdeal) ≤
            ringKrullDim ((R ⧸ p.asIdeal) ⧸
              Ideal.span ({Ideal.Quotient.mk p.asIdeal x} : Set (R ⧸ p.asIdeal))) :=
          ringKrullDim_le_of_surjective g hgsurj
        have hstep : (n : WithBot ℕ∞) + 1 ≤ ringKrullDim (R ⧸ p.asIdeal) := by
          calc
            (n : WithBot ℕ∞) + 1 ≤
                ((localDepth R Q : ℕ∞) : WithBot ℕ∞) + 1 := by
              rw [hQdepth]
              simp only [WithBot.coe_natCast]
              exact le_rfl
            _ ≤ ringKrullDim (R ⧸ q.asIdeal) + 1 := by
              simpa [add_comm] using add_le_add_left hIH 1
            _ ≤ ringKrullDim ((R ⧸ p.asIdeal) ⧸
                Ideal.span ({Ideal.Quotient.mk p.asIdeal x} : Set (R ⧸ p.asIdeal))) + 1 :=
              by simpa [add_comm] using add_le_add_left hdimq 1
            _ = ringKrullDim (R ⧸ p.asIdeal) := hdim.symm
        rw [hdepth]
        have hcast : (n : WithBot ℕ∞) + 1 =
            (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
          change ((n : ℕ∞) : WithBot ℕ∞) +
            ((1 : ℕ∞) : WithBot ℕ∞) =
              (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)
          rw [← WithBot.coe_add]
          exact congrArg WithBot.some (ENat.natCast_add n 1).symm
        rw [hcast] at hstep
        exact hstep
  have hMnontr : Nontrivial M := by
    by_contra h
    have hsub : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
    let : Subsingleton M := hsub
    change ∃ m, (⊥ : Submodule R M).colon ({m} : Set M) = p.asIdeal at hp
    obtain ⟨m, hm⟩ := hp
    have hptop : p.asIdeal = ⊤ := by
      rw [← hm]
      ext r
      constructor
      · intro _
        simp
      · intro _
        rw [Submodule.mem_colon_singleton]
        exact Subsingleton.elim (r • m : M) (0 : M)
    exact p.isPrime.ne_top hptop
  let : Nontrivial M := hMnontr
  have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal R) M
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hlt : localDepth R M < ⊤ :=
    depth_lt_top_of_noetherian (IsLocalRing.maximalIdeal R) M hmax
  cases hdepth : localDepth R M with
  | top =>
      rw [hdepth] at hlt
      exact (lt_irrefl _ hlt).elim
  | coe n => simpa [hdepth] using aux n M p hdepth hp

/-!
Proof roadmaps for the other two unresolved consumers in
`Unit103/CohenMacaulayModules.lean`:

* `isCohenMacaulay_quotient_by_element`: first obtain `Nontrivial M` from
  `hM`.  If `g` is not regular, use
  `Unit63.iUnion_associatedPrimes_eq_module_zeroDivisors` from
  `Unit63/AssociatedPrimes.lean` to choose `p` with
  `p ∈ Unit63.associatedPrimes R M` and `g ∈ p.asIdeal`.  At universe
  instantiations `R : Type u`, `M : Type v`, the theorem immediately above
  and `dim_of_associatedPrime_le_supportDim` sandwich
  `ringKrullDim (R ⧸ p.asIdeal)` between the coerced local depth and
  `Module.supportDim R M`; `hM` makes the endpoints equal.  Furthermore,
  `Unit63.ass_subset_support hp` and `Module.support_quotSMulTop` put `p` in
  the support of `QuotSMulTop g M`, so
  `dim_quotient_le_supportDim_of_mem_support` bounds the same quotient-ring
  dimension by the cut support dimension.  Rewrite `supportCutDim R M [g]`
  with Unit103's local
  `supportDim_quotSMulTop_eq_supportCutDim_singleton`; `hcut` now contradicts
  the two dimension bounds (split `⊥`/`⊤`/coerced-finite cases before
  cancelling `+ 1`).  With regularity established, apply
  `localDepth_drops_by_one`; combine it with
  `Module.supportDim_quotSMulTop_succ_eq_supportDim` and `hM` to prove the
  quotient Cohen--Macaulay equality, then return the depth-drop equality.

* `regularSequence_of_supportDim_quotient_eq`: induct on `c`, writing a
  successor tuple as `Fin.cons (g 0) (Fin.tail g)` and rewriting its list via
  `List.ofFn_cons`.  Iterate
  `Module.supportDim_le_supportDim_quotSMulTop_succ` over the tail and use
  quotient surjectivity for the opposite inequalities.  Together with
  `hMdim`, `hquot`, and `c ≤ d`, these force the first cut to have support
  dimension `((d - 1 : ℕ) : ℕ∞)` coerced to `WithBot`; normalize to this
  common value type before cancelling successors.  Apply
  `isCohenMacaulay_quotient_by_element` to `g 0`, then the induction
  hypothesis to `Fin.tail g` on `QuotSMulTop (g 0) M`.  Transport the final
  quotient dimension through
  `Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner`; Unit103's local
  `supportCutDim_quotSMulTop_eq_cons` packages the same transport.  Assemble
  regularity with `RingTheory.Sequence.IsRegular.cons`, prepend `g 0` to the
  induction hypothesis's extension, and use the depth-drop equality to show
  that the resulting concatenation has length `localDepth R M`, as required
  by `IsMaximalRegularSequence`.
-/

/-- Localizing at a prime cannot reduce the sum of local depth and quotient
dimension below the original local depth. -/

theorem localDepth_localization_add_dim
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : Ideal R) [p.IsPrime] :
    ((localDepth (Localization.AtPrime p)
        (LocalizedModule.AtPrime p M) : ℕ∞) : WithBot ℕ∞) +
      ringKrullDim (R ⧸ p) ≥
      ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
  classical
  have htop_add : ∀ d : WithBot ℕ∞, (0 : WithBot ℕ∞) ≤ d →
      (⊤ : WithBot ℕ∞) + d = ⊤ := by
    intro d hd
    induction d using WithBot.recBotCoe with
    | bot => simp at hd
    | coe d =>
        change ((⊤ : ℕ∞) : WithBot ℕ∞) + (d : WithBot ℕ∞) =
          ((⊤ : ℕ∞) : WithBot ℕ∞)
        rfl
  by_cases hMsub : Subsingleton M
  · let : Subsingleton M := hMsub
    have hdepth : localDepth R M = ⊤ :=
      depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal R) M
    have hloc : localDepth (Localization.AtPrime p)
        (LocalizedModule.AtPrime p M) = ⊤ :=
      depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p M)
    rw [hdepth, hloc]
    change (⊤ : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≥ ⊤
    rw [htop_add (ringKrullDim (R ⧸ p)) ringKrullDim_nonneg_of_nontrivial]
  · have aux : ∀ n : ℕ, ∀ (M : Type u) [AddCommGroup M] [Module R M]
        [Module.Finite R M] (p : Ideal R) [p.IsPrime],
        localDepth R M = (n : ℕ∞) →
        ((localDepth (Localization.AtPrime p)
            (LocalizedModule.AtPrime p M) : ℕ∞) : WithBot ℕ∞) +
            ringKrullDim (R ⧸ p) ≥
          ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
      intro n
      induction n with
      | zero =>
          intro M _ _ _ p _ hdepth
          have : Nontrivial (R ⧸ p) :=
            Ideal.Quotient.nontrivial_iff.mpr (inferInstance : p.IsPrime).ne_top
          have hdim : (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
            exact ringKrullDim_nonneg_of_nontrivial
          rw [hdepth]
          exact add_nonneg (by simp) hdim
      | succ n ih =>
          intro M _ _ _ p hp hdepth
          have hMnontr : Nontrivial M := by
            by_contra h
            let : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
            have htop : localDepth R M = ⊤ :=
              depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal R) M
            have hcontra : (n.succ : ℕ∞) = ⊤ := hdepth ▸ htop
            exact ENat.natCast_ne_top _ hcontra
          have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
          by_cases hle :
              ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
          · exact hle.trans (by
              have hnonneg : (0 : WithBot ℕ∞) ≤
                  ((localDepth (Localization.AtPrime p)
                    (LocalizedModule.AtPrime p M) : ℕ∞) : WithBot ℕ∞) := by simp
              have h := add_le_add_left hnonneg
                (ringKrullDim (R ⧸ p))
              simpa [add_comm] using h)
          · have hnot_ass : ∀ q : PrimeSpectrum R,
                q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M →
                ¬ p ≤ q.asIdeal := by
              intro q hq hpq
              have hqdepth : ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤
                  ringKrullDim (R ⧸ q.asIdeal) :=
                localDepth_le_dim_of_associatedPrime q hq
              let fq : (R ⧸ p) →+* (R ⧸ q.asIdeal) :=
                Ideal.Quotient.lift p (Ideal.Quotient.mk q.asIdeal) (by
                  intro a ha
                  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpq ha))
              have hfq : Function.Surjective fq := by
                intro z
                obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
                exact ⟨Ideal.Quotient.mk p a, by simp [fq]⟩
              have hqdim : ringKrullDim (R ⧸ q.asIdeal) ≤
                  ringKrullDim (R ⧸ p) := ringKrullDim_le_of_surjective fq hfq
              exact hle (hqdepth.trans hqdim)
            obtain ⟨x, hx, hreg⟩ :=
              (Formalization.Books.Algebra.Unit63.ideal_contains_regular_iff
                (R := R) (M := M) p (IsLocalRing.le_maximalIdeal hp.ne_top)).2 hnot_ass
            have hxmax : x ∈ IsLocalRing.maximalIdeal R :=
              (IsLocalRing.le_maximalIdeal hp.ne_top) hx
            let Q := QuotSMulTop x M
            have hQnon : Nontrivial Q :=
              nontrivial_quotSMulTop_of_mem_maximalIdeal M hxmax
            have hQdepth : localDepth R Q = (n : ℕ∞) := by
              let : Nontrivial M := hMnontr
              have hdrop : localDepth R Q = localDepth R M - 1 :=
                localDepth_drops_by_one (R := R) (M := M) x hxmax hreg
              rw [hdrop, hdepth]
              exact (ENat.natCast_sub (n + 1) 1).symm
            have hIH :
                ((localDepth (Localization.AtPrime p)
                    (LocalizedModule.AtPrime p Q) : ℕ∞) : WithBot ℕ∞) +
                    ringKrullDim (R ⧸ p) ≥
                  ((localDepth R Q : ℕ∞) : WithBot ℕ∞) := by
              exact ih Q p hQdepth
            let S := Localization.AtPrime p
            let L := LocalizedModule.AtPrime p M
            let y : S := algebraMap R S x
            have hy : y ∈ IsLocalRing.maximalIdeal S := by
              change x ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime p)).under R
              rw [Localization.AtPrime.under_maximalIdeal]
              exact hx
            have hmapx : LocalizedModule.map p.primeCompl
                (LinearMap.lsmul R M x) =
                LinearMap.lsmul S L (algebraMap R S x) := by
              ext z
              obtain ⟨⟨z, s⟩, rfl⟩ :=
                IsLocalizedModule.mk'_surjective p.primeCompl
                  (LocalizedModule.mkLinearMap p.primeCompl M) z
              simp only [Function.uncurry_apply_pair]
              rw [← IsLocalizedModule.mk_eq_mk' (S := p.primeCompl)]
              rw [LocalizedModule.map_mk]
              simp only [LinearMap.lsmul_apply]
              change LocalizedModule.mk (x • z) s =
                (algebraMap R S x) • LocalizedModule.mk z s
              rw [IsScalarTower.algebraMap_smul S x]
              rw [LocalizedModule.smul'_mk]
            have hregLoc : IsSMulRegular L y := by
              intro a b hab
              have hlin : Function.Injective (LinearMap.lsmul R M x) := by
                intro c d hcd
                exact hreg (by simpa only [LinearMap.lsmul_apply, smul_zero] using hcd)
              apply LocalizedModule.map_injective p.primeCompl
                (LinearMap.lsmul R M x) hlin
              rw [hmapx]
              change (algebraMap R S x) • a = (algebraMap R S x) • b
              simpa [y] using hab
            by_cases hLsub : Subsingleton L
            · let : Subsingleton L := hLsub
              have htopL : localDepth S L = ⊤ :=
                depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal S) L
              rw [htopL]
              change (⊤ : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≥
                ((localDepth R M : ℕ∞) : WithBot ℕ∞)
              rw [htop_add (ringKrullDim (R ⧸ p))
                ringKrullDim_nonneg_of_nontrivial]
              exact le_top
            · let : Nontrivial L := not_subsingleton_iff_nontrivial.mp hLsub
              have hloc_drop : localDepth S (QuotSMulTop y L) =
                  localDepth S L - 1 :=
                localDepth_drops_by_one (R := S) (M := L) y hy hregLoc
              have hone : (1 : ℕ∞) ≤ localDepth S L := by
                unfold localDepth depth
                have hmax : IsLocalRing.maximalIdeal S •
                    (⊤ : Submodule S L) ≠ ⊤ :=
                  smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal S) L
                    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S))
                rw [dif_neg hmax]
                apply le_sSup
                refine ⟨[y], by simp, ?_, ?_⟩
                · intro r hr
                  rcases List.mem_singleton.mp hr with rfl
                  exact hy
                · exact RingTheory.Sequence.IsRegular.cons hregLoc
                    (@RingTheory.Sequence.IsRegular.nil S (QuotSMulTop y L) _ _ _
                      (nontrivial_quotSMulTop_of_mem_maximalIdeal L hy))
              have hlocQ : localDepth S
                  (LocalizedModule.AtPrime p Q) = localDepth S (QuotSMulTop y L) := by
                let e : LocalizedModule.AtPrime p Q ≃ₗ[S] QuotSMulTop y L := by
                  exact (localizedQuotientEquiv p.primeCompl
                    (x • (⊤ : Submodule R M))).symm ≪≫ₗ
                    Submodule.quotEquivOfEq _ _ (by
                      simp only [Submodule.localized]
                      rw [← Submodule.ideal_span_singleton_smul]
                      change (Ideal.span ({x} : Set R) • (⊤ : Submodule R M)).localized'
                        (Localization p.primeCompl) p.primeCompl
                        (LocalizedModule.mkLinearMap p.primeCompl M) =
                        y • (⊤ : Submodule S (LocalizedModule.AtPrime p M))
                      rw [Submodule.localized'_smul, Ideal.localized'_eq_map,
                        Submodule.localized'_top, Ideal.map_span,
                        Set.image_singleton,
                        Submodule.ideal_span_singleton_smul])
                exact depth_congr e (IsLocalRing.maximalIdeal S)
              have hlocal :
                  ((localDepth S L : ℕ∞) : WithBot ℕ∞) +
                      ringKrullDim (R ⧸ p) ≥
                    ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
                rw [hdepth]
                have hstep := add_le_add_right hIH (1 : WithBot ℕ∞)
                rw [hQdepth] at hstep
                rw [hlocQ, hloc_drop] at hstep
                have hcancel : localDepth S L - 1 + 1 = localDepth S L :=
                  tsub_add_cancel_of_le hone
                have hcancel' : (1 : WithBot ℕ∞) +
                    (((localDepth S L - 1 : ℕ∞) : ℕ∞) : WithBot ℕ∞) +
                      ringKrullDim (R ⧸ p) =
                    ((localDepth S L : ℕ∞) : WithBot ℕ∞) +
                      ringKrullDim (R ⧸ p) := by
                  rw [add_comm (1 : WithBot ℕ∞)]
                  change (((localDepth S L - 1 : ℕ∞) : WithBot ℕ∞) +
                    ((1 : ℕ∞) : WithBot ℕ∞)) + ringKrullDim (R ⧸ p) =
                    ((localDepth S L : ℕ∞) : WithBot ℕ∞) +
                      ringKrullDim (R ⧸ p)
                  rw [← WithBot.coe_add, hcancel]
                rw [← add_assoc, hcancel'] at hstep
                simpa [Nat.cast_add, WithBot.coe_add, add_assoc, add_left_comm,
                  add_comm] using hstep
              simpa [S, L, y] using hlocal
    let : Nontrivial M := not_subsingleton_iff_nontrivial.mp hMsub
    obtain ⟨n, hdepth, _⟩ := localDepth_eq_min_ext_universe (R := R) (M := M)
    exact aux n M p hdepth

/-! ## Finite ring extensions -/

/-- The minimum of the depths at all maximal localizations of a finite
`S`-module.  Using `MaximalSpectrum` is the canonical enumeration of maximal
ideals; `sInf` agrees with the finite minimum in the source and is also
well-defined for the subsingleton ring. -/
noncomputable def finiteExtensionMaximalDepth
    (S : Type u) (N : Type v) [CommRing S] [AddCommGroup N]
    [Module S N] [Module.Finite S N] : ℕ∞ :=
  sInf (Set.range fun m : MaximalSpectrum S =>
    localDepth (Localization.AtPrime m.asIdeal)
      (LocalizedModule.AtPrime m.asIdeal N))

/-- Finite descent of depth from a local Noetherian ring to a finite ring
extension. -/
theorem depth_goes_down_finite
    {R S N : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup N] [Module S N]
    [Module.Finite S N] (f : R →+* S) (hf : RingHom.Finite f) :
    finiteExtensionMaximalDepth S N =
      (letI : Algebra R S := f.toAlgebra
       letI : Module.Finite R S := hf
       letI : Module R N := Module.compHom N f
       letI : IsScalarTower R S N := SMul.comp.isScalarTower f
       letI : Module.Finite R N := Module.Finite.trans S N
       localDepth R N) := by
  classical
  let : Algebra R S := f.toAlgebra
  let : Module.Finite R S := hf
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let compDepth (X : Type u) [AddCommGroup X] [Module S X]
      [Module.Finite S X] : ℕ∞ :=
    letI : Module R X := Module.compHom X f
    letI : IsScalarTower R S X := SMul.comp.isScalarTower f
    letI : Module.Finite R X := Module.Finite.trans S X
    localDepth R X
  have aux : ∀ n : ℕ, ∀ (X : Type u) [AddCommGroup X]
      [Module S X] [Module.Finite S X],
      compDepth X = (n : ℕ∞) →
        finiteExtensionMaximalDepth S X = (n : ℕ∞) := by
    intro n
    induction n with
    | zero =>
        intro X _ _ _ hdepth
        let : Module R X := Module.compHom X f
        let : IsScalarTower R S X := SMul.comp.isScalarTower f
        let : Module.Finite R X := Module.Finite.trans S X
        have hdepth' : localDepth R X = 0 := by
          simpa [compDepth] using hdepth
        by_cases hsub : Subsingleton X
        · have htop : localDepth R X = ⊤ :=
            depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal R) X
          exact (ENat.natCast_ne_top 0 (hdepth'.symm.trans htop)).elim
        · let : Nontrivial X := not_subsingleton_iff_nontrivial.mp hsub
          have hno : ¬ ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧
              IsSMulRegular X x :=
            (depth_eq_zero_iff (IsLocalRing.maximalIdeal R) X).mp hdepth' |>.2
          have hnotall : ¬ ∀ q : PrimeSpectrum R,
              q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R X →
                ¬ IsLocalRing.maximalIdeal R ≤ q.asIdeal := by
            intro hall
            exact hno ((Formalization.Books.Algebra.Unit63.ideal_contains_regular_iff
              (R := R) (M := X) (IsLocalRing.maximalIdeal R)
              le_rfl).2 hall)
          obtain ⟨q, hq⟩ := not_forall.mp hnotall
          obtain ⟨hqass, hqmax⟩ := Classical.not_imp.mp hq
          have hqmax' : IsLocalRing.maximalIdeal R ≤ q.asIdeal := by
            by_contra h
            exact hqmax h
          have hqeq : q.asIdeal = IsLocalRing.maximalIdeal R :=
            le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) hqmax'
          let p₀ : PrimeSpectrum R :=
            ⟨IsLocalRing.maximalIdeal R,
              (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩
          have hqp₀ : q = p₀ := by
            apply PrimeSpectrum.ext
            exact hqeq
          have hp₀ : p₀ ∈
              Formalization.Books.Algebra.Unit63.associatedPrimes R X := by
            simpa [hqp₀] using hqass
          have hass_eq :=
            Formalization.Books.Algebra.Unit63.ass_functorial_eq_of_noetherian
              (φ := f) (M := X)
          change PrimeSpectrum.comap f ''
              Formalization.Books.Algebra.Unit63.associatedPrimes S X =
            Formalization.Books.Algebra.Unit63.associatedPrimes R X at hass_eq
          obtain ⟨qS, hqS, hqSmap⟩ := (hass_eq ▸ hp₀)
          have hqScomap : qS.asIdeal.comap f = IsLocalRing.maximalIdeal R := by
            simpa [p₀, PrimeSpectrum.comap_asIdeal] using
              congrArg PrimeSpectrum.asIdeal hqSmap
          have hqSmax : qS.asIdeal.IsMaximal :=
            Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'
              f hf.to_isIntegral qS.asIdeal (by
                rw [hqScomap]
                exact IsLocalRing.maximalIdeal.isMaximal R)
          let m : MaximalSpectrum S := ⟨qS.asIdeal, hqSmax⟩
          let T := Localization.AtPrime m.asIdeal
          let L := LocalizedModule.AtPrime m.asIdeal X
          have hLass :
              IsLocalRing.closedPoint T ∈
                Formalization.Books.Algebra.Unit63.associatedPrimes T L := by
            simpa [T, L, m] using
              (Formalization.Books.Algebra.Unit63.associated_primes_localize_at_prime
                qS).1 hqS
          change ∃ z, (⊥ : Submodule T L).colon ({z} : Set L) =
            IsLocalRing.maximalIdeal T at hLass
          obtain ⟨z, hz⟩ := hLass
          have hzne : z ≠ 0 := by
            intro hz0
            have htop : (⊤ : Ideal T) ≤ IsLocalRing.maximalIdeal T := by
              rw [← hz, hz0, Submodule.colon_singleton_zero]
            exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top (top_unique htop)
          have hnoL : ¬ ∃ y : T, y ∈ IsLocalRing.maximalIdeal T ∧
              IsSMulRegular L y := by
            rintro ⟨y, hy, hyreg⟩
            have hyz : y • z = 0 := by
              change y • z ∈ (⊥ : Submodule T L)
              rw [← Submodule.mem_colon_singleton, hz]
              exact hy
            apply hzne
            apply hyreg
            change y • z = y • (0 : L)
            simpa only [smul_zero] using hyz
          have hdepthL : localDepth T L = 0 := by
            apply (depth_eq_zero_iff (IsLocalRing.maximalIdeal T) L).2
            let : Nontrivial L := ⟨⟨z, 0, hzne⟩⟩
            exact ⟨inferInstance, hnoL⟩
          apply le_antisymm
          · unfold finiteExtensionMaximalDepth
            have hmemb :
                localDepth (Localization.AtPrime m.asIdeal)
                    (LocalizedModule.AtPrime m.asIdeal X) ∈
                  Set.range (fun m : MaximalSpectrum S =>
                    localDepth (Localization.AtPrime m.asIdeal)
                      (LocalizedModule.AtPrime m.asIdeal X)) :=
              ⟨m, rfl⟩
            exact (sInf_le hmemb).trans_eq (by simpa [T, L] using hdepthL)
          · exact bot_le
    | succ n ih =>
        intro X _ _ _ hdepth
        let : Module R X := Module.compHom X f
        let : IsScalarTower R S X := SMul.comp.isScalarTower f
        let : Module.Finite R X := Module.Finite.trans S X
        have hdepth' : localDepth R X = (n.succ : ℕ∞) := by
          simpa [compDepth] using hdepth
        have hXnontr : Nontrivial X := by
          by_contra h
          let : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
          have htop : localDepth R X = ⊤ :=
            depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal R) X
          exact ENat.natCast_ne_top _ (hdepth'.symm.trans htop)
        let : Nontrivial X := hXnontr
        have hreg_exists : ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧
            IsSMulRegular X x := by
          by_contra h
          have hzero : localDepth R X = 0 := by
            apply (depth_eq_zero_iff (IsLocalRing.maximalIdeal R) X).2
            refine ⟨hXnontr, ?_⟩
            simpa [not_exists] using h
          have hne : (n.succ : ℕ∞) ≠ 0 := by simp
          exact hne (hdepth'.symm.trans hzero)
        obtain ⟨x, hx, hreg⟩ := hreg_exists
        let Q := QuotSMulTop (algebraMap R S x) X
        let : Module R Q := Module.compHom Q f
        let : IsScalarTower R S Q := SMul.comp.isScalarTower f
        let : Module.Finite R Q := Module.Finite.trans S Q
        have hP :
            (algebraMap R S x • (⊤ : Submodule S X)).restrictScalars R =
              x • (⊤ : Submodule R X) := by
          simpa using
            (element_smul_restrictScalars (R := R) (S := S) (M := X)
              x (⊤ : Submodule S X))
        let eQ : QuotSMulTop x X ≃ₗ[R] Q :=
          Submodule.quotEquivOfEq _ _ hP.symm ≪≫ₗ
            Submodule.Quotient.restrictScalarsEquiv R
              (algebraMap R S x • (⊤ : Submodule S X))
        have hQdepth0 : localDepth R (QuotSMulTop x X) = (n : ℕ∞) := by
          have hdrop : localDepth R (QuotSMulTop x X) =
              localDepth R X - 1 :=
            localDepth_drops_by_one (R := R) (M := X) x hx hreg
          rw [hdrop, hdepth']
          exact (ENat.natCast_sub (n + 1) 1).symm
        have hQdepth : localDepth R Q = (n : ℕ∞) := by
          change depth (IsLocalRing.maximalIdeal R) Q = (n : ℕ∞)
          rw [← depth_congr eQ (IsLocalRing.maximalIdeal R)]
          simpa [localDepth] using hQdepth0
        have hIH : finiteExtensionMaximalDepth S Q = (n : ℕ∞) :=
          ih Q hQdepth
        have hmaxcomap : ∀ m : MaximalSpectrum S,
            m.asIdeal.comap f = IsLocalRing.maximalIdeal R := by
          intro m
          exact IsLocalRing.eq_maximalIdeal
            (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
              f hf.to_isIntegral m.asIdeal)
        have hlocal_lower : ∀ m : MaximalSpectrum S,
            (n.succ : ℕ∞) ≤ localDepth (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal X) := by
          intro m
          let T := Localization.AtPrime m.asIdeal
          let L := LocalizedModule.AtPrime m.asIdeal X
          let y : T := algebraMap R T x
          have hy : y ∈ IsLocalRing.maximalIdeal T := by
            change x ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)).under R
            rw [← Ideal.under_under (B := S),
              Localization.AtPrime.under_maximalIdeal]
            change x ∈ m.asIdeal.comap f
            rw [hmaxcomap m]
            exact hx
          have hregS : IsSMulRegular X (algebraMap R S x) := by
            intro a b hab
            apply hreg
            simpa only [IsScalarTower.algebraMap_smul S x] using hab
          have hmapx : LocalizedModule.map m.asIdeal.primeCompl
                (LinearMap.lsmul S X (algebraMap R S x)) =
              LinearMap.lsmul T L (algebraMap S T (algebraMap R S x)) := by
            ext z
            obtain ⟨⟨z, s⟩, rfl⟩ :=
              IsLocalizedModule.mk'_surjective m.asIdeal.primeCompl
                (LocalizedModule.mkLinearMap m.asIdeal.primeCompl X) z
            simp only [Function.uncurry_apply_pair]
            rw [← IsLocalizedModule.mk_eq_mk' (S := m.asIdeal.primeCompl)]
            rw [LocalizedModule.map_mk]
            simp only [LinearMap.lsmul_apply]
            change LocalizedModule.mk ((algebraMap R S x) • z) s =
              (algebraMap S T (algebraMap R S x)) • LocalizedModule.mk z s
            rw [IsScalarTower.algebraMap_smul T (algebraMap R S x)]
            rw [LocalizedModule.smul'_mk]
          have hregLoc : IsSMulRegular L y := by
            have hlin : Function.Injective
                (LinearMap.lsmul S X (algebraMap R S x)) := hregS
            have hregLoc' : IsSMulRegular L
                (algebraMap S T (algebraMap R S x)) := by
              change Function.Injective
                (LinearMap.lsmul T L (algebraMap S T (algebraMap R S x)))
              rw [← hmapx]
              exact LocalizedModule.map_injective m.asIdeal.primeCompl
                (LinearMap.lsmul S X (algebraMap R S x)) hlin
            change IsSMulRegular L (algebraMap R T x)
            rw [IsScalarTower.algebraMap_eq R S T]
            exact hregLoc'
          have hlocQ : localDepth T
                (LocalizedModule.AtPrime m.asIdeal Q) =
              localDepth T (QuotSMulTop y L) := by
            let e : LocalizedModule.AtPrime m.asIdeal Q ≃ₗ[T]
                QuotSMulTop y L := by
              exact (localizedQuotientEquiv m.asIdeal.primeCompl
                  (algebraMap R S x • (⊤ : Submodule S X))).symm ≪≫ₗ
                Submodule.quotEquivOfEq _ _ (by
                  simp only [Submodule.localized]
                  rw [← Submodule.ideal_span_singleton_smul]
                  change (Ideal.span ({algebraMap R S x} : Set S) •
                      (⊤ : Submodule S X)).localized'
                    (Localization m.asIdeal.primeCompl) m.asIdeal.primeCompl
                    (LocalizedModule.mkLinearMap m.asIdeal.primeCompl X) =
                    y • (⊤ : Submodule T L)
                  rw [Submodule.localized'_smul, Ideal.localized'_eq_map,
                    Submodule.localized'_top, Ideal.map_span,
                    Set.image_singleton,
                    Submodule.ideal_span_singleton_smul]
                  change (algebraMap S T (algebraMap R S x)) •
                      (⊤ : Submodule T L) =
                    (algebraMap R T x) • (⊤ : Submodule T L)
                  rw [IsScalarTower.algebraMap_eq R S T]
                  rfl)
            exact depth_congr e (IsLocalRing.maximalIdeal T)
          have hIHm : (n : ℕ∞) ≤
                localDepth T (LocalizedModule.AtPrime m.asIdeal Q) := by
            rw [← hIH]
            unfold finiteExtensionMaximalDepth
            exact sInf_le ⟨m, rfl⟩
          by_cases hLsub : Subsingleton L
          · have htop : localDepth T L = ⊤ :=
              depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal T) L
            change (n.succ : ℕ∞) ≤ localDepth T L
            simp [htop]
          · let : Nontrivial L := not_subsingleton_iff_nontrivial.mp hLsub
            have hone : (1 : ℕ∞) ≤ localDepth T L := by
              unfold localDepth depth
              have hmax : IsLocalRing.maximalIdeal T •
                    (⊤ : Submodule T L) ≠ ⊤ :=
                smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal T) L
                  (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal T))
              rw [dif_neg hmax]
              apply le_sSup
              refine ⟨[y], by simp, ?_, ?_⟩
              · intro z hz
                rcases List.mem_singleton.mp hz with rfl
                exact hy
              · exact RingTheory.Sequence.IsRegular.cons hregLoc
                  (@RingTheory.Sequence.IsRegular.nil T (QuotSMulTop y L) _ _ _
                    (nontrivial_quotSMulTop_of_mem_maximalIdeal L hy))
            have hdrop : localDepth T (QuotSMulTop y L) =
                localDepth T L - 1 :=
              localDepth_drops_by_one (R := T) (M := L) y hy hregLoc
            rw [hlocQ, hdrop] at hIHm
            cases hd : localDepth T L with
            | top => simp
            | coe d =>
                rw [hd] at hIHm
                rw [hd] at hone
                have hnat : n ≤ d - 1 := by exact_mod_cast hIHm
                have hdpos : 0 < d := by exact_mod_cast hone
                have hnat' : n + 1 ≤ d :=
                  Nat.lt_iff_add_one_le.mp ((Nat.le_sub_one_iff_lt hdpos).mp hnat)
                exact_mod_cast hnat'
        have hlower : (n.succ : ℕ∞) ≤
            finiteExtensionMaximalDepth S X := by
          unfold finiteExtensionMaximalDepth
          refine le_sInf ?_
          rintro _ ⟨m, rfl⟩
          exact hlocal_lower m
        have hQ_exists : ∃ m : MaximalSpectrum S,
            localDepth (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal Q) ≤ (n : ℕ∞) := by
          by_contra hnone
          have hQ_lower : (n.succ : ℕ∞) ≤
              finiteExtensionMaximalDepth S Q := by
            unfold finiteExtensionMaximalDepth
            refine le_sInf ?_
            rintro _ ⟨m, rfl⟩
            change (n.succ : ℕ∞) ≤ localDepth (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal Q)
            have hnotle : ¬ localDepth (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal Q) ≤ (n : ℕ∞) := by
              intro hle
              exact hnone ⟨m, hle⟩
            have hlt := lt_of_not_ge hnotle
            cases hd : localDepth (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal Q) with
            | top => simp
            | coe d =>
                rw [hd] at hlt
                have hnat : n < d := by exact_mod_cast hlt
                have hnat' : n + 1 ≤ d := Nat.lt_iff_add_one_le.mp hnat
                exact_mod_cast hnat'
          have : (n.succ : ℕ∞) ≤ (n : ℕ∞) := hQ_lower.trans_eq hIH
          exact (by
            have hgt : (n : ℕ∞) < (n.succ : ℕ∞) := by
              exact_mod_cast Nat.lt_succ_self n
            have hne : ¬((n.succ : ℕ∞) ≤ (n : ℕ∞)) := not_le_of_gt hgt
            exact hne this)
        obtain ⟨m, hm⟩ := hQ_exists
        let T := Localization.AtPrime m.asIdeal
        let L := LocalizedModule.AtPrime m.asIdeal X
        let y : T := algebraMap R T x
        have hy : y ∈ IsLocalRing.maximalIdeal T := by
          change x ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)).under R
          rw [← Ideal.under_under (B := S),
            Localization.AtPrime.under_maximalIdeal]
          change x ∈ m.asIdeal.comap f
          rw [hmaxcomap m]
          exact hx
        have hregS : IsSMulRegular X (algebraMap R S x) := by
          intro a b hab
          apply hreg
          simpa only [IsScalarTower.algebraMap_smul S x] using hab
        have hmapx : LocalizedModule.map m.asIdeal.primeCompl
              (LinearMap.lsmul S X (algebraMap R S x)) =
            LinearMap.lsmul T L (algebraMap S T (algebraMap R S x)) := by
          ext z
          obtain ⟨⟨z, s⟩, rfl⟩ :=
            IsLocalizedModule.mk'_surjective m.asIdeal.primeCompl
              (LocalizedModule.mkLinearMap m.asIdeal.primeCompl X) z
          simp only [Function.uncurry_apply_pair]
          rw [← IsLocalizedModule.mk_eq_mk' (S := m.asIdeal.primeCompl)]
          rw [LocalizedModule.map_mk]
          simp only [LinearMap.lsmul_apply]
          change LocalizedModule.mk ((algebraMap R S x) • z) s =
            (algebraMap S T (algebraMap R S x)) • LocalizedModule.mk z s
          rw [IsScalarTower.algebraMap_smul T (algebraMap R S x)]
          rw [LocalizedModule.smul'_mk]
        have hregLoc : IsSMulRegular L y := by
          have hlin : Function.Injective
              (LinearMap.lsmul S X (algebraMap R S x)) := hregS
          have hregLoc' : IsSMulRegular L
              (algebraMap S T (algebraMap R S x)) := by
            change Function.Injective
              (LinearMap.lsmul T L (algebraMap S T (algebraMap R S x)))
            rw [← hmapx]
            exact LocalizedModule.map_injective m.asIdeal.primeCompl
              (LinearMap.lsmul S X (algebraMap R S x)) hlin
          change IsSMulRegular L (algebraMap R T x)
          rw [IsScalarTower.algebraMap_eq R S T]
          exact hregLoc'
        have hlocQ : localDepth T
              (LocalizedModule.AtPrime m.asIdeal Q) =
            localDepth T (QuotSMulTop y L) := by
          let e : LocalizedModule.AtPrime m.asIdeal Q ≃ₗ[T]
              QuotSMulTop y L := by
            exact (localizedQuotientEquiv m.asIdeal.primeCompl
                (algebraMap R S x • (⊤ : Submodule S X))).symm ≪≫ₗ
              Submodule.quotEquivOfEq _ _ (by
                simp only [Submodule.localized]
                rw [← Submodule.ideal_span_singleton_smul]
                change (Ideal.span ({algebraMap R S x} : Set S) •
                    (⊤ : Submodule S X)).localized'
                  (Localization m.asIdeal.primeCompl) m.asIdeal.primeCompl
                  (LocalizedModule.mkLinearMap m.asIdeal.primeCompl X) =
                  y • (⊤ : Submodule T L)
                rw [Submodule.localized'_smul, Ideal.localized'_eq_map,
                  Submodule.localized'_top, Ideal.map_span,
                  Set.image_singleton,
                  Submodule.ideal_span_singleton_smul]
                change (algebraMap S T (algebraMap R S x)) •
                    (⊤ : Submodule T L) =
                  (algebraMap R T x) • (⊤ : Submodule T L)
                rw [IsScalarTower.algebraMap_eq R S T]
                rfl)
          exact depth_congr e (IsLocalRing.maximalIdeal T)
        have hLsub : ¬ Subsingleton L := by
          intro hsub
          let : Subsingleton L := hsub
          have htop : localDepth T (QuotSMulTop y L) = ⊤ :=
            depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal T)
              (QuotSMulTop y L)
          have htopQ : localDepth T
              (LocalizedModule.AtPrime m.asIdeal Q) = ⊤ := hlocQ.trans htop
          rw [htopQ] at hm
          exact ENat.natCast_ne_top n (top_unique hm)
        let : Nontrivial L := not_subsingleton_iff_nontrivial.mp hLsub
        have hdrop : localDepth T (QuotSMulTop y L) =
            localDepth T L - 1 :=
          localDepth_drops_by_one (R := T) (M := L) y hy hregLoc
        have hone : (1 : ℕ∞) ≤ localDepth T L := by
          unfold localDepth depth
          have hmax : IsLocalRing.maximalIdeal T •
                (⊤ : Submodule T L) ≠ ⊤ :=
            smul_top_ne_top_of_le_ring_jacobson (IsLocalRing.maximalIdeal T) L
              (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal T))
          rw [dif_neg hmax]
          apply le_sSup
          refine ⟨[y], by simp, ?_, ?_⟩
          · intro z hz
            rcases List.mem_singleton.mp hz with rfl
            exact hy
          · exact RingTheory.Sequence.IsRegular.cons hregLoc
              (@RingTheory.Sequence.IsRegular.nil T (QuotSMulTop y L) _ _ _
                (nontrivial_quotSMulTop_of_mem_maximalIdeal L hy))
        have hupper : localDepth T L ≤ (n.succ : ℕ∞) := by
          have hqle : localDepth T (QuotSMulTop y L) ≤ (n : ℕ∞) := by
            rw [← hlocQ]
            exact hm
          rw [hdrop] at hqle
          have hstep := add_le_add_right hqle (1 : ℕ∞)
          have hcancel : 1 + (localDepth T L - 1) = localDepth T L := by
            rw [add_comm, tsub_add_cancel_of_le hone]
          rw [hcancel] at hstep
          simpa [Nat.cast_add, add_comm] using hstep
        have hupper' : finiteExtensionMaximalDepth S X ≤
            (n.succ : ℕ∞) := by
          unfold finiteExtensionMaximalDepth
          have hmemb :
              localDepth (Localization.AtPrime m.asIdeal)
                  (LocalizedModule.AtPrime m.asIdeal X) ∈
                Set.range (fun m : MaximalSpectrum S =>
                  localDepth (Localization.AtPrime m.asIdeal)
                    (LocalizedModule.AtPrime m.asIdeal X)) :=
            ⟨m, rfl⟩
          exact (sInf_le hmemb).trans (by simpa [T, L] using hupper)
        exact le_antisymm hupper' hlower
  let : Module R N := Module.compHom N f
  let : IsScalarTower R S N := SMul.comp.isScalarTower f
  let : Module.Finite R N := Module.Finite.trans S N
  by_cases hNsub : Subsingleton N
  · let : Subsingleton N := hNsub
    have hfinite : finiteExtensionMaximalDepth S N = ⊤ := by
      unfold finiteExtensionMaximalDepth
      apply le_antisymm le_top
      refine le_sInf ?_
      rintro _ ⟨m, rfl⟩
      unfold localDepth
      exact le_of_eq (depth_eq_top_of_subsingleton
        (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal))
        (LocalizedModule.AtPrime m.asIdeal N)).symm
    have hlocal : localDepth R N = ⊤ :=
      depth_eq_top_of_subsingleton (IsLocalRing.maximalIdeal R) N
    rw [hfinite, hlocal]
  · let : Nontrivial N := not_subsingleton_iff_nontrivial.mp hNsub
    obtain ⟨n, hdepth, _⟩ := localDepth_eq_min_ext_universe (R := R) (M := N)
    simpa [compDepth, hdepth] using aux n N hdepth

end

end Formalization.Books.Algebra.Unit72
