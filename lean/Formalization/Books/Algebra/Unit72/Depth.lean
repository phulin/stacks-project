import Formalization.Books.Algebra.Unit60
import Formalization.Books.Algebra.Unit63
import Formalization.Books.Algebra.Unit68
import Formalization.Books.Algebra.Unit71
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

universe u v

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
              simpa [sub_smul, hfm]⟩
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
              · letI : Subsingleton (QuotSMulTop r N) := by
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
            letI : Nontrivial (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) :=
              hreg.quot_ofList_smul_nontrivial ⊤
            have hqne : Module.supportDim R
                (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ≠ ⊥ :=
              Module.supportDim_ne_bot_of_nontrivial R _
            have hqzero : (0 : WithBot ℕ∞) ≤ Module.supportDim R
                (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) := by
              cases hq : Module.supportDim R
                  (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) with
              | bot => exact (hqne hq).elim
              | coe q => simp [hq]
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
  letI : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hIM
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := Q)
  change p ∈ Module.support R (M ⧸ (I • (⊤ : Submodule R M))) at hp
  rw [Module.support_quotient] at hp
  have hpM : p ∈ Module.support R M := hp.1
  have hpI : I ≤ p.asIdeal := by
    exact hp.2
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal M
  letI : Nontrivial N := Module.mem_support_iff.mp hpM
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
        letI := hqnon
        exact Module.supportDim_ne_bot_of_nontrivial S _
      have hqzero : (0 : WithBot ℕ∞) ≤ Module.supportDim S
          (N ⧸ (Ideal.ofList (rs.map (algebraMap R S)) •
            (⊤ : Submodule S N))) := by
        cases hq : Module.supportDim S
            (N ⧸ (Ideal.ofList (rs.map (algebraMap R S)) •
              (⊤ : Submodule S N))) with
        | bot => exact (hqne hq).elim
        | coe q => simp [hq]
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
    letI : Nonempty {n : ℕ∞ | ∃ rs : List R,
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
      simpa [hyslen] using hleNat
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
  sorry

/-! ## Regular elements and depth drops -/

/-- A nonzerodivisor in the maximal ideal lowers local depth by one. -/
theorem localDepth_drops_by_one
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M x) :
    localDepth R (QuotSMulTop x M) = localDepth R M - 1 := by
  sorry

/-- Every regular sequence can be extended to one of maximal local depth. -/
theorem regular_sequence_extend_to_localDepth
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∀ xs : List R, RingTheory.Sequence.IsRegular M xs →
      ∃ ys : List R,
        RingTheory.Sequence.IsRegular M (xs ++ ys) ∧
          localDepth R M = ((xs ++ ys).length : ℕ∞) := by
  sorry

/-! ## Associated primes and localization -/

/-- An associated prime survives in a suitable power quotient after adjoining
an element and taking a minimal prime. -/
theorem associatedPrime_inherit_minimal_prime
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (p q : PrimeSpectrum R)
    (hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M)
    (hq : q.asIdeal ∈ (p.asIdeal ⊔ Ideal.span ({x} : Set R)).minimalPrimes) :
    ∃ n : ℕ, 1 ≤ n ∧
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R
        (QuotSMulTop (x ^ n) M) := by
  sorry

/-- Every associated prime gives a quotient whose dimension bounds local
depth. -/
theorem localDepth_le_dim_of_associatedPrime
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (p : PrimeSpectrum R)
    (hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) :
    ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (R ⧸ p.asIdeal) := by
  sorry

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
  sorry

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
  sorry

end

end Formalization.Books.Algebra.Unit72
