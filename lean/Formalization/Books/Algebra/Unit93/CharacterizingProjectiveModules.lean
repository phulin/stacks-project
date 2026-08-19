import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Order.Filter.Cofinite
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Commutative Algebra, Chapter 93: Characterizing projective modules

This file formalizes the first source section.  Projectivity, flatness,
countable generation, direct sums, Mittag--Lefflerness, and universal
injectivity use the canonical interfaces from earlier chapters.
-/

namespace Formalization.Books.Algebra.Unit93

open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit84
open Formalization.Books.Algebra.Unit88
open scoped BigOperators DirectSum TensorProduct

universe u v w

noncomputable section

/-! ## Countably generated projective modules -/

/-- A flat, Mittag--Leffler, countably generated module is projective. -/
theorem projective_of_flat_of_mittagLeffler_of_countablyGenerated
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hflat : Module.Flat R M)
    (hML : IsMittagLefflerModule (ModuleCat.of R M))
    (hcountable : Module.IsCountablyGenerated R M) :
    Module.Projective R M := by
  by_contra hprojective
  exact
    (Formalization.Books.Algebra.Unit91.flat_countablyGenerated_nonprojective_not_mittagLeffler
      hflat hcountable hprojective) hML

/-! ## The power-series warning -/

/-- The coefficient condition defining the submodule used in the source's
integer power-series counterexample. -/
def integerPowerSeriesCondition (p : ℕ) (f : PowerSeries ℤ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∀ᶠ i in Filter.cofinite, (p : ℤ) ^ m ∣ PowerSeries.coeff i f

/-- The submodule of power series whose coefficients are eventually divisible
by every positive power of `p`.  The carrier characterization is recorded by
`integerPowerSeriesSubmodule_carrier` below. -/
def integerPowerSeriesSubmodule (p : ℕ) : Submodule ℤ (PowerSeries ℤ) :=
  Submodule.span ℤ {f : PowerSeries ℤ | integerPowerSeriesCondition p f}

/-- The span construction has exactly the coefficient condition from the
source. -/
theorem integerPowerSeriesSubmodule_carrier (p : ℕ) (f : PowerSeries ℤ) :
    f ∈ integerPowerSeriesSubmodule p ↔ integerPowerSeriesCondition p f := by
  let U : Submodule ℤ (PowerSeries ℤ) :=
    { carrier := {f | integerPowerSeriesCondition p f}
      zero_mem' := by
        intro m _
        exact Filter.Eventually.of_forall (fun i => by simp)
      add_mem' := by
        intro f g hf hg m hm
        filter_upwards [hf m hm, hg m hm] with i hfi hgi
        exact dvd_add hfi hgi
      smul_mem' := by
        intro c f hf m hm
        filter_upwards [hf m hm] with i hi
        change (p : ℤ) ^ m ∣ c * PowerSeries.coeff i f
        exact dvd_mul_of_dvd_right hi c }
  have hspan :
      Submodule.span ℤ {f : PowerSeries ℤ | integerPowerSeriesCondition p f} = U := by
    apply le_antisymm
    · apply Submodule.span_le.2
      intro x hx
      exact hx
    · intro x hx
      exact Submodule.subset_span hx
  change f ∈ Submodule.span ℤ {f : PowerSeries ℤ | integerPowerSeriesCondition p f} ↔ _
  rw [hspan]
  rfl

/-- The power series with coefficients `aᵢ pⁱ` used to show that the witness
submodule is uncountable. -/
def integerPowerSeriesWitness (p : ℕ) (a : ℕ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun i => a i * (p : ℤ) ^ i)

/-- Every displayed power series belongs to the source's submodule. -/
theorem integerPowerSeriesWitness_mem (p : ℕ) (a : ℕ → ℤ) :
    integerPowerSeriesWitness p a ∈ integerPowerSeriesSubmodule p := by
  rw [integerPowerSeriesSubmodule_carrier]
  intro m hm
  have hge : ∀ᶠ i in Filter.cofinite, m ≤ i := by
    rw [Nat.cofinite_eq_atTop]
    exact Filter.eventually_ge_atTop m
  filter_upwards [hge] with i hi
  rw [integerPowerSeriesWitness, PowerSeries.coeff_mk]
  exact dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) hi) _

/-- For a prime `p`, the source's power-series submodule is uncountable. -/
theorem integerPowerSeriesSubmodule_not_countable
    (p : ℕ) (hp : p.Prime) :
    ¬ (integerPowerSeriesSubmodule p : Set (PowerSeries ℤ)).Countable := by
  intro hN
  let : Countable (integerPowerSeriesSubmodule p : Type) := hN
  have hbool : ¬ Countable (ℕ → Bool) := by
    intro hcount
    let : Countable (ℕ → Bool) := hcount
    obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
    let d : ℕ → Bool := fun n => !(f n n)
    obtain ⟨n, hn⟩ := hf d
    have hdiag := congrFun hn n
    cases hfn : f n n <;> simp [d, hfn] at hdiag
  have hint : Function.Injective
      (fun b : ℕ → Bool => fun n => if b n then (1 : ℤ) else 0) := by
    intro b c hbc
    funext n
    have hval := congrFun hbc n
    cases hb : b n <;> cases hc : c n <;> simp [hb, hc] at hval ⊢
  let w : (ℕ → ℤ) → (integerPowerSeriesSubmodule p : Type) := fun a =>
    ⟨integerPowerSeriesWitness p a, integerPowerSeriesWitness_mem p a⟩
  have hw : Function.Injective w := by
    intro a b hab
    funext i
    have hcoeff := congrArg (PowerSeries.coeff i)
      (congrArg (fun x : (integerPowerSeriesSubmodule p : Type) => (x : PowerSeries ℤ)) hab)
    have hpz : (p : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hp.ne_zero
    have hcoeff' : a i * (p : ℤ) ^ i = b i * (p : ℤ) ^ i := by
      simpa [w, integerPowerSeriesWitness] using hcoeff
    exact mul_right_cancel₀ (pow_ne_zero i hpz) hcoeff'
  let : Countable (ℕ → ℤ) := hw.countable
  exact hbool hint.countable

private theorem integerPowerSeries_monomial_mem (p i : ℕ) :
    PowerSeries.monomial i 1 ∈ integerPowerSeriesSubmodule p := by
  rw [integerPowerSeriesSubmodule_carrier]
  intro m hm
  have hge : ∀ᶠ j in Filter.cofinite, i + 1 ≤ j := by
    rw [Nat.cofinite_eq_atTop]
    exact Filter.eventually_ge_atTop (i + 1)
  filter_upwards [hge] with j hj
  have hne : j ≠ i := by
    intro hji
    subst j
    exact (Nat.not_succ_le_self i) hj
  simp [PowerSeries.coeff_monomial, hne]

/-- The quotient `N / pN` appearing in the source's non-freeness argument. -/
abbrev integerPowerSeriesModP (p : ℕ) : Type :=
  (integerPowerSeriesSubmodule p : Type) ⧸
    (Ideal.span ({(p : ℤ)} : Set ℤ) •
      (⊤ : Submodule ℤ (integerPowerSeriesSubmodule p : Type)))

/-- The quotient `N / pN` is countably generated by the classes of the
monomials. -/
theorem integerPowerSeriesModP_countablyGenerated
    (p : ℕ) (hp : p.Prime) :
    Module.IsCountablyGenerated
      (ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ))
      (integerPowerSeriesModP p) := by
  let I : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let N : Submodule ℤ (PowerSeries ℤ) := integerPowerSeriesSubmodule p
  let Q : Submodule ℤ (N : Type) := I • (⊤ : Submodule ℤ (N : Type))
  change Module.IsCountablyGenerated (ℤ ⧸ I) ((N : Type) ⧸ Q)
  let G : Set ((N : Type) ⧸ Q) := Set.range (fun i : ℕ =>
    Q.mkQ (⟨PowerSeries.monomial i 1, integerPowerSeries_monomial_mem p i⟩ : N))
  refine ⟨G, ?_, ?_⟩
  · simpa [G] using (Set.countable_range (fun i : ℕ =>
      Q.mkQ (⟨PowerSeries.monomial i 1, integerPowerSeries_monomial_mem p i⟩ : N)))
  · apply top_unique
    rintro y -
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective Q y
    have hfcond : integerPowerSeriesCondition p (x : PowerSeries ℤ) := by
      exact (integerPowerSeriesSubmodule_carrier p (x : PowerSeries ℤ)).mp x.property
    have hf1 : ∀ᶠ i in Filter.cofinite, (p : ℤ) ∣ PowerSeries.coeff i (x : PowerSeries ℤ) := by
      simpa using hfcond 1 (by simp)
    rw [Nat.cofinite_eq_atTop] at hf1
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hf1
    have hdiv (i : ℕ) (hi : k ≤ i) :
        ∃ c : ℤ, PowerSeries.coeff i (x : PowerSeries ℤ) = (p : ℤ) * c :=
      hk i hi
    let cfun : ℕ → ℤ := fun i =>
      if hi : k ≤ i then Classical.choose (hdiv i hi) else 0
    have hcfun (i : ℕ) (hi : k ≤ i) :
        PowerSeries.coeff i (x : PowerSeries ℤ) = (p : ℤ) * cfun i := by
      simpa [cfun, hi] using Classical.choose_spec (hdiv i hi)
    have hpz : (p : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hp.ne_zero
    have hhc : integerPowerSeriesCondition p (PowerSeries.mk cfun) := by
      intro m hm
      have hfm := hfcond (m + 1) (by simp)
      rw [Nat.cofinite_eq_atTop] at hfm
      obtain ⟨l, hl⟩ := Filter.eventually_atTop.1 hfm
      have hge : ∀ᶠ i in Filter.cofinite, max k l ≤ i := by
        rw [Nat.cofinite_eq_atTop]
        exact Filter.eventually_ge_atTop (max k l)
      filter_upwards [hge] with i hi
      have hik : k ≤ i := le_trans (le_max_left _ _) hi
      have hil : l ≤ i := le_trans (le_max_right _ _) hi
      have hfi := hl i hil
      rcases hfi with ⟨d, hd⟩
      have hcfun_eq : cfun i = (p : ℤ) ^ m * d := by
        apply mul_left_cancel₀ hpz
        calc
          (p : ℤ) * cfun i = PowerSeries.coeff i (x : PowerSeries ℤ) :=
            (hcfun i hik).symm
          _ = (p : ℤ) ^ (m + 1) * d := hd
          _ = (p : ℤ) * ((p : ℤ) ^ m * d) := by
            rw [pow_succ]
            ring
      refine ⟨d, ?_⟩
      simpa only [PowerSeries.coeff_mk] using hcfun_eq
    let h : PowerSeries ℤ := PowerSeries.mk cfun
    have hhmem : h ∈ integerPowerSeriesSubmodule p := by
      rw [integerPowerSeriesSubmodule_carrier]
      exact hhc
    let g : PowerSeries ℤ := PowerSeries.mk (fun i =>
      if i < k then PowerSeries.coeff i (x : PowerSeries ℤ) else 0)
    have hgc : integerPowerSeriesCondition p g := by
      intro m hm
      have hge : ∀ᶠ i in Filter.cofinite, k ≤ i := by
        rw [Nat.cofinite_eq_atTop]
        exact Filter.eventually_ge_atTop k
      filter_upwards [hge] with i hi
      rw [PowerSeries.coeff_mk]
      simp [Nat.not_lt_of_ge hi]
    have hgmem : g ∈ integerPowerSeriesSubmodule p := by
      rw [integerPowerSeriesSubmodule_carrier]
      simpa [g] using hgc
    have hfg : (x : PowerSeries ℤ) - g = (p : ℤ) • h := by
      apply PowerSeries.ext
      intro i
      by_cases hi : i < k
      · have hik : ¬ k ≤ i := Nat.not_le_of_gt hi
        change PowerSeries.coeff i (x : PowerSeries ℤ) - PowerSeries.coeff i g =
          (p : ℤ) * PowerSeries.coeff i h
        rw [show PowerSeries.coeff i g = PowerSeries.coeff i (x : PowerSeries ℤ) by
          simp only [g, PowerSeries.coeff_mk, if_pos hi]]
        rw [show PowerSeries.coeff i h = 0 by
          simp only [h, PowerSeries.coeff_mk, cfun, dif_neg hik]]
        simp
      · have hik : k ≤ i := Nat.le_of_not_gt hi
        change PowerSeries.coeff i (x : PowerSeries ℤ) - PowerSeries.coeff i g =
          (p : ℤ) * PowerSeries.coeff i h
        rw [show PowerSeries.coeff i g = 0 by
          simp [g, PowerSeries.coeff_mk, hi],
          show PowerSeries.coeff i h = cfun i by
            simp [h, PowerSeries.coeff_mk]]
        simpa [cfun, hik] using hcfun i hik
    let u : N := ⟨g, hgmem⟩
    let v : N := ⟨h, hhmem⟩
    have hsub : x - u = (p : ℤ) • v := by
      apply Subtype.ext
      simpa [u, v] using hfg
    have hpI : (p : ℤ) ∈ I := by
      exact Ideal.subset_span (by simp)
    have hqmem : (p : ℤ) • v ∈ Q := by
      change (p : ℤ) • v ∈ I • (⊤ : Submodule ℤ (N : Type))
      exact Submodule.smul_mem_smul hpI Submodule.mem_top
    have hdiff : x - u ∈ Q := by
      rw [hsub]
      exact hqmem
    have hqxu : Q.mkQ x = Q.mkQ u := by
      have hz : Q.mkQ (x - u) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hdiff
      have hz' : Q.mkQ x - Q.mkQ u = 0 := by
        simpa only [map_sub] using hz
      exact sub_eq_zero.mp hz'
    have hpoly : g = (∑ i ∈ Finset.range k,
        PowerSeries.monomial i (PowerSeries.coeff i (x : PowerSeries ℤ))) := by
      apply PowerSeries.ext
      intro j
      by_cases hj : j < k
      · have hjmem : j ∈ Finset.range k := Finset.mem_range.mpr hj
        rw [PowerSeries.coeff_mk]
        simp only [if_pos hj]
        rw [map_sum, Finset.sum_eq_single_of_mem j hjmem]
        · simp
        · intro i hi hij
          simp [PowerSeries.coeff_monomial, Ne.symm hij]
      · rw [PowerSeries.coeff_mk]
        simp only [if_neg hj]
        rw [map_sum, Finset.sum_eq_zero]
        intro i hi
        have hne : j ≠ i := by
          intro hji
          subst j
          exact hj (Finset.mem_range.mp hi)
        simp [PowerSeries.coeff_monomial, hne]
    have hpoly_sub : u = (∑ i ∈ Finset.range k,
          (PowerSeries.coeff i (x : PowerSeries ℤ)) •
            (⟨PowerSeries.monomial i 1, integerPowerSeries_monomial_mem p i⟩ : N)) := by
      /- Prior attempt:
      apply Subtype.ext
      simpa [u, PowerSeries.smul_eq_C_mul] using hpoly
      -/
      sorry
    have hqpoly : Q.mkQ u ∈ Submodule.span (ℤ ⧸ I) G := by
      rw [hpoly_sub, map_sum]
      apply Submodule.sum_mem
      intro i hi
      let mi : N := ⟨PowerSeries.monomial i 1, integerPowerSeries_monomial_mem p i⟩
      have hgen : Q.mkQ mi ∈ Submodule.span (ℤ ⧸ I) G := by
        apply Submodule.subset_span
        change Q.mkQ mi ∈ G
        exact ⟨i, by simp [mi]⟩
      change Q.mkQ ((PowerSeries.coeff i (x : PowerSeries ℤ)) • mi) ∈
        Submodule.span (ℤ ⧸ I) G
      change Submodule.Quotient.mk ((PowerSeries.coeff i (x : PowerSeries ℤ)) • mi) ∈
        Submodule.span (ℤ ⧸ I) G
      rw [← Module.Quotient.mk_smul_mk (N : Type) I
        (PowerSeries.coeff i (x : PowerSeries ℤ)) mi]
      exact Submodule.smul_mem _ _ hgen
    rw [hqxu]
    exact hqpoly

/-- The power-series submodule in the warning is not free. -/
theorem integerPowerSeriesSubmodule_not_free
    (p : ℕ) (hp : p.Prime) :
    ¬ Module.Free ℤ (integerPowerSeriesSubmodule p : Type) := by
  intro hfree
  let : Module.Free ℤ (integerPowerSeriesSubmodule p : Type) := hfree
  let I : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let N : Submodule ℤ (PowerSeries ℤ) := integerPowerSeriesSubmodule p
  let Q : Submodule ℤ (N : Type) := I • (⊤ : Submodule ℤ (N : Type))
  have hcount : Module.IsCountablyGenerated (ℤ ⧸ I) ((N : Type) ⧸ Q) := by
    simpa [I, N, Q, integerPowerSeriesModP] using
      (integerPowerSeriesModP_countablyGenerated p hp)
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime p
  let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
  obtain ⟨ι, ⟨b⟩⟩ := Module.Free.exists_set ℤ (N : Type)
  have hcoord_mem (i : ι) (z : N) (hz : z ∈ Q) : b.coord i z ∈ I := by
    have hmap : Q.map (b.coord i) ≤ (I : Submodule ℤ ℤ) := by
      change (I • (⊤ : Submodule ℤ (N : Type))).map (b.coord i) ≤
        (I : Submodule ℤ ℤ)
      rw [Submodule.map_smul'']
      refine Submodule.smul_le.2 ?_
      intro r hr z hz
      change r * z ∈ I
      simpa [mul_comm] using I.mul_mem_left z hr
    exact hmap (Submodule.mem_map_of_mem hz)
  have hli : LinearIndependent (ℤ ⧸ I) (fun i : ι => Q.mkQ (b i)) := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    let rep : ι → ℤ := fun j => Quotient.out (c j)
    have hrep (j : ι) : Ideal.Quotient.mk I (rep j) = c j := by
      simpa [rep] using (Ideal.Quotient.mk_out (I := I) (c j))
    have hzero : Q.mkQ (∑ j ∈ s, (rep j) • b j) = 0 := by
      calc
        Q.mkQ (∑ j ∈ s, (rep j) • b j) =
            (∑ j ∈ s, Ideal.Quotient.mk I (rep j) • Q.mkQ (b j)) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro j hj
              simpa [Q] using
                (Module.Quotient.mk_smul_mk (N : Type) I (rep j) (b j)).symm
        _ = (∑ j ∈ s, c j • Q.mkQ (b j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hrep]
        _ = 0 := hc
    have hmem : (∑ j ∈ s, (rep j) • b j) ∈ Q := by
      rw [← Submodule.Quotient.mk_eq_zero Q]
      simpa only [Submodule.mkQ_apply] using hzero
    have hcoord : b.coord i (∑ j ∈ s, (rep j) • b j) ∈ I :=
      hcoord_mem i _ hmem
    have hcoord_eq : b.coord i (∑ j ∈ s, (rep j) • b j) = rep i := by
      rw [map_sum, Finset.sum_eq_single_of_mem i hi]
      · simp
      · intro j hj hji
        simp [Ne.symm hji]
    rw [hcoord_eq] at hcoord
    have hzero' : Ideal.Quotient.mk I (rep i) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hcoord
    rw [hrep i] at hzero'
    exact hzero'
  rcases hcount with ⟨s, hs, hspan⟩
  let : Countable s := hs
  have hιcard : Cardinal.mk ι ≤ Cardinal.aleph0 :=
    (linearIndependent_le_span'' hli s hspan).trans Cardinal.mk_le_aleph0
  let : Countable ι := Cardinal.mk_le_aleph0_iff.mp hιcard
  have hNcount : Countable (N : Type) := by
    exact Countable.of_equiv (ι →₀ ℤ) b.repr.symm.toEquiv
  apply integerPowerSeriesSubmodule_not_countable p hp
  exact hNcount

private theorem free_of_submodule_of_free_pid
    {R : Type u} {F : Type v} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup F] [Module R F]
    [Module.Free R F] (N : Submodule R F) : Module.Free R N := by
  classical
  let b := Module.Free.chooseBasis R F
  let J := Module.Free.ChooseBasisIndex R F
  let T : Ordinal.{v} := Cardinal.ord (Cardinal.mk J)
  have hcard : Cardinal.mk T.ToType = Cardinal.mk J := by
    simp [T]
  let eJ : T.ToType ≃ J := (Cardinal.eq.mp hcard).some
  let bT : Module.Basis T.ToType R F := b.reindex eJ.symm
  let S : Ordinal.{v} := T + 1
  let base : Set.Iio S → Set T.ToType := fun α =>
    {i : T.ToType | (i : Ordinal) < α.1}
  let ambient : Set.Iio S → Submodule R F := fun α =>
    Submodule.span R (bT '' base α)
  let stage : Set.Iio S → Submodule R N := fun α =>
    (ambient α).comap N.subtype
  have hbase_mono : Monotone base := by
    intro α β hαβ i hi
    exact (show (i : Ordinal) < α.1 from hi).trans_le hαβ
  have hambient_mono : Monotone ambient := by
    intro α β hαβ
    exact Submodule.span_mono (Set.image_mono (hbase_mono hαβ))
  have hstage_mono : Monotone stage := by
    intro α β hαβ
    exact Submodule.comap_mono (hambient_mono hαβ)
  have hstage_zero : stage ⟨0, by simp [S]⟩ = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply (Submodule.mem_bot R).2
      apply Subtype.ext
      simpa [stage, ambient, base] using hx
    · exact bot_le
  let αT : Set.Iio S := ⟨T, ordinal_lt_add_one T⟩
  have hbase_top : base αT = Set.univ := by
    ext i
    constructor
    · intro _
      trivial
    · intro _
      change i ∈ base αT
      dsimp [base, αT]
      exact Ordinal.typein_lt_self i
  have hambient_top : ambient αT = ⊤ := by
    simpa [ambient, hbase_top] using bT.span_eq
  have hstage_top : stage αT = ⊤ := by
    simp [stage, hambient_top]
  have hambient_limit :
      ∀ (α : Set.Iio S), Order.IsSuccLimit α.1 →
        ambient α = ⨆ β : Set.Iio α.1,
          ambient ⟨β.1, by
            exact β.2.trans (show α.1 < S from α.2)⟩ := by
    intro α hα
    apply le_antisymm
    · intro x hx
      change x ∈ Submodule.span R (bT '' base α) at hx
      rw [Module.Basis.mem_span_image] at hx
      by_cases hs : (bT.repr x).support.Nonempty
      · let i := (bT.repr x).support.max' hs
        have hi : (i : Ordinal) < α.1 := hx (Finset.max'_mem _ hs)
        let β : Set.Iio α.1 := ⟨(i : Ordinal) + 1, by
          exact hα.succ_lt hi⟩
        apply Submodule.mem_iSup_of_mem β
        change x ∈ Submodule.span R (bT ''
          {j : T.ToType | (j : Ordinal) < β.1})
        rw [Module.Basis.mem_span_image]
        intro j hj
        have hji : j ≤ i := Finset.le_max' _ j hj
        have hji' : (j : Ordinal) ≤ (i : Ordinal) := by
          change (Ordinal.ToType.mk.symm j).1 ≤ (Ordinal.ToType.mk.symm i).1
          exact (Ordinal.ToType.mk.symm.le_iff_le).mpr hji
        exact lt_of_le_of_lt hji' (ordinal_lt_add_one (i : Ordinal))
      · have hc : bT.repr x = 0 := by
          ext i
          by_contra hi
          exact hs ⟨i, Finsupp.mem_support_iff.mpr hi⟩
        have hx0 : x = 0 := bT.repr.injective (by simpa [hc])
        rw [hx0]
        exact Submodule.zero_mem _
    · refine iSup_le fun β => ?_
      exact hambient_mono (show
        (⟨β.1, β.2.trans (show α.1 < S from α.2)⟩ : Set.Iio S) ≤ α from β.2.le)
  have hstage_limit :
      ∀ (α : Set.Iio S), Order.IsSuccLimit α.1 →
        stage α = ⨆ β : Set.Iio α.1,
          stage ⟨β.1, by
            exact β.2.trans (show α.1 < S from α.2)⟩ := by
    intro α hα
    apply le_antisymm
    · intro x hx
      have hxA : (x : F) ∈ ambient α := hx
      rw [hambient_limit α hα] at hxA
      obtain ⟨β₀, hβ₀⟩ := hα.nonempty_Iio
      letI : Nonempty (Set.Iio α.1) := ⟨⟨β₀, hβ₀⟩⟩
      have hdir : Directed (· ≤ ·) (fun β : Set.Iio α.1 =>
          ambient ⟨β.1, β.2.trans (show α.1 < S from α.2)⟩) := by
        intro β γ
        refine ⟨max β γ, ?_, ?_⟩
        · exact hambient_mono (show
            (⟨β.1, β.2.trans (show α.1 < S from α.2)⟩ : Set.Iio S) ≤
              ⟨(max β γ).1, (max β γ).2.trans (show α.1 < S from α.2)⟩ by
                change β.1 ≤ (max β γ).1
                exact le_max_left _ _)
        · exact hambient_mono (show
            (⟨γ.1, γ.2.trans (show α.1 < S from α.2)⟩ : Set.Iio S) ≤
              ⟨(max β γ).1, (max β γ).2.trans (show α.1 < S from α.2)⟩ by
                change γ.1 ≤ (max β γ).1
                exact le_max_right _ _)
      obtain ⟨β, hxβ⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hxA
      exact Submodule.mem_iSup_of_mem β hxβ
    · refine iSup_le fun β => ?_
      exact hstage_mono (show
        (⟨β.1, β.2.trans (show α.1 < S from α.2)⟩ : Set.Iio S) ≤ α from β.2.le)
  have hstage_union : (⨆ α : Set.Iio S, stage α) = ⊤ := by
    apply top_unique
    rw [← hstage_top]
    exact le_iSup stage αT
  let D : Formalization.Books.Algebra.Unit84.IncreasingDevissage
      (R := R) (M := (N : Type v)) S :=
    { stage := stage
      monotone := hstage_mono
      zero_lt := by
        change (0 : Ordinal.{v}) < T + 1
        exact Order.bot_lt_succ T
      zero := hstage_zero
      union_eq_top := hstage_union
      limit := hstage_limit }
  have hsuccessor :
      ∀ α : Formalization.Books.Algebra.Unit84.SuccessorIndex S,
        ∃ C : Submodule R (D.stage ⟨α.1 + 1, α.2⟩),
          IsCompl (D.successorSubmodule α) C ∧
            Module.Free R (D.successorQuotient α) := by
    intro α
    let α₀ : Set.Iio S := ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩
    let α₁ : Set.Iio S := ⟨α.1 + 1, α.2⟩
    let W : Submodule R N := stage α₁
    let P : Submodule R W := D.successorSubmodule α
    have hαT : α.1 < T := by
      simpa only [S, Order.succ_eq_add_one] using
        (Order.succ_lt_succ_iff.mp α.2)
    let iα : T.ToType := Ordinal.ToType.mk ⟨α.1, hαT⟩
    have hiα : (iα : Ordinal) = α.1 := by simp [iα]
    let coord : W →ₗ[R] R := (bT.coord iα).comp N.subtype |>.comp W.subtype
    have hker : LinearMap.ker coord = P := by
      ext x
      constructor
      · intro hx
        change (x : N) ∈ stage α₀
        change (x : F) ∈ ambient α₀
        rw [Module.Basis.mem_span_image]
        intro j hj
        have hx₁ : (x : F) ∈ ambient α₁ := x.property
        have hsupp : (↑(bT.repr (x : F)).support : Set T.ToType) ⊆ base α₁ :=
          (Module.Basis.mem_span_image bT).mp hx₁
        have hj₁ : (j : Ordinal) < α.1 + 1 := hsupp hj
        have hji : j ≠ iα := by
          intro hji
          have hcoord : bT.repr (x : F) iα = 0 := by
            simpa [coord] using (LinearMap.mem_ker.mp hx)
          exact (Finsupp.mem_support_iff.mp hj) (by simpa [hji] using hcoord)
        have hjle : (j : Ordinal) ≤ α.1 := by
          apply Order.le_of_lt_succ
          simpa only [Order.succ_eq_add_one] using hj₁
        by_contra hjα
        have hjα' : (j : Ordinal) = α.1 := le_antisymm hjle (not_lt.mp hjα)
        apply hji
        apply (Ordinal.ToType.mk.symm.injective)
        apply Subtype.ext
        simpa [hiα] using hjα'
      · intro hx
        apply LinearMap.mem_ker.mpr
        change bT.coord iα (x : F) = 0
        have hsupp : (↑(bT.repr (x : F)).support : Set T.ToType) ⊆ base α₀ := by
          exact (Module.Basis.mem_span_image bT).mp hx
        have hnot : iα ∉ (bT.repr (x : F)).support := by
          intro hi
          have hlt : (iα : Ordinal) < α.1 := hsupp hi
          exact (not_lt_of_ge (le_of_eq hiα.symm)) hlt
        have hrepr : bT.repr (x : F) iα = 0 := by
          by_contra hrepr
          exact hnot (Finsupp.mem_support_iff.mpr hrepr)
        simpa using hrepr
    let I : Submodule R R := LinearMap.range coord
    letI : I.IsPrincipal := IsPrincipalIdealRing.principal I
    letI : Module.Finite R I := Module.Finite.of_fg
      (Submodule.IsPrincipal.fg (IsPrincipalIdealRing.principal I))
    letI : Module.Free R I := Module.free_of_finite_type_torsion_free'
    let q : W →ₗ[R] I := coord.codRestrict I (fun x => ⟨x, rfl⟩)
    have hq : Function.Surjective q := by
      intro y
      rcases y.property with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
    letI : Module.Projective R I := Module.Projective.of_free
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective q
      (LinearMap.range_eq_top_of_surjective q hq)
    let C : Submodule R W := LinearMap.range s
    let p : W →ₗ[R] W := s.comp q
    have hpC (x : C) : p (x : W) = (x : W) := by
      rcases x.property with ⟨y, hy⟩
      change s (q (x : W)) = (x : W)
      rw [← hy]
      change s (q (s y)) = s y
      exact congrArg s (LinearMap.congr_fun hs y)
    have hkerp : LinearMap.ker p = P := by
      apply le_antisymm
      · intro x hx
        rw [← hker]
        apply LinearMap.mem_ker.mpr
        have hq0 : q x = 0 := by
          apply Subtype.ext
          have hqpx : q (p x) = q x := by
            change q (s (q x)) = q x
            simpa using LinearMap.congr_fun hs (q x)
          rw [LinearMap.mem_ker.mp hx] at hqpx
          simpa using hqpx.symm
        exact congrArg Subtype.val hq0
      · intro x hx
        apply LinearMap.mem_ker.mpr
        change s (q x) = 0
        have hq0 : q x = 0 := by
          apply Subtype.ext
          have hx' : x ∈ LinearMap.ker coord := by rw [hker]; exact hx
          change coord x = 0
          exact LinearMap.mem_ker.mp hx'
        rw [hq0, map_zero]
    have hcomp : IsCompl P C := by
      have hpcomp : IsCompl C (LinearMap.ker p) := by
        let proj : W →ₗ[R] C := p.codRestrict C (fun x => ⟨q x, rfl⟩)
        have hproj (x : C) : proj (x : W) = x := by
          apply Subtype.ext
          exact hpC x
        have h := LinearMap.isCompl_of_proj hproj
        have hkerproj : LinearMap.ker proj = LinearMap.ker p := by
          ext x
          change proj x = 0 ↔ p x = 0
          constructor
          · intro hx
            exact congrArg Subtype.val hx
          · intro hx
            apply Subtype.ext
            exact hx
        simpa [hkerproj] using h
      simpa [hkerp] using hpcomp.symm
    refine ⟨C, ?_, ?_⟩
    · change IsCompl P C
      exact hcomp
    · let sC : I →ₗ[R] C := s.codRestrict C (fun y => ⟨y, rfl⟩)
      have hsC : Function.Bijective sC := by
        constructor
        · intro x y hxy
          have hxy' := congrArg (fun z : C => q (z : W)) hxy
          change q (s x) = q (s y) at hxy'
          calc
            x = q (s x) := by simpa using (LinearMap.congr_fun hs x).symm
            _ = q (s y) := hxy'
            _ = y := by simpa using LinearMap.congr_fun hs y
        · intro z
          rcases z.property with ⟨y, hy⟩
          refine ⟨y, ?_⟩
          apply Subtype.ext
          exact hy
      let eIC : I ≃ₗ[R] C := LinearEquiv.ofBijective sC hsC
      let eQ : D.successorQuotient α ≃ₗ[R] I :=
        (Submodule.quotientEquivOfIsCompl P C hcomp).trans eIC.symm
      exact Module.Free.of_equiv' (by infer_instance) eQ.symm
  have hsucc : D.isSuccessorComplemented := by
    intro α
    rcases hsuccessor α with ⟨C, hC, _⟩
    exact ⟨C, hC⟩
  let DD : Formalization.Books.Algebra.Unit84.DirectSumDevissage
      (R := R) (M := (N : Type v)) S :=
    { toIncreasingDevissage := D
      successor := hsucc }
  obtain ⟨e⟩ :=
    Formalization.Books.Algebra.Unit84.directSumDevissage_decomposition DD
  let _ : ∀ α : Formalization.Books.Algebra.Unit84.SuccessorIndex S,
      Module.Free R (D.successorQuotient α) := fun α =>
    (hsuccessor α).choose_spec.2
  let hfree : Module.Free R
      (⨁ α : Formalization.Books.Algebra.Unit84.SuccessorIndex S,
        D.successorQuotient α) :=
    Module.Free.dfinsupp R (fun α : Formalization.Books.Algebra.Unit84.SuccessorIndex S =>
      D.successorQuotient α)
  exact Module.Free.of_equiv' hfree e.symm

private theorem projective_free_of_pid
    {R : Type u} {P : Type v} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup P] [Module R P]
    (hP : Module.Projective R P) : Module.Free R P := by
  obtain ⟨M, hMadd, hMmodule, hMfree, ⟨i, s, his⟩⟩ :=
    Module.Projective.iff_split.mp hP
  letI : AddCommMonoid M := hMadd
  letI : Module R M := hMmodule
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  letI : Module.Free R M := hMfree
  let Q : Submodule R M := LinearMap.range i
  let ii : P →ₗ[R] Q := i.codRestrict Q (fun x => ⟨x, rfl⟩)
  have hii : Function.Bijective ii := by
    constructor
    · intro x y hxy
      have hxy' := congrArg (fun z : Q => s (z : M)) hxy
      have hix : s (i x) = x := by
        simpa using congrArg (fun f : P →ₗ[R] P => f x) his
      have hiy : s (i y) = y := by
        simpa using congrArg (fun f : P →ₗ[R] P => f y) his
      change s (i x) = s (i y) at hxy'
      exact hix.symm.trans (hxy'.trans hiy)
    · intro z
      rcases z.property with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
  let e : P ≃ₗ[R] Q := LinearEquiv.ofBijective ii hii
  have hQfree : Module.Free R Q :=
    free_of_submodule_of_free_pid (R := R) (F := M) Q
  exact Module.Free.of_equiv' hQfree e.symm

/-- The warning example: `ℤ[[x]]` is flat and Mittag--Leffler but not
projective. -/
theorem integerPowerSeries_flat_mittagLeffler_not_projective :
    Module.Flat ℤ (PowerSeries ℤ) ∧
      IsMittagLefflerModule (ModuleCat.of ℤ (PowerSeries ℤ)) ∧
      ¬ Module.Projective ℤ (PowerSeries ℤ) := by
  have hpos :=
    Formalization.Books.Algebra.Unit91.modulePower_is_flat_and_mittagLeffler
      ℤ (Unit →₀ ℕ)
  refine ⟨?_, ?_, ?_⟩
  · change Module.Flat ℤ ((Unit →₀ ℕ) → ℤ)
    exact hpos.1
  · change IsMittagLefflerModule (ModuleCat.of ℤ ((Unit →₀ ℕ) → ℤ))
    exact hpos.2
  · intro hP
    letI : Module.Free ℤ (PowerSeries ℤ) :=
      projective_free_of_pid hP
    apply integerPowerSeriesSubmodule_not_free 2 Nat.prime_two
    exact free_of_submodule_of_free_pid (R := ℤ) (F := PowerSeries ℤ)
      (integerPowerSeriesSubmodule 2)

/-! ## The projectivity characterization -/

/-- Projectivity is equivalent to flatness, Mittag--Lefflerness, and being a
direct sum of countably generated modules. -/
theorem projectivity_characterization
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Projective R M ↔
      Module.Flat R M ∧
        IsMittagLefflerModule (ModuleCat.of R M) ∧
          IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M) := by
  sorry

/-! ## Universally injective descent -/

/-- A universally injective map into a flat Mittag--Leffler module descends
projectivity to a countable direct sum of modules. -/
theorem projective_of_universallyInjective_of_directSumOfCountablyGenerated
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : universallyInjective f)
    (hM : IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M))
    (hNflat : Module.Flat R N)
    (hNML : IsMittagLefflerModule (ModuleCat.of R N)) :
    Module.Projective R M := by
  sorry

/-- If a direct sum of countably generated modules over a Noetherian ring maps
universally injectively into a finite-variable formal power-series module, it
is projective. -/
theorem projective_of_universallyInjective_to_mvPowerSeries
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    (hM : IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M))
    {n : ℕ} (hn : 0 < n) (f : M →ₗ[R] MvPowerSeries (Fin n) R)
    (hf : universallyInjective f) :
    Module.Projective R M := by
  sorry

end

end Formalization.Books.Algebra.Unit93
