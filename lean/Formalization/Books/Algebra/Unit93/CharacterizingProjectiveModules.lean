import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Order.Filter.Cofinite
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Ideal.Int

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
open scoped DirectSum TensorProduct

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
  letI : Countable (integerPowerSeriesSubmodule p : Type) := hN
  have hbool : ¬ Countable (ℕ → Bool) := by
    intro hcount
    letI : Countable (ℕ → Bool) := hcount
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
  letI : Countable (ℕ → ℤ) := hw.countable
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
    have hf1 : ∀ᶠ i in Filter.cofinite, (p : ℤ) ∣ PowerSeries.coeff i (x : PowerSeries ℤ) :=
      hfcond 1 (by simp)
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
      have hfm := hfcond (m + 1) (by
        simpa [Nat.succ_eq_add_one] using Nat.succ_le_succ (Nat.zero_le m))
      rw [Nat.cofinite_eq_atTop] at hfm
      obtain ⟨l, hl⟩ := Filter.eventually_atTop.1 hfm
      have hge : ∀ᶠ i in Filter.cofinite, max k l ≤ i := by
        rw [Nat.cofinite_eq_atTop]
        exact Filter.eventually_ge_atTop (max k l)
      filter_upwards [hge] with i hi
      have hik : k ≤ i := le_trans (le_max_left _ _) hi
      have hil : l ≤ i := le_trans (le_max_right _ _) hi
      have hfi := hl i hil
      rw [PowerSeries.coeff_mk, dif_pos hik]
      rcases hfi with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply mul_left_cancel₀ hpz
      calc
        (p : ℤ) * cfun i = PowerSeries.coeff i (x : PowerSeries ℤ) :=
          (hcfun i hik).symm
        _ = (p : ℤ) ^ (m + 1) * d := hd
        _ = (p : ℤ) * ((p : ℤ) ^ m * d) := by
          rw [pow_succ]
          ring
    let h : PowerSeries ℤ := PowerSeries.mk cfun
    have hhmem : h ∈ integerPowerSeriesSubmodule p := by
      rw [integerPowerSeriesSubmodule_carrier]
      simpa [h] using hhc
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
        simp [g, h, cfun, hi, hik]
      · have hik : k ≤ i := Nat.le_of_not_gt hi
        simp [g, h, cfun, hi, hik, hcfun i hik]
    let u : N := ⟨g, hgmem⟩
    let v : N := ⟨h, hhmem⟩
    have hsub : x - u = (p : ℤ) • v := by
      apply Subtype.ext
      simpa [u, v] using hfg
    have hpI : (p : ℤ) ∈ I := by
      exact Ideal.subset_span (by simp [I])
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
    have hpoly : g = ∑ i in Finset.range k,
        PowerSeries.coeff i (x : PowerSeries ℤ) • PowerSeries.monomial i 1 := by
      apply PowerSeries.ext
      intro j
      by_cases hj : j < k
      · have hjmem : j ∈ Finset.range k := Finset.mem_range.mpr hj
        rw [PowerSeries.coeff_mk]
        simp only [if_pos hj]
        rw [map_sum, Finset.sum_eq_single j hjmem]
        · simp [PowerSeries.coeff_smul, PowerSeries.coeff_monomial]
        · intro i hi hij
          simp [PowerSeries.coeff_smul, PowerSeries.coeff_monomial, hij,
            Ne.symm hij]
      · rw [PowerSeries.coeff_mk]
        simp only [if_neg hj]
        rw [map_sum, Finset.sum_eq_zero]
        intro i hi
        have hne : j ≠ i := by
          intro hji
          subst j
          exact hj (Finset.mem_range.mp hi)
        simp [PowerSeries.coeff_smul, PowerSeries.coeff_monomial, hne]
  have hpoly_sub : u = ∑ i in Finset.range k,
        (PowerSeries.coeff i (x : PowerSeries ℤ)) •
          (⟨PowerSeries.monomial i 1, integerPowerSeries_monomial_mem p i⟩ : N) := by
      apply Subtype.ext
      simpa [u] using hpoly
    have hqpoly : Q.mkQ u ∈ Submodule.span (ℤ ⧸ I) G := by
      rw [hpoly_sub, map_sum]
      apply Submodule.sum_mem
      intro i hi
      let mi : N := ⟨PowerSeries.monomial i 1, integerPowerSeries_monomial_mem p i⟩
      have hgen : Q.mkQ mi ∈ Submodule.span (ℤ ⧸ I) G := by
        apply Submodule.subset_span
        change Q.mkQ mi ∈ G
        exact ⟨i, by simp [G, mi]⟩
      change Q.mkQ ((PowerSeries.coeff i (x : PowerSeries ℤ)) • mi) ∈
        Submodule.span (ℤ ⧸ I) G
      rw [← Module.Quotient.mk_smul_mk I
        (PowerSeries.coeff i (x : PowerSeries ℤ)) mi]
      exact Submodule.smul_mem _ _ hgen
    rw [hqxu]
    exact hqpoly

/-- The power-series submodule in the warning is not free. -/
theorem integerPowerSeriesSubmodule_not_free
    (p : ℕ) (hp : p.Prime) :
    ¬ Module.Free ℤ (integerPowerSeriesSubmodule p : Type) := by
  intro hfree
  letI : Module.Free ℤ (integerPowerSeriesSubmodule p : Type) := hfree
  let I : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let N : Submodule ℤ (PowerSeries ℤ) := integerPowerSeriesSubmodule p
  let Q : Submodule ℤ (N : Type) := I • (⊤ : Submodule ℤ (N : Type))
  have hcount : Module.IsCountablyGenerated (ℤ ⧸ I) ((N : Type) ⧸ Q) := by
    simpa [I, N, Q, integerPowerSeriesModP] using
      (integerPowerSeriesModP_countablyGenerated p hp)
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime p
  letI : Field (ℤ ⧸ I) := Ideal.Quotient.field I
  obtain ⟨ι, ⟨b⟩⟩ := Module.Free.exists_set ℤ (N : Type)
  have hcoord_mem (i : ι) (z : N) (hz : z ∈ Q) : b.coord i z ∈ I := by
    have hmap : Q.map (b.coord i) ≤ (I : Submodule ℤ ℤ) := by
      change (I • (⊤ : Submodule ℤ (N : Type))).map (b.coord i) ≤
        (I : Submodule ℤ ℤ)
      rw [Submodule.map_smul'']
      refine Submodule.smul_le.2 ?_
      intro r hr z hz
      change r * z ∈ I
      exact I.mul_mem_left z hr
    exact hmap (Submodule.mem_map_of_mem hz)
  have hli : LinearIndependent (ℤ ⧸ I) (fun i : ι => Q.mkQ (b i)) := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    let rep : ι → ℤ := fun j => Quotient.out (c j)
    have hrep (j : ι) : Ideal.Quotient.mk I (rep j) = c j := by
      simpa [rep] using Ideal.Quotient.mk_out I (c j)
    have hzero : Q.mkQ (∑ j in s, (rep j) • b j) = 0 := by
      calc
        Q.mkQ (∑ j in s, (rep j) • b j) =
            ∑ j in s, Ideal.Quotient.mk I (rep j) • Q.mkQ (b j) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro j hj
              simpa [Q] using
                (Module.Quotient.mk_smul_mk I (rep j) (b j)).symm
        _ = ∑ j in s, c j • Q.mkQ (b j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hrep]
        _ = 0 := hc
    have hmem : (∑ j in s, (rep j) • b j) ∈ Q := by
      rw [← Submodule.Quotient.mk_eq_zero Q]
      simpa only [Submodule.mkQ_apply] using hzero
    have hcoord : b.coord i (∑ j in s, (rep j) • b j) ∈ I :=
      hcoord_mem i _ hmem
    have hcoord_eq : b.coord i (∑ j in s, (rep j) • b j) = rep i := by
      rw [map_sum, Finset.sum_eq_single i hi]
      · simp [Basis.coord_apply]
      · intro j hj hji
        simp [Basis.coord_apply, hji, Ne.symm hji]
    rw [hcoord_eq] at hcoord
    have hzero' : Ideal.Quotient.mk I (rep i) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hcoord
    rw [hrep i] at hzero'
    exact hzero'
  rcases hcount with ⟨s, hs, hspan⟩
  letI : Countable s := hs
  have hιcard : #ι ≤ ℵ₀ :=
    (linearIndependent_le_span'' hli s hspan).trans Cardinal.mk_le_aleph0
  letI : Countable ι := Cardinal.mk_le_aleph0_iff.mp hιcard
  have hNcount : Countable (N : Type) := by
    exact Countable.of_equiv (ι →₀ ℤ) b.repr.symm.toEquiv
  apply integerPowerSeriesSubmodule_not_countable p hp
  exact hNcount

/-- The warning example: `ℤ[[x]]` is flat and Mittag--Leffler but not
projective. -/
theorem integerPowerSeries_flat_mittagLeffler_not_projective :
    Module.Flat ℤ (PowerSeries ℤ) ∧
      IsMittagLefflerModule (ModuleCat.of ℤ (PowerSeries ℤ)) ∧
        ¬ Module.Projective ℤ (PowerSeries ℤ) := by
  sorry

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
