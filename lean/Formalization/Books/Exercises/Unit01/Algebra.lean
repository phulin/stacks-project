import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Exercises, Chapter 1: Algebra

This file records the definitions and theorem interfaces from the numbered
exercises in `books/exercises.tex`.  The propositions are intentionally left
unproved at this stage.
-/

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open IsLocalRing
open scoped TensorProduct

namespace Formalization.Books.Exercises.Unit01

/-! ## Localization and coherent rings -/

/-- The ideal `(m, p)` in a polynomial ring, written using Mathlib's ideal maps. -/
def shiftedPolynomialIdeal {A : Type*} [CommRing A] (m : Ideal A) (p : Polynomial A) :
    Ideal (Polynomial A) :=
  Ideal.map (Polynomial.C : A →+* Polynomial A) m ⊔ Ideal.span {p}

/-- The localization at the complement of a specified prime ideal. -/
abbrev localizationAtPrime {R : Type v} [CommRing R] (P : Ideal R) (hP : P.IsPrime) : Type v :=
  Localization (M := R) (@Ideal.primeCompl R _ P hP)

/-- The two localizations at `(m, X)` and `(m, X - 1)` are isomorphic. -/
theorem polynomial_shifted_localizations_equiv {A : Type v} [CommRing A]
    (m : Ideal A) [m.IsMaximal] :
    (shiftedPolynomialIdeal m Polynomial.X).IsMaximal ∧
      (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).IsMaximal ∧
      ∃ (h₁ : (shiftedPolynomialIdeal m Polynomial.X).IsPrime)
        (h₂ : (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).IsPrime),
        Nonempty
          (localizationAtPrime (shiftedPolynomialIdeal m Polynomial.X) h₁ ≃+*
            localizationAtPrime (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)) h₂) := by
  sorry

/-- A commutative ring is coherent when finitely generated ideals are finitely presented. -/
def IsCoherentRing (R : Type*) [CommRing R] : Prop :=
  ∀ I : Ideal R, I.FG → Module.FinitePresentation R I

/-- There is a coherent ring which is not Noetherian. -/
theorem exists_coherent_non_noetherian_ring :
    ∃ R : CommRingCat.{u}, IsCoherentRing R ∧ ¬ IsNoetherianRing R := by
  sorry

/-! ## Minimal numbers of generators and flat ideals -/

/-- In a Noetherian local ring, the span rank of a finite module is its residue-field dimension. -/
theorem minimal_generators_eq_residue_field_dimension
    {A M : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (⊤ : Submodule A M).spanFinrank =
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
        ((⊤ : Submodule A M) ⧸
          (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (⊤ : Submodule A M))) ∧
      (⊤ : Submodule A M).spanFinrank =
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A ⊗[A] M) := by
  sorry

/-- Minimal generator counts multiply under tensor products over a local ring. -/
theorem minimal_generators_tensorProduct_mul
    {A M N : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] :
    (⊤ : Submodule A (M ⊗[A] N)).spanFinrank =
      (⊤ : Submodule A M).spanFinrank * (⊤ : Submodule A N).spanFinrank := by
  sorry

/-- A non-principal ideal has strictly fewer generators after squaring than the naive bound. -/
theorem ideal_square_spanFinrank_lt
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : 1 < I.spanFinrank) :
    (I ^ 2).spanFinrank < I.spanFinrank ^ 2 := by
  sorry

/-- If every ideal is flat, a Noetherian local ring is a PID or a field. -/
theorem flat_ideals_imply_pid_or_field
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hflat : ∀ I : Ideal A, Module.Flat A I) :
    IsField A ∨ (IsDomain A ∧ IsPrincipalIdealRing A) := by
  sorry

/-! ## Non-isomorphic polynomial rings -/

/-- Polynomial rings in successive positive finite numbers of variables are not isomorphic. -/
theorem mvPolynomial_fin_not_ringEquiv {k : Type*} [Field k] (n : ℕ) (hn : 1 ≤ n) :
    ¬ Nonempty (MvPolynomial (Fin n) k ≃+* MvPolynomial (Fin (n + 1)) k) := by
  sorry

/-- The six-variable quadratic used in the two quotient-ring exercises. -/
def sixVariableQuadratic (k : Type*) [CommSemiring k] : MvPolynomial (Fin 6) k :=
  MvPolynomial.X (0 : Fin 6) * MvPolynomial.X (1 : Fin 6) +
    MvPolynomial.X (2 : Fin 6) * MvPolynomial.X (3 : Fin 6) +
    MvPolynomial.X (4 : Fin 6) * MvPolynomial.X (5 : Fin 6)

/-- The six-variable quadratic quotient is not a polynomial ring in five variables. -/
theorem sixVariableQuadratic_quotient_not_mvPolynomial_five
    {k : Type*} [Field k] :
    ¬ Nonempty
      ((MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) ≃+*
        MvPolynomial (Fin 5) k) := by
  sorry

/-- The same quotient is not a polynomial ring in six variables. -/
theorem sixVariableQuadratic_quotient_not_mvPolynomial_six
    {k : Type*} [Field k] :
    ¬ Nonempty
      ((MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) ≃+*
        MvPolynomial (Fin 6) k) := by
  sorry

/-! ## Short exact sequences -/

/-- A short exact sequence becomes split after faithfully flat base change. -/
def SplitsAfterFaithfullyFlatBaseChange {A B : CommRingCat.{u}} (f : A ⟶ B)
    (S : ShortComplex (ModuleCat A)) : Prop :=
  RingHom.FaithfullyFlat f.hom ∧
    (S.map (ModuleCat.extendScalars f.hom)).ShortExact ∧
      Nonempty (S.map (ModuleCat.extendScalars f.hom)).Splitting

/-- There is a nonsplit short exact sequence of modules over the integers. -/
theorem exists_nonsplit_short_exact_sequence :
    ∃ S : ShortComplex (ModuleCat ℤ), S.ShortExact ∧ ¬ Nonempty S.Splitting := by
  sorry

/-- There is a nonsplit sequence whose tensor sequence splits after a faithfully flat extension. -/
theorem exists_nonsplit_sequence_split_after_faithfullyFlat_baseChange :
    ∃ (A B : CommRingCat.{u}) (f : A ⟶ B) (S : ShortComplex (ModuleCat A)),
      S.ShortExact ∧ ¬ Nonempty S.Splitting ∧ SplitsAfterFaithfullyFlatBaseChange f S := by
  sorry

/-! ## Kummer extensions -/

/-- A primitive `n`th root of unity forces the characteristic to be coprime to `n`. -/
theorem primitive_root_characteristic_coprime
    {k : Type*} [Field k] {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) :
    ringChar k = 0 ∨ Nat.Coprime (ringChar k) n := by
  sorry

/-- The standard Kummer irreducibility criterion gives a field quotient. -/
theorem kummer_polynomial_quotient_is_field
    {k : Type*} [Field k] {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (a : k)
    (ha : ∀ d : ℕ, d ∣ n → d ≤ n → 1 < d → ¬ ∃ b : k, b ^ d = a) :
    IsField (Polynomial k ⧸ Ideal.span {Polynomial.X ^ n - Polynomial.C a}) := by
  sorry

/-! ## Integer-valued valuations on `k[x]` -/

/-- The valuation axioms used in the exercise, restricted to nonzero polynomials. -/
structure PolynomialValuation (k : Type*) [Field k] where
  toFun : {f : Polynomial k // f ≠ 0} → ℤ
  map_mul' : ∀ {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0),
    toFun ⟨f * g, mul_ne_zero hf hg⟩ = toFun ⟨f, hf⟩ + toFun ⟨g, hg⟩
  map_add_min' : ∀ {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0),
    min (toFun ⟨f, hf⟩) (toFun ⟨g, hg⟩) ≤ toFun ⟨f + g, hfg⟩
  map_C' : ∀ {c : k} (hc : c ≠ 0),
    toFun ⟨Polynomial.C c, Polynomial.C_ne_zero.mpr hc⟩ = 0

instance {k : Type*} [Field k] : CoeFun (PolynomialValuation k)
    (fun _ => {f : Polynomial k // f ≠ 0} → ℤ) :=
  ⟨PolynomialValuation.toFun⟩

/-- Evaluation of a valuation at a polynomial together with its nonvanishing proof. -/
def PolynomialValuation.value {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) : ℤ :=
  ν.toFun ⟨f, hf⟩

/-- The value of `X`, used in the termwise lower bound. -/
def PolynomialValuation.xValue {k : Type*} [Field k] (ν : PolynomialValuation k) : ℤ :=
  ν.value Polynomial.X Polynomial.X_ne_zero

/-- The set which is asserted to be a prime ideal when `ν(X) ≥ 0`. -/
def PolynomialValuation.positiveSet {k : Type*} [Field k] (ν : PolynomialValuation k) :
    Set (Polynomial k) :=
  {f | f = 0 ∨ ∃ hf : f ≠ 0, 0 < ν.value f hf}

/-- The values of the monomials occurring in a polynomial. -/
def PolynomialValuation.termValues {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) : Finset ℤ :=
  f.support.image (fun i : ℕ => (i : ℤ) * ν.xValue)

/-- The minimum of the term values of a nonzero polynomial. -/
def PolynomialValuation.termMinimum {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) : ℤ :=
  (ν.termValues f).min' (by
    change (f.support.image (fun i : ℕ => (i : ℤ) * ν.xValue)).Nonempty
    exact (Polynomial.support_nonempty.mpr hf).image _)

/-- Unequal values cannot cancel in a sum. -/
theorem polynomial_valuation_add_of_unequal_values
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hneq : ν.value f hf ≠ ν.value g hg) :
    ν.value (f + g) hfg = min (ν.value f hf) (ν.value g hg) := by
  let hnegone : (-1 : Polynomial k) ≠ 0 := by simp
  have hC : ν.toFun ⟨(-1 : Polynomial k), hnegone⟩ = 0 := by
    simpa [PolynomialValuation.value] using
      (ν.map_C' (c := (-1 : k)) (neg_ne_zero.mpr one_ne_zero))
  have hneg (p : Polynomial k) (hp : p ≠ 0) :
      ν.value (-p) (neg_ne_zero.mpr hp) = ν.value p hp := by
    have hm := ν.map_mul' (f := (-1 : Polynomial k)) (g := p) hnegone hp
    simpa [PolynomialValuation.value, hC] using hm
  have hlow : min (ν.value f hf) (ν.value g hg) ≤ ν.value (f + g) hfg :=
    ν.map_add_min' hf hg hfg
  have hrev0 := ν.map_add_min' (f := f + g) (g := -g) hfg
    (neg_ne_zero.mpr hg) (by simpa using hf)
  change min (ν.value (f + g) hfg) (ν.value (-g) (neg_ne_zero.mpr hg)) ≤
    ν.value ((f + g) + (-g)) (by simpa using hf) at hrev0
  rw [hneg g hg] at hrev0
  have hrev : min (ν.value (f + g) hfg) (ν.value g hg) ≤ ν.value f hf := by
    simpa only [add_neg_cancel_right] using hrev0
  by_cases hab : ν.value f hf < ν.value g hg
  · have hac : ν.value f hf ≤ ν.value (f + g) hfg := by
      simpa only [min_eq_left (le_of_lt hab)] using hlow
    have hca : ν.value (f + g) hfg ≤ ν.value f hf := by
      by_cases hcb : ν.value (f + g) hfg ≤ ν.value g hg
      · simpa only [min_eq_left hcb] using hrev
      · have hbc : ν.value g hg ≤ ν.value (f + g) hfg := le_of_not_ge hcb
        have hba : ν.value g hg ≤ ν.value f hf := by
          simpa only [min_eq_right hbc] using hrev
        exact False.elim ((not_lt_of_ge hba) hab)
    rw [min_eq_left (le_of_lt hab)]
    exact le_antisymm hca hac
  · have hba : ν.value g hg < ν.value f hf :=
      lt_of_le_of_ne (le_of_not_gt hab) hneq.symm
    have hbc : ν.value g hg ≤ ν.value (f + g) hfg := by
      simpa only [min_eq_right (le_of_lt hba)] using hlow
    have hrev'0 := ν.map_add_min' (f := f + g) (g := -f) hfg
      (neg_ne_zero.mpr hf) (by simpa using hg)
    change min (ν.value (f + g) hfg) (ν.value (-f) (neg_ne_zero.mpr hf)) ≤
      ν.value ((f + g) + (-f)) (by simpa using hg) at hrev'0
    rw [hneg f hf] at hrev'0
    have hrev' : min (ν.value (f + g) hfg) (ν.value f hf) ≤ ν.value g hg := by
      simpa [add_assoc, add_left_comm, add_comm] using hrev'0
    have hcb : ν.value (f + g) hfg ≤ ν.value g hg := by
      by_cases hca : ν.value (f + g) hfg ≤ ν.value f hf
      · simpa only [min_eq_left hca] using hrev'
      · have hac : ν.value f hf ≤ ν.value (f + g) hfg := le_of_not_ge hca
        have hac' : ν.value f hf ≤ ν.value g hg := by
          simpa only [min_eq_right hac] using hrev'
        exact False.elim ((not_lt_of_ge hac') hba)
    rw [min_eq_right (le_of_lt hba)]
    exact le_antisymm hcb hbc

/-- Every nonzero coefficient term gives a lower bound on the value of a polynomial. -/
theorem polynomial_valuation_lower_bound
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) :
    ν.value f hf ≥ ν.termMinimum f hf := by
  classical
  have hpow : ∀ n : ℕ, ν.value (Polynomial.X ^ n) (pow_ne_zero n Polynomial.X_ne_zero) =
      (n : ℤ) * ν.xValue := by
    intro n
    induction n with
    | zero =>
        simpa [PolynomialValuation.value, PolynomialValuation.xValue] using
          (ν.map_C' (c := (1 : k)) one_ne_zero)
    | succ n ih =>
        have hm := ν.map_mul' (f := Polynomial.X ^ n) (g := Polynomial.X)
          (pow_ne_zero n Polynomial.X_ne_zero) Polynomial.X_ne_zero
        have hm' := hm
        change ν.value (Polynomial.X ^ n * Polynomial.X) _ =
          ν.value (Polynomial.X ^ n) _ + ν.value Polynomial.X _ at hm'
        rw [ih] at hm'
        calc
          ν.value (Polynomial.X ^ (n + 1)) _ =
              ν.value (Polynomial.X ^ n * Polynomial.X) _ := by
            rfl
          _ = (n : ℤ) * ν.xValue + ν.xValue := hm'
          _ = ((n + 1 : ℕ) : ℤ) * ν.xValue := by
            norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
              mul_add, add_mul]
  have hmono : ∀ (n : ℕ) (a : k) (ha : a ≠ 0) (hmn : Polynomial.monomial n a ≠ 0),
      ν.value (Polynomial.monomial n a) hmn = (n : ℤ) * ν.xValue := by
    intro n a ha hmn
    have hm := ν.map_mul' (f := Polynomial.C a) (g := Polynomial.X ^ n)
      (Polynomial.C_ne_zero.mpr ha) (pow_ne_zero n Polynomial.X_ne_zero)
    have hm' := hm
    change ν.value (Polynomial.C a * Polynomial.X ^ n) _ =
      ν.value (Polynomial.C a) _ + ν.value (Polynomial.X ^ n) _ at hm'
    have hC : ν.value (Polynomial.C a) (Polynomial.C_ne_zero.mpr ha) = 0 := by
      simpa [PolynomialValuation.value] using ν.map_C' ha
    rw [hC, hpow n] at hm'
    have hval : ν.value (Polynomial.monomial n a) hmn = (n : ℤ) * ν.xValue := by
      simpa only [Polynomial.C_mul_X_pow_eq_monomial, zero_add] using hm'
    exact hval
  have hbound : ∀ (s : Finset ℕ) (p : Polynomial k),
      p.support = s → ∀ hp : p ≠ 0, ν.value p hp ≥ ν.termMinimum p hp := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro p hps hp
        exact False.elim (hp (Polynomial.support_eq_empty.mp hps))
    | @insert i s hi ih =>
        intro p hps hp
        have hi_mem : i ∈ p.support := by
          rw [hps]
          simp
        have hcoeff : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi_mem
        let g := p.erase i
        have hg_support : g.support = s := by
          simp [g, hps, hi]
        have hdecomp : Polynomial.monomial i (p.coeff i) + g = p := by
          simpa [g] using Polynomial.monomial_add_erase p i
        have hmonzero : Polynomial.monomial i (p.coeff i) ≠ 0 :=
          (Polynomial.monomial_eq_zero_iff (p.coeff i) i).not.mpr hcoeff
        have hmonval := hmono i (p.coeff i) hcoeff hmonzero
        have hmin_i : ν.termMinimum p hp ≤
            (i : ℤ) * ν.xValue := by
          change (ν.termValues p).min' _ ≤ _
          apply Finset.min'_le
          exact Finset.mem_image.mpr ⟨i, hi_mem, rfl⟩
        by_cases hg : g = 0
        · have hs0 : s = ∅ := by
            rw [← hg_support, hg]
            simp
          have hpsingle : p.support = {i} := by
            simpa [hs0] using hps
          have hterm : ν.termMinimum p hp = (i : ℤ) * ν.xValue := by
            simp [PolynomialValuation.termMinimum, PolynomialValuation.termValues, hpsingle]
          have hp_eq : p = Polynomial.monomial i (p.coeff i) := by
            calc
              p = Polynomial.monomial i (p.coeff i) + g := hdecomp.symm
              _ = Polynomial.monomial i (p.coeff i) := by rw [hg, add_zero]
          have heq : ν.value p hp = ν.termMinimum p hp := by
            calc
              ν.value p hp = ν.value (Polynomial.monomial i (p.coeff i)) hmonzero := by
                simpa [PolynomialValuation.value] using
                  congrArg ν.toFun (Subtype.ext hp_eq)
              _ = (i : ℤ) * ν.xValue := hmonval
              _ = ν.termMinimum p hp := hterm.symm
          exact le_of_eq heq.symm
        · have hgbound := ih g hg_support hg
          have hsupp : g.support ⊆ p.support := by
            intro j hj
            have hj' : j ∈ (p.support).erase i := by
              simpa [g] using hj
            exact Finset.mem_of_mem_erase hj'
          have htv : ν.termValues g ⊆ ν.termValues p := by
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
            exact Finset.mem_image.mpr ⟨j, hsupp hj, rfl⟩
          have hmin_g : ν.termMinimum p hp ≤ ν.termMinimum g hg := by
            have hng : (ν.termValues g).Nonempty := by
              change (g.support.image (fun j : ℕ => (j : ℤ) * ν.xValue)).Nonempty
              exact (Polynomial.support_nonempty.mpr hg).image _
            change (ν.termValues p).min' _ ≤ (ν.termValues g).min' _
            exact Finset.min'_subset hng htv
          have hsum : Polynomial.monomial i (p.coeff i) + g ≠ 0 := by
            rw [hdecomp]
            exact hp
          have hmap := ν.map_add_min' hmonzero hg hsum
          have hmap' : min ((i : ℤ) * ν.xValue) (ν.value g hg) ≤
              ν.value (Polynomial.monomial i (p.coeff i) + g) hsum := by
            rw [← hmonval]
            exact hmap
          have hgbound' : ν.termMinimum g hg ≤ ν.value g hg := hgbound
          have hmap'' : min ((i : ℤ) * ν.xValue) (ν.termMinimum g hg) ≤
              ν.value (Polynomial.monomial i (p.coeff i) + g) hsum :=
            (min_le_min_left _ hgbound').trans hmap'
          calc
            ν.termMinimum p hp ≤ min ((i : ℤ) * ν.xValue)
                (ν.termMinimum g hg) :=
              le_min hmin_i hmin_g
            _ ≤ ν.value (Polynomial.monomial i (p.coeff i) + g) hsum := hmap''
            _ = ν.value p hp := by simpa [hdecomp]
  exact hbound f.support f rfl hf

/-- A unique lowest-valued term forces equality in the lower bound. -/
theorem polynomial_valuation_eq_lower_bound_of_unique_min
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0)
    (hmin : ∃ i ∈ f.support,
      (∀ j ∈ f.support, (i : ℤ) * ν.xValue ≤ (j : ℤ) * ν.xValue) ∧
        (∀ j ∈ f.support, (i : ℤ) * ν.xValue = (j : ℤ) * ν.xValue → j = i)) :
    ν.value f hf = ν.termMinimum f hf := by
  classical
  have hpow : ∀ n : ℕ, ν.value (Polynomial.X ^ n) (pow_ne_zero n Polynomial.X_ne_zero) =
      (n : ℤ) * ν.xValue := by
    intro n
    induction n with
    | zero =>
        simpa [PolynomialValuation.value, PolynomialValuation.xValue] using
          (ν.map_C' (c := (1 : k)) one_ne_zero)
    | succ n ih =>
        have hm := ν.map_mul' (f := Polynomial.X ^ n) (g := Polynomial.X)
          (pow_ne_zero n Polynomial.X_ne_zero) Polynomial.X_ne_zero
        have hm' := hm
        change ν.value (Polynomial.X ^ n * Polynomial.X) _ =
          ν.value (Polynomial.X ^ n) _ + ν.value Polynomial.X _ at hm'
        rw [ih] at hm'
        calc
          ν.value (Polynomial.X ^ (n + 1)) _ =
              ν.value (Polynomial.X ^ n * Polynomial.X) _ := by rfl
          _ = (n : ℤ) * ν.xValue + ν.xValue := hm'
          _ = ((n + 1 : ℕ) : ℤ) * ν.xValue := by
            norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
              mul_add, add_mul]
  have hmono : ∀ (n : ℕ) (a : k) (ha : a ≠ 0) (hmn : Polynomial.monomial n a ≠ 0),
      ν.value (Polynomial.monomial n a) hmn = (n : ℤ) * ν.xValue := by
    intro n a ha hmn
    have hm := ν.map_mul' (f := Polynomial.C a) (g := Polynomial.X ^ n)
      (Polynomial.C_ne_zero.mpr ha) (pow_ne_zero n Polynomial.X_ne_zero)
    have hm' := hm
    change ν.value (Polynomial.C a * Polynomial.X ^ n) _ =
      ν.value (Polynomial.C a) _ + ν.value (Polynomial.X ^ n) _ at hm'
    have hC : ν.value (Polynomial.C a) (Polynomial.C_ne_zero.mpr ha) = 0 := by
      simpa [PolynomialValuation.value] using ν.map_C' ha
    rw [hC, hpow n] at hm'
    have hval : ν.value (Polynomial.monomial n a) hmn = (n : ℤ) * ν.xValue := by
      simpa only [Polynomial.C_mul_X_pow_eq_monomial, zero_add] using hm'
    exact hval
  obtain ⟨i, hi, hle, huniq⟩ := hmin
  have hcoeff : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  let g := f.erase i
  have hg_support : g.support = f.support.erase i := by
    simp [g]
  have hdecomp : Polynomial.monomial i (f.coeff i) + g = f := by
    simpa [g] using Polynomial.monomial_add_erase f i
  have hmonzero : Polynomial.monomial i (f.coeff i) ≠ 0 :=
    (Polynomial.monomial_eq_zero_iff (f.coeff i) i).not.mpr hcoeff
  have hmonval := hmono i (f.coeff i) hcoeff hmonzero
  have hterm : ν.termMinimum f hf = (i : ℤ) * ν.xValue := by
    apply le_antisymm
    · change (ν.termValues f).min' _ ≤ _
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · change (i : ℤ) * ν.xValue ≤ (ν.termValues f).min' _
      apply Finset.le_min'
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
      exact hle j hj
  by_cases hg : g = 0
  · have hf_eq : f = Polynomial.monomial i (f.coeff i) := by
      calc
        f = Polynomial.monomial i (f.coeff i) + g := hdecomp.symm
        _ = Polynomial.monomial i (f.coeff i) := by rw [hg, add_zero]
    have hval : ν.value f hf = (i : ℤ) * ν.xValue := by
      calc
        ν.value f hf = ν.value (Polynomial.monomial i (f.coeff i)) hmonzero := by
          simpa [PolynomialValuation.value] using
            congrArg ν.toFun (Subtype.ext hf_eq)
        _ = (i : ℤ) * ν.xValue := hmonval
    exact hval.trans hterm.symm
  · have hstrict : (i : ℤ) * ν.xValue < ν.termMinimum g hg := by
      change (i : ℤ) * ν.xValue < (ν.termValues g).min' _
      rw [Finset.lt_min'_iff]
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
      have hj' : j ∈ f.support.erase i := by
        simpa [hg_support] using hj
      have hjf : j ∈ f.support := Finset.mem_of_mem_erase hj'
      have hne : (i : ℤ) * ν.xValue ≠ (j : ℤ) * ν.xValue := by
        intro heq
        have hji : j = i := huniq j hjf heq
        exact (Finset.mem_erase.mp hj').1 hji
      exact lt_of_le_of_ne (hle j hjf) hne
    have hgbound : ν.termMinimum g hg ≤ ν.value g hg :=
      polynomial_valuation_lower_bound ν g hg
    have hgv : (i : ℤ) * ν.xValue < ν.value g hg := hstrict.trans_le hgbound
    have hneq : ν.value (Polynomial.monomial i (f.coeff i)) hmonzero ≠
        ν.value g hg := by
      intro heq
      exact (ne_of_lt hgv) (hmonval.symm.trans heq)
    have hsum : Polynomial.monomial i (f.coeff i) + g ≠ 0 := by
      rw [hdecomp]
      exact hf
    have hadd := polynomial_valuation_add_of_unequal_values ν hmonzero hg hsum hneq
    have hval : ν.value f hf = (i : ℤ) * ν.xValue := by
      calc
        ν.value f hf = ν.value (Polynomial.monomial i (f.coeff i) + g) hsum := by
          simpa [PolynomialValuation.value] using
            congrArg ν.toFun (Subtype.ext hdecomp.symm)
        _ = min (ν.value (Polynomial.monomial i (f.coeff i)) hmonzero)
            (ν.value g hg) := hadd
        _ = (i : ℤ) * ν.xValue := by
          rw [hmonval, min_eq_left hgv.le]
    exact hval.trans hterm.symm

/-- If `ν(X) ≠ 0`, the term minimum is attained uniquely and equality holds. -/
theorem polynomial_valuation_eq_lower_bound_of_xValue_ne_zero
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    {f : Polynomial k} (hf : f ≠ 0) (hx : ν.xValue ≠ 0) :
    ν.value f hf = ν.termMinimum f hf := by
  classical
  have hs : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  have hcancel : ∀ a b : ℕ, (a : ℤ) * ν.xValue = (b : ℤ) * ν.xValue → a = b := by
    intro a b hab
    have hab' := mul_right_cancel₀ hx hab
    exact_mod_cast hab'
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · let i := f.support.max' hs
    have hi : i ∈ f.support := by
      exact Finset.max'_mem _ _
    have hle : ∀ j ∈ f.support, (i : ℤ) * ν.xValue ≤ (j : ℤ) * ν.xValue := by
      intro j hj
      have hji : (j : ℤ) ≤ (i : ℤ) := by
        exact_mod_cast (Finset.le_max' f.support j hj)
      exact mul_le_mul_of_nonpos_right hji (le_of_lt hxneg)
    have huniq : ∀ j ∈ f.support,
        (i : ℤ) * ν.xValue = (j : ℤ) * ν.xValue → j = i := by
      intro j hj heq
      exact (hcancel i j heq).symm
    exact polynomial_valuation_eq_lower_bound_of_unique_min ν f hf
      ⟨i, hi, hle, huniq⟩
  · let i := f.support.min' hs
    have hi : i ∈ f.support := by
      exact Finset.min'_mem _ _
    have hle : ∀ j ∈ f.support, (i : ℤ) * ν.xValue ≤ (j : ℤ) * ν.xValue := by
      intro j hj
      have hij : (i : ℤ) ≤ (j : ℤ) := by
        exact_mod_cast (Finset.min'_le f.support j hj)
      exact mul_le_mul_of_nonneg_right hij (le_of_lt hxpos)
    have huniq : ∀ j ∈ f.support,
        (i : ℤ) * ν.xValue = (j : ℤ) * ν.xValue → j = i := by
      intro j hj heq
      exact (hcancel i j heq).symm
    exact polynomial_valuation_eq_lower_bound_of_unique_min ν f hf
      ⟨i, hi, hle, huniq⟩

/-- A valuation which takes a negative value is a negative multiple of degree. -/
theorem polynomial_valuation_negative_is_negative_degree
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (hneg : ∃ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf < 0) :
    ∃ n : ℕ, 0 < n ∧
      ∀ (f : Polynomial k) (hf : f ≠ 0),
        ν.value f hf = -(n : ℤ) * (f.natDegree : ℤ) := by
  sorry

/-- For nonnegative `ν(X)`, the positive-value set is a prime ideal. -/
theorem polynomial_valuation_positiveSet_is_prime
    {k : Type*} [Field k] (ν : PolynomialValuation k) (hx : 0 ≤ ν.xValue) :
    ∃ I : Ideal (Polynomial k),
      (I : Set (Polynomial k)) = ν.positiveSet ∧ I.IsPrime := by
  sorry

/-- All such valuations are either trivial, degree valuations, or orders at an irreducible. -/
theorem polynomial_valuation_classification
    {k : Type*} [Field k] (ν : PolynomialValuation k) :
    (∀ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf = 0) ∨
      (∃ n : ℕ, 0 < n ∧
        ∀ (f : Polynomial k) (hf : f ≠ 0),
          ν.value f hf = -(n : ℤ) * (f.natDegree : ℤ)) ∨
      (∃ (p : Polynomial k) (n : ℕ), Irreducible p ∧ 0 < n ∧
        ∀ (f : Polynomial k) (hf : f ≠ 0),
          ν.value f hf = (n : ℤ) * (multiplicity p f : ℤ)) := by
  sorry

/-! ## Idempotents and products -/

/-- The canonical idempotent elements `0` and `1`. -/
theorem zero_one_are_idempotent {A : Type*} [MonoidWithZero A] :
    IsIdempotentElem (0 : A) ∧ IsIdempotentElem (1 : A) := by
  exact ⟨IsIdempotentElem.zero, IsIdempotentElem.one⟩

/-- The corrected nontrivial-idempotent predicate needed for a product decomposition. -/
def IsNontrivialIdempotent {A : Type*} [MonoidWithZero A] (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1

/-- The pairwise notion of orthogonality is Mathlib's `OrthogonalIdempotents` on `Fin 2`. -/
theorem orthogonal_idempotents_pair_iff {A : Type*} [CommRing A] (e e' : A) :
    OrthogonalIdempotents ![e, e'] ↔
      IsIdempotentElem e ∧ IsIdempotentElem e' ∧ e * e' = 0 := by
  rw [orthogonalIdempotents_iff]
  constructor
  · intro h
    have he : IsIdempotentElem e := by simpa using h.1 0
    have he' : IsIdempotentElem e' := by simpa using h.1 1
    have hp : e * e' = 0 := by
      simpa using h.2 (show (0 : Fin 2) ≠ 1 by decide)
    exact ⟨he, he', hp⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using h.1
      · simpa using h.2.1
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [mul_comm]

/-- A commutative ring is a product of two nonzero rings. -/
def IsProductOfTwoNonzeroRings (A : CommRingCat.{u}) : Prop :=
  ∃ B C : CommRingCat.{u}, Nontrivial B ∧ Nontrivial C ∧ Nonempty (A ≃+* (B × C))

/-- A product decomposition is equivalent to a nontrivial idempotent. -/
theorem product_ring_iff_nontrivial_idempotent (A : CommRingCat.{u}) :
    IsProductOfTwoNonzeroRings A ↔ ∃ e : A, IsNontrivialIdempotent e := by
  sorry

/-! ## Lifting idempotents -/

/-- The quotient map on the subtypes of idempotents. -/
def quotientIdempotentMap {A : Type*} [CommRing A] (I : Ideal A) :
    {e : A // IsIdempotentElem e} → {e : A ⧸ I // IsIdempotentElem e} :=
  fun e => ⟨Ideal.Quotient.mk I e.1, e.2.map (Ideal.Quotient.mk I)⟩

/-- Locally nilpotent ideals do not change the set of idempotents. -/
theorem quotient_idempotent_map_bijective {A : Type*} [CommRing A] (I : Ideal A)
    (hI : ∀ x ∈ I, IsNilpotent x) :
    Function.Bijective (quotientIdempotentMap I) := by
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hker : ∀ x ∈ RingHom.ker q, IsNilpotent x := by
    intro x hx
    apply hI x
    rw [← Ideal.mk_ker (I := I)]
    exact hx
  constructor
  · intro e e' he
    apply Subtype.ext
    apply eq_of_isNilpotent_sub_of_isIdempotentElem e.property e'.property
    apply hker
    rw [RingHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val he)
  · intro e
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective e.1
    obtain ⟨y, hy, hqy⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
      q hker (q x) ⟨x, rfl⟩ e.2
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    rw [show q = Ideal.Quotient.mk I from rfl, hqy, hx]

end Formalization.Books.Exercises.Unit01
