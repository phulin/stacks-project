import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Exercises, Chapter 5: Flat ring maps

This file records the flat non-free module over `ℤ_(2)`.  The base ring is
Mathlib's localization of `ℤ` at the complement of `(2)`, and the module is
its localization obtained by inverting `2`.
-/

noncomputable section

namespace Formalization.Books.Exercises.Unit05

/-! ## A flat non-free module over `ℤ_(2)` -/

/-- The ideal `(2)` in `ℤ`. -/
def integerTwoIdeal : Ideal ℤ :=
  Ideal.span {(2 : ℤ)}

instance integerTwoIdeal_isMaximal : integerTwoIdeal.IsMaximal := by
  simpa [integerTwoIdeal] using
    (@Int.ideal_span_isMaximal_of_prime 2 ⟨Nat.prime_two⟩)

instance integerTwoIdeal_isPrime : integerTwoIdeal.IsPrime :=
  integerTwoIdeal_isMaximal.isPrime

/-- The local ring `ℤ_(2)`, represented by localization at `(2)ᶜ`. -/
abbrev integersLocalizedAtTwo : Type :=
  Localization.AtPrime integerTwoIdeal

/-- The localization of `ℤ_(2)` in which `2` is invertible. -/
abbrev fractionLocalizationAtTwo : Type :=
  Localization (Submonoid.powers (2 : integersLocalizedAtTwo))

/-- The module in the example is flat over `ℤ_(2)`. -/
theorem fractionLocalizationAtTwo_flat :
    Module.Flat integersLocalizedAtTwo fractionLocalizationAtTwo := by
  exact IsLocalization.flat fractionLocalizationAtTwo
    (Submonoid.powers (2 : integersLocalizedAtTwo))

/-- The displayed flat module is not free over `ℤ_(2)`. -/
theorem fractionLocalizationAtTwo_not_free :
    ¬ Module.Free integersLocalizedAtTwo fractionLocalizationAtTwo := by
  intro hfree
  let : IsDomain integersLocalizedAtTwo :=
    IsLocalization.isDomain_of_atPrime integersLocalizedAtTwo integerTwoIdeal
  have htwo_ne_zero : (2 : integersLocalizedAtTwo) ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap ℤ integersLocalizedAtTwo) :=
      IsLocalization.injective integersLocalizedAtTwo
        integerTwoIdeal.primeCompl_le_nonZeroDivisors
    apply (show (2 : ℤ) ≠ 0 by norm_num)
    apply hinj
    simpa using h
  let : IsDomain fractionLocalizationAtTwo :=
    IsLocalization.isDomain_of_le_nonZeroDivisors fractionLocalizationAtTwo
      (powers_le_nonZeroDivisors_of_noZeroDivisors htwo_ne_zero)
  have hunit : IsUnit (algebraMap integersLocalizedAtTwo fractionLocalizationAtTwo
      (2 : integersLocalizedAtTwo)) := by
    exact IsLocalization.map_units fractionLocalizationAtTwo
      ⟨2, Submonoid.mem_powers (2 : integersLocalizedAtTwo)⟩
  have hsurj : Function.Surjective
      (fun x : fractionLocalizationAtTwo =>
        algebraMap integersLocalizedAtTwo fractionLocalizationAtTwo
            (2 : integersLocalizedAtTwo) * x) :=
    (IsUnit.isUnit_iff_mulLeft_bijective.mp hunit).2
  obtain ⟨ι, b⟩ := hfree.exists_basis
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨x, hx⟩ := hsurj (b i)
  have hx' : (2 : integersLocalizedAtTwo) • x = b i := by
    rw [← IsScalarTower.algebraMap_smul fractionLocalizationAtTwo, smul_eq_mul]
    exact hx
  have hdiv : (2 : integersLocalizedAtTwo) ∣ 1 := by
    have hcoord := b.dvd_coord_smul i x (2 : integersLocalizedAtTwo)
    rw [hx'] at hcoord
    simpa using hcoord
  have hunit_base : IsUnit (2 : integersLocalizedAtTwo) :=
    isUnit_of_dvd_one hdiv
  apply (show ¬ IsUnit (2 : integersLocalizedAtTwo) from ?_) hunit_base
  intro h
  have h' : IsUnit (algebraMap ℤ integersLocalizedAtTwo (2 : ℤ)) := by
    simpa using h
  have hmem : (2 : ℤ) ∈ integerTwoIdeal.primeCompl :=
    (IsLocalization.AtPrime.isUnit_to_map_iff integersLocalizedAtTwo integerTwoIdeal 2).mp h'
  exact hmem (Ideal.mem_span_singleton_self (2 : ℤ))

/-- The requested flat but non-free module over `ℤ_(2)`. -/
theorem fractionLocalizationAtTwo_flat_not_free :
    Module.Flat integersLocalizedAtTwo fractionLocalizationAtTwo ∧
      ¬ Module.Free integersLocalizedAtTwo fractionLocalizationAtTwo :=
  ⟨fractionLocalizationAtTwo_flat, fractionLocalizationAtTwo_not_free⟩

end Formalization.Books.Exercises.Unit05
