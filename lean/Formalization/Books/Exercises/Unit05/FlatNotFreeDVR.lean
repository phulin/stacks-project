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
  Localization (integerTwoIdeal.primeCompl)

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
  sorry

/-- The requested flat but non-free module over `ℤ_(2)`. -/
theorem fractionLocalizationAtTwo_flat_not_free :
    Module.Flat integersLocalizedAtTwo fractionLocalizationAtTwo ∧
      ¬ Module.Free integersLocalizedAtTwo fractionLocalizationAtTwo :=
  ⟨fractionLocalizationAtTwo_flat, fractionLocalizationAtTwo_not_free⟩

end Formalization.Books.Exercises.Unit05
