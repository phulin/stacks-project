import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Exercises, Chapter 11: Ext groups of abelian groups

The source asks for four computations in `Mod_ℤ`.  The canonical Ext group is
the `ExtGroup` interface from Algebra, Chapter 71.  Finite cyclic groups are
represented by `ZMod`, and `ℚ/ℤ` is represented by the canonical additive-group
quotient by the integer multiples of `1`.
-/

namespace Formalization.Books.Exercises.Unit11

open Formalization.Books.Algebra.Unit71

/-! ## The four modules in the source exercise -/

abbrev integerModule : ModuleCat ℤ := ModuleCat.of ℤ ℤ

abbrev integerModFourModule : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 4)

abbrev integerModEightModule : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 8)

abbrev rationalModule : ModuleCat ℤ := ModuleCat.of ℤ ℚ

abbrev modTwoModule : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 2)

/-- The additive group `ℚ/ℤ` used in the fourth case. -/
abbrev rationalModInteger : Type := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

abbrev rationalModIntegerModule : ModuleCat ℤ :=
  ModuleCat.of ℤ rationalModInteger

/-! ## The Ext computations -/

/-- `Ext^0_ℤ(ℤ, ℤ)` is `ℤ`, while all positive Ext groups vanish. -/
theorem ext_integer_integer_degree_zero :
    Nonempty (ExtGroup integerModule integerModule 0 ≃+ ℤ) := by
  sorry

theorem ext_integer_integer_positive_vanishes {i : ℕ} (hi : 0 < i) :
    Nonempty (ExtGroup integerModule integerModule i ≃+ (Fin 0 → ℤ)) := by
  sorry

/-- For the pair `(ℤ/4, ℤ/8)`, both `Ext^0` and `Ext^1` are `ℤ/4`, and
all higher Ext groups vanish. -/
theorem ext_mod_four_mod_eight_degree_zero :
    Nonempty (ExtGroup integerModFourModule integerModEightModule 0 ≃+ ZMod 4) := by
  sorry

theorem ext_mod_four_mod_eight_degree_one :
    Nonempty (ExtGroup integerModFourModule integerModEightModule 1 ≃+ ZMod 4) := by
  sorry

theorem ext_mod_four_mod_eight_higher_vanishes {i : ℕ} (hi : 2 ≤ i) :
    Nonempty
      (ExtGroup integerModFourModule integerModEightModule i ≃+ (Fin 0 → ZMod 4)) := by
  sorry

/-- All Ext groups from `ℚ` to `ℤ/2` vanish. -/
theorem ext_rational_mod_two_vanishes (i : ℕ) :
    Nonempty (ExtGroup rationalModule modTwoModule i ≃+ (Fin 0 → ZMod 2)) := by
  sorry

/-- For the pair `(ℤ/2, ℚ/ℤ)`, degree zero is `ℤ/2` and all positive
degrees vanish. -/
theorem ext_mod_two_rational_mod_integer_degree_zero :
    Nonempty (ExtGroup modTwoModule rationalModIntegerModule 0 ≃+ ZMod 2) := by
  sorry

theorem ext_mod_two_rational_mod_integer_positive_vanishes {i : ℕ} (hi : 0 < i) :
    Nonempty
      (ExtGroup modTwoModule rationalModIntegerModule i ≃+ (Fin 0 → ZMod 2)) := by
  sorry

end Formalization.Books.Exercises.Unit11
