import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Examples, Chapter 31: A nonfinite module with finite free rank 1 stalks

This file records the constructions and theorem interfaces in the source
section.  The proposition proofs belong to the proving stage.
-/

noncomputable section

namespace Formalization.«Books.Examples».Unit31

/-! ## The fractional module over `ℚ[x]` -/

/-- The polynomial ring `R = ℚ[x]` used in the example. -/
abbrev exampleBaseRing := Polynomial ℚ

/-- The fraction ring containing the displayed fractional generators. -/
abbrev exampleFractionRing := FractionRing exampleBaseRing

/-- The denominator `x - n` in `ℚ[x]`. -/
def exampleDenominator (n : ℕ) : exampleBaseRing :=
  Polynomial.X - Polynomial.C (n : ℚ)

/-- The element `1 / (x - n)` in the fraction ring of `ℚ[x]`. -/
def exampleFractionalGenerator (n : ℕ) : exampleFractionRing :=
  (algebraMap exampleBaseRing exampleFractionRing (exampleDenominator n))⁻¹

/-- The `ℚ[x]`-submodule `M = ∑ₙ (1 / (x - n)) R` in the fraction ring. -/
def exampleModule : Submodule exampleBaseRing exampleFractionRing :=
  Submodule.span exampleBaseRing (Set.range exampleFractionalGenerator)

abbrev ExampleModule := (exampleModule : Type)

/-- The localization `Rₚ` of `R` at a prime ideal `p`. -/
abbrev exampleBaseRingAtPrime (p : Ideal exampleBaseRing) [p.IsPrime] :=
  Localization p.primeCompl

/-- The localization `Mₚ` of `M` at the same prime ideal. -/
abbrev exampleModuleAtPrime (p : Ideal exampleBaseRing) [p.IsPrime] :=
  LocalizedModule p.primeCompl ExampleModule

/-- The module `M` is not finitely generated over `ℚ[x]`. -/
theorem exampleModule_not_finite :
    ¬ Module.Finite exampleBaseRing ExampleModule := by
  sorry

/-- Every prime localization of `M` is a free rank-one module over `Rₚ`. -/
theorem exampleModule_localized_equiv
    (p : Ideal exampleBaseRing) [p.IsPrime] :
    Nonempty (exampleModuleAtPrime p ≃ₗ[exampleBaseRingAtPrime p]
      exampleBaseRingAtPrime p) := by
  sorry

/-! ## The analogous prime-reciprocal module over `ℤ` -/

/-- The base ring `R = ℤ` in the analogous example. -/
abbrev integerExampleBaseRing := ℤ

/-- The ambient fraction field `ℚ` in the analogous example. -/
abbrev integerExampleFractionRing := ℚ

/-- The element `1 / p` of `ℚ` for a prime natural number `p`. -/
def integerExampleFractionalGenerator (p : Nat.Primes) :
    integerExampleFractionRing :=
  (algebraMap integerExampleBaseRing integerExampleFractionRing (p.1 : ℤ))⁻¹

/-- The `ℤ`-submodule `M = ∑ₚ (1 / p) ℤ` in `ℚ`. -/
def integerExampleModule :
    Submodule integerExampleBaseRing integerExampleFractionRing :=
  Submodule.span integerExampleBaseRing (Set.range integerExampleFractionalGenerator)

/-- The set of rational fractions with a nonzero squarefree natural denominator. -/
def integerExampleSquarefreeFractions : Set integerExampleFractionRing :=
  {q | ∃ a : ℤ, ∃ b : ℕ, b ≠ 0 ∧ Squarefree b ∧
    q = (a : ℚ) / (b : ℚ)}

/-- The prime-reciprocal module consists exactly of the squarefree-denominator fractions. -/
theorem integerExampleModule_eq_squarefreeFractions :
    (integerExampleModule : Set integerExampleFractionRing) =
      integerExampleSquarefreeFractions := by
  sorry

end Formalization.«Books.Examples».Unit31
