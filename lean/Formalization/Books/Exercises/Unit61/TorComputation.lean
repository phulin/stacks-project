import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exercises, Chapter 61: Tor computation

The Tor groups are taken from Mathlib's categorical left-derived tensor
construction on `ModuleCat`.  The source indexes degrees by integers, so the
small adapter below records nonvanishing only for nonnegative degrees and
uses the canonical natural degree for `CategoryTheory.Tor`.
-/

namespace Formalization.Books.Exercises.Unit61

open CategoryTheory

universe u

noncomputable section

/-- The ring `ℂ[x,y,z]` in the Tor computation. -/
abbrev torPolynomialRing := MvPolynomial (Fin 3) ℂ

/-- The module `R/(x,z)`. -/
abbrev torFirstModule : Type :=
  torPolynomialRing ⧸
    Ideal.span
      ({MvPolynomial.X (0 : Fin 3), MvPolynomial.X (2 : Fin 3)} :
        Set torPolynomialRing)

/-- The module `R/(y,z)`. -/
abbrev torSecondModule : Type :=
  torPolynomialRing ⧸
    Ideal.span
      ({MvPolynomial.X (1 : Fin 3), MvPolynomial.X (2 : Fin 3)} :
        Set torPolynomialRing)

/-- The canonical categorical Tor group in a natural degree. -/
noncomputable abbrev torGroup (i : ℕ) : ModuleCat torPolynomialRing :=
  ((CategoryTheory.Tor (ModuleCat torPolynomialRing) i).obj
      (ModuleCat.of torPolynomialRing torFirstModule)).obj
    (ModuleCat.of torPolynomialRing torSecondModule)

/-- Nonvanishing of the source's integer-indexed Tor computation. -/
def TorComputationNonzero (i : ℤ) : Prop :=
  0 ≤ i ∧ Nontrivial (torGroup i.toNat)

/-- For `M = R/(x,z)` and `N = R/(y,z)`, Tor is nonzero exactly in degrees
zero and one. -/
theorem tor_computation_nonzero_iff (i : ℤ) :
    TorComputationNonzero i ↔ i = 0 ∨ i = 1 := by
  sorry

end

end Formalization.Books.Exercises.Unit61
