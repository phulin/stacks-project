import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Formalization.Books.Exercises.Unit63.Definitions

/-!
# Exercises, Chapter 63: Tor and Ext

The canonical derived-functor objects are used for Tor and Ext.  For the
successive quotients of the maximal-ideal filtration, `Module.length` is the
ring-theoretic presentation of the residue-field dimension; the relevant
modules are finite length over a Noetherian local ring.
-/

namespace Formalization.Books.Exercises.Unit63

open CategoryTheory

universe u

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- A subquotient `P/Q`, with `Q` pulled back to the subtype `P`. -/
abbrev LocalGradedSubquotient
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    (P Q : Submodule R M) : Type u :=
  HasQuotient.Quotient (P : Type u) (Q.comap P.subtype)

/-- The quotient `𝔪ⁿ/𝔪ⁿ⁺¹`, written as a quotient of the submodule `𝔪ⁿ`. -/
abbrev LocalGradedPiece (n : ℕ) : Type u :=
  LocalGradedSubquotient
    ((IsLocalRing.maximalIdeal A) ^ n : Submodule A A)
    ((IsLocalRing.maximalIdeal A) ^ (n + 1) : Submodule A A)

/-- The Hilbert-function value, represented by the length of the graded piece. -/
def localPhi (n : ℕ) : ℕ∞ :=
  Module.length A (LocalGradedPiece (A := A) n)

/-- The canonical Tor group of two `A`-modules. -/
noncomputable abbrev TorGroup (M N : Type u) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (i : ℕ) : Type u :=
  (TorModule A (ModuleCat.of A M) (ModuleCat.of A N) i : Type u)

/-- The canonical Ext group of two `A`-modules. -/
noncomputable abbrev ExtGroup (M N : Type u) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (i : ℕ) : Type u :=
  (((Ext A (ModuleCat A) i).obj
      (Opposite.op (ModuleCat.of A M))).obj (ModuleCat.of A N) : Type u)

/-! ## The two dimension computations -/

/-- The first Tor group of `A/𝔪ⁿ` with the residue field has the expected
graded-piece length. The positive-index hypothesis makes the source's
implicit convention on `n` explicit. -/
theorem tor_one_power_quotient_length
    (n : ℕ) (hn : 0 < n) :
    Module.length A
        (TorGroup (A := A) (M := A ⧸ (IsLocalRing.maximalIdeal A) ^ n)
          (N := IsLocalRing.ResidueField A) 1) = localPhi (A := A) n := by
  sorry

/-- The first Ext group of `A/𝔪ⁿ` with the residue field has the same expected
graded-piece length. -/
theorem ext_one_power_quotient_length
    (n : ℕ) (hn : 0 < n) :
    Module.length A
        (ExtGroup (A := A) (M := A ⧸ (IsLocalRing.maximalIdeal A) ^ n)
          (N := IsLocalRing.ResidueField A) 1) = localPhi (A := A) n := by
  sorry

end

end Formalization.Books.Exercises.Unit63
