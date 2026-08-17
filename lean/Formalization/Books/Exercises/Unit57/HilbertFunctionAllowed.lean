import Formalization.Books.Exercises.Unit57.Definitions
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Exercises, Chapter 57: Hilbert functions

The source's successive quotients are represented by the canonical submodule
quotient.  Writing the denominator as the maximal ideal acting on the
`n`th-power submodule gives the quotient its canonical residue-field module
structure.
-/

namespace Formalization.Books.Exercises.Unit57

universe u

noncomputable section

/-- The `n`th associated-graded piece `𝔪^n / 𝔪^(n+1)` of a local ring. -/
abbrev hilbertGradedPiece
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) : Type u :=
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let N : Submodule R R := m ^ n • (⊤ : Submodule R R)
  N ⧸ (m • (⊤ : Submodule R N))

/-- The Hilbert function `φ_R(n) = dim_κ(𝔪^n / 𝔪^(n+1))`. -/
def hilbertFunction
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) : ℕ :=
  Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (hilbertGradedPiece R n)

/-- There is a noetherian local ring whose Hilbert function is `n + 1`. -/
theorem exists_noetherian_local_ring_hilbertFunction_eq_succ :
    ∃ (R : Type u) (hR : CommRing R) (hlocal : IsLocalRing R)
      (hnoeth : IsNoetherianRing R),
      ∀ n : ℕ, @hilbertFunction R hR hlocal hnoeth n = n + 1 := by
  sorry

end

end Formalization.Books.Exercises.Unit57
