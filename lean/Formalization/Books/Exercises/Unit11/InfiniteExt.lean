import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exercises, Chapter 11: Ext groups — non-finite Ext¹

An infinite square-zero extension of a field supplies a ring and ideal for
which the first self-Ext group of the residue module is not finite.
-/

namespace Formalization.Books.Exercises.Unit11

open Formalization.Books.Algebra.Unit71

universe u

noncomputable section

/-! ## An infinite square-zero example -/

/-- The infinite-dimensional square-zero module used in the example. -/
abbrev infiniteSquareZeroModule (k : Type u) [Field k] := ℕ →₀ k

/-- The trivial square-zero extension of `k` by an infinite-dimensional module. -/
abbrev infiniteSquareZeroRing (k : Type u) [Field k] :=
  TrivSqZeroExt k (infiniteSquareZeroModule k)

/-- The square-zero ideal in the trivial square-zero extension. -/
def infiniteSquareZeroIdeal (k : Type u) [Field k] :
    Ideal (infiniteSquareZeroRing k) :=
  TrivSqZeroExt.kerIdeal k (infiniteSquareZeroModule k)

/-- The residue module of the infinite square-zero extension. -/
abbrev infiniteSquareZeroResidueModule (k : Type u) [Field k] :
    ModuleCat (infiniteSquareZeroRing k) :=
  ModuleCat.of (infiniteSquareZeroRing k)
    (infiniteSquareZeroRing k ⧸ infiniteSquareZeroIdeal k)

/-- The first self-Ext of the residue module is not finite over the ring. -/
theorem infinite_square_zero_ext_one_not_finite (k : Type u) [Field k] :
    ¬ Module.Finite (infiniteSquareZeroRing k)
        (ExtGroup (infiniteSquareZeroResidueModule k)
          (infiniteSquareZeroResidueModule k) 1) := by
  sorry

/-! ## The Noetherian contrast -/

/-- Over a Noetherian ring, the corresponding Ext group of a quotient by an
ideal is finite. -/
theorem noetherian_quotient_ext_one_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Module.Finite R
      (ExtGroup (ModuleCat.of R (R ⧸ I))
        (ModuleCat.of R (R ⧸ I)) 1) := by
  let _ : Module.Finite R (R ⧸ I) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective R I)
  exact ext_finite_of_noetherian
    (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ I)) 1

end

end Formalization.Books.Exercises.Unit11
