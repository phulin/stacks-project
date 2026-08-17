import Formalization.Books.Exercises.Unit57.Definitions

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Exercises, Chapter 57: components of a coordinate hypersurface

The four-variable polynomial ring is represented by `MvPolynomial (Fin 4) k`,
with indices `0, 1, 2, 3` corresponding to `x, y, z, w`.  Components of the
zero locus are written as subsets of the zero-locus subtype, matching
Mathlib's `irreducibleComponents` interface for a closed subspace.
-/

namespace Formalization.Books.Exercises.Unit57

open Set

universe u

noncomputable section

/-! ## The polynomial ring, ideal, and its two candidate components -/

abbrev fourVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 4) k

def coordinateXIdeal (k : Type u) [Field k] :
    Ideal (fourVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 4)} : Set (fourVariablePolynomialRing k))

def coordinateYZWIdeal (k : Type u) [Field k] :
    Ideal (fourVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4),
      MvPolynomial.X (3 : Fin 4)} : Set (fourVariablePolynomialRing k))

def coordinateVarietyIdeal (k : Type u) [Field k] :
    Ideal (fourVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4),
      MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4),
      MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (3 : Fin 4)} :
      Set (fourVariablePolynomialRing k))

def coordinateVariety (k : Type u) [Field k] :
    Set (PrimeSpectrum (fourVariablePolynomialRing k)) :=
  PrimeSpectrum.zeroLocus (coordinateVarietyIdeal k : Set (fourVariablePolynomialRing k))

def coordinateXComponent (k : Type u) [Field k] :
    Set (coordinateVariety k) :=
  {p | (p : PrimeSpectrum (fourVariablePolynomialRing k)) ∈
    PrimeSpectrum.zeroLocus (coordinateXIdeal k : Set (fourVariablePolynomialRing k))}

def coordinateYZWComponent (k : Type u) [Field k] :
    Set (coordinateVariety k) :=
  {p | (p : PrimeSpectrum (fourVariablePolynomialRing k)) ∈
    PrimeSpectrum.zeroLocus (coordinateYZWIdeal k : Set (fourVariablePolynomialRing k))}

/-! ## Exercise `find-components` -/

/-- The two irreducible components of `V(xy, xz, xw)` are `V(x)` and
`V(y,z,w)`, of dimensions three and one respectively. -/
theorem irreducible_components_of_coordinate_variety
    (k : Type u) [Field k] :
    (coordinateVarietyIdeal k).minimalPrimes =
        {coordinateXIdeal k, coordinateYZWIdeal k} ∧
      irreducibleComponents (coordinateVariety k) =
        {coordinateXComponent k, coordinateYZWComponent k} ∧
      ringKrullDim
          (fourVariablePolynomialRing k ⧸ coordinateXIdeal k) =
        (3 : WithBot ℕ∞) ∧
      ringKrullDim
          (fourVariablePolynomialRing k ⧸ coordinateYZWIdeal k) =
        (1 : WithBot ℕ∞) := by
  sorry

end

end Formalization.Books.Exercises.Unit57
