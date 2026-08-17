import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Spectrum.Prime.Topology

import Formalization.Books.Exercises.Unit16.Core

/-!
# Exercises, Chapter 16: Hilbert Nullstellensatz

The declarations follow the numbered exercises and remarks in the source.
The proofs are intentionally left for the prove stage; the definitions use
Mathlib's canonical polynomial, power-series, spectrum, and spectrum-topology
objects directly.
-/

noncomputable section

universe u

open Set

namespace Formalization.Books.Exercises.Unit16

/-! ## Exercise `uncountable` -/

/-- The rational function field `ℂ(X)` has uncountable vector-space dimension
over `ℂ`. -/
theorem rational_function_field_uncountable_dimension :
    Cardinal.aleph0 < Module.rank ℂ (RatFunc ℂ) := by
  sorry

/-- Mathlib's spectrum agrees with the source's convention for a linear
operator: `λ` is spectral precisely when `T - λ • id` is not a unit. -/
theorem linear_operator_spectrum_mem_iff
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (z : ℂ) :
    z ∈ spectrum ℂ T ↔
      ¬ IsUnit (T - algebraMap ℂ (Module.End ℂ V) z) := by
  sorry

/-- Every endomorphism of a nonzero finite- or countable-dimensional complex
vector space has nonempty spectrum. -/
theorem linear_operator_spectrum_nonempty
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (T : V →ₗ[ℂ] V)
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0) :
    (spectrum ℂ T).Nonempty := by
  sorry

/-- A finite-type complex algebra which is a field has bijective structure
map from `ℂ`. -/
theorem complex_finite_type_field_algebraMap_bijective
    {R : Type u} [Field R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] :
    Function.Bijective (algebraMap ℂ R) := by
  sorry

/-- Every maximal ideal of `ℂ[x₁, ..., xₙ]` is a coordinate maximal ideal. -/
theorem complex_polynomial_maximal_ideal_eq_coordinate
    (n : ℕ) (m : Ideal (polynomialRing ℂ n)) (hm : m.IsMaximal) :
    ∃ α : Fin n → ℂ,
      m = polynomialCoordinateIdeal ℂ n α := by
  sorry

/-! ## Remark `HNSS` -/

/-- A maximal ideal in a polynomial algebra over a field has a finite field
extension as quotient. -/
theorem polynomial_maximal_ideal_quotient_finite_field_extension
    (k : Type u) [Field k] (n : ℕ)
    (m : Ideal (polynomialRing k n)) (hm : m.IsMaximal) :
    IsField (polynomialRing k n ⧸ m) ∧
      Module.Finite k (polynomialRing k n ⧸ m) := by
  sorry

/-- The same finite-field-extension conclusion for maximal ideals of any
finite-type algebra over a field. -/
theorem finite_type_maximal_ideal_quotient_finite_field_extension
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R]
    (m : Ideal R) (hm : m.IsMaximal) :
    IsField (R ⧸ m) ∧ Module.Finite k (R ⧸ m) := by
  sorry

/-! ## Exercise `Hilbert-Nullstellensatz` -/

/-- A finite-dimensional domain algebra over a field is a field. -/
theorem finite_dimensional_domain_algebra_is_field
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    [Module.Finite k R] [IsDomain R] :
    IsField R := by
  exact IsField.of_isDomain_of_finite k R

/-- A nonnilpotent element of a finite-type algebra is avoided by a maximal
ideal. -/
theorem finite_type_exists_maximal_ideal_not_mem
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (f : R) (hf : ¬ IsNilpotent f) :
    ∃ m : Ideal R, m.IsMaximal ∧ f ∉ m := by
  sorry

/-! ### The non-finite-type counterexample -/

/-- The ring used for the counterexample is the formal power-series ring. -/
abbrev powerSeriesCounterexampleRing (k : Type u) [Semiring k] := PowerSeries k

/-- The counterexample element is the formal variable `X`. -/
def powerSeriesCounterexampleElement (k : Type u) [Semiring k] :
    powerSeriesCounterexampleRing k :=
  PowerSeries.X

/-- Formal power series over a field are not finite type as algebras over that
field. -/
theorem power_series_counterexample_not_finite_type
    (k : Type u) [Field k] :
    ¬ Algebra.FiniteType k (powerSeriesCounterexampleRing k) := by
  sorry

/-- The formal variable in the power-series counterexample is not nilpotent. -/
theorem power_series_counterexample_element_not_nilpotent
    (k : Type u) [Field k] :
    ¬ IsNilpotent (powerSeriesCounterexampleElement k) := by
  sorry

/-- The unique maximal ideal description of formal power series over a field. -/
theorem power_series_counterexample_maximal_ideal
    (k : Type u) [Field k] :
    IsLocalRing.maximalIdeal (powerSeriesCounterexampleRing k) =
      Ideal.span {powerSeriesCounterexampleElement k} := by
  simpa [powerSeriesCounterexampleRing, powerSeriesCounterexampleElement] using
    (PowerSeries.maximalIdeal_eq_span_X (k := k))

/-- Every maximal ideal in the power-series counterexample contains `X`. -/
theorem power_series_counterexample_maximal_ideals_contain_element
    (k : Type u) [Field k] :
    ∀ m : Ideal (powerSeriesCounterexampleRing k),
      m.IsMaximal → powerSeriesCounterexampleElement k ∈ m := by
  sorry

/-- A radical ideal in `ℂ[x₁, ..., xₙ]` is the infimum of the maximal ideals
which contain it. -/
theorem complex_polynomial_radical_ideal_eq_intersection_maximal_ideals
    (n : ℕ) (I : Ideal (polynomialRing ℂ n)) (hI : I.IsRadical) :
    I = sInf {m : Ideal (polynomialRing ℂ n) | I ≤ m ∧ m.IsMaximal} := by
  sorry

/-! ## Remark `Hilbert-Nullstellensatz` -/

/-- Closed subsets of an affine polynomial spectrum are exactly the zero loci
of radical ideals. -/
theorem polynomial_closed_sets_correspond_to_radical_ideals
    (k : Type u) [Field k] (n : ℕ)
    (Z : Set (PrimeSpectrum (polynomialRing k n))) :
    IsClosed Z ↔
      ∃ I : Ideal (polynomialRing k n), I.IsRadical ∧
        Z = PrimeSpectrum.zeroLocus (I : Set (polynomialRing k n)) := by
  sorry

/-- Closed subsets of the spectrum of a finite-variable polynomial ring are
determined by the maximal ideals, equivalently the closed points, they contain. -/
theorem polynomial_closed_subsets_determined_by_closed_points
    (k : Type u) [Field k] (n : ℕ)
    {Z W : Set (PrimeSpectrum (polynomialRing k n))}
    (hZ : IsClosed Z) (hW : IsClosed W)
    (hclosed : ∀ p : PrimeSpectrum (polynomialRing k n),
      p.asIdeal.IsMaximal → (p ∈ Z ↔ p ∈ W)) :
    Z = W := by
  sorry

/-! ## Exercise `product-matrices-ring` -/

/-- The polynomial ring in the matrix-product exercise.  Variables `0` through
`3` are the entries of `X`, and variables `4` through `7` those of `Y`, in
row-major order. -/
abbrev matrixProductRing := polynomialRing ℂ 8

/-- The four entries of the matrix product `XY`. -/
def matrixProductEquations : Set matrixProductRing :=
  {
    MvPolynomial.X (0 : Fin 8) * MvPolynomial.X (4 : Fin 8) +
        MvPolynomial.X (1 : Fin 8) * MvPolynomial.X (6 : Fin 8),
    MvPolynomial.X (0 : Fin 8) * MvPolynomial.X (5 : Fin 8) +
        MvPolynomial.X (1 : Fin 8) * MvPolynomial.X (7 : Fin 8),
    MvPolynomial.X (2 : Fin 8) * MvPolynomial.X (4 : Fin 8) +
        MvPolynomial.X (3 : Fin 8) * MvPolynomial.X (6 : Fin 8),
    MvPolynomial.X (2 : Fin 8) * MvPolynomial.X (5 : Fin 8) +
        MvPolynomial.X (3 : Fin 8) * MvPolynomial.X (7 : Fin 8)
  }

/-- The ideal generated by the entries of the displayed matrix product. -/
def matrixProductIdeal : Ideal matrixProductRing :=
  Ideal.span matrixProductEquations

/-- The determinant of the `X` matrix in the matrix-product exercise. -/
def matrixXDeterminant : matrixProductRing :=
  MvPolynomial.X (0 : Fin 8) * MvPolynomial.X (3 : Fin 8) -
    MvPolynomial.X (1 : Fin 8) * MvPolynomial.X (2 : Fin 8)

/-- The determinant of the `Y` matrix in the matrix-product exercise. -/
def matrixYDeterminant : matrixProductRing :=
  MvPolynomial.X (4 : Fin 8) * MvPolynomial.X (7 : Fin 8) -
    MvPolynomial.X (5 : Fin 8) * MvPolynomial.X (6 : Fin 8)

/-- The component on which the matrix `X` is zero. -/
def matrixXZeroIdeal : Ideal matrixProductRing :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 8), MvPolynomial.X (1 : Fin 8),
      MvPolynomial.X (2 : Fin 8), MvPolynomial.X (3 : Fin 8)} :
      Set matrixProductRing)

/-- The component on which the matrix `Y` is zero. -/
def matrixYZeroIdeal : Ideal matrixProductRing :=
  Ideal.span
    ({MvPolynomial.X (4 : Fin 8), MvPolynomial.X (5 : Fin 8),
      MvPolynomial.X (6 : Fin 8), MvPolynomial.X (7 : Fin 8)} :
      Set matrixProductRing)

/-- The third component, cut out by `XY = 0` together with the two rank-one
determinant equations. -/
def matrixProductMiddleIdeal : Ideal matrixProductRing :=
  Ideal.span (matrixProductEquations ∪
    {matrixXDeterminant, matrixYDeterminant})

/-- The closed subset `V(I)` in the matrix-product exercise. -/
def matrixProductClosedSet : Set (PrimeSpectrum matrixProductRing) :=
  PrimeSpectrum.zeroLocus (matrixProductIdeal : Set matrixProductRing)

/-- The canonical correspondence between minimal primes over the matrix
product ideal and irreducible components of `V(I)`. -/
noncomputable def matrixProductComponentCorrespondence :
    matrixProductIdeal.minimalPrimes ≃o
      (irreducibleComponents matrixProductClosedSet)ᵒᵈ := by
  exact Ideal.minimalPrimes.equivIrreducibleComponents matrixProductIdeal

/-- The three irreducible components of `V(XY)`, represented by their prime
ideals of equations. -/
theorem matrix_product_irreducible_components :
    matrixProductIdeal.minimalPrimes =
      {matrixXZeroIdeal, matrixYZeroIdeal, matrixProductMiddleIdeal} := by
  sorry

end Formalization.Books.Exercises.Unit16
