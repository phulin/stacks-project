import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.KrullDimension

/-!
# Exercises, Chapter 63: Two vectors

The source condition is encoded as failure of linear independence after base
change to the residue field at a prime.  The three two-by-two minors are kept
explicit because their zero locus is the closed dependence locus.
-/

namespace Formalization.Books.Exercises.Unit63

open Set

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The polynomial ring in the six coordinates of two vectors in dimension 3. -/
abbrev TwoVectorsRing := MvPolynomial (Fin 6) R

/-- The coordinate vectors in `R[a₁,a₂,a₃,b₁,b₂,b₃]`. -/
def twoVectorsA : Fin 3 → TwoVectorsRing R :=
  ![MvPolynomial.X (0 : Fin 6), MvPolynomial.X (1 : Fin 6),
    MvPolynomial.X (2 : Fin 6)]

def twoVectorsB : Fin 3 → TwoVectorsRing R :=
  ![MvPolynomial.X (3 : Fin 6), MvPolynomial.X (4 : Fin 6),
    MvPolynomial.X (5 : Fin 6)]

/-- The three two-by-two minors of the coordinate matrix. -/
def twoVectorsMinors : Set (TwoVectorsRing R) :=
  {twoVectorsA R 0 * twoVectorsB R 1 - twoVectorsA R 1 * twoVectorsB R 0,
   twoVectorsA R 0 * twoVectorsB R 2 - twoVectorsA R 2 * twoVectorsB R 0,
   twoVectorsA R 1 * twoVectorsB R 2 - twoVectorsA R 2 * twoVectorsB R 1}

def twoVectorsMinorIdeal : Ideal (TwoVectorsRing R) :=
  Ideal.span (twoVectorsMinors R)

/-- The condition that the two vectors become linearly dependent at a prime. -/
def TwoVectorsDependentAt (p : PrimeSpectrum (TwoVectorsRing R)) : Prop :=
  ¬ LinearIndependent p.asIdeal.ResidueField
      ![fun i => algebraMap (TwoVectorsRing R) p.asIdeal.ResidueField (twoVectorsA R i),
       fun i => algebraMap (TwoVectorsRing R) p.asIdeal.ResidueField (twoVectorsB R i)]

/-- The dependence locus in the spectrum. -/
def twoVectorsZ : Set (PrimeSpectrum (TwoVectorsRing R)) :=
  {p | TwoVectorsDependentAt R p}

/-- The dependence locus is the zero locus of the three minors. -/
theorem twoVectorsZ_eq_zeroLocus :
    twoVectorsZ R = PrimeSpectrum.zeroLocus (twoVectorsMinorIdeal R) := by
  sorry

/-- The dependence locus is closed. -/
theorem twoVectorsZ_isClosed : IsClosed (twoVectorsZ R) := by
  sorry

/-! ## Dimensions -/

/-- Over `ℤ`, the determinantal dependence locus has dimension five. -/
theorem twoVectorsZ_dimension_over_integers :
    topologicalKrullDim (↥(twoVectorsZ ℤ)) = (5 : WithBot ℕ∞) := by
  sorry

/-- Over a field, the same dependence locus has dimension four. -/
theorem twoVectorsZ_dimension_over_field
    (k : Type u) [Field k] :
    topologicalKrullDim (↥(twoVectorsZ k)) = (4 : WithBot ℕ∞) := by
  sorry

end

end Formalization.Books.Exercises.Unit63
