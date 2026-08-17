import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.KrullDimension

/-!
# Exercises, Chapter 21: Dimension of fibres

This file fixes the polynomial-ring, fibre, and component notation used by
the two exercises in the chapter.  Ring extensions are represented by the
canonical `RingHom` interface: the source inclusions are injective ring
homomorphisms of finite type, and a fibre is the quotient by the mapped
source ideal.
-/

namespace Formalization.Books.Exercises.Unit21

universe u v

noncomputable section

/-! ## Polynomial rings and source ideals -/

/- The source's `k[x]` and `k[x₁, ..., xₙ]` use Mathlib's canonical
   univariate and finitely supported multivariate polynomial rings. -/

/-- The one-variable polynomial ring in the source notation `k[x]`. -/
abbrev oneVariablePolynomialRing (k : Type u) [CommRing k] := Polynomial k

/-- The `n`-variable polynomial ring in the source notation
`k[x₁, ..., xₙ]`. -/
abbrev nVariablePolynomialRing (k : Type u) [CommRing k] (n : ℕ) :=
  MvPolynomial (Fin n) k

/-- The two-variable polynomial ring in the source notation `k[x, y]`. -/
abbrev twoVariablePolynomialRing (k : Type u) [CommRing k] :=
  nVariablePolynomialRing k 2

/-- The principal ideal `(x)` in `k[x]`. -/
def oneVariableOriginIdeal (k : Type u) [CommRing k] :
    Ideal (oneVariablePolynomialRing k) :=
  Ideal.span {Polynomial.X}

/-- The point ideal `(x - α)` in `k[x]`. -/
def oneVariablePointIdeal (k : Type u) [CommRing k] (α : k) :
    Ideal (oneVariablePolynomialRing k) :=
  Ideal.span {Polynomial.X - Polynomial.C α}

/-- The point ideal `(x - α, y - β)` in `k[x, y]`. -/
def twoVariablePointIdeal (k : Type u) [CommRing k] (α β : k) :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2) - MvPolynomial.C α,
      MvPolynomial.X (1 : Fin 2) - MvPolynomial.C β} :
      Set (twoVariablePolynomialRing k))

/-- The origin ideal `(x₁, ..., xₙ)` in `k[x₁, ..., xₙ]`. -/
def coordinateOriginIdeal (k : Type u) [CommRing k] (n : ℕ) :
    Ideal (nVariablePolynomialRing k n) :=
  Ideal.span (Set.range (fun i : Fin n => MvPolynomial.X i))

/-! ## Fibres and their dimensions -/

/- The mapped ideal is the canonical image under the extension map.  Thus the
   quotient below is exactly `A / IA` for a source ideal `I`. -/

/-- The fibre quotient of a ring map over a source ideal. -/
abbrev fibreRing
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) : Type v :=
  A ⧸ I.map f

/-- The cardinality of the irreducible components of a fibre. -/
def fibreComponentCardinal
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) : ℕ∞ :=
  Set.encard (irreducibleComponents (PrimeSpectrum (fibreRing f I)))

/-- The source property that a fibre spectrum is irreducible. -/
def fibreIsIrreducible
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) : Prop :=
  IsIrreducible (Set.univ : Set (PrimeSpectrum (fibreRing f I)))

/-- The source property that a fibre spectrum is reducible. -/
def fibreIsReducible
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) : Prop :=
  ¬ fibreIsIrreducible f I

/-- The topological Krull dimension of a fibre component. -/
def fibreComponentDimension
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R)
    (C : Set (PrimeSpectrum (fibreRing f I))) : WithBot ℕ∞ :=
  topologicalKrullDim C

end

end Formalization.Books.Exercises.Unit21
