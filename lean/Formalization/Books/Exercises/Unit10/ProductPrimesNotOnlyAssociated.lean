import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Exercises, Chapter 10: products of incomparable primes

The first result in this file is the general intersection statement.  The
second part records a concrete polynomial example where passing from an
intersection to a product creates an additional associated prime.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit10

/-! ## Intersections of incomparable primes -/

/-- The quotient by the intersection of two ideals.  The lattice meet is the
ideal-theoretic intersection. -/
abbrev intersectionPrimeQuotient {R : Type*} [CommRing R]
    (p q : Ideal R) := R ⧸ (p ⊓ q)

/-- In a Noetherian ring, incomparable prime ideals are exactly the associated
primes of the quotient by their intersection. -/
theorem associated_primes_intersection_prime_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) (hp : p.IsPrime) (hq : q.IsPrime)
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    associatedPrimes R (intersectionPrimeQuotient p q) =
      ({p, q} : Set (Ideal R)) := by
  sorry

/-! ## The product example in `k[x,y,z]` -/

/-- The three-variable polynomial ring used in the example. -/
abbrev productExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 3) k

/-- The coordinate variables. -/
def productExampleX (k : Type u) [Field k] : productExamplePolynomialRing k :=
  MvPolynomial.X (0 : Fin 3)

def productExampleY (k : Type u) [Field k] : productExamplePolynomialRing k :=
  MvPolynomial.X (1 : Fin 3)

def productExampleZ (k : Type u) [Field k] : productExamplePolynomialRing k :=
  MvPolynomial.X (2 : Fin 3)

/-- The incomparable primes `p=(x,y)` and `q=(x,z)`. -/
def productExamplePrimeP (k : Type u) [Field k] :
    Ideal (productExamplePolynomialRing k) :=
  Ideal.span ({productExampleX k, productExampleY k} :
    Set (productExamplePolynomialRing k))

def productExamplePrimeQ (k : Type u) [Field k] :
    Ideal (productExamplePolynomialRing k) :=
  Ideal.span ({productExampleX k, productExampleZ k} :
    Set (productExamplePolynomialRing k))

/-- The product quotient `R/(p q)`. -/
abbrev productExampleQuotient (k : Type u) [Field k] :=
  productExamplePolynomialRing k ⧸
    (productExamplePrimeP k * productExamplePrimeQ k)

/-- The maximal ideal `m=(x,y,z)` which becomes an associated prime of the
product quotient. -/
def productExampleMaximalIdeal (k : Type u) [Field k] :
    Ideal (productExamplePolynomialRing k) :=
  Ideal.span ({productExampleX k, productExampleY k, productExampleZ k} :
    Set (productExamplePolynomialRing k))

/-- The displayed polynomial ring is Noetherian. -/
theorem product_example_ring_is_noetherian (k : Type u) [Field k] :
    IsNoetherianRing (productExamplePolynomialRing k) := by
  infer_instance

/-- The two displayed ideals are incomparable prime ideals. -/
theorem product_example_primes_incomparable (k : Type u) [Field k] :
    (productExamplePrimeP k).IsPrime ∧
      (productExamplePrimeQ k).IsPrime ∧
      ¬ productExamplePrimeP k ≤ productExamplePrimeQ k ∧
      ¬ productExamplePrimeQ k ≤ productExamplePrimeP k := by
  sorry

/-- The maximal ideal is an associated prime of `R/(p q)` and is distinct from
both factors. -/
theorem product_example_has_extra_associated_prime (k : Type u) [Field k] :
    productExampleMaximalIdeal k ∈
        associatedPrimes (productExamplePolynomialRing k)
          (productExampleQuotient k) ∧
      productExampleMaximalIdeal k ≠ productExamplePrimeP k ∧
      productExampleMaximalIdeal k ≠ productExamplePrimeQ k := by
  sorry

end Formalization.Books.Exercises.Unit10
