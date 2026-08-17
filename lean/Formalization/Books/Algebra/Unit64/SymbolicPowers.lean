import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 64: symbolic powers

The symbolic power is expressed using Mathlib's canonical localization at a
prime, ideal extension, quotient map, and ring-homomorphism kernel.  The
associated-prime statement uses Mathlib's canonical set of associated prime
ideals; under the chapter's Noetherian hypothesis this agrees with the exact
annihilator formulation recorded in Chapter 63.
-/

namespace Formalization.Books.Algebra.Unit64

universe u v

noncomputable section

/-! ## Symbolic powers -/

/-- The `n`th symbolic power of a prime ideal, defined as the kernel of
the map to the quotient of the localization by the extended ordinary power. -/
def symbolicPower {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (n : ℕ) : Ideal R :=
  RingHom.ker
    ((Ideal.Quotient.mk
        ((p ^ n).map (algebraMap R (Localization.AtPrime p)))).comp
      (algebraMap R (Localization.AtPrime p)))

/-- Ordinary powers are contained in the corresponding symbolic powers. -/
theorem pow_le_symbolicPower
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    p ^ n ≤ symbolicPower p n := by
  sorry

/-- Equality of ordinary and symbolic powers is not valid for all prime ideals. -/
theorem symbolicPower_eq_pow_not_general :
    ¬ ∀ (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ),
      p ^ n = symbolicPower p n := by
  sorry

/-! ## Associated primes -/

/-- For positive exponent, the symbolic-power quotient has exactly the given
prime ideal as its associated prime. -/
theorem associatedPrimes_symbolicPower
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] {n : ℕ} (hn : 0 < n) :
    _root_.associatedPrimes R (R ⧸ symbolicPower p n) = {p} := by
  sorry

/-! ## Flat extension -/

/-- Symbolic powers commute with a flat extension when the extended prime is
prime.  The displayed equality is the source's `q = pS` case, with `q`
retained as an explicit ideal to make the primality hypothesis available. -/
theorem symbolicPower_map_of_flat
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hflat : RingHom.Flat f)
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] (hq : q = p.map f) (n : ℕ) :
    (symbolicPower p n).map f = symbolicPower q n := by
  sorry

/- Unfolding `RingHom.ker` and `Ideal.Quotient.mk` gives the source's
`R ∩ p ^ n Rₚ` kernel description, so it needs no parallel intersection
definition.  The associated-prime proof also uses the fact that elements
outside `p` act regularly on the quotient.  The flat-extension proof reduces
to injectivity of the map between the two localized quotients, observes that
the target is a further localization, and uses the finite filtration by
powers of `p` with the displayed tensor-product/vector-space subquotients;
these are proof-level reductions and introduce no additional chapter-facing
construction. -/

end

end Formalization.Books.Algebra.Unit64
