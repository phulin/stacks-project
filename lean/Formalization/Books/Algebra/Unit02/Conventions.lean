import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Matrix.Diagonal
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Commutative Algebra, Chapter 2: Conventions

The source uses “ring” for a commutative ring with a multiplicative identity.
This is Mathlib's `CommRing` typeclass.  It does not include a
`Nontrivial` assumption, so the canonical one-element ring `PUnit` is
included.

The source's assertion that the zero ring is the only ring with no prime
ideal is recorded below in the equivalent form `0 = 1`.  The proof uses
Mathlib's stronger characterization of an empty prime spectrum by a
subsingleton ring.

The Kronecker symbol `δᵢⱼ` is a notation convention rather than a new
construction.  For identity matrices its standard Mathlib realization is
`Matrix.one_apply`, which is `1` on the diagonal and `0` off the diagonal.

For a ring homomorphism `f : R →+* S` and `q : PrimeSpectrum S`, the source's
notation `R ∩ q` is represented by the existing construction
`PrimeSpectrum.comap f q`; its underlying ideal is
`Ideal.comap f q.asIdeal` by `PrimeSpectrum.comap_asIdeal`.  The type of `f`
has no injectivity hypothesis, and the construction likewise does not require
that `R` be a subring of `S`.
-/

namespace Formalization.Books.Algebra.Unit02

universe u

/- The source-facing version of “the zero ring is the only ring with no prime
   ideal.” -/
theorem primeSpectrum_isEmpty_iff_zero_eq_one (R : Type u) [CommRing R] :
    IsEmpty (PrimeSpectrum R) ↔ (0 : R) = 1 :=
  PrimeSpectrum.isEmpty_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm

end Formalization.Books.Algebra.Unit02
