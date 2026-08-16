import Mathlib.Data.Matrix.Diagonal
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Commutative Algebra, Chapter 2: Conventions

The book's word “ring” is represented by Mathlib's `CommRing` typeclass.  In
particular, `CommRing` does not impose `Nontrivial`, so the zero ring is
included.  The assertion that it is the only commutative ring with no prime
ideal is already recorded by the stronger canonical equivalences
`PrimeSpectrum.nonempty_iff_nontrivial` and
`PrimeSpectrum.isEmpty_iff_subsingleton`.

For a ring homomorphism `f : R →+* S` and a prime `q : PrimeSpectrum S`, the
book's notation `R ∩ q` is represented by `PrimeSpectrum.comap f q`; on
underlying ideals this is `Ideal.comap f q.asIdeal`.  These are the existing
Mathlib constructions and require neither a subring inclusion nor an
injectivity hypothesis.

The Kronecker symbol is used through the standard identity-matrix entry API
`Matrix.one_apply`, whose value is `1` on the diagonal and `0` off it.
-/

