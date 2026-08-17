import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit35.JacobsonRings
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Commutative Algebra, Chapter 61: Applications of dimension theory

The source's dimension-zero and Jacobson criteria are stated using Mathlib's
canonical Krull dimension, spectra, finite-dimensional modules, Artinian and
Jacobson predicates, and discrete topologies.  The fourth condition in the
finite-type equivalence is represented by condition (5) of the earlier
"only minimal primes" characterization: there are no nontrivial inclusions
between prime ideals.
-/

namespace Formalization.Books.Algebra.Unit61

open Set

universe u

noncomputable section

/-! ## Infinite spectra and finite-prime rings -/

/-- A nonempty open subset of the spectrum of a Noetherian local domain of
dimension at least two is infinite. -/
theorem nonempty_open_primeSpectrum_infinite_of_local_noetherian_domain_dim_ge_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hdim : 2 ≤ ringKrullDim R)
    {U : Set (PrimeSpectrum R)} (hUopen : IsOpen U)
    (hUnonempty : U.Nonempty) :
    U.Infinite := by
  sorry

/-- A Noetherian ring with finitely many prime ideals has Krull dimension at
most one. -/
theorem noetherian_ring_with_finite_primeSpectrum_dim_le_one
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [Finite (PrimeSpectrum R)] :
    ringKrullDim R ≤ 1 := by
  sorry

/- The source's examples are the one-variable formal power-series ring over a
   field and the ring of p-adic integers.  The latter is the only p-adic
   interpretation compatible with the stated dimension-one conclusion. -/

/-- Formal power series over a field give a Noetherian dimension-one ring with
finitely many prime ideals. -/
theorem powerSeries_field_is_noetherian_dim_one_finite_primeSpectrum
    (k : Type u) [Field k] :
    IsNoetherianRing (PowerSeries k) ∧
      ringKrullDim (PowerSeries k) = 1 ∧
        Finite (PrimeSpectrum (PowerSeries k)) := by
  sorry

/-- The p-adic integers give a Noetherian dimension-one ring with finitely
many prime ideals. -/
theorem padicIntegers_is_noetherian_dim_one_finite_primeSpectrum
    (p : ℕ) [Fact p.Prime] :
    IsNoetherianRing ℤ_[p] ∧
      ringKrullDim ℤ_[p] = 1 ∧
        Finite (PrimeSpectrum ℤ_[p]) := by
  sorry

/-! ## Finite-type algebras of dimension zero -/

/-- For a nonzero finite-type algebra over a field, the seven conditions in
the source are equivalent.  The fourth condition uses the earlier equivalent
formulation that prime ideals have no nontrivial inclusions. -/
theorem finite_type_algebra_finite_nr_primes
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Nontrivial S] :
    List.TFAE
      [ ringKrullDim S = 0
      , Finite (PrimeSpectrum S)
      , Finite (MaximalSpectrum S)
      , ∀ p q : Ideal S, p.IsPrime → q.IsPrime → p ≤ q → p = q
      , FiniteDimensional k S
      , IsArtinianRing S
      , DiscreteTopology (PrimeSpectrum S) ] := by
  sorry

/-! ## Noetherian Jacobson rings -/

/-- A Noetherian domain of dimension one with infinitely many primes is a
Jacobson ring. -/
theorem noetherian_domain_dim_one_infinite_primes_isJacobson
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1)
    (hinfinite : Infinite (PrimeSpectrum R)) :
    IsJacobsonRing R := by
  sorry

/-- A Noetherian ring is Jacobson when every prime is either maximal or is
contained in infinitely many prime ideals. -/
theorem noetherian_ring_isJacobson_of_prime_maximal_or_infinite_over
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hprime : ∀ p : Ideal R, p.IsPrime →
      p.IsMaximal ∨
        Set.Infinite {q : Ideal R | q.IsPrime ∧ p ≤ q}) :
    IsJacobsonRing R := by
  sorry

end

end Formalization.Books.Algebra.Unit61
