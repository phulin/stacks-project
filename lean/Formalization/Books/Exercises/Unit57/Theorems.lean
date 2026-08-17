import Formalization.Books.Exercises.Unit57.Definitions

import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Formalization.Books.Algebra.Unit114.DimensionFiniteTypeAlgebras
import Formalization.Books.Algebra.Unit29.ImagesOfFinitePresentation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Exercises, Chapter 57: theorem statements

The source asks for one precise lecture fact related to each of four topics.
The declarations below use the existing project and Mathlib interfaces; the
proofs are intentionally deferred.
-/

namespace Formalization.Books.Exercises.Unit57

open Set
open _root_.Topology

universe u v

noncomputable section

/-! ## Regular rings -/

/-- A polynomial algebra over a field is a regular ring. -/
theorem polynomial_ring_over_field_is_regular
    (k : Type u) [Field k] (n : ℕ) :
    IsRegularRing (MvPolynomial (Fin n) k) := by
  sorry

/-! ## Associated primes of Cohen--Macaulay modules -/

/-- An associated prime of a finite Cohen--Macaulay module is minimal in its
support; the displayed dimension equality is the stronger standard form. -/
theorem associated_prime_of_cohen_macaulay_module_is_minimal
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : Formalization.Books.Algebra.Unit103.IsCohenMacaulay R M)
    (p : PrimeSpectrum R)
    (hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) :
    ringKrullDim (R ⧸ p.asIdeal) = Module.supportDim R M ∧
      Minimal (fun q : PrimeSpectrum R => q ∈ Module.support R M) p := by
  exact
    Formalization.Books.Algebra.Unit103.associatedPrime_is_minimal_support_of_isCohenMacaulay
      hM p hp

/-! ## Dimension of finite-type domains over a field -/

/-- For a finite-type domain over a field, the ring dimension agrees with the
dimension of every maximal localization. -/
theorem finite_type_domain_dimension_at_maximal
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S]
    (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  exact Formalization.Books.Algebra.Unit114.dimension_spell_it_out (k := k) (S := S) m

/-! ## Chevalley's theorem -/

/-- The image of a constructible subset under the spectrum map of a finitely
presented ring homomorphism is constructible. -/
theorem chevalley_constructible_image
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : RingHom.FinitePresentation f)
    {E : Set (PrimeSpectrum S)} (hE : IsConstructible E) :
    IsConstructible (PrimeSpectrum.comap f '' E) := by
  exact PrimeSpectrum.isConstructible_comap_image hf hE

end

end Formalization.Books.Exercises.Unit57
