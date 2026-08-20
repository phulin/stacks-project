import Formalization.Books.Exercises.Unit57.Definitions

import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Exercises, Chapter 57: a prime over the maximal ideal

The finite ring map is represented by an `A`-algebra structure on `B` and the
source's finiteness hypothesis by `Module.Finite A B`.  A prime ideal is
represented by a `PrimeSpectrum` point, so contraction is the canonical
`Ideal.comap`.
-/

namespace Formalization.Books.Exercises.Unit57

universe u

noncomputable section

/-! ## Exercise `finite-injective` -/

/-- A finite injective algebra over a local ring has a prime over its maximal
ideal, with the prescribed contraction. -/
theorem exists_prime_over_maximalIdeal_of_finite_injective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) :
    ∃ q : PrimeSpectrum B,
      q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A := by
  let faithful : FaithfulSMul A B :=
    { eq_of_smul_eq_smul := by
        intro a₁ a₂ h
        apply hinj
        simpa [Algebra.smul_def] using h (1 : B) }
  obtain ⟨Q, hQmax, hQover⟩ :=
    @Ideal.exists_maximal_ideal_liesOver_of_isIntegral _ _ _ _ _ _ faithful
      (IsLocalRing.maximalIdeal A) inferInstance
  refine ⟨⟨Q, hQmax.isPrime⟩, ?_⟩
  rcases hQover with ⟨hQover⟩
  simpa using hQover.symm

end

end Formalization.Books.Exercises.Unit57
