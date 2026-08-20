import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Exercises, Chapter 61: Frobenius

Mathlib's `frobenius` is the canonical ring homomorphism in exponential
characteristic.  The source assumptions are recorded both in their explicit
form and in the typeclass form needed to use that construction.
-/

namespace Formalization.Books.Exercises.Unit61

universe u

noncomputable section

/-- The Frobenius ring homomorphism in characteristic `p`. -/
def frobeniusMap
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] : R →+* R :=
  frobenius R p

/-- Pointwise formula for the canonical Frobenius map. -/
theorem frobeniusMap_apply
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (x : R) :
    frobeniusMap R p x = x ^ p := by
  rfl

/-- The explicit source hypotheses admit a Frobenius ring homomorphism. -/
theorem exists_frobenius_ring_hom_of_char_p
    (R : Type u) [CommRing R] (p : ℕ) (hp : p.Prime) (hchar : (p : R) = 0) :
    ∃ F : R →+* R, ∀ x, F x = x ^ p := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨RingHom.id R, ?_⟩
    intro x
    have hx : x = 0 := @Subsingleton.elim R hR x 0
    rw [hx]
    simp [hp.ne_zero]
  · have hCharP : CharP R p :=
      (CharP.charP_iff_prime_eq_zero (R := R) hp).2 hchar
    let F : R →+* R :=
      @frobenius R _ p (@ExpChar.prime R _ p hp hCharP)
    refine ⟨F, ?_⟩
    intro x
    rfl

/-- Under the source's explicit hypotheses, Frobenius and its identity map on
the spectrum can be packaged together. -/
theorem exists_frobenius_ring_hom_and_spec_identity_of_char_p
    (R : Type u) [CommRing R] (p : ℕ) (hp : p.Prime) (hchar : (p : R) = 0) :
    ∃ F : R →+* R,
      (∀ x, F x = x ^ p) ∧ PrimeSpectrum.comap F = id := by
  obtain ⟨F, hF⟩ := exists_frobenius_ring_hom_of_char_p R p hp hchar
  refine ⟨F, hF, ?_⟩
  funext P
  apply PrimeSpectrum.ext
  ext a
  change F a ∈ P.asIdeal ↔ a ∈ P.asIdeal
  rw [hF]
  exact P.2.pow_mem_iff_mem p hp.pos

/-- The map induced by Frobenius on the prime spectrum is the identity. -/
theorem frobenius_spec_map_eq_identity
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    PrimeSpectrum.comap (frobeniusMap R p) = id := by
  funext P
  apply PrimeSpectrum.ext
  ext a
  change frobeniusMap R p a ∈ P.asIdeal ↔ a ∈ P.asIdeal
  rw [frobeniusMap_apply]
  exact P.2.pow_mem_iff_mem p (Nat.Prime.pos (Fact.out : p.Prime))

end

end Formalization.Books.Exercises.Unit61
