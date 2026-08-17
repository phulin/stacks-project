import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Commutative Algebra, Chapter 19: The Jacobson radical of a ring

The Jacobson radical is represented by Mathlib's canonical `Ring.jacobson`
ideal.  This file records the source-facing facts about that ideal, the
criterion for an ideal to be contained in it, and the criterion for units
along a ring map whose map on spectra is surjective.
-/

namespace Formalization.Books.Algebra.Unit19

universe u v

noncomputable section

/-! The recalled description of the Jacobson radical and its local-ring case. -/

theorem jacobson_radical_eq_sInf_maximal (R : Type u) [CommRing R] :
    Ring.jacobson R = sInf {I : Ideal R | I.IsMaximal} :=
  Ring.jacobson_eq_sInf_isMaximal R

theorem jacobson_radical_eq_maximalIdeal (R : Type u) [CommRing R]
    [IsLocalRing R] :
    Ring.jacobson R = IsLocalRing.maximalIdeal R :=
  IsLocalRing.ringJacobson_eq_maximalIdeal R

/-! The first lemma in the source section. -/

theorem ideal_le_jacobson_iff_one_add_isUnit {R : Type u} [CommRing R]
    (I : Ideal R) :
    I ≤ Ring.jacobson R ↔ ∀ x ∈ I, IsUnit (1 + x) := by
  sorry

theorem isUnit_of_isUnit_quotient_of_le_jacobson {R : Type u} [CommRing R]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  sorry

/-! The second lemma in the source section. -/

theorem isUnit_iff_isUnit_map_of_spec_surjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective (PrimeSpectrum.comap φ)) (x : R) :
    IsUnit x ↔ IsUnit (φ x) := by
  sorry

end

end Formalization.Books.Algebra.Unit19
