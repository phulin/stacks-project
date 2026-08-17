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
  rw [← Ideal.jacobson_bot]
  constructor
  · intro h x hx
    have hunit := (Ideal.mem_jacobson_bot.mp (h hx)) 1
    simpa [add_comm] using hunit
  · intro h x hx
    apply Ideal.mem_jacobson_bot.mpr
    intro y
    simpa [add_comm] using h (x * y) (I.mul_mem_right y hx)

theorem isUnit_of_isUnit_quotient_of_le_jacobson {R : Type u} [CommRing R]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmem : x * y - 1 ∈ I := by
    rw [← Ideal.Quotient.mk_eq_one_iff_sub_mem]
    simpa only [map_mul] using hy
  apply isUnit_of_mul_isUnit_left
  simpa using
    (ideal_le_jacobson_iff_one_add_isUnit I).mp hI (x * y - 1) hmem

/-! The second lemma in the source section. -/

theorem isUnit_iff_isUnit_map_of_spec_surjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective (PrimeSpectrum.comap φ)) (x : R) :
    IsUnit x ↔ IsUnit (φ x) := by
  constructor
  · intro hx
    exact hx.map φ
  · intro hx
    by_contra hnx
    obtain ⟨M, hM, hMx⟩ := exists_max_ideal_of_mem_nonunits hnx
    let p : PrimeSpectrum R := ⟨M, hM.isPrime⟩
    obtain ⟨q, hq⟩ := hφ p
    have hxp : x ∈ (PrimeSpectrum.comap φ q).asIdeal := by
      rw [hq]
      exact hMx
    have hxq : φ x ∈ q.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using hxp
    exact (Ideal.notMem_of_isUnit q.asIdeal hx) hxq

end

end Formalization.Books.Algebra.Unit19
