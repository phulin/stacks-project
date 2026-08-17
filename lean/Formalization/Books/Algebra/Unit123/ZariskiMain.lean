import Formalization.Books.Algebra.Unit122.QuasiFinite
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Maps.Basic

/-!
# Commutative Algebra, Chapter 123: Zariski's Main Theorem

The chapter uses Mathlib's canonical `IsIntegral`, `integralClosure`,
`conductor`, `IsStronglyTranscendental`, `Algebra.QuasiFiniteAt`, and
`Algebra.ZariskisMainProperty` declarations.  The declarations below retain
the order and interfaces of the source while exposing the corresponding
Mathlib constructions in a chapter namespace.
-/

namespace Formalization.Books.Algebra.Unit123

open Set
open Polynomial

universe u v

noncomputable section

/-! ## The first integral-element lemmas -/

/- The source's coefficient relation is represented by evaluation of a
   polynomial.  `isIntegral_leadingCoeff_smul` is exactly the determinant-trick
   statement used in the source proof. -/
theorem make_integral_trivial
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : R[X]) (t : S) (hp : aeval t p = 0) :
    IsIntegral R (p.leadingCoeff • t) := by
  exact isIntegral_leadingCoeff_smul p t hp

/- The Euclidean-division step in the source is Mathlib's integral-subtraction
   interface for a monic polynomial. -/
theorem make_integral_trick
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (φ : R[X] →ₐ[R] S) (t : S) (ht : φ.IsIntegralElem t)
    (p : R[X]) (hp : p.Monic) (hpt : φ p * t ∈ φ.range) :
    ∃ q : R[X], IsIntegral R (t - φ q) := by
  exact exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range φ t p ht hp hpt

/- The leading coefficient and denominator-clearing conclusion is retained in
   the scalar form used by the canonical Mathlib theorem. -/
theorem combine_lemmas
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (φ : R[X] →ₐ[R] S) (t : S) (ht : φ.IsIntegralElem t)
    (p : R[X]) (hpt : φ p * t ∈ φ.range) :
    ∃ q : R[X], ∃ n : ℕ,
      IsIntegral R (p.leadingCoeff ^ n • t - φ q) := by
  exact exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
    φ t p ht hpt

/-! ## The one-transcendental-element situation -/

/- `integralClosure R S = ⊥` records that the image of `R` in `S` is
   integrally closed, without adding an injectivity assumption. -/
structure OneTranscendentalElementSituation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  φ : R[X] →ₐ[R] S
  finite : RingHom.Finite φ.toRingHom
  integralClosure_eq_bot : integralClosure R S = ⊥

/- Mathlib's conductor of `R[φ(X)]` is the source's ideal
   `J = {g | gS ⊆ Im(φ)}`. -/
def conductorIdeal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : OneTranscendentalElementSituation R S) : Ideal S :=
  conductor R (H.φ X)

theorem leading_coefficient_in_conductor
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : OneTranscendentalElementSituation R S) (u : S) (p : R[X])
    (hp : H.φ p * u ∈ conductorIdeal H) :
    ∃ n : ℕ, p.leadingCoeff ^ n • u ∈ conductorIdeal H := by
  simpa [conductorIdeal, mul_comm] using
    (exists_leadingCoeff_pow_smul_mem_conductor H.φ u p
      H.integralClosure_eq_bot H.finite hp)

theorem all_coefficients_in_radical_conductor
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : OneTranscendentalElementSituation R S) (u : S) (p : R[X])
    (hp : H.φ p * u ∈ (conductorIdeal H).radical) :
    ∀ i : ℕ, p.coeff i • u ∈ (conductorIdeal H).radical := by
  simpa [conductorIdeal, mul_comm] using
    (exists_leadingCoeff_pow_smul_mem_radical_conductor H.φ u p
      H.integralClosure_eq_bot H.finite hp)

/-! ## Strong transcendence -/

/- The source definition is Mathlib's `IsStronglyTranscendental`; no parallel
   predicate is introduced. -/
theorem strongly_transcendental_iff_fraction_ring
    {R S K : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Field K] [Algebra S K] [Algebra R K] [IsFractionRing S K]
    [IsScalarTower R S K] [FaithfulSMul R S] (x : S) :
    IsStronglyTranscendental R x ↔
      Transcendental R (algebraMap S K x) := by
  exact IsStronglyTranscendental.iff_of_isFractionRing K

theorem strongly_transcendental_iff_fraction_fields
    {R S K L : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [Algebra K L] [IsScalarTower R S L]
    [IsScalarTower R K L] [FaithfulSMul K L] (x : S) :
    IsStronglyTranscendental R x ↔
      Transcendental K (algebraMap S L x) := by
  sorry

/- The quotient-base formulation is kept explicit because the source contracts
   `R` to `R / (R ∩ q)` at a minimal prime. -/
theorem reduced_strongly_transcendental_minimal_prime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsReduced R] [IsReduced S]
    (x : S) (hx : IsStronglyTranscendental R x)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) :
    IsStronglyTranscendental (R ⧸ q.under R)
      (Ideal.Quotient.mk q x) := by
  sorry

/- In the domain case, the source's “finite over `R[x]`” hypothesis is the
   canonical finiteness of the evaluation map `R[X] → S`. -/
theorem domains_transcendental_not_quasi_finite
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S]
    (x : S) (hx : IsStronglyTranscendental R x)
    (hfinite : (aeval (R := R) x).toRingHom.Finite)
    (q : Ideal S) [q.IsPrime] :
    ¬ Algebra.QuasiFiniteAt R q := by
  intro hq
  exact (Algebra.not_isStronglyTranscendental_of_quasiFiniteAt hfinite q) hx

theorem reduced_strongly_transcendental_not_quasi_finite
    {R S : Type u} [CommRing R] [CommRing S] [IsReduced R] [IsReduced S]
    [Algebra R S]
    (x : S) (hx : IsStronglyTranscendental R x)
    (hfinite : (aeval (R := R) x).toRingHom.Finite)
    (q : Ideal S) [q.IsPrime] :
    ¬ Algebra.QuasiFiniteAt R q := by
  intro hq
  exact (Algebra.not_isStronglyTranscendental_of_quasiFiniteAt hfinite q) hx

/-! ## The monogenic case and Zariski's Main Theorem -/

/- The integral closure is represented by Mathlib's `integralClosure`, and the
   isomorphism of localizations is represented by bijectivity of its canonical
   localization map. -/
theorem quasi_finite_monogenic
    {R : Type u} [CommRing R] (I : Ideal R[X])
    (q : PrimeSpectrum (R[X] ⧸ I))
    [Algebra.QuasiFiniteAt R q.asIdeal] :
    ∃ g : integralClosure R (R[X] ⧸ I),
      g.1 ∉ q.asIdeal ∧
        Function.Bijective
          (Localization.awayMap (integralClosure R (R[X] ⧸ I)).val.toRingHom g) := by
  exact Algebra.ZariskisMainProperty.of_finiteType q.asIdeal

theorem zariskis_main_theorem
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    [Algebra.QuasiFiniteAt R q.asIdeal] :
    ∃ g : integralClosure R S, g.1 ∉ q.asIdeal ∧
      Function.Bijective
        (Localization.awayMap (integralClosure R S).val.toRingHom g) := by
  exact Algebra.ZariskisMainProperty.of_finiteType q.asIdeal

/-! ## Openness of the quasi-finite locus -/

def quasiFiniteLocus
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Set (PrimeSpectrum S) :=
  {q | Algebra.QuasiFiniteAt R q.asIdeal}

theorem isOpen_quasiFiniteLocus
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] :
    IsOpen (quasiFiniteLocus R S) := by
  sorry

/-! ## The quasi-finite integral-closure refinement -/

theorem quasi_finite_open_integral_closure
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] :
    Topology.IsOpenEmbedding
        (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) ∧
      (∀ g : integralClosure R S,
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (integralClosure R S))) ⊆
            Set.range (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) →
          Function.Bijective
            (Localization.awayMap (integralClosure R S).val.toRingHom g)) ∧
      ∃ S'' : Subalgebra R S,
        S'' ≤ integralClosure R S ∧
          Module.Finite R S'' ∧
            Topology.IsOpenEmbedding (PrimeSpectrum.comap S''.val.toRingHom) ∧
              (∀ g : S'',
                (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S'')) ⊆
                    Set.range (PrimeSpectrum.comap S''.val.toRingHom) →
                  Function.Bijective (Localization.awayMap S''.val.toRingHom g)) := by
  sorry

end

end Formalization.Books.Algebra.Unit123
