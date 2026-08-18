import Formalization.Books.Algebra.Unit151.UnramifiedRingMaps
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 152: Local structure of unramified ring maps

This file records the local standard-étale presentation and the two étale
neighborhood separation statements in the section.
-/

namespace Formalization.Books.Algebra.Unit152

open Set
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Locally standard presentations -/

/-- If `R → S` is unramified at `q`, it is locally a quotient of a standard
étale algebra.  `HasStandardEtaleSurjectionOn` is Mathlib's canonical
predicate for the standard-étale algebra and surjection in the source
proposition. -/
theorem proposition_unramified_locally_standard
    {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S)
    (h : Formalization.Books.Algebra.Unit151.UnramifiedAt R S q) :
    ∃ g : S, g ∉ q.asIdeal ∧ HasStandardEtaleSurjectionOn R g := by
  sorry

/-! ## Étale neighborhoods at a chosen point -/

/-- Data expressing that an étale base change separates a chosen unramified
point as a closed factor.  The first factor is represented by `A`, while the
remaining factor is `B`. -/
structure EtaleClosedAtPrimeData
    {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) where
  R' : Type v
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : Algebra.Etale R R'
  p' : PrimeSpectrum R'
  p'_over : PrimeSpectrum.comap (algebraMap R R') p' = p
  A : Type max u v
  [commRingA : CommRing A]
  [algebraR'A : Algebra R' A]
  B : Type max u v
  [commRingB : CommRing B]
  [algebraR'B : Algebra R' B]
  decomposition :
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    (R' ⊗[R] S) ≃ₐ[R'] A × B
  surjective : Function.Surjective (algebraMap R' A)
  pA : PrimeSpectrum A
  pA_eq_map : pA.asIdeal = p'.asIdeal.map (algebraMap R' A)
  pA_over_p' : PrimeSpectrum.comap (algebraMap R' A) pA = p'
  pA_over_q :
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    PrimeSpectrum.comap
        (((RingHom.fst A B).comp decomposition.toRingEquiv.toRingHom).comp
          (Algebra.TensorProduct.includeRight :
            S →ₐ[R] R' ⊗[R] S).toRingHom) pA = q

/-- An étale neighborhood of a finite-type unramified point has a closed
factor containing that point. -/
theorem lemma_etale_makes_unramified_closed_at_prime
    {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (hfinite : Algebra.FiniteType R S)
    (hunramified : Formalization.Books.Algebra.Unit151.UnramifiedAt R S q) :
    Nonempty (EtaleClosedAtPrimeData (R := R) (S := S) p q hq) := by
  sorry

/-! ## Separation of all points in a fiber -/

/-- Data for an étale neighborhood on which every point in a fiber is a
surjective closed factor and the complementary factor has no point over the
chosen base prime. -/
structure EtaleSeparatedUnramifiedData
    {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) where
  R' : Type v
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : Algebra.Etale R R'
  p' : PrimeSpectrum R'
  p'_over : PrimeSpectrum.comap (algebraMap R R') p' = p
  n : ℕ
  A : Fin n → Type max u v
  [commRingA : ∀ i, CommRing (A i)]
  [algebraR'A : ∀ i, Algebra R' (A i)]
  B : Type max u v
  [commRingB : CommRing B]
  [algebraR'B : Algebra R' B]
  decomposition :
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    (R' ⊗[R] S) ≃ₐ[R'] (∀ i, A i) × B
  surjective : ∀ i, Function.Surjective (algebraMap R' (A i))
  pA : ∀ i, PrimeSpectrum (A i)
  pA_eq_map : ∀ i, (pA i).asIdeal = p'.asIdeal.map (algebraMap R' (A i))
  pA_over_p' : ∀ i,
    PrimeSpectrum.comap (algebraMap R' (A i)) (pA i) = p'
  noPrimeOver : ∀ qB : PrimeSpectrum B,
    PrimeSpectrum.comap (algebraMap R' B) qB ≠ p'

/-- After an étale base change, the points in an unramified fiber can be
separated into surjective closed factors. -/
theorem lemma_etale_makes_unramified_closed
    {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) [Algebra.Unramified R S] :
    Nonempty (EtaleSeparatedUnramifiedData (R := R) (S := S) p) := by
  sorry

end

end Formalization.Books.Algebra.Unit152
