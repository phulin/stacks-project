import Formalization.Books.Smoothing.Unit01.Introduction
import Formalization.Books.MoreAlgebra.Unit50

/-!
# Smoothing Ring Maps, Chapter 14: Approximation for henselian pairs

The source's completion is the canonical `ringCompletion`, polynomial systems
reuse Chapter 1's `SolvesPolynomialSystem`, and the henselian-pair and
G-ring predicates are reused from More on Algebra.  The theorem is stated
without its proof; the bridge below packages the source's phrase “is the
henselization of a pair” in a form invariant under the choice of a ring model.
-/

namespace Formalization.Books.Smoothing.Unit14

open Formalization.Books.Algebra.Unit96
open Formalization.Books.MoreAlgebra.Unit12
open Formalization.Books.MoreAlgebra.Unit41
open Formalization.Books.MoreAlgebra.Unit50
open Formalization.Books.Smoothing.Unit01

noncomputable section

universe u

/-! ## The henselization case -/

/-- Data identifying `(A, I)` with the henselization of a pair `(B, J)`.

The base ring is bundled as a `CommRingCat` object so that the existential
quantification carries its commutative-ring structure.  The ring equivalence
and the ideal equality make the identification independent of the chosen
representative of the henselization. -/
structure PairHenselizationWitness
    {A : Type u} [CommRing A] (I : Ideal A) where
  base : CommRingCat.{u}
  baseIdeal : Ideal (base : Type u)
  baseMap : (base : Type u) →+* A
  henselization : HenselizationData
    ({ ideal := baseIdeal } : Pair (base : Type u))
  equivalence : henselization.carrier ≃+* A
  equivalence_map : equivalence.toRingHom.comp henselization.map = baseMap
  equivalence_ideal :
    Ideal.map equivalence.toRingHom
        (Ideal.map henselization.map baseIdeal) = I

/-- The three alternative hypotheses in the chapter's approximation lemma.
The `IsGRing` predicate includes the source's Noetherian requirement on the
base of the henselization in the third alternative. -/
def HenselianPairApproximationHypotheses
    {A : Type u} [CommRing A] (I : Ideal A) : Prop :=
  IsRegularRingMap (algebraMap A (ringCompletion I)) ∨
    IsGRing A ∨
      ∃ witness : PairHenselizationWitness I,
        IsGRing (witness.base : Type u)

/-! ## Approximation -/

/-- Approximation of a solution of a finite polynomial system over the
completion of a Noetherian henselian pair. -/
theorem approximation_for_henselian_pair
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    (hI : HenselianPair ({ ideal := I } : Pair A))
    (hconditions : HenselianPairApproximationHypotheses I)
    {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) A)
    (ahat : Fin n → ringCompletion I)
    (hahat : SolvesPolynomialSystem
      (algebraMap A (ringCompletion I)) f ahat) :
    ∀ N : ℕ, 1 ≤ N →
      ∃ a : Fin n → A,
        (∀ i, ahat i - algebraMap A (ringCompletion I) (a i) ∈
          completionPowerIdeal I N) ∧
        SolvesPolynomialSystem (RingHom.id A) f a := by
  sorry

end

end Formalization.Books.Smoothing.Unit14
