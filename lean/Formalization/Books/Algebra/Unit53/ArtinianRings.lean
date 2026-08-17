import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Commutative Algebra, Chapter 53: Artinian rings

The source's Artinian condition is Mathlib's canonical `IsArtinianRing`.
The source's locally nilpotent ideal condition is the elementwise predicate
`Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal` from Chapter 3.
-/

namespace Formalization.Books.Algebra.Unit53

open Set

universe u v

noncomputable section

/-! ## Artinian rings -/

/- The definition in the source is exactly `IsArtinianRing`; no parallel
   wrapper is introduced. -/

theorem finiteDimensional_algebra_isArtinian
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] :
    IsArtinianRing R := by
  exact IsArtinianRing.of_finite k R

theorem artinian_finite_maximal_ideals
    {R : Type u} [CommRing R] [IsArtinianRing R] :
    Set.Finite {I : Ideal R | I.IsMaximal} :=
  IsArtinianRing.setOfPred_isMaximal_finite R

theorem artinian_jacobson_radical_is_nilpotent
    {R : Type u} [CommRing R] [IsArtinianRing R] :
    IsNilpotent (Ring.jacobson R) :=
  by
    simpa only [Ideal.jacobson_bot] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := R))

/- The product of localizations at maximal ideals is Mathlib's
   `MaximalSpectrum.PiLocalization`.  The conclusion also records the
   source's assertion that every prime is maximal. -/
theorem product_localizations_of_finite_maximal_ideals
    {R : Type u} [CommRing R]
    (hmax : Set.Finite {I : Ideal R | I.IsMaximal})
    (hjac : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal
      (Ring.jacobson R)) :
    (∀ p : Ideal R, p.IsPrime → p.IsMaximal) ∧
      Nonempty (R ≃ₐ[R] MaximalSpectrum.PiLocalization R) := by
  sorry

/- Hopkins--Levitzki supplies the source's Artinian/finite-length
   equivalence. -/
theorem artinian_iff_finite_length
    {R : Type u} [CommRing R] :
    IsArtinianRing R ↔ IsFiniteLength R R :=
  isArtinianRing_iff_isFiniteLength R

/- The remaining assertions in the source lemma are collected in one usable
   interface.  `Finite (MaximalSpectrum R)` records that the product is finite. -/
theorem finite_length_ring_properties
    {R : Type u} [CommRing R] (hR : IsFiniteLength R R) :
    IsArtinianRing R ∧
      IsNoetherianRing R ∧
      (∀ p : Ideal R, p.IsPrime → p.IsMaximal) ∧
      Finite (MaximalSpectrum R) ∧
      Nonempty (R ≃ₐ[R] MaximalSpectrum.PiLocalization R) := by
  sorry

end

end Formalization.Books.Algebra.Unit53
