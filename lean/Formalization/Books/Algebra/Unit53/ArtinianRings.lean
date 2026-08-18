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
  have hsInf : sInf {I : Ideal R | I.IsMaximal} ≤ nilradical R := by
    rw [← Ring.jacobson_eq_sInf_isMaximal R]
    intro x hx
    exact (mem_nilradical).2 (hjac x hx)
  have hdisc : DiscreteTopology (PrimeSpectrum R) :=
    (PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical).2
      ⟨(Set.finite_coe_iff).mp hmax, hsInf⟩
  have hdim : Ring.KrullDimLE 0 R :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero).mp hdisc |>.2
  have hprime : ∀ p : Ideal R, p.IsPrime → p.IsMaximal := by
    intro p hp
    exact (Ring.krullDimLE_zero_iff.mp hdim) p hp
  exact ⟨hprime, ⟨@MaximalSpectrum.toPiLocalizationEquiv R _ hdisc⟩⟩

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
  have hArt : IsArtinianRing R := (artinian_iff_finite_length (R := R)).2 hR
  have hN : IsNoetherianRing R :=
    ((IsArtinianRing.tfae R R).out 2 1).mp hArt
  have hmax : Set.Finite {I : Ideal R | I.IsMaximal} :=
    @artinian_finite_maximal_ideals R _ hArt
  have hjac₀ : IsNilpotent (Ring.jacobson R) :=
    @artinian_jacobson_radical_is_nilpotent R _ hArt
  have hjac : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal
      (Ring.jacobson R) := by
    obtain ⟨n, hn⟩ := hjac₀
    intro x hx
    refine ⟨n, ?_⟩
    have hxpow : x ^ n ∈ (Ring.jacobson R) ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hxpow
    exact hxpow
  have hprod := product_localizations_of_finite_maximal_ideals hmax hjac
  haveI : Finite {I : Ideal R // I.IsMaximal} := Set.finite_coe_iff.mp hmax
  have hfinite : Finite (MaximalSpectrum R) :=
    Finite.of_equiv _ (MaximalSpectrum.equivSubtype R).symm
  exact ⟨hArt, hN, hprod.1, hfinite, hprod.2⟩

end

end Formalization.Books.Algebra.Unit53
