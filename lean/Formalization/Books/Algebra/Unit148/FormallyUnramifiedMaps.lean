import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Mathlib.RingTheory.RingHom.Unramified

/-!
# Commutative Algebra, Chapter 148: Formally unramified maps

The formally unramified predicate is Mathlib's canonical
`Algebra.FormallyUnramified` class.  The declarations below expose the
square-zero lifting, base-change, localization, local, and filtered-colimit
statements from the source section.
-/

namespace Formalization.Books.Algebra.Unit148

open scoped TensorProduct

noncomputable section

universe u v

/-! ## The lifting definition and the differential criterion -/

/-- The source's square-zero lifting definition of formal unramifiedness. -/
theorem formallyUnramified_iff_lifting
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallyUnramified R S ↔
      ∀ {A : Type u} [CommRing A] [Algebra R A]
        (I : Ideal A) (_hI : I ^ 2 = ⊥),
        Function.Injective
          ((Ideal.Quotient.mkₐ R I).comp :
            (S →ₐ[R] A) → S →ₐ[R] A ⧸ I) := by
  simpa using (Algebra.FormallyUnramified.iff_comp_injective (R := R) (A := S))

/-- Formal unramifiedness is stable under arbitrary base change. -/
theorem formallyUnramified_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (h : Algebra.FormallyUnramified R S) :
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    Algebra.FormallyUnramified R' (R' ⊗[R] S) := by
  sorry

/-- Formal unramifiedness is equivalent to vanishing Kähler differentials. -/
theorem formallyUnramified_iff_differentials
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallyUnramified R S ↔
      Subsingleton (KaehlerDifferential R S) :=
  Algebra.formallyUnramified_iff R S

/-! ## Local and localized forms -/

/-- The canonical algebra structure on the two localizations at a prime and its
contraction. -/
@[instance_reducible]
noncomputable def localizedAtPrimeAlgebra
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    Algebra (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
      (Localization.AtPrime q.asIdeal) :=
  (Localization.localRingHom _ _ _ rfl).toAlgebra

/-- The three local characterizations of a formally unramified map. -/
theorem formallyUnramified_iff_local
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE
      [ Algebra.FormallyUnramified R S,
        ∀ q : PrimeSpectrum S, Algebra.IsUnramifiedAt R q.asIdeal,
        ∀ q : PrimeSpectrum S,
          letI : Algebra
              (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
              (Localization.AtPrime q.asIdeal) :=
            localizedAtPrimeAlgebra q
          Algebra.FormallyUnramified
            (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
            (Localization.AtPrime q.asIdeal) ] := by
  sorry

/-- The formal-unramified property is preserved by localization.  This is the
canonical Mathlib statement for localization of the target. -/
theorem formallyUnramified_localization :
    RingHom.HoldsForLocalization RingHom.FormallyUnramified :=
  RingHom.FormallyUnramified.holdsForLocalization

/-- Formal unramifiedness is preserved by the canonical map between arbitrary
source and target localizations. -/
theorem formallyUnramified_localize_source_and_target
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    {M : Submonoid A} {T : Submonoid B}
    [Algebra A A'] [IsLocalization M A']
    [Algebra B B'] [IsLocalization T B']
    {f : A →+* B} (hM : M ≤ Submonoid.comap f T)
    (hf : RingHom.FormallyUnramified f) :
    RingHom.FormallyUnramified
      (IsLocalization.map (S := A') B' f hM) := by
  sorry

/-! ## Directed colimits -/

/-- A directed colimit of formally unramified algebras is formally unramified. -/
theorem formallyUnramified_directedColimit
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (D : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit
      (algebraMap R S))
    (h : ∀ i,
      letI : Preorder D.index := D.indexPreorder
      RingHom.FormallyUnramified (D.diagram.obj i).hom.hom) :
    Algebra.FormallyUnramified R S := by
  sorry

end

end Formalization.Books.Algebra.Unit148
