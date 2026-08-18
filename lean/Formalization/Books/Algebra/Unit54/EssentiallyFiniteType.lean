import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Commutative Algebra, Chapter 54: Homomorphisms essentially of finite type

The source's essentially finite type condition is Mathlib's canonical
`RingHom.EssFiniteType` predicate.  Mathlib does not currently provide the
analogous essentially finite presentation predicate, so the source's second
definition is represented by the explicit intermediate-algebra predicate
below.
-/

namespace Formalization.Books.Algebra.Unit54

universe u v

/-! ## Definitions -/

/- The source's first definition is exactly `RingHom.EssFiniteType`; no
   parallel predicate is introduced. -/

/- The source's second definition allows an arbitrary intermediate algebra:
   its map to the target need not be injective before localization. -/
def essFinitePresentation
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (T : Type (max u v)) (hT : CommRing T),
    letI : CommRing T := hT
    ∃ (g : R →+* T) (M : Submonoid T) (q : T →+* S),
      RingHom.FinitePresentation g ∧
        q.comp g = algebraMap R S ∧
          letI : Algebra T S := q.toAlgebra
          IsLocalization M S

/- The ring-hom version uses the algebra structure induced by the map, just as
   Mathlib's `RingHom.EssFiniteType` does. -/
def RingHom.EssFinitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  essFinitePresentation R S

/- A quotient followed by a localization, with the displayed map retained,
   is the source-facing form needed in the final lemma. -/
def RingHom.IsLocalizationOfQuotient
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∃ (I : Ideal A) (M : Submonoid (A ⧸ I)) (q : (A ⧸ I) →+* B),
    q.comp (Ideal.Quotient.mk I) = f ∧
      letI : Algebra (A ⧸ I) B := q.toAlgebra
      IsLocalization M B

/-! ## Composition and base change -/

/- Mathlib supplies the composition and base-change interfaces for essentially
   finite type ring homomorphisms. -/
theorem essFiniteType_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.EssFiniteType f) (hg : RingHom.EssFiniteType g) :
    RingHom.EssFiniteType (g.comp f) := by
  exact RingHom.EssFiniteType.comp hf hg

theorem essFiniteType_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange @RingHom.EssFiniteType :=
  RingHom.EssFiniteType.isStableUnderBaseChange

/- The corresponding assertions for essentially finite presentation are
   recorded with the source's predicate. -/
theorem essFinitePresentation_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.EssFinitePresentation f)
    (hg : RingHom.EssFinitePresentation g) :
    RingHom.EssFinitePresentation (g.comp f) := by
  sorry

theorem essFinitePresentation_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange @RingHom.EssFinitePresentation := by
  sorry

/-! ## Essentially finite type maps into Artinian local rings -/

/- The three numbered assertions in the source lemma are kept as separate
   equivalences so that each finiteness notion can be used independently. -/
theorem finite_iff_finite_residue
    {R S : Type*} [CommRing R] [CommRing S]
    [IsArtinianRing S] [IsLocalRing S]
    (f : R →+* S) (m : Ideal S) [m.IsMaximal] :
    RingHom.Finite f ↔
      RingHom.Finite ((Ideal.Quotient.mk m).comp f) := by
  sorry

theorem finiteType_iff_finiteType_residue
    {R S : Type*} [CommRing R] [CommRing S]
    [IsArtinianRing S] [IsLocalRing S]
    (f : R →+* S) (m : Ideal S) [m.IsMaximal] :
    RingHom.FiniteType f ↔
      RingHom.FiniteType ((Ideal.Quotient.mk m).comp f) := by
  sorry

theorem essFiniteType_iff_essFiniteType_residue
    {R S : Type*} [CommRing R] [CommRing S]
    [IsArtinianRing S] [IsLocalRing S]
    (f : R →+* S) (m : Ideal S) [m.IsMaximal] :
    RingHom.EssFiniteType f ↔
      RingHom.EssFiniteType ((Ideal.Quotient.mk m).comp f) := by
  sorry

/-! ## Localization at a closed point of the special fibre -/

/- The polynomial ring is `MvPolynomial (Fin n) R`.  The maximal ideal is
   represented by `MaximalSpectrum`, which also supplies the prime instance
   needed for `Localization.AtPrime`. -/
theorem exists_localization_at_closed_point_special_fibre
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : RingHom.EssFiniteType f) :
    ∃ (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)),
      m.asIdeal.comap (algebraMap R (MvPolynomial (Fin n) R)) =
          IsLocalRing.maximalIdeal R ∧
        ∃ h : Localization.AtPrime m.asIdeal →+* S,
          h.comp
              ((algebraMap (MvPolynomial (Fin n) R)
                (Localization.AtPrime m.asIdeal)).comp
                (algebraMap R (MvPolynomial (Fin n) R))) = f ∧
            RingHom.IsLocalizationOfQuotient h := by
  sorry

end Formalization.Books.Algebra.Unit54
