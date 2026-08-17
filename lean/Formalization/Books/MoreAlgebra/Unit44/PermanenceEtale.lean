import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# More Algebra, Chapter 44: Permanence of properties under étale maps

This file records the local permanence results for an étale ring map.  Prime
localizations, Noetherian rings, Krull dimension, regular local rings,
Dedekind domains, and discrete valuation rings use Mathlib's canonical
interfaces.
-/

namespace Formalization.Books.MoreAlgebra.Unit44

universe u

/- The introductory flatness facts are already covered by Mathlib's
`RingHom.Etale.iff_flat_and_formallyUnramified` and
`Module.FaithfullyFlat.of_flat_of_isLocalHom`; no chapter-specific aliases
are needed. -/

/-! ## Noetherian localizations -/

/-- An étale map preserves Noetherianity of corresponding prime localizations.
-/
theorem isNoetherianRing_localization_atPrime_iff_of_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p) :
    IsNoetherianRing (Localization.AtPrime p.asIdeal) ↔
      IsNoetherianRing (Localization.AtPrime q.asIdeal) := by
  sorry

/-! ## Local dimension -/

/-- Corresponding prime localizations of an étale map have equal Krull
dimension. -/
theorem ringKrullDim_localization_atPrime_eq_of_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p) :
    ringKrullDim (Localization.AtPrime p.asIdeal) =
      ringKrullDim (Localization.AtPrime q.asIdeal) := by
  sorry

/-! ## Regular local rings -/

/-- Corresponding prime localizations of an étale map are regular local rings
simultaneously. -/
theorem isRegularLocalRing_localization_atPrime_iff_of_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) ↔
      IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  sorry

/-! ## Dedekind domains -/

/-- A ring is a finite product of Dedekind domains when it is ring-isomorphic
to a finite product of commutative Dedekind domains.

The bundled `CommRingCat` factors retain their ring structures while the
finite index type records that this is a finite product. -/
def IsFiniteProductOfDedekindDomains
    (B : Type u) [CommRing B] : Prop :=
  ∃ (ι : Type u) (hι : Fintype ι) (S : ι → CommRingCat.{u}),
    letI : Fintype ι := hι
    (∀ i, IsDedekindDomain (S i)) ∧
      Nonempty (B ≃+* (∀ i, (S i : Type u)))

/-- An étale extension of a Dedekind domain is a finite product of Dedekind
domains. -/
theorem isFiniteProductOfDedekindDomains_of_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f) [IsDedekindDomain A] :
    IsFiniteProductOfDedekindDomains B := by
  sorry

/-- If the base Dedekind domain is not a field, the localizations at maximal
ideals of an étale extension are discrete valuation rings.

The non-field hypothesis is needed because Mathlib's discrete valuation ring
notion excludes fields. -/
theorem isDiscreteValuationRing_localization_atPrime_of_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f) [IsDedekindDomain A]
    (hA : ¬ IsField A) :
    ∀ q : MaximalSpectrum B,
      ∃ hq : IsDomain (Localization.AtPrime q.asIdeal),
        @IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) _ hq := by
  sorry

end Formalization.Books.MoreAlgebra.Unit44
