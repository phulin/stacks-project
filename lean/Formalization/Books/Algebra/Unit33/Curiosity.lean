import Formalization.Books.Algebra.Unit31.NoetherianRings
import Mathlib.Algebra.Ring.Prod
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.NoetherianSpace

/-!
# Commutative Algebra, Chapter 33: Curiosity

The two source lemmas are represented using Mathlib's canonical localization
`Localization`, spectrum map `PrimeSpectrum.comap`, closed-set predicate
`IsClosed`, Noetherian-ring predicate `IsNoetherianRing`, Noetherian-space
predicate `TopologicalSpace.NoetherianSpace`, and finitely generated-submonoid
predicate `Submonoid.FG`.  The quotient statement records that its ideal is the
kernel of the canonical localization map, which is the ideal used by the
subsequent product-decomposition argument.
-/

namespace Formalization.Books.Algebra.Unit33

universe u

/-! ## Closed images of localization spectra -/

/-- A localization whose spectrum image is closed is a quotient of the base ring. -/
theorem localization_closed_image_quotient
    {R : Type u} [CommRing R] (S : Submonoid R)
    (hclosed :
      IsClosed
        (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    ∃ I : Ideal R,
      I = RingHom.ker (algebraMap R (Localization S)) ∧
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
          PrimeSpectrum.zeroLocus (I : Set R) ∧
        Nonempty (Localization S ≃+* R ⧸ I) := by
  sorry

/-- Under any of the source's finiteness hypotheses, the localization splits off
as a direct product factor of the original ring. -/
theorem localization_closed_image_product
    {R : Type u} [CommRing R] (S : Submonoid R)
    (hclosed :
      IsClosed
        (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S)))))
    (hfinite :
      IsNoetherianRing R ∨
        TopologicalSpace.NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    ∃ (R' : Type u) (hR' : CommRing R'),
      letI : CommRing R' := hR'
      Nonempty (R ≃+* (Localization S × R')) := by
  sorry

end Formalization.Books.Algebra.Unit33
