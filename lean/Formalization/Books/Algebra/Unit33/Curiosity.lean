import Mathlib.Algebra.Category.Ring.Basic
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
predicate `Submonoid.FG`.
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
    ∃ I : Ideal R, Nonempty (Localization S ≃+* R ⧸ I) := by
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
    ∃ R' : CommRingCat.{u}, Nonempty (R ≃+* (Localization S × R')) := by
  sorry

end Formalization.Books.Algebra.Unit33
