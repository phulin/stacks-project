import Formalization.Books.MoreAlgebra.Unit41.RegularRingMaps
import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings

/-!
# More Algebra, Chapter 42: Ascending properties along regular ring maps

This file records the four ascent statements in the source section.  The
regularity hypothesis uses the canonical regular-ring-map predicate from the
preceding chapter; the ring properties use the canonical predicates from the
earlier Algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit42

open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit104
open Formalization.Books.MoreAlgebra.Unit41

universe u

noncomputable section

/-! ## Reducedness -/

/-- Reducedness ascends along a regular map with Noetherian source and target.
-/
theorem reduced_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hregular : IsRegularRingMap f)
    [IsNoetherianRing S] [IsNoetherianRing R]
    (hR : IsReduced R) :
    IsReduced S := by
  sorry

/-! ## Normality -/

/-- Normality ascends along a regular map with Noetherian source and target.
-/
theorem normal_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hregular : IsRegularRingMap f)
    [IsNoetherianRing S] [IsNoetherianRing R]
    (hR : IsNormalRing R) :
    IsNormalRing S := by
  sorry

/-! ## Regularity -/

/-- Regularity ascends along a regular map with Noetherian source and target.
-/
theorem regular_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hregular : IsRegularRingMap f)
    [IsNoetherianRing S] (hR : IsRegularRing R) :
    IsRegularRing S := by
  sorry

/-! ## Cohen--Macaulayness -/

/-- Cohen–Macaulayness ascends along a regular map with Noetherian source and
target.
-/
theorem cohenMacaulay_goes_up
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hregular : IsRegularRingMap f)
    [IsNoetherianRing S] [IsNoetherianRing R]
    (hR : IsCohenMacaulayRing R) :
    IsCohenMacaulayRing S := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit42
