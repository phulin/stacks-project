import Formalization.Books.Smoothing.Unit01.Introduction

/-!
# Smoothing Ring Maps, Chapter 12: The main theorem

The section closes the proof of Popescu's theorem.  The theorem interface is
repeated here as the chapter-owned declaration, while its established
filtered-smooth-colimit package and regular-map hypothesis are reused from
the earlier formalization.
-/

namespace Formalization.Books.Smoothing.Unit12

open Formalization.Books.Algebra.Unit147
open Formalization.Books.MoreAlgebra.Unit41

noncomputable section

universe u

/-! ## The main theorem -/

/-- Any regular homomorphism of Noetherian rings is a filtered colimit of
smooth ring maps. -/
theorem popescu
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hregular : IsRegularRingMap f) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (FilteredSmoothAlgebraColimit R S) := by
  exact Formalization.Books.Smoothing.Unit01.popescu_main_theorem f hregular

end

end Formalization.Books.Smoothing.Unit12
