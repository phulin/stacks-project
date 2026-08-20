import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RingHom.Flat

import Formalization.Books.Algebra.Unit72.Depth

/-!
# Exercises, Chapter 61: Depth goes up

Flatness is expressed by Mathlib's `RingHom.Flat`, while locality is the
canonical `IsLocalHom` instance on the ring homomorphism.  The depth values
are the established `Formalization.Books.Algebra.Unit72.localDepth` of each
ring viewed as its regular module.
-/

namespace Formalization.Books.Exercises.Unit61

universe u v

noncomputable section

/-- A flat local homomorphism of Noetherian local rings cannot decrease the
depth of the ring. -/
theorem depth_goes_up_of_flat_local_hom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hflat : RingHom.Flat f)
    (k : ℕ∞)
    (hdepth : Formalization.Books.Algebra.Unit72.localDepth A A = k) :
    k ≤ Formalization.Books.Algebra.Unit72.localDepth B B := by
  sorry

end

end Formalization.Books.Exercises.Unit61
