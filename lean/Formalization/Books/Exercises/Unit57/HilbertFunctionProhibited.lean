import Formalization.Books.Exercises.Unit57.HilbertFunctionAllowed

/-!
# Exercises, Chapter 57: a prohibited Hilbert function

This file records the numerical consequence of the three initial values in
the source.
-/

namespace Formalization.Books.Exercises.Unit57

universe u

theorem hilbertFunction_third_le_seven
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h0 : hilbertFunction R 0 = 1)
    (h1 : hilbertFunction R 1 = 3)
    (h2 : hilbertFunction R 2 = 5) :
    hilbertFunction R 3 ≤ 7 := by
  sorry

end Formalization.Books.Exercises.Unit57
