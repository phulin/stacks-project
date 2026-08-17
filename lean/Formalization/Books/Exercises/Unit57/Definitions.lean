import Formalization.Books.Algebra.Unit105.CatenaryRings
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Exercises, Chapter 57: definitions

The six italicized notions in the source already have canonical usable
declarations.  We therefore keep their established interfaces rather than
introducing aliases with the same mathematical content:

* the local ring of `R` at a prime `p` is `Localization.AtPrime p`;
* a finite module is expressed by the typeclass `Module.Finite R M`;
* a finitely presented module is expressed by
  `Module.FinitePresentation R M`;
* a regular ring is Mathlib's `IsRegularRing R`;
* a catenary ring is
  `Formalization.Books.Algebra.Unit105.IsCatenaryRing R`;
* a Cohen--Macaulay ring is
  `Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing R`.

These are definitions, not additional theorem interfaces: the declarations
above are the canonical constructions used by the later statements in this
chapter.
-/

namespace Formalization.Books.Exercises.Unit57

end Formalization.Books.Exercises.Unit57
