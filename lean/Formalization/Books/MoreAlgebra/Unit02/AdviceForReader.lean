import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# More on Algebra, Chapter 2: Advice for the reader

The source section is primarily reading advice: the sections are intended to
stand on their own. Its mathematical convention is that, from the section on
derived categories of modules onward, the unbounded derived category of
modules over a ring is used together with its standard machinery.

Mathlib's `DerivedCategory` is the localization of complexes indexed by
`ℤ`, so it supplies the unbounded derived category. The typeclass
`HasDerivedCategory` records the chosen localization; keeping that choice
explicit exposes the existing categorical machinery without introducing a
competing derived-category construction.
-/

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit02

/-!
This abbreviation exposes the source convention while delegating the
construction and all of its categorical machinery to Mathlib.
-/

/-- The unbounded derived category of modules over a ring. -/
abbrev UnboundedDerivedCategory (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] :=
  DerivedCategory (ModuleCat.{v} R)

end Formalization.Books.MoreAlgebra.Unit02
