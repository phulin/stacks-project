import Formalization.Books.Sets.Unit01.Introduction

/-!
# Set Theory, Chapter 2: Everything is a set

This section explains how the usual mathematical structures can be unfolded
into set-theoretic data.  The concrete set-coded interfaces needed by the
discussion are already supplied by the preceding chapter:

* `Formalization.Books.Sets.Unit01.IsOrderedPair` uses the Kuratowski pair
  `{{a}, {a, b}}`;
* `Formalization.Books.Sets.Unit01.IsTopologyOn` says that a family `d` is a
  topology on the carrier `c`; and
* `Formalization.Books.Sets.Unit01.IsTopologicalSpaceEncoding` packages the
  carrier and its topology as an ordered pair.

The other definitions in the source are the canonical typed interfaces
already imported by that file: `TopologicalSpace`,
`AlgebraicGeometry.RingedSpace`, `AlgebraicGeometry.LocallyRingedSpace`, and
`AlgebraicGeometry.Scheme`.  They are not duplicated here with parallel
set-coded structures.  In particular, Mathlib's `Scheme.local_affine`
records the source's local affine-neighbourhood condition.

The final observation about writing a first-order formula for “is a scheme”
concerns metamathematical definability rather than a concrete object or
proposition in this chapter, so it requires no additional Lean declaration.
-/

namespace Formalization.Books.Sets.Unit02

end Formalization.Books.Sets.Unit02
