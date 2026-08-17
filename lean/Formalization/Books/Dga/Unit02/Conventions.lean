import Mathlib.Algebra.Algebra.Bilinear

/-!
# Differential Graded Algebra, Chapter 2: Conventions

The source convention that a ring is a commutative ring with `1` is already
Mathlib's `[CommRing R]` typeclass.  For an `R`-algebra `A`, the canonical
interface is `[Ring A] [Algebra R A]` (with `[CommRing R]`).  The `Ring A`
interface supplies the associative unital multiplication, while `Algebra R A`
supplies the `R`-module structure, the structure map, and its centrality.

The source's `R`-bilinear multiplication is the existing
`LinearMap.mul R A`; its application is the multiplication on `A`.  The
centrality reformulation is `Algebra.commutes`, and compatibility of scalar
multiplication with the structure map is `Algebra.smul_def`.  Thus the source
definition is represented directly by Mathlib's interfaces; no parallel local
algebra structure is introduced.

The sign-rules paragraph is a compatibility convention for the graded
constructions that follow.  It does not specify an independent predicate or
operation in this section, so it is recorded here rather than duplicated as a
new local sign API.
-/

namespace Formalization.Books.Dga.Unit02

/-! The precise content of this section is supplied by the imported Mathlib
interfaces described above. -/

end Formalization.Books.Dga.Unit02
