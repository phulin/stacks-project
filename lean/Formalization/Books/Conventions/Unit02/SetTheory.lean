import Mathlib.SetTheory.ZFC.Basic

/-!
# Conventions, §2: Set theory

This section records the ambient foundation used by the book.  Mathlib's
`ZFSet` is a model of Zermelo--Fraenkel set theory with choice, so importing
`Mathlib.SetTheory.ZFC.Basic` makes the established set-theoretic API
available without introducing a parallel foundation here.  The imported
module's model is built using Lean's existing classical choice principle.

The remaining source text records conventions about universe management and
the care taken with set-theoretic details.  They do not define a mathematical
object or assert a standalone proposition; this file therefore adds no
redundant declaration for them.  In particular, the book's convention of not
using universes is an expository convention, not a claim that Lean's internal
universe parameters can be eliminated.  Lean's elaborator checks the
well-formedness of the declarations that use the imported API.
-/
