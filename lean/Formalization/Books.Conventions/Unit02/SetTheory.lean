import Mathlib.SetTheory.ZFC.Basic

/-!
# Conventions, §2: Set theory

This section records the ambient foundation used by the book.  Mathlib's
`ZFSet` is its canonical model of Zermelo--Fraenkel set theory with choice,
so importing `Mathlib.SetTheory.ZFC.Basic` makes that established API
available without introducing a parallel set-theoretic foundation here.

The remaining source text records conventions about universe management and
the care taken with set-theoretic details.  They do not define a mathematical
object or assert a standalone proposition; this file therefore adds no
redundant declaration for them.  The chapter introduces no explicit universe
declarations, and Lean's elaborator checks the resulting declarations for
well-formedness.
-/
