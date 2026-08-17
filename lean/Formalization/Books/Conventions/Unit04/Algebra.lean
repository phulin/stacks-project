import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Module.Defs

/-!
# Conventions, §4: Algebra

The source uses “ring” for a commutative ring with a multiplicative identity.
This is exactly Mathlib's `CommRing` typeclass; in particular, it does not
silently add a `Nontrivial` hypothesis, so the zero ring is included.

The corresponding category of rings is Mathlib's bundled category
`CommRingCat`.  Its canonical declarations
`CommRingCat.zIsInitial` and `CommRingCat.punitIsTerminal` state that
`CommRingCat.of ℤ` is initial and `CommRingCat.of PUnit` is the strict
terminal object, respectively.  The one-element type `PUnit` carries the
canonical `CommRing` instance, so it is the book's zero ring `{0}`.

The parenthetical uniqueness assertion for the zero ring is already covered
by Mathlib's `subsingleton_iff_zero_eq_one` and `uniqueOfZeroEqOne`: a
commutative ring with `1 = 0` has exactly one element.  Thus no parallel
zero-ring definition or chapter-specific uniqueness theorem is needed.

Finally, Mathlib's `Module R M` is the unitary module convention used by the
source.  Its inherited `MulAction` structure includes the axiom and theorem
`one_smul`, so scalar multiplication by `1` is the identity.
-/
