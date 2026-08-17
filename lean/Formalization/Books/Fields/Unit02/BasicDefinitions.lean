import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Fields, Chapter 2: Basic definitions

The source defines fields, subfields, and domains.  Mathlib already provides
the corresponding canonical interfaces: `[Field K]`, `Subfield K`, and
`[CommRing R] [IsDomain R]`.  The source's notation `K^*` is represented by
Mathlib's canonical non-zero-divisor submonoid `K⁰`; in a field its underlying
set is exactly `K \ {0}`.
-/

namespace Formalization.Books.Fields.Unit02

universe u

/-!
The field and subfield definitions are used directly from Mathlib.  A
`Field K` is a nontrivial commutative ring with inverses for nonzero elements,
and `Subfield K` is the bundled subfield of a division ring.  Likewise, the
source's domain/integral-domain definition is the established Mathlib
combination `[CommRing R] [IsDomain R]`; no parallel predicates are needed.
-/

open scoped nonZeroDivisors

/-!
The source writes `K^*` for the nonzero elements of a field.  Mathlib's
`K⁰` is the canonical reusable interface for this set, and the following
identity records the source's set-theoretic description.
-/
theorem nonzeroElements_eq_compl_singleton (K : Type u) [Field K] :
    (K⁰ : Set K) = Set.univ \ ({0} : Set K) := by
  ext x
  simp

end Formalization.Books.Fields.Unit02
