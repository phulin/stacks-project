import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.PNat.Notation
import Mathlib.Data.Real.Basic

/-!
# Conventions, §5: Notation

The source's notation is already provided by Mathlib's canonical number
types.  Its natural integers start at `1`, so the corresponding Lean type is
`ℕ+` (`PNat`), the subtype of positive natural numbers, rather than `ℕ`,
which includes `0`.  The integers are the canonical type `ℤ`.

The number systems called fields in the source are Mathlib's canonical types
`ℚ`, `ℝ`, and `ℂ`.  The focused imports above provide their existing `Field`
instances (and the standard coercions and operations), so no parallel
chapter-specific aliases or field structures are introduced.

Thus the five source conventions are represented directly by the established
declarations:

* positive natural integers: `ℕ+`;
* integers: `ℤ`;
* rational numbers: `ℚ`;
* real numbers: `ℝ`;
* complex numbers: `ℂ`.

There are no additional definitions, identities, diagrams, examples,
hypotheses, exact sequences, or warnings in this source section.
-/
