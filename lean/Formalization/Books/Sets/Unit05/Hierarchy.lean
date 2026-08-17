import Formalization.Books.Sets.Unit04
import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# Set Theory, Chapter 5: The hierarchy of sets

Mathlib's `ZFSet.vonNeumann` is the canonical cumulative hierarchy used by
this section.  Its defining recursion and the source's displayed clauses are
already exposed by `ZFSet.vonNeumann_zero`, `ZFSet.vonNeumann_add_one`, and
`ZFSet.vonNeumann_of_isSuccPrelimit`; the latter gives the limit clause for
the standard `IsSuccPrelimit` formulation (and hence for `IsSuccLimit`).
The transitivity and regularity assertions are respectively
`ZFSet.isTransitive_vonNeumann` and `ZFSet.exists_mem_vonNeumann`.

The source's rank is Mathlib's `ZFSet.rank`: `ZFSet.mem_vonNeumann` and the
theorem below record its characterization as the least level whose successor
contains the set.  The source's phrase “suitably large” is intentionally left
as contextual; the formal predicate records the precise part of the
definition, namely being a level of the hierarchy.

The remark relating hierarchy coverage to the axiom of foundation is
metatheoretic.  Mathlib's `ZFSet` is already a model with foundation, so the
usable object-level interfaces here are the coverage theorem and the existing
`ZFSet.regularity` theorem rather than a parallel axiom wrapper.
-/

universe u

namespace Formalization.Books.Sets.Unit05

/-! ### Partial universes -/

/-- A partial universe is a level of the von Neumann hierarchy. -/
def IsPartialUniverse (U : ZFSet.{u}) : Prop :=
  ∃ α : Ordinal.{u}, U = ZFSet.vonNeumann α

/-! ### Rank -/

/-- `ZFSet.rank S` is the least ordinal whose successor level contains `S`. -/
theorem rank_isLeast_vonNeumann (S : ZFSet.{u}) :
    IsLeast {α : Ordinal.{u} | S ∈ ZFSet.vonNeumann (α + 1)} (ZFSet.rank S) := by
  sorry

end Formalization.Books.Sets.Unit05
