import Mathlib.SetTheory.ZFC.Class

/-!
# Set Theory, Chapter 3: Classes

The source introduces a class by fixing the parameters in a formula
`φ(x, p₁, ..., pₙ)` and collecting the `x` satisfying it.  Mathlib's
`Class` is exactly the corresponding predicate on `ZFSet`: after the
parameters are fixed, the predicate itself has type `Class`, so no parallel
formula wrapper is needed here.  Mathlib also supplies the coercion from a
`ZFSet` to the class of its elements and the universal class `Class.univ`.

The examples involving all modules over a ring, all schemes, and all rings
refer to the corresponding set-theoretic encodings of those structures.  The
source does not specify such encodings, so these examples are represented by
the general `Class` interface rather than by invented set-coded structures.
Likewise, the phrase “big category” records that the object collection is a
proper class; it does not introduce a separate category construction in this
section.
-/

universe u

namespace Class

/-! ### Proper classes -/

/-! A class is proper when it is not represented by a `ZFSet`. -/
def IsProper (C : Class.{u}) : Prop :=
  C ∉ Class.univ

theorem isProper_iff_not_coe (C : Class.{u}) :
    IsProper C ↔ ∀ s : ZFSet.{u}, (s : Class.{u}) ≠ C := by
  constructor
  · intro h s hs
    exact h (Class.mem_univ.2 ⟨s, hs⟩)
  · intro h hs
    obtain ⟨s, hs⟩ := Class.mem_univ.1 hs
    exact h s hs

end Class
