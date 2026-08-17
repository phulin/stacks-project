import Mathlib.CategoryTheory.Category.Basic

/-!
# Conventions, §3: Categories

The source's category convention is already the Mathlib typeclass
`CategoryTheory.Category`: its object type is a Lean type, and the hom type
for every pair of objects is another Lean type equipped with identity and
composition operations satisfying the category laws.  Consequently this
section uses that canonical declaration directly rather than introducing a
parallel category structure.

The source calls this a small category and also permits a restricted list of
big categories.  Mathlib records the corresponding universe conventions in
`CategoryTheory.SmallCategory` and `CategoryTheory.LargeCategory`.  A Lean
universe is not a proper class, so the latter is the universe-polymorphic
representation of the book's big-category convention; the book's external
list of permitted examples remains a scope convention, not a new category
construction or proposition to declare here.
-/
