import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Categories, Chapter 12: Initial and final objects

Mathlib's `CategoryTheory.Limits.IsInitial` and `IsTerminal` are the canonical
universal-property interfaces for the two definitions in the source.  The
source's phrase “exactly one morphism” is recorded below using `Unique`, while
the category-of-sets examples use Mathlib's universe-indexed category
`Type u`.

The source says that the empty set is “the only” initial object and that
singletons are final objects.  In `Type u`, the principled categorical
formulation of the first assertion is that every initial type is isomorphic to
`PEmpty`; the second is characterized by `Unique X`, so it deliberately does
not select a single terminal representative.
-/

namespace Formalization.Books.Categories.Unit12

open CategoryTheory
open CategoryTheory.Limits

universe v u

/-! ## Initial and final objects -/

/- The two source definitions are exactly the canonical `IsInitial` and
   `IsTerminal` structures.  These interfaces expose the unique morphisms as
   `IsInitial.to` and `IsTerminal.from`; the following propositions spell out
   the source's “exactly one” wording without introducing parallel predicates. -/

theorem initial_object_iff_unique_homs {C : Type u} [Category.{v} C] (X : C) :
    Nonempty (IsInitial X) ↔
      ∀ Y : C, Nonempty (Unique (X ⟶ Y)) := by
  constructor
  · rintro ⟨h⟩ Y
    exact ⟨⟨⟨h.to Y⟩, fun f => h.hom_ext f (h.to Y)⟩⟩
  · intro h
    classical
    exact ⟨@IsInitial.ofUnique C _ X (fun Y => Classical.choice (h Y))⟩

theorem final_object_iff_unique_homs {C : Type u} [Category.{v} C] (X : C) :
    Nonempty (IsTerminal X) ↔
      ∀ Y : C, Nonempty (Unique (Y ⟶ X)) := by
  constructor
  · rintro ⟨h⟩ Y
    exact ⟨⟨⟨h.from Y⟩, fun f => h.hom_ext f (h.from Y)⟩⟩
  · intro h
    classical
    exact ⟨@IsTerminal.ofUnique C _ X (fun Y => Classical.choice (h Y))⟩

/-! ## The category of sets -/

/- `Type u` is Mathlib's category of universe-`u` types, used here for the
   source's category of sets. -/

/- The empty type is an initial object of `Type u`. -/
noncomputable def empty_set_is_initial :
    IsInitial (PEmpty : Type u) :=
  Types.isInitialPEmpty

/- An object of `Type u` is initial exactly when it is empty. -/
theorem initial_set_iff_empty (X : Type u) :
    Nonempty (IsInitial X) ↔ IsEmpty X :=
  Types.initial_iff_empty X

/- Every initial type is uniquely isomorphic to the empty type. -/
noncomputable def initial_set_isomorphic_to_empty {X : Type u} (hX : IsInitial X) :
    X ≅ (PEmpty : Type u) :=
  hX.uniqueUpToIso empty_set_is_initial

/- A type is final exactly when it has one element. -/
noncomputable def final_set_iff_unique (X : Type u) :
    IsTerminal X ≃ Unique X :=
  Types.isTerminalEquivUnique X

/- Every singleton type is a final object of `Type u`. -/
noncomputable def singleton_set_is_final (X : Type u) [Unique X] :
    IsTerminal X :=
  (final_set_iff_unique X).symm inferInstance

end Formalization.Books.Categories.Unit12
