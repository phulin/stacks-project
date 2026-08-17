import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Set Theory, Chapter 12: Abelian categories and injectives

The source section contains one lemma.  Mathlib's `LargeCategory` universe
convention is the Lean representation of the source's big category, and
`ObjectProperty.FullSubcategory` is the canonical full-subcategory
construction.  The five numbered conclusions are packaged together so that
the resulting subcategory can be used with Mathlib's category-theoretic APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Formalization.Books.Sets.Unit12

/--
The data supplied by the conclusion of the chapter's abelian-injectives
lemma.

The ambient category has objects in `Type (u + 1)` and morphisms in `Type u`,
which is Mathlib's universe-polymorphic representation of a big category.
The object property is small in `Type u`, so its full subcategory has a set of
objects in the source's sense.  Exactness of the inclusion is expressed by
the canonical finite-limit and finite-colimit preservation predicates.
-/
structure AbelianInjectiveSubcategory
    (A : Type (u + 1)) [LargeCategory A] [Abelian A]
    (S : Type u) (A₀ : S → A) where
  /-- The objects selected for the full subcategory. -/
  property : ObjectProperty A
  /-- The selected full subcategory is abelian. -/
  abelian : Abelian property.FullSubcategory
  /-- The inclusion of the selected full subcategory is exact. -/
  exact_inclusion :
    PreservesFiniteLimits property.ι ∧ PreservesFiniteColimits property.ι
  /-- The selected objects form a set at the ambient small universe. -/
  small : ObjectProperty.Small.{u} property
  /-- Every prescribed object belongs to the selected subcategory. -/
  contains : ∀ s : S, property (A₀ s)
  /-- The selected full subcategory has enough injectives. -/
  enough_injectives : EnoughInjectives property.FullSubcategory
  /-- Injectivity agrees with injectivity in the ambient category. -/
  injective_iff :
    ∀ X : property.FullSubcategory,
      Injective X ↔ Injective (property.ι.obj X)

/-!
The source's `\{A_s\}_{s \in S}` is represented by an explicit index type
and family.  The theorem is a statement interface; its construction is
deferred to the proof stage.
-/
theorem exists_abelian_injective_subcategory
    {A : Type (u + 1)} [LargeCategory A] [Abelian A]
    [EnoughInjectives A] (S : Type u) (A₀ : S → A) :
    Nonempty (AbelianInjectiveSubcategory A S A₀) := by
  sorry

end Formalization.Books.Sets.Unit12
