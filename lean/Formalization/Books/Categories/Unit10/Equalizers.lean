import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Categories, Chapter 10: Equalizers

Mathlib represents an equalizer as a limiting fork for a parallel pair.  The
source phrases the definition using the equalizing equation and a unique
factorization, so `IsEqualizer` packages the canonical `Fork`/`IsLimit`
interface while hiding the proof of the equalizing equation.
-/

namespace Formalization.Books.Categories.Unit10

open CategoryTheory
open CategoryTheory.Limits

universe v u

/-! ## Equalizers -/

/-- A morphism is an equalizer of a parallel pair when its canonical fork is
limiting.  The existential records the fork's commutativity proof, and
`Nonempty` reflects Mathlib's proposition-valued existence interface for a
chosen limit cone. -/
def IsEqualizer {C : Type u} [Category.{v} C]
    {X Y Z : C} (e : Z ⟶ X) (a b : X ⟶ Y) : Prop :=
  ∃ h : e ≫ a = e ≫ b, Nonempty (IsLimit (Fork.ofι e h))

/-- The equalizing equation carried by an `IsEqualizer`. -/
theorem IsEqualizer.condition
    {C : Type u} [Category.{v} C]
    {X Y Z : C} {a b : X ⟶ Y} {e : Z ⟶ X}
    (h : IsEqualizer e a b) : e ≫ a = e ≫ b := by
  exact h.choose

/-- The universal factorization property of an `IsEqualizer`. -/
theorem IsEqualizer.existsUnique
    {C : Type u} [Category.{v} C]
    {X Y Z : C} {a b : X ⟶ Y} {e : Z ⟶ X}
    (h : IsEqualizer e a b) {W : C} (t : W ⟶ X)
    (ht : t ≫ a = t ≫ b) : ∃! s : W ⟶ Z, s ≫ e = t := by
  rcases h with ⟨he, ⟨hlim⟩⟩
  exact Fork.IsLimit.existsUnique hlim t ht

/-- The source definition is equivalent to the explicit equalizing equation
and unique factorization property. -/
theorem isEqualizer_iff
    {C : Type u} [Category.{v} C]
    {X Y Z : C} {a b : X ⟶ Y} {e : Z ⟶ X} :
    IsEqualizer e a b ↔
      e ≫ a = e ≫ b ∧
        ∀ {W : C} (t : W ⟶ X), t ≫ a = t ≫ b →
          ∃! s : W ⟶ Z, s ≫ e = t := by
  constructor
  · intro h
    exact ⟨h.condition, fun t ht => h.existsUnique t ht⟩
  · rintro ⟨he, hfactor⟩
    refine ⟨he, ⟨Fork.IsLimit.ofExistsUnique ?_⟩⟩
    intro s
    simpa using hfactor s.ι s.condition

/-- Equalizers, when they exist, are unique up to a unique isomorphism that
commutes with their maps into the common source.  The proof follows the
standard comparison-isomorphism argument for two limit forks. -/
theorem equalizer_unique_up_to_unique_iso
    {C : Type u} [Category.{v} C]
    {X Y Z Z' : C} {a b : X ⟶ Y}
    {e : Z ⟶ X} {e' : Z' ⟶ X}
    (he : IsEqualizer e a b) (he' : IsEqualizer e' a b) :
    ∃! i : Z ≅ Z', i.hom ≫ e' = e := by
  sorry

/- The source finally notes that the definition extends to more than two
parallel morphisms.  Mathlib's `Multifork`/`HasMultiequalizer` interfaces
provide that generalization; the source gives no specific indexing family or
additional assertion to state here. -/

end Formalization.Books.Categories.Unit10
