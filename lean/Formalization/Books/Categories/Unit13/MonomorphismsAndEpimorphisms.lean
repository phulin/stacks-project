import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Types.Basic

/-!
# Categories, Chapter 13: Monomorphisms and Epimorphisms

Mathlib's `CategoryTheory.Mono` and `CategoryTheory.Epi` are the canonical
interfaces for the two source definitions.  Their cancellation fields give
the source-facing formulations below.  In `Type u`, Mathlib identifies
monomorphisms with injective functions and epimorphisms with surjective
functions.

The source's fibre product and pushout characterizations are represented by
the canonical identity pullback square and identity pushout cocone.  This is
the precise categorical meaning of the displayed diagrams and does not
require separately choosing pullbacks or pushouts.
-/

namespace Formalization.Books.Categories.Unit13

open CategoryTheory
open CategoryTheory.Limits

universe v u

/-! ## Monomorphisms and epimorphisms -/

/- The source definitions are exactly the fields of Mathlib's `Mono` and
   `Epi` classes; these theorems expose their quantifier forms without
   introducing duplicate predicates. -/

theorem monomorphism_iff_right_cancellation
    {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔
      ∀ (W : C) (a b : W ⟶ X), a ≫ f = b ≫ f → a = b := by
  constructor
  · intro hf W a b h
    exact hf.right_cancellation a b h
  · intro h
    exact ⟨fun {W} a b hab => h W a b hab⟩

theorem epimorphism_iff_left_cancellation
    {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔
      ∀ (W : C) (a b : Y ⟶ W), f ≫ a = f ≫ b → a = b := by
  constructor
  · intro hf W a b h
    exact hf.left_cancellation a b h
  · intro h
    exact ⟨fun {W} a b hab => h W a b hab⟩

/-! ## The category of sets -/

/- `Type u` is the universe-indexed Lean category used for the source's
   category of sets. -/

theorem type_monomorphism_iff_injective {X Y : Type u} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f :=
  CategoryTheory.mono_iff_injective f

theorem type_epimorphism_iff_surjective {X Y : Type u} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f :=
  CategoryTheory.epi_iff_surjective f

/-! ## Fibre products and pushouts -/

/- The diagonal square has both top and left maps equal to `𝟙 X`; its
   pullback property is the source's assertion that `X` is `X ×_Y X`. -/

theorem monomorphism_iff_diagonal_is_pullback
    {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f :=
  CategoryTheory.mono_iff_isPullback f

/- The dual identity cocone has both pushout legs equal to `𝟙 Y`; its
   pushout property is the source's assertion that `Y` is `Y ⨿_X Y`. -/

theorem epimorphism_iff_codiagonal_is_pushout
    {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y) :=
  CategoryTheory.epi_iff_isPushout f

end Formalization.Books.Categories.Unit13
