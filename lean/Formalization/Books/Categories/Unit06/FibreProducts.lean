import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Categories, Chapter 6: Fibre products

Mathlib calls a fibre product a pullback.  The source definition, its
commutativity condition, and its universal property are therefore represented
by `CategoryTheory.IsPullback`; this file does not introduce a second cone
structure.  Likewise, `HasPullbacks` is the canonical assertion that a
category has all fibre products.
-/

namespace Formalization.Books.Categories.Unit06

open CategoryTheory
open CategoryTheory.Limits

universe v u

/-! ## Fibre products and cartesian squares -/

/-
`IsPullback p q f g` is exactly the source's data of a fibre product of
`f : X ⟶ Y` and `g : Z ⟶ Y`: its `CommSq` field is the displayed commuting
square, while `IsPullback.lift`, `lift_fst`, `lift_snd`, and `hom_ext` give the
existence, projection equations, and uniqueness in the universal property.
The source's fibre-product, Cartesian-square, and “has fibre products”
definitions therefore use Mathlib's canonical `IsPullback` and `HasPullbacks`
interfaces directly.
-/

/-! ## Uniqueness -/

/-- Two fibre products of the same pair are uniquely isomorphic compatibly
with both projections.  This is Mathlib's cone-point uniqueness theorem for
pullback limits, written in the language of the source. -/
theorem fibre_product_unique_up_to_unique_iso
    {C : Type u} [Category.{v} C]
    {X Y Z P P' : C} {f : X ⟶ Y} {g : Z ⟶ Y}
    {p : P ⟶ X} {q : P ⟶ Z} {p' : P' ⟶ X} {q' : P' ⟶ Z}
    (h : IsPullback p q f g) (h' : IsPullback p' q' f g) :
    ∃! e : P ≅ P', e.hom ≫ p' = p ∧ e.hom ≫ q' = q := by
  refine ⟨h.isoIsPullback _ _ h', ?_, ?_⟩
  · exact ⟨h.isoIsPullback_hom_fst _ _ h', h.isoIsPullback_hom_snd _ _ h'⟩
  · intro e he
    apply Iso.ext
    apply h'.hom_ext
    · exact he.1.trans (h.isoIsPullback_hom_fst _ _ h').symm
    · exact he.2.trans (h.isoIsPullback_hom_snd _ _ h').symm

/-!
The source's Yoneda explanation of this uniqueness is already packaged by
the stronger pullback-limit API: `h.isLimit` identifies the square as a limit
cone, and `fibre_product_unique_up_to_unique_iso` is the corresponding
projection-preserving unique isomorphism.  No separate presheaf definition is
needed.
-/

/-! ## Representable morphisms -/

/-- A representable morphism has a pullback with every morphism into its
codomain, in the orientation used by `pullback f g`. -/
theorem has_pullback_of_representable
    {C : Type u} [Category.{v} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : HasPullbacksAlong f) :
    HasPullback f g := by
  exact @hasPullback_symmetry_of_hasPullbacksAlong C _ Y X Z f hf g

/-! ## Stability of representability -/

/-- The composite of representable morphisms is representable.

The source proof constructs the pullback of a morphism into the final target
by pasting the pullback along `g` with the pullback along `f`; Mathlib's
`IsPullback.paste_horiz` and the pullback universal-property API provide the
corresponding route. -/
theorem representable_comp
    {C : Type u} [Category.{v} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasPullbacksAlong f) (hg : HasPullbacksAlong g) :
    HasPullbacksAlong (f ≫ g) := by
  sorry

/-- Base change preserves representability.  The statement is phrased for an
arbitrary chosen pullback square, so it does not identify isomorphic choices
of the fibre-product object by definitional equality. -/
theorem representable_base_change
    {C : Type u} [Category.{v} C]
    {X Y Y' P : C} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasPullbacksAlong f)
    {p : P ⟶ X} {q : P ⟶ Y'}
    (h : IsPullback p q f g) :
    HasPullbacksAlong q := by
  sorry

/-- In particular, a representable morphism admits a representable base
change for every morphism into its codomain. -/
theorem exists_representable_base_change
    {C : Type u} [Category.{v} C]
    {X Y Y' : C} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasPullbacksAlong f) :
    ∃ (P : C) (p : P ⟶ X) (q : P ⟶ Y'),
      IsPullback p q f g ∧ HasPullbacksAlong q := by
  let hfg : HasPullback f g := has_pullback_of_representable f g hf
  let h : IsPullback
      (@pullback.fst C _ X Y' Y f g hfg)
      (@pullback.snd C _ X Y' Y f g hfg) f g :=
    @IsPullback.of_hasPullback C _ X Y' Y f g hfg
  exact ⟨@pullback C _ X Y' Y f g hfg,
    @pullback.fst C _ X Y' Y f g hfg,
    @pullback.snd C _ X Y' Y f g hfg, h,
    representable_base_change f g hf h⟩

end Formalization.Books.Categories.Unit06
