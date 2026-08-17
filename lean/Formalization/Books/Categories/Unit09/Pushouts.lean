import Formalization.Books.Categories.Unit06.FibreProducts

/-!
# Categories, Chapter 9: Pushouts

Mathlib's `CategoryTheory.IsPushout` is the canonical interface for the
source's pushout definition.  Its commutativity field and colimit universal
property give the square and the unique induced morphism, while `HasPushout`
and `pushout` provide existence and a chosen pushout when one is available.
The source's cocartesian terminology is recorded below as an abbreviation;
the opposite-category description reuses the fibre-product interface from
the preceding chapter.
-/

namespace Formalization.Books.Categories.Unit09

open CategoryTheory
open CategoryTheory.Limits

universe v u

/-! ## Pushouts -/

/- The source's factorization property, written with the two named pushout
   legs instead of Mathlib's general colimit cocone interface. -/
theorem pushout_universal_property
    {C : Type u} [Category.{v} C]
    {Y X Z P : C} {f : Y ⟶ X} {g : Y ⟶ Z}
    {p : X ⟶ P} {q : Z ⟶ P}
    (h : IsPushout f g p q) {W : C}
    (α : X ⟶ W) (β : Z ⟶ W) (hαβ : f ≫ α = g ≫ β) :
    ∃! γ : P ⟶ W, p ≫ γ = α ∧ q ≫ γ = β := by
  refine ⟨h.desc α β hαβ, ?_, ?_⟩
  · exact ⟨h.inl_desc α β hαβ, h.inr_desc α β hαβ⟩
  · intro γ hγ
    apply h.hom_ext
    · exact hγ.1.trans (h.inl_desc α β hαβ).symm
    · exact hγ.2.trans (h.inr_desc α β hαβ).symm

/- The source's uniqueness assertion is the standard uniqueness of a
colimit cocone, expressed with the two pushout legs fixed. -/
theorem pushout_unique_up_to_unique_iso
    {C : Type u} [Category.{v} C]
    {Y X Z P P' : C} {f : Y ⟶ X} {g : Y ⟶ Z}
    {p : X ⟶ P} {q : Z ⟶ P} {p' : X ⟶ P'} {q' : Z ⟶ P'}
    (h : IsPushout f g p q) (h' : IsPushout f g p' q') :
    ∃! e : P ≅ P', p ≫ e.hom = p' ∧ q ≫ e.hom = q' := by
  refine ⟨h.isoIsPushout _ _ h', ?_, ?_⟩
  · exact ⟨h.inl_isoIsPushout_hom _ _ h', h.inr_isoIsPushout_hom _ _ h'⟩
  · intro e he
    apply Iso.ext
    apply h.hom_ext
    · exact he.1.trans (h.inl_isoIsPushout_hom _ _ h').symm
    · exact he.2.trans (h.inr_isoIsPushout_hom _ _ h').symm

/- The source also points out that a pushout is a fibre product after passing
to the opposite category.  This is Mathlib's `IsPushout.op`/`unop` API,
written with the source-facing `IsFibreProduct` abbreviation. -/
theorem pushout_iff_fibre_product_op
    {C : Type u} [Category.{v} C]
    {Y X Z P : C} {f : Y ⟶ X} {g : Y ⟶ Z}
    {p : X ⟶ P} {q : Z ⟶ P} :
    IsPushout f g p q ↔
      Formalization.Books.Categories.Unit06.IsFibreProduct q.op p.op g.op f.op := by
  constructor
  · intro h
    exact h.op
  · intro h
    exact h.unop

/- A cocartesian square is exactly a pushout square.  The canonical
`IsPushout` structure already includes both the commutativity condition and
the universal property, so no parallel square structure is needed. -/
abbrev IsCocartesianSquare {C : Type u} [Category.{v} C]
    {Y X Z W : C} (f : Y ⟶ X) (g : Y ⟶ Z)
    (p : X ⟶ W) (q : Z ⟶ W) : Prop :=
  IsPushout f g p q

end Formalization.Books.Categories.Unit09
