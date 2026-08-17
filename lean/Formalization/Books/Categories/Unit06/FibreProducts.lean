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

/- A fibre product square is exactly Mathlib's `IsPullback` predicate.  The
   argument order follows the source diagram: `p` and `q` are the maps from the
   fibre-product object, followed by the two maps to the common base. -/
abbrev IsFibreProduct {C : Type u} [Category.{v} C]
    {P X Z Y : C} (p : P ⟶ X) (q : P ⟶ Z)
    (f : X ⟶ Y) (g : Z ⟶ Y) : Prop :=
  IsPullback p q f g

/- A cartesian square is the same pullback predicate, with the square's four
   maps made explicit. -/
abbrev IsCartesianSquare {C : Type u} [Category.{v} C]
    {W X Z Y : C} (p : W ⟶ X) (q : W ⟶ Z)
    (f : X ⟶ Y) (g : Z ⟶ Y) : Prop :=
  IsPullback p q f g

/- A category has fibre products exactly when it has all limits of the
   walking-cospan shape. -/
abbrev HasFibreProducts (C : Type u) [Category.{v} C] : Prop :=
  HasPullbacks C

theorem has_fibre_products_iff
    {C : Type u} [Category.{v} C] :
    HasFibreProducts C ↔
      ∀ {X Z Y : C} (f : X ⟶ Y) (g : Z ⟶ Y),
        Nonempty (LimitCone (cospan f g)) := by
  constructor
  · intro h X Z Y f g
    let _ : HasFibreProducts C := h
    exact (inferInstance : HasPullback f g).exists_limit
  · intro h
    let _ : ∀ {X Z Y : C} (f : X ⟶ Y) (g : Z ⟶ Y),
        HasLimit (cospan f g) := by
      intro X Z Y f g
      exact ⟨h f g⟩
    exact hasPullbacks_of_hasLimit_cospan C

/- The source's universal property is Mathlib's pullback lift API, written
   with the source-facing name and Lean's composition convention. -/
theorem fibre_product_universal_property
    {C : Type u} [Category.{v} C]
    {P X Z Y : C} {p : P ⟶ X} {q : P ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsFibreProduct p q f g) {W : C}
    (α : W ⟶ X) (β : W ⟶ Z) (hαβ : α ≫ f = β ≫ g) :
    ∃! γ : W ⟶ P, γ ≫ p = α ∧ γ ≫ q = β := by
  refine ⟨h.lift α β hαβ, ?_, ?_⟩
  · exact ⟨h.lift_fst α β hαβ, h.lift_snd α β hαβ⟩
  · intro γ hγ
    apply h.hom_ext
    · exact hγ.1.trans (h.lift_fst α β hαβ).symm
    · exact hγ.2.trans (h.lift_snd α β hαβ).symm

/- The hom-set bijection induced by the universal property identifies the
   represented fibre-product functor with the set-theoretic pullback of the
   two hom-set maps.  The subtype is the explicit pullback of those maps. -/
noncomputable def fibreProductHomEquiv
    {C : Type u} [Category.{v} C]
    {P X Z Y : C} {p : P ⟶ X} {q : P ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsFibreProduct p q f g) (W : C) :
    (W ⟶ P) ≃
      {a : (W ⟶ X) × (W ⟶ Z) // a.1 ≫ f = a.2 ≫ g} where
  toFun γ :=
    ⟨(γ ≫ p, γ ≫ q), by
      simpa [Category.assoc] using congrArg (fun k => γ ≫ k) h.w⟩
  invFun a := h.lift a.1.1 a.1.2 a.2
  left_inv γ := by
    apply h.hom_ext
    · exact h.lift_fst _ _ _
    · exact h.lift_snd _ _ _
  right_inv a := by
    apply Subtype.ext
    change
      (h.lift a.1.1 a.1.2 a.2 ≫ p,
        h.lift a.1.1 a.1.2 a.2 ≫ q) = a.1
    exact Prod.ext (h.lift_fst _ _ _) (h.lift_snd _ _ _)

theorem fibreProductHomEquiv_natural
    {C : Type u} [Category.{v} C]
    {P X Z Y : C} {p : P ⟶ X} {q : P ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsFibreProduct p q f g) {V W : C} (r : V ⟶ W) (γ : W ⟶ P) :
    (fibreProductHomEquiv h V (r ≫ γ)).1 =
      (r ≫ (fibreProductHomEquiv h W γ).1.1,
        r ≫ (fibreProductHomEquiv h W γ).1.2) := by
  simp [fibreProductHomEquiv, Category.assoc]

/-! ## Uniqueness -/

/-- Two fibre products of the same pair are uniquely isomorphic compatibly
with both projections.  This is Mathlib's cone-point uniqueness theorem for
pullback limits, written in the language of the source. -/
theorem fibre_product_unique_up_to_unique_iso
    {C : Type u} [Category.{v} C]
    {X Y Z P P' : C} {f : X ⟶ Y} {g : Z ⟶ Y}
    {p : P ⟶ X} {q : P ⟶ Z} {p' : P' ⟶ X} {q' : P' ⟶ Z}
    (h : IsFibreProduct p q f g) (h' : IsFibreProduct p' q' f g) :
    ∃! e : P ≅ P', e.hom ≫ p' = p ∧ e.hom ≫ q' = q := by
  refine ⟨h.isoIsPullback _ _ h', ?_, ?_⟩
  · exact ⟨h.isoIsPullback_hom_fst _ _ h', h.isoIsPullback_hom_snd _ _ h'⟩
  · intro e he
    apply Iso.ext
    apply h'.hom_ext
    · exact he.1.trans (h.isoIsPullback_hom_fst _ _ h').symm
    · exact he.2.trans (h.isoIsPullback_hom_snd _ _ h').symm

/-!
The source's Yoneda explanation is expressed by `fibreProductHomEquiv` and its
naturality theorem: these are the pointwise natural equivalences between the
represented fibre-product functor and the pullback of the two representables.
The limit API then gives the compatible unique isomorphism above, so no second
cone structure is needed.
-/

/-! ## Representable morphisms -/

/- A morphism is representable exactly when pullbacks along it exist for all
   maps into its codomain.  This is Mathlib's `HasPullbacksAlong` predicate. -/
abbrev IsRepresentable {C : Type u} [Category.{v} C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  HasPullbacksAlong f

/-- A representable morphism has a pullback with every morphism into its
codomain, in the orientation used by `pullback f g`. -/
theorem has_pullback_of_representable
    {C : Type u} [Category.{v} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsRepresentable f) :
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
    (hf : IsRepresentable f) (hg : IsRepresentable g) :
    IsRepresentable (f ≫ g) := by
  sorry

/-- Base change preserves representability.  The statement is phrased for an
arbitrary chosen pullback square, so it does not identify isomorphic choices
of the fibre-product object by definitional equality. -/
theorem representable_base_change
    {C : Type u} [Category.{v} C]
    {X Y Y' P : C} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsRepresentable f)
    {p : P ⟶ X} {q : P ⟶ Y'}
    (h : IsFibreProduct p q f g) :
    IsRepresentable q := by
  sorry

/-- In particular, a representable morphism admits a representable base
change for every morphism into its codomain. -/
theorem exists_representable_base_change
    {C : Type u} [Category.{v} C]
    {X Y Y' : C} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsRepresentable f) :
    ∃ (P : C) (p : P ⟶ X) (q : P ⟶ Y'),
      IsFibreProduct p q f g ∧ IsRepresentable q := by
  let hfg : HasPullback f g := has_pullback_of_representable f g hf
  let h : IsFibreProduct
      (@pullback.fst C _ X Y' Y f g hfg)
      (@pullback.snd C _ X Y' Y f g hfg) f g :=
    @IsPullback.of_hasPullback C _ X Y' Y f g hfg
  exact ⟨@pullback C _ X Y' Y f g hfg,
    @pullback.fst C _ X Y' Y f g hfg,
    @pullback.snd C _ X Y' Y f g hfg, h,
    representable_base_change f g hf h⟩

end Formalization.Books.Categories.Unit06
