import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Categories, Chapter 5: Coproducts of pairs

The source's coproduct is Mathlib's colimit cocone on the walking-pair
diagram.  `CoproductOfPair` packages that canonical cocone together with its
universal property; `HasCoproductsOfPairs` is the source-facing name for
Mathlib's `HasBinaryCoproducts` class.
-/

namespace Formalization.Books.Categories.Unit05

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Coproducts of pairs -/

/- A `ColimitCocone (pair X Y)` is exactly an object with two inclusions and
   the colimit universal property.  We retain Mathlib's fields
   `c.cocone.pt`, `BinaryCofan.inl c.cocone`, `BinaryCofan.inr c.cocone`, and
   `c.isColimit` rather than
   introducing a parallel structure. -/
abbrev CoproductOfPair (X Y : C) := ColimitCocone (pair X Y)

/- The source's factorization property, written with the two named
   inclusions instead of the general cocone indexing type. -/
theorem coproduct_universal_property (X Y : C) (c : CoproductOfPair X Y)
    (W : C) (α : X ⟶ W) (β : Y ⟶ W) :
    ∃! γ : c.cocone.pt ⟶ W,
      BinaryCofan.inl c.cocone ≫ γ = α ∧ BinaryCofan.inr c.cocone ≫ γ = β := by
  refine ⟨BinaryCofan.IsColimit.desc c.isColimit α β, ?_, ?_⟩
  · exact ⟨BinaryCofan.IsColimit.inl_desc c.isColimit α β,
      BinaryCofan.IsColimit.inr_desc c.isColimit α β⟩
  · intro γ hγ
    apply BinaryCofan.IsColimit.hom_ext c.isColimit
    · rw [hγ.1, BinaryCofan.IsColimit.inl_desc]
    · rw [hγ.2, BinaryCofan.IsColimit.inr_desc]

/- This is the hom-set product in the source's displayed formula. -/
def coproductHomEquiv (c : CoproductOfPair X Y) (W : C) :
    (c.cocone.pt ⟶ W) ≃ (X ⟶ W) × (Y ⟶ W) where
  toFun γ := (BinaryCofan.inl c.cocone ≫ γ, BinaryCofan.inr c.cocone ≫ γ)
  invFun p := BinaryCofan.IsColimit.desc c.isColimit p.1 p.2
  left_inv γ := by
    apply BinaryCofan.IsColimit.hom_ext c.isColimit
    · exact BinaryCofan.IsColimit.inl_desc c.isColimit _ _
    · exact BinaryCofan.IsColimit.inr_desc c.isColimit _ _
  right_inv p := by
    rcases p with ⟨α, β⟩
    apply Prod.ext
    · exact BinaryCofan.IsColimit.inl_desc c.isColimit _ _
    · exact BinaryCofan.IsColimit.inr_desc c.isColimit _ _

/- The equivalences above are natural in the target object, as required by the
   source's phrase “functorially in w”. -/
theorem coproductHomEquiv_natural (c : CoproductOfPair X Y)
    {W W' : C} (f : W ⟶ W') (γ : c.cocone.pt ⟶ W) :
    coproductHomEquiv c W' (γ ≫ f) =
      ((BinaryCofan.inl c.cocone ≫ γ) ≫ f,
        (BinaryCofan.inr c.cocone ≫ γ) ≫ f) := by
  change
    (BinaryCofan.inl c.cocone ≫ γ ≫ f,
      BinaryCofan.inr c.cocone ≫ γ ≫ f) =
      ((BinaryCofan.inl c.cocone ≫ γ) ≫ f,
        (BinaryCofan.inr c.cocone ≫ γ) ≫ f)
  rw [Category.assoc, Category.assoc]

/- The canonical isomorphism between any two chosen coproduct cocones. -/
noncomputable def coproductIso {X Y : C}
    (c d : CoproductOfPair X Y) : c.cocone.pt ≅ d.cocone.pt :=
  IsColimit.coconePointUniqueUpToIso c.isColimit d.isColimit

theorem coproductIso_hom_inl {X Y : C} (c d : CoproductOfPair X Y) :
    BinaryCofan.inl c.cocone ≫ (coproductIso c d).hom =
      BinaryCofan.inl d.cocone := by
  simpa [coproductIso] using
    IsColimit.comp_coconePointUniqueUpToIso_hom c.isColimit d.isColimit
      (⟨WalkingPair.left⟩ : Discrete WalkingPair)

theorem coproductIso_hom_inr {X Y : C} (c d : CoproductOfPair X Y) :
    BinaryCofan.inr c.cocone ≫ (coproductIso c d).hom =
      BinaryCofan.inr d.cocone := by
  simpa [coproductIso] using
    IsColimit.comp_coconePointUniqueUpToIso_hom c.isColimit d.isColimit
      (⟨WalkingPair.right⟩ : Discrete WalkingPair)

/- This is the source's “unique up to unique isomorphism” assertion, with the
   compatibility with both coproduct inclusions made explicit. -/
theorem coproduct_unique_up_to_unique_iso {X Y : C}
    (c d : CoproductOfPair X Y) :
    ∃! e : c.cocone.pt ≅ d.cocone.pt,
      BinaryCofan.inl c.cocone ≫ e.hom = BinaryCofan.inl d.cocone ∧
        BinaryCofan.inr c.cocone ≫ e.hom = BinaryCofan.inr d.cocone := by
  refine ⟨coproductIso c d,
    ⟨coproductIso_hom_inl c d, coproductIso_hom_inr c d⟩, ?_⟩
  intro e he
  apply Iso.ext
  apply BinaryCofan.IsColimit.hom_ext c.isColimit
  · rw [he.1, coproductIso_hom_inl]
  · rw [he.2, coproductIso_hom_inr]

/- Mathlib's canonical name for the source's existence condition. -/
abbrev HasCoproductsOfPairs (C : Type u) [Category.{v} C] :=
  HasBinaryCoproducts C

theorem hasCoproductsOfPairs_iff (C : Type u) [Category.{v} C] :
    HasCoproductsOfPairs C ↔
      ∀ X Y : C, Nonempty (CoproductOfPair X Y) := by
  constructor
  · intro h X Y
    let _ : HasCoproductsOfPairs C := h
    exact ⟨getColimitCocone (pair X Y)⟩
  · intro h
    let _ : ∀ {X Y : C}, HasColimit (pair X Y) :=
      fun {X Y} => ⟨h X Y⟩
    exact hasBinaryCoproducts_of_hasColimit_pair (C := C)

/- The source distinguishes pairwise coproducts from finite coproducts.  The
   latter includes the empty coproduct, hence an initial object. -/
theorem hasFiniteCoproducts_hasInitial (C : Type u) [Category.{v} C]
    [HasFiniteCoproducts C] : HasInitial C := by
  infer_instance

end Formalization.Books.Categories.Unit05
