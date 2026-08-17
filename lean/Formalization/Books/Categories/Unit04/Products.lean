import Formalization.Books.Categories.Unit03.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Categories, Chapter 4: Products of pairs

Mathlib's `BinaryFan` and `IsLimit` are the canonical interfaces for the
product object, its two projections, and the universal property in the source.
The declarations below record the source-facing universal property, its
uniqueness consequence, and the functor-of-points formulation without
introducing a parallel product structure.
-/

namespace Formalization.Books.Categories.Unit04

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit03
open Opposite

universe v u

section ProductsOfPairs

variable {C : Type u} [Category.{v} C]

/- The source's definition is exactly a limiting `BinaryFan` whose point is
  the proposed product and whose legs are the two projections. -/

theorem binaryProduct_universal_property
    {X Y P : C} {p : P ⟶ X} {q : P ⟶ Y}
    (h : IsLimit (BinaryFan.mk p q)) (W : C) (α : W ⟶ X) (β : W ⟶ Y) :
    ∃! γ : W ⟶ P, γ ≫ p = α ∧ γ ≫ q = β := by
  refine ⟨h.lift (BinaryFan.mk α β), ?_, ?_⟩
  · exact ⟨by simpa using h.fac (BinaryFan.mk α β) ⟨WalkingPair.left⟩,
      by simpa using h.fac (BinaryFan.mk α β) ⟨WalkingPair.right⟩⟩
  · intro γ hγ
    apply BinaryFan.IsLimit.hom_ext h
    · simpa using hγ.1.trans
        (h.fac (BinaryFan.mk α β) ⟨WalkingPair.left⟩).symm
    · simpa using hγ.2.trans
        (h.fac (BinaryFan.mk α β) ⟨WalkingPair.right⟩).symm

/- The universal morphisms assemble into the hom-set bijection used by the
  source's functor-of-points explanation. -/

noncomputable def productHomEquiv
    {X Y P : C} {p : P ⟶ X} {q : P ⟶ Y}
    (h : IsLimit (BinaryFan.mk p q)) (W : C) :
    (W ⟶ P) ≃ (W ⟶ X) × (W ⟶ Y) where
  toFun γ := (γ ≫ p, γ ≫ q)
  invFun z := h.lift (BinaryFan.mk z.1 z.2)
  left_inv γ := by
    apply BinaryFan.IsLimit.hom_ext h
    · simpa using h.fac (BinaryFan.mk (γ ≫ p) (γ ≫ q)) ⟨WalkingPair.left⟩
    · simpa using h.fac (BinaryFan.mk (γ ≫ p) (γ ≫ q)) ⟨WalkingPair.right⟩
  right_inv z := by
    apply Prod.ext
    · simpa using h.fac (BinaryFan.mk z.1 z.2) ⟨WalkingPair.left⟩
    · simpa using h.fac (BinaryFan.mk z.1 z.2) ⟨WalkingPair.right⟩

theorem productHomEquiv_natural
    {X Y P : C} {p : P ⟶ X} {q : P ⟶ Y}
    (h : IsLimit (BinaryFan.mk p q)) {V W : C} (f : V ⟶ W) (γ : W ⟶ P) :
    productHomEquiv h V (f ≫ γ) =
      (f ≫ (productHomEquiv h W γ).1, f ≫ (productHomEquiv h W γ).2) := by
  simp [productHomEquiv, Category.assoc]

/- This is the source's `h_P(W) = h_X(W) × h_Y(W)` statement, expressed as
  the canonical equivalence of hom-sets rather than literal equality of
  types. -/

noncomputable def representablePresheaf_product_obj_equiv
    {X Y P : C} {p : P ⟶ X} {q : P ⟶ Y}
    (h : IsLimit (BinaryFan.mk p q)) (W : C) :
    (representablePresheaf P).obj (op W) ≃
      (representablePresheaf X).obj (op W) ×
        (representablePresheaf Y).obj (op W) :=
  productHomEquiv h W

theorem representablePresheaf_product_representation
    {X Y P : C} {p : P ⟶ X} {q : P ⟶ Y}
    (h : IsLimit (BinaryFan.mk p q)) :
    Nonempty
      (representablePresheaf P ≅
        FunctorToTypes.prod (representablePresheaf X) (representablePresheaf Y)) := by
  refine ⟨NatIso.ofComponents (fun W =>
    (representablePresheaf_product_obj_equiv h W.unop).toIso) ?_⟩
  intro V W f
  ext γ <;>
    simp [representablePresheaf_product_obj_equiv, productHomEquiv,
      FunctorToTypes.prod, Category.assoc]

/- The canonical limit-cone isomorphism has exactly the projection equations
  in the source's “unique up to unique isomorphism” assertion. -/

theorem binaryProduct_unique_up_to_unique_iso
    {X Y P Q : C} {pP : P ⟶ X} {qP : P ⟶ Y}
    {pQ : Q ⟶ X} {qQ : Q ⟶ Y}
    (hP : IsLimit (BinaryFan.mk pP qP))
    (hQ : IsLimit (BinaryFan.mk pQ qQ)) :
    ∃! e : P ≅ Q, e.hom ≫ pQ = pP ∧ e.hom ≫ qQ = qP := by
  let e := hP.conePointUniqueUpToIso hQ
  refine ⟨e, ?_, ?_⟩
  · exact ⟨by simpa using hP.conePointUniqueUpToIso_hom_comp hQ ⟨WalkingPair.left⟩,
      by simpa using hP.conePointUniqueUpToIso_hom_comp hQ ⟨WalkingPair.right⟩⟩
  · intro e' he'
    apply Iso.ext
    apply BinaryFan.IsLimit.hom_ext hQ
    · exact he'.1.trans (hP.conePointUniqueUpToIso_hom_comp hQ ⟨WalkingPair.left⟩).symm
    · exact he'.2.trans (hP.conePointUniqueUpToIso_hom_comp hQ ⟨WalkingPair.right⟩).symm

/- Mathlib's `HasBinaryProducts` is precisely the source's notion that a
  product exists for every pair of objects. -/

theorem has_products_of_pairs_iff :
    HasBinaryProducts C ↔
      ∀ X Y : C, Nonempty (LimitCone (pair X Y)) := by
  constructor
  · intro h X Y
    exact (h.has_limit (pair X Y)).exists_limit
  · intro h
    let _ : ∀ {X Y : C}, HasLimit (pair X Y) := by
      intro X Y
      exact ⟨h X Y⟩
    apply hasBinaryProducts_of_hasLimit_pair C

/- The source's warning about finite products is represented by the canonical
  finite-product class: its nullary product supplies a terminal object. -/

theorem has_terminal_of_has_finite_products [HasFiniteProducts C] :
    HasTerminal C := by
  infer_instance

theorem has_terminal_of_has_products [HasProducts.{v} C] :
    HasTerminal C := by
  let h : HasFiniteProducts C := hasFiniteProducts_of_hasProducts C
  exact @has_terminal_of_has_finite_products C _ h

end ProductsOfPairs

end Formalization.Books.Categories.Unit04
