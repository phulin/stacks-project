import Formalization.Books.Simplicial.Unit05.CosimplicialObjects
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Simplicial Methods, Chapter 9: Products of cosimplicial objects

The source deliberately defines this product degree by degree.  We reuse
Mathlib's `HasBinaryProduct`, `prod`, and `prod.map` rather than introducing a
second product object or a parallel universal-property interface.
-/

namespace Formalization.Books.Simplicial.Unit09

open CategoryTheory
open CategoryTheory.Limits
open scoped _root_.Simplicial

universe v u

/-! ## The degreewise construction -/

/-- The source's hypothesis that all degreewise products exist. -/
abbrev HasDegreewiseProducts
    {C : Type u} [Category.{v} C]
    (U V : CosimplicialObject C) : Prop :=
  ∀ n : ℕ,
    HasBinaryProduct
      (U.obj (SimplexCategory.mk n))
      (V.obj (SimplexCategory.mk n))

/-- The chosen product in degree `n`. -/
noncomputable def degreewiseCosimplicialProduct
    {C : Type u} [Category.{v} C]
    (U V : CosimplicialObject C) (h : HasDegreewiseProducts U V)
    (n : ℕ) : C :=
  letI : HasBinaryProduct
      (U.obj (SimplexCategory.mk n))
      (V.obj (SimplexCategory.mk n)) := h n
  U.obj (SimplexCategory.mk n) ⨯ V.obj (SimplexCategory.mk n)

/--
The product of two cosimplicial objects, formed degree by degree.  At an
arbitrary object `X : SimplexCategory`, the hypothesis at `X.len` is
transported along `SimplexCategory.mk_len`.

The warning in the source is intentional: a product in the abstract category
of cosimplicial objects need not have been presented by these chosen
degreewise products, so this declaration records the source's direct model.
-/
noncomputable def cosimplicialProduct
    {C : Type u} [Category.{v} C]
    (U V : CosimplicialObject C) (h : HasDegreewiseProducts U V) :
    CosimplicialObject C :=
  { obj := fun X =>
      letI : HasBinaryProduct (U.obj X) (V.obj X) := by
        simpa only [SimplexCategory.mk_len] using h X.len
      U.obj X ⨯ V.obj X
    map := fun {X Y} f =>
      letI : HasBinaryProduct (U.obj X) (V.obj X) := by
        simpa only [SimplexCategory.mk_len] using h X.len
      letI : HasBinaryProduct (U.obj Y) (V.obj Y) := by
        simpa only [SimplexCategory.mk_len] using h Y.len
      prod.map (U.map f) (V.map f)
    map_id := by
      intro X
      let _ : HasBinaryProduct (U.obj X) (V.obj X) := by
        simpa only [SimplexCategory.mk_len] using h X.len
      change prod.map (U.map (𝟙 X)) (V.map (𝟙 X)) = 𝟙 _
      rw [U.map_id, V.map_id, prod.map_id_id]
    map_comp := by
      intro X Y Z f g
      let _ : HasBinaryProduct (U.obj X) (V.obj X) := by
        simpa only [SimplexCategory.mk_len] using h X.len
      let _ : HasBinaryProduct (U.obj Y) (V.obj Y) := by
        simpa only [SimplexCategory.mk_len] using h Y.len
      let _ : HasBinaryProduct (U.obj Z) (V.obj Z) := by
        simpa only [SimplexCategory.mk_len] using h Z.len
      change prod.map (U.map (f ≫ g)) (V.map (f ≫ g)) =
        prod.map (U.map f) (V.map f) ≫ prod.map (U.map g) (V.map g)
      rw [U.map_comp, V.map_comp, prod.map_map] }

/-- In degree `n`, the product has the prescribed product object. -/
theorem cosimplicialProduct_obj
    {C : Type u} [Category.{v} C]
    (U V : CosimplicialObject C) (h : HasDegreewiseProducts U V)
    (n : ℕ) :
    (cosimplicialProduct U V h).obj (SimplexCategory.mk n) =
      degreewiseCosimplicialProduct U V h n := by
  rfl

/-- The map in degree `φ` is the product of the maps of `U` and `V`. -/
theorem cosimplicialProduct_map
    {C : Type u} [Category.{v} C]
    (U V : CosimplicialObject C) (h : HasDegreewiseProducts U V)
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    (cosimplicialProduct U V h).map φ =
      letI : HasBinaryProduct
          (U.obj (SimplexCategory.mk n))
          (V.obj (SimplexCategory.mk n)) := h n
      letI : HasBinaryProduct
          (U.obj (SimplexCategory.mk m))
          (V.obj (SimplexCategory.mk m)) := h m
      prod.map (U.map φ) (V.map φ) := by
  rfl

/-! The componentwise projections and lifts used by the hom-set equivalence. -/

/-- The first projection from the chosen product in degree `X`. -/
noncomputable def cosimplicialProductFst
    {C : Type u} [Category.{v} C]
    (U V : CosimplicialObject C) (h : HasDegreewiseProducts U V)
    (X : SimplexCategory) :
    (cosimplicialProduct U V h).obj X ⟶ U.obj X :=
  letI : HasBinaryProduct (U.obj X) (V.obj X) := by
    simpa only [SimplexCategory.mk_len] using h X.len
  prod.fst

/-- The second projection from the chosen product in degree `X`. -/
noncomputable def cosimplicialProductSnd
    {C : Type u} [Category.{v} C]
    (U V : CosimplicialObject C) (h : HasDegreewiseProducts U V)
    (X : SimplexCategory) :
    (cosimplicialProduct U V h).obj X ⟶ V.obj X :=
  letI : HasBinaryProduct (U.obj X) (V.obj X) := by
    simpa only [SimplexCategory.mk_len] using h X.len
  prod.snd

/-- The product lift of two natural-transformation components in degree `X`. -/
noncomputable def cosimplicialProductLift
    {C : Type u} [Category.{v} C]
    {W : CosimplicialObject C} (U V : CosimplicialObject C)
    (h : HasDegreewiseProducts U V) (f : W ⟶ U) (g : W ⟶ V)
    (X : SimplexCategory) :
    W.obj X ⟶ (cosimplicialProduct U V h).obj X :=
  letI : HasBinaryProduct (U.obj X) (V.obj X) := by
    simpa only [SimplexCategory.mk_len] using h X.len
  prod.lift (f.app X) (g.app X)

/-! ## The hom-set formula -/

/--
The source's displayed equality of hom-sets, expressed as the canonical
equivalence between maps into the degreewise product and pairs of maps.
The componentwise proof uses the binary-product universal property and
naturality of the two resulting natural transformations.
-/
noncomputable def cosimplicialProduct_hom_equiv
    {C : Type u} [Category.{v} C]
    (U V : CosimplicialObject C) (h : HasDegreewiseProducts U V)
    (W : CosimplicialObject C) :
    (W ⟶ cosimplicialProduct U V h) ≃
      (W ⟶ U) × (W ⟶ V) where
  toFun f :=
    ( { app := fun X =>
          f.app X ≫ cosimplicialProductFst U V h X
        naturality := by
          intro X Y φ
          simpa [Category.assoc, cosimplicialProduct,
            cosimplicialProductFst] using
            congrArg (fun k => k ≫ cosimplicialProductFst U V h Y)
              (f.naturality φ) },
      { app := fun X =>
          f.app X ≫ cosimplicialProductSnd U V h X
        naturality := by
          intro X Y φ
          simpa [Category.assoc, cosimplicialProduct,
            cosimplicialProductSnd] using
            congrArg (fun k => k ≫ cosimplicialProductSnd U V h Y)
              (f.naturality φ) } )
  invFun f :=
    { app := fun X =>
        cosimplicialProductLift U V h f.1 f.2 X
      naturality := by
        intro X Y φ
        simp [cosimplicialProductLift, cosimplicialProduct]
        rw [f.1.naturality φ, f.2.naturality φ] }
  left_inv := by
    intro f
    ext X
    simp [cosimplicialProductLift, cosimplicialProductFst,
      cosimplicialProductSnd]
    apply prod.hom_ext
    · exact prod.lift_fst _ _
    · exact prod.lift_snd _ _
  right_inv := by
    intro f
    apply Prod.ext
    · apply NatTrans.ext
      funext X
      simp [cosimplicialProductLift, cosimplicialProductFst]
      exact prod.lift_fst _ _
    · apply NatTrans.ext
      funext X
      simp [cosimplicialProductLift, cosimplicialProductSnd]
      exact prod.lift_snd _ _

end Formalization.Books.Simplicial.Unit09
