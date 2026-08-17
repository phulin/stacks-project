import Formalization.Books.Simplicial.Unit04.SimplicialPresheaves
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Simplicial Methods, Chapter 6: Products of simplicial objects

The source chooses products degree by degree.  We retain that hypothesis as
an explicit family of `HasBinaryProduct` instances and use Mathlib's
pointwise product in the functor category for the resulting simplicial
object.  The source-facing object and face/degeneracy clauses are recorded
below, together with the canonical hom-set equivalence.
-/

namespace Formalization.Books.Simplicial.Unit06

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u

/-! ## The degreewise construction -/

/-- The source's hypothesis that all degreewise products exist. -/
abbrev HasDegreewiseProducts
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) : Prop :=
  ∀ n : ℕ,
    HasBinaryProduct
      (U.obj (op (SimplexCategory.mk n)))
      (V.obj (op (SimplexCategory.mk n)))

/-- A degreewise product instance at an arbitrary object of `Δᵒᵖ`. -/
theorem degreewiseProductInstance
    {C : Type u} [Category.{v} C]
    {U V : SimplicialObject C} (h : HasDegreewiseProducts U V)
    (X : SimplexCategoryᵒᵖ) :
    HasBinaryProduct (U.obj X) (V.obj X) := by
  simpa only [SimplexCategory.mk_len] using h X.unop.len

/-- The induced binary product instance in the category of simplicial objects. -/
theorem simplicialProductInstance
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V) :
    HasBinaryProduct U V := by
  have h' : ∀ X : SimplexCategoryᵒᵖ,
      HasLimit ((pair U V).flip.obj X) := fun X =>
    (hasLimit_iff_of_iso
      (pairComp U V ((evaluation (SimplexCategoryᵒᵖ) C).obj X)).symm).mp
      (degreewiseProductInstance h X)
  exact @functorCategoryHasLimit C _ _ _ _ _ (pair U V) h'

/-- The chosen product at an arbitrary object of `Δᵒᵖ`. -/
noncomputable def degreewiseProductAt
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V)
    (X : SimplexCategoryᵒᵖ) : C :=
  letI := degreewiseProductInstance h X
  U.obj X ⨯ V.obj X

/-- The chosen product in degree `n`. -/
noncomputable def degreewiseProduct
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V) (n : ℕ) : C :=
  degreewiseProductAt U V h (op (SimplexCategory.mk n))

/-- The product of two simplicial objects, formed pointwise. -/
noncomputable def simplicialProduct
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V) :
    SimplicialObject C :=
  letI := simplicialProductInstance U V h
  U ⨯ V

/-- The first projection from the simplicial product. -/
noncomputable def simplicialProductFst
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V) :
    simplicialProduct U V h ⟶ U := by
  letI := simplicialProductInstance U V h
  exact Limits.prod.fst

/-- The second projection from the simplicial product. -/
noncomputable def simplicialProductSnd
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V) :
    simplicialProduct U V h ⟶ V := by
  letI := simplicialProductInstance U V h
  exact Limits.prod.snd

/-! ## The source's object, face, and degeneracy clauses -/

/-- In each degree, the pointwise product is canonically isomorphic to the
chosen degreewise product.  This is the Lean form of the source's object
clause, since categorical products are unique only up to canonical isomorphism.
-/
noncomputable def simplicialProductObjIso
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V)
    (X : SimplexCategoryᵒᵖ) :
    (simplicialProduct U V h).obj X ≅ degreewiseProductAt U V h X := by
  letI : ∀ Y : SimplexCategoryᵒᵖ,
      HasLimit ((pair U V).flip.obj Y) := fun Y =>
    (hasLimit_iff_of_iso
      (pairComp U V ((evaluation (SimplexCategoryᵒᵖ) C).obj Y)).symm).mp
      (degreewiseProductInstance h Y)
  letI : HasLimit (pair U V) := simplicialProductInstance U V h
  letI : HasLimit (pair (U.obj X) (V.obj X)) := degreewiseProductInstance h X
  exact preservesLimitIso ((evaluation (SimplexCategoryᵒᵖ) C).obj X) (pair U V) ≪≫
    HasLimit.isoOfNatIso (pairComp U V ((evaluation (SimplexCategoryᵒᵖ) C).obj X))

/-- The object clause at the source's degree `n`. -/
noncomputable def simplicialProductObjIsoAtDegree
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V) (n : ℕ) :
    (simplicialProduct U V h).obj (op (SimplexCategory.mk n)) ≅
      degreewiseProduct U V h n := by
  simpa only [degreewiseProduct] using
    simplicialProductObjIso U V h (op (SimplexCategory.mk n))

/-! The chosen pointwise products need not be definitionally the same objects
as the functor-category limit at each degree.  The following componentwise
naturality equations are the usable form of the source's pair-of-maps clauses.
-/

theorem simplicialProduct_face_fst
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V)
    {n : ℕ} (i : Fin (n + 2)) :
    (simplicialProduct U V h).δ i ≫
        (simplicialProductFst U V h).app (op (SimplexCategory.mk n)) =
      (simplicialProductFst U V h).app
          (op (SimplexCategory.mk (n + 1))) ≫ U.δ i := by
  sorry

theorem simplicialProduct_face_snd
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V)
    {n : ℕ} (i : Fin (n + 2)) :
    (simplicialProduct U V h).δ i ≫
        (simplicialProductSnd U V h).app (op (SimplexCategory.mk n)) =
      (simplicialProductSnd U V h).app
          (op (SimplexCategory.mk (n + 1))) ≫ V.δ i := by
  sorry

theorem simplicialProduct_degeneracy_fst
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V)
    {n : ℕ} (i : Fin (n + 1)) :
    (simplicialProduct U V h).σ i ≫
        (simplicialProductFst U V h).app
          (op (SimplexCategory.mk (n + 1))) =
      (simplicialProductFst U V h).app
          (op (SimplexCategory.mk n)) ≫ U.σ i := by
  sorry

theorem simplicialProduct_degeneracy_snd
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V)
    {n : ℕ} (i : Fin (n + 1)) :
    (simplicialProduct U V h).σ i ≫
        (simplicialProductSnd U V h).app
          (op (SimplexCategory.mk (n + 1))) =
      (simplicialProductSnd U V h).app
          (op (SimplexCategory.mk n)) ≫ V.σ i := by
  sorry

/-! ## The presheaf-product universal property -/

/-- The pointwise construction is the product in the category of simplicial
objects, hence also the product of the associated presheaves. -/
noncomputable def simplicialProductIsLimit
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V) :
    IsLimit (BinaryFan.mk (simplicialProductFst U V h)
      (simplicialProductSnd U V h)) := by
  letI := simplicialProductInstance U V h
  simpa [simplicialProduct, simplicialProductFst, simplicialProductSnd] using
    (Limits.prodIsProd U V)

/-- The source's hom-set product formula, expressed by its canonical
equivalence of hom-sets. -/
noncomputable def simplicialProductHomEquiv
    {C : Type u} [Category.{v} C]
    (U V : SimplicialObject C) (h : HasDegreewiseProducts U V)
    (W : SimplicialObject C) :
    (W ⟶ simplicialProduct U V h) ≃ (W ⟶ U) × (W ⟶ V) := by
  letI := simplicialProductInstance U V h
  exact
    { toFun := fun f =>
        (f ≫ (Limits.prod.fst : U ⨯ V ⟶ U),
          f ≫ (Limits.prod.snd : U ⨯ V ⟶ V))
      invFun := fun p => Limits.prod.lift p.1 p.2
      left_inv := by
        intro f
        apply Limits.prod.hom_ext
        · exact Limits.prod.lift_fst _ _
        · exact Limits.prod.lift_snd _ _
      right_inv := by
        rintro ⟨f, g⟩
        apply Prod.ext
        · exact Limits.prod.lift_fst _ _
        · exact Limits.prod.lift_snd _ _ }

end Formalization.Books.Simplicial.Unit06
