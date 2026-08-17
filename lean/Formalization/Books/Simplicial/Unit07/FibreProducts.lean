import Formalization.Books.Simplicial.Unit04.SimplicialPresheaves
import Formalization.Books.Categories.Unit06.FibreProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Simplicial Methods, Chapter 7: Fibre products of simplicial objects

The source defines the fibre product degree by degree.  Mathlib's
`PullbackCone.combine` is exactly the canonical construction that turns a
chosen pullback cone at every object of the indexing category into a
pullback cone in the functor category.  We use it with the degreewise
pullbacks of the three simplicial objects.
-/

namespace Formalization.Books.Simplicial.Unit07

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u

/-! ## The degreewise construction -/

/-- The source's hypothesis that all degreewise fibre products exist. -/
abbrev HasDegreewiseFibreProducts
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U) : Prop :=
  ∀ n : ℕ,
    HasPullback
      (a.app (op (SimplexCategory.mk n)))
      (b.app (op (SimplexCategory.mk n)))

/-- The chosen degree-`n` fibre product used by the direct construction. -/
noncomputable def degreewiseFibreProduct
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (n : ℕ) : C :=
  letI : HasPullback
      (a.app (op (SimplexCategory.mk n)))
      (b.app (op (SimplexCategory.mk n))) := h n
  pullback (a.app (op (SimplexCategory.mk n)))
    (b.app (op (SimplexCategory.mk n)))

/-- The degreewise pullback cone at an arbitrary object of `Δᵒᵖ`. -/
noncomputable def degreewiseFibreProductCone
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (X : SimplexCategoryᵒᵖ) :
    PullbackCone (a.app X) (b.app X) :=
  letI : HasPullback (a.app X) (b.app X) := by
    simpa only [SimplexCategory.mk_len] using h X.unop.len
  pullback.cone (a.app X) (b.app X)

/-- The universal property of each chosen degreewise pullback cone. -/
noncomputable def degreewiseFibreProductConeIsLimit
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (X : SimplexCategoryᵒᵖ) :
    IsLimit (degreewiseFibreProductCone a b h X) := by
  letI : HasPullback (a.app X) (b.app X) := by
    simpa only [SimplexCategory.mk_len] using h X.unop.len
  exact pullback.isLimit (a.app X) (b.app X)

/-- The pullback cone obtained by stitching the degreewise cones together. -/
noncomputable def simplicialFibreProductCone
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) : PullbackCone a b :=
  PullbackCone.combine a b
    (fun X => degreewiseFibreProductCone a b h X)
    (fun X => degreewiseFibreProductConeIsLimit a b h X)

/-- The fibre product of `V` and `W` over `U`, formed degree by degree. -/
noncomputable def simplicialFibreProduct
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) : SimplicialObject C :=
  (simplicialFibreProductCone a b h).pt

/-- The two canonical projections from the simplicial fibre product. -/
noncomputable def simplicialFibreProductFst
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) :
    simplicialFibreProduct a b h ⟶ V :=
  (simplicialFibreProductCone a b h).fst

noncomputable def simplicialFibreProductSnd
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) :
    simplicialFibreProduct a b h ⟶ W :=
  (simplicialFibreProductCone a b h).snd

/-- The degreewise construction is a pullback in the category of simplicial
objects, while retaining the source's explicit pointwise choice. -/
noncomputable def simplicialFibreProductIsLimit
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) :
    IsLimit (simplicialFibreProductCone a b h) :=
  PullbackCone.combineIsLimit a b
    (fun X => degreewiseFibreProductCone a b h X)
    (fun X => degreewiseFibreProductConeIsLimit a b h X)

/-- The resulting projections satisfy the categorical fibre-product
universal property. -/
theorem simplicialFibreProductIsPullback
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) :
    IsPullback (simplicialFibreProductFst a b h)
      (simplicialFibreProductSnd a b h) a b :=
  IsPullback.of_isLimit (simplicialFibreProductIsLimit a b h)

/-! ## The source's object, face, and degeneracy clauses -/

/-- In degree `n`, the construction has the prescribed pullback object. -/
theorem simplicialFibreProduct_obj
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (n : ℕ) :
    (simplicialFibreProduct a b h).obj (op (SimplexCategory.mk n)) =
      degreewiseFibreProduct a b h n := by
  rfl

/-!
The source writes the face and degeneracy maps as pairs of the corresponding
maps of `V` and `W`.  The following naturality equations are the stronger
generic form of those two clauses: they characterize every simplicial map of
the constructed pullback by its two projections, and hence specialize to all
faces and degeneracies.
-/

@[reassoc]
theorem simplicialFibreProduct_map_fst
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) {X Y : SimplexCategoryᵒᵖ}
    (f : X ⟶ Y) :
    (simplicialFibreProduct a b h).map f ≫
        (simplicialFibreProductFst a b h).app Y =
      (simplicialFibreProductFst a b h).app X ≫ V.map f := by
  exact (simplicialFibreProductFst a b h).naturality f

@[reassoc]
theorem simplicialFibreProduct_map_snd
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) {X Y : SimplexCategoryᵒᵖ}
    (f : X ⟶ Y) :
    (simplicialFibreProduct a b h).map f ≫
        (simplicialFibreProductSnd a b h).app Y =
      (simplicialFibreProductSnd a b h).app X ≫ W.map f := by
  exact (simplicialFibreProductSnd a b h).naturality f

/-! ## The hom-set formula -/

/-- The source's displayed hom-set identity, as the canonical equivalence
between maps into the simplicial fibre product and compatible pairs of maps.
The target is Mathlib's explicit pullback object in `Type`. -/
noncomputable def simplicialFibreProductHomEquiv
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (T : SimplicialObject C) :
    (T ⟶ simplicialFibreProduct a b h) ≃
      Types.PullbackObj
        (TypeCat.ofHom (fun f : T ⟶ V => f ≫ a))
        (TypeCat.ofHom (fun g : T ⟶ W => g ≫ b)) :=
  Formalization.Books.Categories.Unit06.fibreProductHomEquiv
    (simplicialFibreProductIsPullback a b h) T

/-- Equivalently, compatible maps into `V` and `W` admit a unique map into
the degreewise fibre product with the prescribed composites. -/
theorem simplicialFibreProduct_universal_property
    {C : Type u} [Category.{v} C]
    {V W U : SimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (T : SimplicialObject C)
    (f : T ⟶ V) (g : T ⟶ W) (compatibility : f ≫ a = g ≫ b) :
    ∃! lift : T ⟶ simplicialFibreProduct a b h,
      lift ≫ simplicialFibreProductFst a b h = f ∧
        lift ≫ simplicialFibreProductSnd a b h = g := by
  exact Formalization.Books.Categories.Unit06.fibre_product_universal_property
    (simplicialFibreProductIsPullback a b h) f g compatibility

end Formalization.Books.Simplicial.Unit07
