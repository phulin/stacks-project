import Formalization.Books.Simplicial.Unit05.CosimplicialObjects
import Formalization.Books.Categories.Unit06.FibreProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Simplicial Methods, Chapter 10: Fibre products of cosimplicial objects

The source defines the fibre product degree by degree.  Mathlib's
`PullbackCone.combine` is the canonical construction that stitches chosen
pullback cones at the objects of the indexing category into a pullback cone
in the category of cosimplicial objects.
-/

namespace Formalization.Books.Simplicial.Unit10

open CategoryTheory
open CategoryTheory.Limits
open scoped _root_.Simplicial

universe v u

/-! ## The degreewise construction -/

/-- The source's hypothesis that all degreewise fibre products exist. -/
abbrev HasDegreewiseFibreProducts
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U) : Prop :=
  ∀ n : ℕ,
    HasPullback
      (a.app (SimplexCategory.mk n))
      (b.app (SimplexCategory.mk n))

/-- The chosen degree-`n` fibre product used by the direct construction. -/
noncomputable def degreewiseFibreProduct
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (n : ℕ) : C :=
  letI : HasPullback
      (a.app (SimplexCategory.mk n))
      (b.app (SimplexCategory.mk n)) := h n
  pullback (a.app (SimplexCategory.mk n))
    (b.app (SimplexCategory.mk n))

/-- The degreewise pullback cone at an arbitrary object of `Δ`. -/
noncomputable def degreewiseFibreProductCone
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (X : SimplexCategory) :
    PullbackCone (a.app X) (b.app X) :=
  letI : HasPullback (a.app X) (b.app X) := by
    simpa only [SimplexCategory.mk_len] using h X.len
  pullback.cone (a.app X) (b.app X)

/- The universal property of each chosen degreewise pullback cone. -/
noncomputable def degreewiseFibreProductConeIsLimit
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (X : SimplexCategory) :
    IsLimit (degreewiseFibreProductCone a b h X) := by
  letI : HasPullback (a.app X) (b.app X) := by
    simpa only [SimplexCategory.mk_len] using h X.len
  exact pullback.isLimit (a.app X) (b.app X)

/-- The pullback cone obtained by stitching the degreewise cones together. -/
noncomputable def cosimplicialFibreProductCone
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) : PullbackCone a b :=
  PullbackCone.combine a b
    (fun X => degreewiseFibreProductCone a b h X)
    (fun X => degreewiseFibreProductConeIsLimit a b h X)

/-- The fibre product of `V` and `W` over `U`, formed degree by degree. -/
noncomputable def cosimplicialFibreProduct
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) : CosimplicialObject C :=
  (cosimplicialFibreProductCone a b h).pt

/-- The two canonical projections from the cosimplicial fibre product. -/
noncomputable def cosimplicialFibreProductFst
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) :
    cosimplicialFibreProduct a b h ⟶ V :=
  (cosimplicialFibreProductCone a b h).fst

noncomputable def cosimplicialFibreProductSnd
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) :
    cosimplicialFibreProduct a b h ⟶ W :=
  (cosimplicialFibreProductCone a b h).snd

/-- The degreewise construction is a pullback in the category of cosimplicial
objects, while retaining the source's explicit pointwise choice. -/
noncomputable def cosimplicialFibreProductIsLimit
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) :
    IsLimit (cosimplicialFibreProductCone a b h) :=
  PullbackCone.combineIsLimit a b
    (fun X => degreewiseFibreProductCone a b h X)
    (fun X => degreewiseFibreProductConeIsLimit a b h X)

/-- The resulting projections satisfy the categorical fibre-product
universal property. -/
theorem cosimplicialFibreProductIsPullback
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) :
    IsPullback (cosimplicialFibreProductFst a b h)
      (cosimplicialFibreProductSnd a b h) a b :=
  IsPullback.of_isLimit (cosimplicialFibreProductIsLimit a b h)

/-! ## The source's object and map clauses -/

/-- In degree `n`, the construction has the prescribed pullback object. -/
theorem cosimplicialFibreProduct_obj
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (n : ℕ) :
    (cosimplicialFibreProduct a b h).obj (SimplexCategory.mk n) =
      degreewiseFibreProduct a b h n := by
  rfl

/-!
The source writes the map associated to `φ : [n] ⟶ [m]` as the map induced
by the two maps of `V` and `W` over the map of `U`.  The following naturality
equations are the stronger generic form: they characterize every map of the
constructed pullback by its two projections, and hence specialize to all
cofaces, codegeneracies, and other maps in `Δ`.
-/

@[reassoc]
theorem cosimplicialFibreProduct_map_fst
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) {X Y : SimplexCategory}
    (f : X ⟶ Y) :
    (cosimplicialFibreProduct a b h).map f ≫
        (cosimplicialFibreProductFst a b h).app Y =
      (cosimplicialFibreProductFst a b h).app X ≫ V.map f := by
  exact (cosimplicialFibreProductFst a b h).naturality f

@[reassoc]
theorem cosimplicialFibreProduct_map_snd
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) {X Y : SimplexCategory}
    (f : X ⟶ Y) :
    (cosimplicialFibreProduct a b h).map f ≫
        (cosimplicialFibreProductSnd a b h).app Y =
      (cosimplicialFibreProductSnd a b h).app X ≫ W.map f := by
  exact (cosimplicialFibreProductSnd a b h).naturality f

/-! ## The hom-set formula -/

/-- The source's displayed hom-set identity, as the canonical equivalence
between maps into the cosimplicial fibre product and compatible pairs of maps.
The target is Mathlib's explicit pullback object in `Type`. -/
noncomputable def cosimplicialFibreProductHomEquiv
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (T : CosimplicialObject C) :
    (T ⟶ cosimplicialFibreProduct a b h) ≃
      Types.PullbackObj
        (TypeCat.ofHom (fun f : T ⟶ V => f ≫ a))
        (TypeCat.ofHom (fun g : T ⟶ W => g ≫ b)) :=
  Formalization.Books.Categories.Unit06.fibreProductHomEquiv
    (cosimplicialFibreProductIsPullback a b h) T

/-- Compatible maps into `V` and `W` admit a unique map into the
cosimplicial fibre product with the prescribed composites. -/
theorem cosimplicialFibreProduct_universal_property
    {C : Type u} [Category.{v} C]
    {V W U : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
    (h : HasDegreewiseFibreProducts a b) (T : CosimplicialObject C)
    (f : T ⟶ V) (g : T ⟶ W) (compatibility : f ≫ a = g ≫ b) :
    ∃! lift : T ⟶ cosimplicialFibreProduct a b h,
      lift ≫ cosimplicialFibreProductFst a b h = f ∧
        lift ≫ cosimplicialFibreProductSnd a b h = g := by
  exact Formalization.Books.Categories.Unit06.fibre_product_universal_property
    (cosimplicialFibreProductIsPullback a b h) f g compatibility

end Formalization.Books.Simplicial.Unit10
