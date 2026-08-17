import Formalization.Books.Categories.Unit37.PresheavesOfGroupoids
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Categories, Chapter 41: The 2-Yoneda lemma

The source identifies morphisms out of a slice category with objects in a
fiber.  The canonical formalization of the strict ``over the base`` condition
is a Mathlib `Functor.Fiber` of the postcomposition functor.  For fibred
categories we take the full subcategory on functors preserving strongly
Cartesian arrows; in the groupoid case the source's full sub-2-category is
represented by the whole fiber.
-/

namespace Formalization.Books.Categories.Unit41

open CategoryTheory
open CategoryTheory.Functor
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit36
open Formalization.Books.Categories.Unit37

universe vC uC vS uS vT uT

noncomputable section

/-! ## The categories of morphisms over a base -/

/- Postcomposition by a functor `q : B ⥤ C` records the strict triangle over
   `C`.  Its fiber at `p : A ⥤ C` is the category of functors `A ⥤ B` over
   `C`. -/
abbrev twoYonedaPostcompositionGeneral
    {A : Type uS} [Category.{vS} A]
    {B : Type uT} [Category.{vT} B]
    {C : Type uC} [Category.{vC} C]
    (q : B ⥤ C) :
    (A ⥤ B) ⥤ (A ⥤ C) :=
  (Functor.whiskeringRight A B C).obj q

/-- The category of strict functors `A ⥤ B` over `C`. -/
abbrev twoYonedaMorphismCategory
    {A : Type uS} [Category.{vS} A]
    {B : Type uT} [Category.{vT} B]
    {C : Type uC} [Category.{vC} C]
    (p : A ⥤ C) (q : B ⥤ C) :=
  Functor.Fiber (twoYonedaPostcompositionGeneral q) p

/-- The condition that a strict functor over `C` is a 1-morphism of fibred
categories. -/
def twoYonedaMorphismPreservesCartesian
    {A : Type uS} [Category.{vS} A]
    {B : Type uT} [Category.{vT} B]
    {C : Type uC} [Category.{vC} C]
    (p : A ⥤ C) (q : B ⥤ C) :
    ObjectProperty (twoYonedaMorphismCategory p q) :=
  fun F => MapsStronglyCartesian p q F.1

/-- The category of 1-morphisms between fibred categories over `C`. -/
abbrev twoYonedaFibredMorphismCategoryGeneral
    {A : Type uS} [Category.{vS} A]
    {B : Type uT} [Category.{vT} B]
    {C : Type uC} [Category.{vC} C]
    (p : A ⥤ C) (q : B ⥤ C) :=
  (twoYonedaMorphismPreservesCartesian p q).FullSubcategory

/-- If both source and target are fibred in groupoids, the category of
1-morphisms over the base is a groupoid. -/
theorem twoYonedaMorphismCategory_isGroupoid
    {A : Type uS} [Category.{vS} A]
    {B : Type uT} [Category.{vT} B]
    {C : Type uC} [Category.{vC} C]
    (p : A ⥤ C) (q : B ⥤ C)
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids) :
    IsGroupoid (twoYonedaMorphismCategory p q) := by
  sorry

/-! ## The two categories of slice morphisms -/

/- Postcomposition by `p` records the strict triangle over `C`.  Its fiber at
   `Over.forget U` is the category of functors `C/U ⥤ S` and natural
   transformations over `C`. -/
abbrev twoYonedaPostcomposition
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :
    (Over U ⥤ S) ⥤ (Over U ⥤ C) :=
  twoYonedaPostcompositionGeneral p

/-- The category of strict functors `C/U ⥤ S` over `C`. -/
abbrev twoYonedaOverCategory
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :=
  twoYonedaMorphismCategory (Over.forget U) p

/- A functor over the base is a 1-morphism of fibred categories when it
   preserves the strongly Cartesian arrows. -/
def twoYonedaPreservesCartesian
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :
    ObjectProperty (twoYonedaOverCategory p U) :=
  twoYonedaMorphismPreservesCartesian (Over.forget U) p

/-- The category of 1-morphisms `C/U ⥤ S` in the 2-category of fibred
categories over `C`. -/
abbrev twoYonedaFibredMorphismCategory
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :=
  (twoYonedaPreservesCartesian p U).FullSubcategory

/-! ## Evaluation at the identity -/

/- Evaluation is first defined on all strict functors over the base.  The
   preservation condition is then imposed by restricting the source to the
   full subcategory above. -/
def twoYonedaEvaluationCore
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :
    twoYonedaOverCategory p U ⥤ Functor.Fiber p U where
  obj G :=
    ⟨G.1.obj (Over.mk (𝟙 U)), by
      sorry⟩
  map {G H} η :=
    ⟨η.1.app (Over.mk (𝟙 U)), by
      sorry⟩
  map_id := by
    intro G
    apply Functor.Fiber.hom_ext
    rfl
  map_comp := by
    intro G H K η θ
    apply Functor.Fiber.hom_ext
    rfl

/-- Evaluation at `id_U`, written on the fibred-morphism category. -/
def twoYonedaEvaluation
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :
    twoYonedaFibredMorphismCategory p U ⥤ Functor.Fiber p U :=
  (twoYonedaPreservesCartesian p U).ι ⋙ twoYonedaEvaluationCore p U

/-- The 2-Yoneda lemma for fibred categories over a fixed base. -/
theorem twoYoneda_fibred_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (U : C) :
    (twoYonedaEvaluation p U).IsEquivalence := by
  sorry

/-! ## The groupoid case -/

/- In the full 2-subcategory of categories fibred in groupoids, every strict
   functor over `C/U` is a 1-morphism. -/
abbrev twoYonedaGroupoidMorphismCategory
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :=
  twoYonedaOverCategory p U

/-- The morphism category in the groupoid version is a groupoid. -/
theorem twoYonedaGroupoidMorphismCategory_isGroupoid
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    IsGroupoid (twoYonedaGroupoidMorphismCategory p U) := by
  sorry

/-- The 2-Yoneda lemma for categories fibred in groupoids. -/
theorem twoYoneda_groupoid_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    (twoYonedaEvaluationCore p U).IsEquivalence := by
  sorry

/-! ## The alternative presheaf construction -/

/- For `f : U ⟶ V`, precomposition with `Over.map f` gives the restriction
   from the morphism category over `V` to the one over `U`. -/
def twoYonedaGroupoidRestriction
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {U V : C} (f : U ⟶ V) :
    twoYonedaGroupoidMorphismCategory p V ⥤
      twoYonedaGroupoidMorphismCategory p U where
  obj G :=
    ⟨Over.map f ⋙ G.1, by
      sorry⟩
  map {G H} η :=
    ⟨Functor.whiskerLeft (Over.map f) η.1, by
      sorry⟩
  map_id := by
    intro G
    apply Functor.Fiber.hom_ext
    rfl
  map_comp := by
    intro G H K η θ
    apply Functor.Fiber.hom_ext
    rfl

/-- The contravariant functor of categories of slice morphisms appearing in
the alternative proof. -/
def twoYonedaHomPresheaf
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) :
    Cᵒᵖ ⥤ Cat.{max (max uC vC) vS,
      max (max (max uS vS) uC) vC} where
  obj U := Cat.of (twoYonedaGroupoidMorphismCategory p U.unop)
  map f := (twoYonedaGroupoidRestriction p f.unop).toCatHom
  map_id := by
    sorry
  map_comp := by
    sorry

/- The CoGrothendieck construction is Mathlib's associated fibred category
   from the preceding presheaf formalization. -/
abbrev twoYonedaAssociatedCategory
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) :=
  groupoidPresheafCategory (twoYonedaHomPresheaf p)

/-- The projection of the associated category to the base. -/
abbrev twoYonedaAssociatedProjection
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) :
    twoYonedaAssociatedCategory p ⥤ C :=
  groupoidPresheafProjection (twoYonedaHomPresheaf p)

/-- The associated category is fibred in groupoids when `S` is. -/
theorem twoYonedaAssociatedProjection_isFibredInGroupoids
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    (twoYonedaAssociatedProjection p).IsFibredInGroupoids := by
  apply groupoidPresheafProjection_isFibredInGroupoids
  intro U
  exact twoYonedaGroupoidMorphismCategory_isGroupoid p U

/- The functor `G` of the source evaluates the fiber component at the
   identity object and then uses the arrow in the slice to reach the target
   identity. -/
def twoYonedaAssociatedFunctor
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    twoYonedaAssociatedCategory p ⥤ S where
  obj X :=
    Functor.Fiber.fiberInclusion.obj
      ((twoYonedaEvaluationCore p X.base).obj X.fiber)
  map {X Y} f :=
    ((Functor.Fiber.fiberInclusion.map
        ((twoYonedaEvaluationCore p X.base).map f.fiber)) ≫
        (show twoYonedaGroupoidMorphismCategory p Y.base from Y.fiber).1.map
        (Over.homMk (X := Y.base)
          (U := (Over.map f.base).obj (Over.mk (𝟙 X.base)))
          (V := Over.mk (𝟙 Y.base)) f.base (by simp)))
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The associated evaluation functor is over the base. -/
theorem twoYonedaAssociatedFunctor_over
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    twoYonedaAssociatedFunctor p ⋙ p =
      twoYonedaAssociatedProjection p := by
  sorry

/- The source identifies the fiber of the associated construction with the
   chosen value of the presheaf.  We use Mathlib's `HasFibers` interface for
   this canonical equivalence. -/
def twoYonedaAssociatedFiberFunctor
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    twoYonedaGroupoidMorphismCategory p U ⥤ Functor.Fiber p U :=
  HasFibers.inducedFunctor (twoYonedaAssociatedProjection p) U ⋙
    fibreFunctor (twoYonedaAssociatedProjection p) p
      (twoYonedaAssociatedFunctor p) (twoYonedaAssociatedFunctor_over p) U

/-- The fiberwise functor in the alternative proof is an equivalence. -/
theorem twoYonedaAssociatedFiberFunctor_isEquivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    (twoYonedaAssociatedFiberFunctor p U).IsEquivalence := by
  sorry

/-- The final equivalence in the alternative proof. -/
theorem twoYonedaAssociatedFunctor_isEquivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    (twoYonedaAssociatedFunctor p).IsEquivalence := by
  sorry

end

end Formalization.Books.Categories.Unit41
