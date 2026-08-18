import Formalization.Books.Categories.Unit28.FormalProperties
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
open Opposite
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit36
open Formalization.Books.Categories.Unit37

universe vC uC vS uS vT uT

noncomputable section

/- Unit 35 records the equivalence between the lifting definition of a
   category fibred in groupoids and `IsFibered`, but does not register its
   `IsFibered` consequence as an instance.  The chosen-pullback formulas in
   this chapter use that canonical consequence. -/
noncomputable instance twoYoneda_isFibered_of_isFibredInGroupoids
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibredInGroupoids] : p.IsFibered :=
  ((fibredInGroupoids_iff_fibred_groupoid_fibres p).mp
    (inferInstance : p.IsFibredInGroupoids)).2

/-! ## The categories of morphisms over a base

The first lemma in the source identifies the category of fibred functors
from a slice with a fibre.  We model a strict functor over the base by the
canonical `Functor.Fiber` of postcomposition and then impose preservation of
strongly Cartesian arrows by a full-subcategory construction. -/

/- Postcomposition by a functor `q : B ⥤ C` records the strict triangle over
   `C`.  Its fiber at `p : A ⥤ C` is the category of functors `A ⥤ B` over
   `C`. -/
abbrev twoYonedaPostcompositionGeneral
    {A : Type uS} [Category.{vS} A]
    {B : Type uT} [Category.{vT} B]
    {C : Type uC} [Category.{vC} C]
    (q : B ⥤ C) :
    (A ⥤ B) ⥤ (A ⥤ C) :=
  Formalization.Books.Categories.Unit28.postcompositionFunctor q

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
  twoYonedaFibredMorphismCategoryGeneral (Over.forget U) p

/-! ## The pullback construction in the proof -/

/- The source constructs a functor from the fibre over `U` back to the
   category of fibred morphisms.  These declarations retain the actual
   object and arrow formulas, using the chosen pullback data from Unit 33. -/
def twoYonedaPullbackFunctorObj
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) (f : Over U) : S :=
  Functor.Fiber.fiberInclusion.obj (P.pullback f.hom x)

/- The earlier chapter states the comparison as a unique existence result;
   choose that canonical comparison here so the displayed arrow formula below
   has an actual isomorphism to use. -/
noncomputable def twoYonedaPullbackCompositionIso
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p)
    {R T V : C} (f : R ⟶ T) (g : T ⟶ V) :
    P.pullbackFunctor (f ≫ g) ≅
      P.pullbackFunctor g ⋙ P.pullbackFunctor f :=
  Classical.choose (ExistsUnique.exists (pullback_composition_iso p P f g))

theorem twoYonedaPullbackCompositionIso_hom_app
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p)
    {R T V : C} (f : R ⟶ T) (g : T ⟶ V)
    (x : Functor.Fiber p V) :
    Functor.Fiber.fiberInclusion.map
          ((twoYonedaPullbackCompositionIso p P f g).hom.app x) ≫
        P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x =
      P.pullbackMap (f ≫ g) x := by
  exact Classical.choose_spec
    (ExistsUnique.exists (pullback_composition_iso p P f g)) x

def twoYonedaPullbackFunctorMap
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) {f g : Over U} (k : f ⟶ g) :
    twoYonedaPullbackFunctorObj p P U x f ⟶
      twoYonedaPullbackFunctorObj p P U x g :=
  ((Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
      (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm))) ≫
    ((Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
      ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x)) ≫
    P.pullbackMap k.left (P.pullback g.hom x)

private theorem twoYonedaPullbackFunctorMap_isHomLift
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) {f g : Over U} (k : f ⟶ g) :
    p.IsHomLift k.left (twoYonedaPullbackFunctorMap p P U x k) := by
  unfold twoYonedaPullbackFunctorMap twoYonedaPullbackFunctorObj
  have h₁ : p.IsHomLift (𝟙 f.left)
      (Functor.Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm))) := by
    exact (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm)).2
  have h₂ : p.IsHomLift (𝟙 f.left)
      (Functor.Fiber.fiberInclusion.map
        ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x)) := by
    exact ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x).2
  have hp : p.IsHomLift k.left (P.pullbackMap k.left (P.pullback g.hom x)) :=
    (P.pullbackMap_isStronglyCartesian k.left (P.pullback g.hom x)).toIsHomLift
  have h₂p : p.IsHomLift k.left
      (Functor.Fiber.fiberInclusion.map
        ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x) ≫
        P.pullbackMap k.left (P.pullback g.hom x)) := by
    simpa [Functor.Fiber.fiberInclusion] using
      (@IsHomLift.comp _ _ _ _ p
        f.left f.left g.left
        (Functor.Fiber.fiberInclusion.obj
          ((P.pullbackFunctor (k.left ≫ g.hom)).obj x))
        (Functor.Fiber.fiberInclusion.obj
          ((P.pullbackFunctor g.hom ⋙ P.pullbackFunctor k.left).obj x))
        (Functor.Fiber.fiberInclusion.obj (P.pullback g.hom x))
        (𝟙 f.left) k.left
        (Functor.Fiber.fiberInclusion.map
          ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x))
        (P.pullbackMap k.left (P.pullback g.hom x)) h₂ hp)
  have hfinal : p.IsHomLift (𝟙 f.left ≫ k.left)
      (Functor.Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm)) ≫
        (Functor.Fiber.fiberInclusion.map
          ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x) ≫
          P.pullbackMap k.left (P.pullback g.hom x))) := by
    exact @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
      (𝟙 f.left) k.left
      (Functor.Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm)))
      (Functor.Fiber.fiberInclusion.map
        ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x) ≫
        P.pullbackMap k.left (P.pullback g.hom x)) h₁ h₂p
  convert hfinal using 1 <;> simp [Category.id_comp, Functor.Fiber.fiberInclusion]

private theorem twoYonedaPullbackFunctorMap_fac
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) {f g : Over U} (k : f ⟶ g) :
    twoYonedaPullbackFunctorMap p P U x k ≫ P.pullbackMap g.hom x =
      P.pullbackMap f.hom x := by
  unfold twoYonedaPullbackFunctorMap
  have pullbackMap_eq_of_eq {R S : C} {a b : R ⟶ S} (h : a = b)
      (z : Functor.Fiber p S) :
      Functor.Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun q => P.pullback q z) h)) ≫
        P.pullbackMap b z = P.pullbackMap a z := by
    subst b
    simp
  let e := congrArg (fun h => P.pullback h x) (Over.w k).symm
  have hcomp :
      Functor.Fiber.fiberInclusion.map
          ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x) ≫
        P.pullbackMap k.left (P.pullback g.hom x) ≫
        P.pullbackMap g.hom x =
      P.pullbackMap (k.left ≫ g.hom) x :=
    twoYonedaPullbackCompositionIso_hom_app p P k.left g.hom x
  calc
    (Functor.Fiber.fiberInclusion.map (eqToHom e) ≫
        Functor.Fiber.fiberInclusion.map
          ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x) ≫
        P.pullbackMap k.left (P.pullback g.hom x)) ≫
        P.pullbackMap g.hom x =
      Functor.Fiber.fiberInclusion.map (eqToHom e) ≫
        (Functor.Fiber.fiberInclusion.map
          ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x) ≫
          P.pullbackMap k.left (P.pullback g.hom x) ≫
          P.pullbackMap g.hom x) := by
            exact (Category.assoc _ _ _).trans
              (congrArg
                (fun m => Functor.Fiber.fiberInclusion.map (eqToHom e) ≫ m)
                (Category.assoc _ _ _))
    _ = Functor.Fiber.fiberInclusion.map (eqToHom e) ≫
        P.pullbackMap (k.left ≫ g.hom) x := by
      exact congrArg
        (fun m => Functor.Fiber.fiberInclusion.map (eqToHom e) ≫ m) hcomp
    _ = P.pullbackMap f.hom x := by
      exact pullbackMap_eq_of_eq (Over.w k).symm x

theorem twoYonedaPullbackFunctorMap_map_id
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) (f : Over U) :
    twoYonedaPullbackFunctorMap p P U x (𝟙 f) =
      𝟙 (twoYonedaPullbackFunctorObj p P U x f) := by
  unfold twoYonedaPullbackFunctorObj
  have hmap : p.IsHomLift (𝟙 f.left)
      (twoYonedaPullbackFunctorMap p P U x (𝟙 f)) := by
    simpa using twoYonedaPullbackFunctorMap_isHomLift p P U x (𝟙 f)
  have hid : p.IsHomLift (𝟙 f.left)
      (𝟙 (Functor.Fiber.fiberInclusion.obj (P.pullback f.hom x))) :=
    IsHomLift.id (P.pullback f.hom x).2
  exact @Functor.IsStronglyCartesian.ext _ _ _ _ p
    f.left U
    (Functor.Fiber.fiberInclusion.obj (P.pullback f.hom x)) x.1
    f.hom (P.pullbackMap f.hom x)
    (P.pullbackMap_isStronglyCartesian f.hom x)
    f.left (Functor.Fiber.fiberInclusion.obj (P.pullback f.hom x))
    (𝟙 f.left)
    (twoYonedaPullbackFunctorMap p P U x (𝟙 f))
    (𝟙 (Functor.Fiber.fiberInclusion.obj (P.pullback f.hom x)))
    hmap hid
    (by
      simpa only [twoYonedaPullbackFunctorObj, Category.id_comp] using
        twoYonedaPullbackFunctorMap_fac p P U x (𝟙 f))

theorem twoYonedaPullbackFunctorMap_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) {f g h : Over U}
    (k : f ⟶ g) (l : g ⟶ h) :
    twoYonedaPullbackFunctorMap p P U x (k ≫ l) =
      twoYonedaPullbackFunctorMap p P U x k ≫
        twoYonedaPullbackFunctorMap p P U x l := by
  sorry

def twoYonedaPullbackFunctor
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) : Over U ⥤ S where
  obj f := twoYonedaPullbackFunctorObj p P U x f
  map k := twoYonedaPullbackFunctorMap p P U x k
  map_id := by
    intro f
    exact twoYonedaPullbackFunctorMap_map_id p P U x f
  map_comp := by
    intro f g h k l
    exact twoYonedaPullbackFunctorMap_map_comp p P U x k l

theorem twoYonedaPullbackFunctor_isOver
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) :
    twoYonedaPullbackFunctor p P U x ⋙ p = Over.forget U := by
  sorry

theorem twoYonedaPullbackFunctor_mapsStronglyCartesian
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) :
    MapsStronglyCartesian (Over.forget U) p
      (twoYonedaPullbackFunctor p P U x) := by
  sorry

def twoYonedaPullbackMorphism
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) : twoYonedaFibredMorphismCategory p U :=
  ⟨⟨twoYonedaPullbackFunctor p P U x,
      twoYonedaPullbackFunctor_isOver p P U x⟩,
    twoYonedaPullbackFunctor_mapsStronglyCartesian p P U x⟩

def twoYonedaPullbackNatTransApp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    {x y : Functor.Fiber p U} (η : x ⟶ y) (f : Over U) :
    twoYonedaPullbackFunctorObj p P U x f ⟶
      twoYonedaPullbackFunctorObj p P U y f :=
  (Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
    ((P.pullbackFunctor f.hom).map η)

theorem twoYonedaPullbackNatTransApp_naturality
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    {x y : Functor.Fiber p U} (η : x ⟶ y)
    {f g : Over U} (k : f ⟶ g) :
    twoYonedaPullbackFunctorMap p P U x k ≫
        twoYonedaPullbackNatTransApp p P U η g =
      twoYonedaPullbackNatTransApp p P U η f ≫
        twoYonedaPullbackFunctorMap p P U y k := by
  sorry

def twoYonedaPullbackNatTrans
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    {x y : Functor.Fiber p U} (η : x ⟶ y) :
    twoYonedaPullbackFunctor p P U x ⟶
    twoYonedaPullbackFunctor p P U y where
  app f := twoYonedaPullbackNatTransApp p P U η f
  naturality := by
    intro f g k
    exact twoYonedaPullbackNatTransApp_naturality p P U η k

theorem twoYonedaPullbackNatTrans_isOver
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    {x y : Functor.Fiber p U} (η : x ⟶ y) :
    (twoYonedaPostcomposition p U).IsHomLift (𝟙 (Over.forget U))
      (twoYonedaPullbackNatTrans p P U η) := by
  sorry

def twoYonedaPullbackMorphismMap
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    {x y : Functor.Fiber p U} (η : x ⟶ y) :
    twoYonedaPullbackMorphism p P U x ⟶
      twoYonedaPullbackMorphism p P U y :=
  ObjectProperty.homMk
    ⟨twoYonedaPullbackNatTrans p P U η,
      twoYonedaPullbackNatTrans_isOver p P U η⟩

theorem twoYonedaPullbackMorphismMap_map_id
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) :
    twoYonedaPullbackMorphismMap p P U (𝟙 x) =
      𝟙 (twoYonedaPullbackMorphism p P U x) := by
  sorry

theorem twoYonedaPullbackMorphismMap_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    {x y z : Functor.Fiber p U} (η : x ⟶ y) (θ : y ⟶ z) :
    twoYonedaPullbackMorphismMap p P U (η ≫ θ) =
      twoYonedaPullbackMorphismMap p P U η ≫
        twoYonedaPullbackMorphismMap p P U θ := by
  sorry

/- The functor below is the inverse constructed in the source after choosing
   pullbacks.  Its functoriality is exactly the omitted verification in the
   textbook proof. -/
def twoYonedaPullback
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C) :
    Functor.Fiber p U ⥤ twoYonedaFibredMorphismCategory p U where
  obj x := twoYonedaPullbackMorphism p P U x
  map η := twoYonedaPullbackMorphismMap p P U η
  map_id := by
    intro x
    exact twoYonedaPullbackMorphismMap_map_id p P U x
  map_comp := by
    intro x y z η θ
    exact twoYonedaPullbackMorphismMap_map_comp p P U η θ

/-! ## Evaluation at the identity -/

/- The following two interfaces isolate the only non-definitional parts of
   evaluation.  They are the pointwise form of the equality witnessing that
   a functor is over `C`; the proof of the 2-Yoneda lemma is allowed to supply
   these proposition-valued facts later. -/
theorem twoYonedaEvaluationCore_obj_isFiber
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) (G : twoYonedaOverCategory p U) :
    p.obj (G.1.obj (Over.mk (𝟙 U))) = U := by
  exact Functor.congr_obj G.2 (Over.mk (𝟙 U))

private theorem twoYonedaMorphismCategory_map_isHomLift
    {A : Type uS} [Category.{vS} A]
    {B : Type uT} [Category.{vT} B]
    {C : Type uC} [Category.{vC} C]
    (p : A ⥤ C) (q : B ⥤ C)
    {G H : twoYonedaMorphismCategory p q} (η : G ⟶ H) (X : A) :
    q.IsHomLift (𝟙 (p.obj X)) (η.1.app X) := by
  have hG : q.obj (G.1.obj X) = p.obj X :=
    congrArg (fun F : A ⥤ C => F.obj X) G.2
  have hH : q.obj (H.1.obj X) = p.obj X :=
    congrArg (fun F : A ⥤ C => F.obj X) H.2
  apply IsHomLift.of_fac' q (𝟙 (p.obj X)) (η.1.app X) hG hH
  let : (twoYonedaPostcompositionGeneral q).IsHomLift (𝟙 p) η.1 := η.2
  have hfac := IsHomLift.fac' (twoYonedaPostcompositionGeneral q)
    (𝟙 p) η.1
  have hfacX := congrArg (fun t => t.app X) hfac
  simpa [twoYonedaPostcompositionGeneral, Formalization.Books.Categories.Unit28.postcompositionFunctor]
    using hfacX

theorem twoYonedaEvaluationCore_map_isHomLift
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C)
    {G H : twoYonedaOverCategory p U} (η : G ⟶ H) :
    p.IsHomLift (𝟙 U) (η.1.app (Over.mk (𝟙 U))) := by
  simpa using twoYonedaMorphismCategory_map_isHomLift
    (Over.forget U) p η (Over.mk (𝟙 U))

def twoYonedaEvaluationCoreObj
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) (G : twoYonedaOverCategory p U) :
    Functor.Fiber p U :=
  ⟨G.1.obj (Over.mk (𝟙 U)), twoYonedaEvaluationCore_obj_isFiber p U G⟩

def twoYonedaEvaluationCoreMap
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C)
    {G H : twoYonedaOverCategory p U} (η : G ⟶ H) :
    twoYonedaEvaluationCoreObj p U G ⟶ twoYonedaEvaluationCoreObj p U H :=
  ⟨η.1.app (Over.mk (𝟙 U)), twoYonedaEvaluationCore_map_isHomLift p U η⟩

/- Evaluation is first defined on all strict functors over the base.  The
   preservation condition is then imposed by restricting the source to the
   full subcategory above. -/
def twoYonedaEvaluationCore
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :
    twoYonedaOverCategory p U ⥤ Functor.Fiber p U where
  obj G := twoYonedaEvaluationCoreObj p U G
  map η := twoYonedaEvaluationCoreMap p U η
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

/-- The source's first 2-Yoneda lemma: evaluation at `id_U` is an
equivalence from fibred functors `Over U ⥤ S` over `C` to the fibre of `p`
over `U`. -/
theorem twoYoneda_fibred_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (U : C) :
    (twoYonedaEvaluation p U).IsEquivalence := by
  sorry

/- The source's `Cat / C` morphism categories are groupoids when the target
   projection is fibred in groupoids.  This is the general form of the
   assertion used by the second 2-Yoneda lemma below; the source projection
   need not be fibred in groupoids (and `Over.forget U` is not so in general).
   A natural transformation over `C` is pointwise vertical, hence pointwise
   invertible in the target fibres. -/
theorem twoYonedaMorphismCategory_isGroupoid
    {A : Type uS} [Category.{vS} A]
    {B : Type uT} [Category.{vT} B]
    {C : Type uC} [Category.{vC} C]
    (p : A ⥤ C) (q : B ⥤ C)
    (hq : q.IsFibredInGroupoids) :
    IsGroupoid (twoYonedaMorphismCategory p q) := by
  sorry

/-! ## The groupoid case -/

/- In the full 2-subcategory of categories fibred in groupoids, every strict
   functor over `C/U` is a 1-morphism. -/
abbrev twoYonedaGroupoidMorphismCategory
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :=
  twoYonedaOverCategory p U

/- Every arrow in a category fibred in groupoids is strongly Cartesian.  Thus
   in the groupoid case the preservation condition defining the fibred
   morphism category is automatic, as asserted by the source's full
   sub-2-category discussion. -/
theorem twoYonedaGroupoidMorphism_preservesCartesian
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C)
    (G : twoYonedaGroupoidMorphismCategory p U) :
    MapsStronglyCartesian (Over.forget U) p G.1 := by
  intro _ _ φ _
  exact fibredInGroupoids_all_morphisms_stronglyCartesian p
    (inferInstance : p.IsFibredInGroupoids) (G.1.map φ)

/- The pullback functor constructed above lands in the full subcategory of
   fibred morphisms.  In the groupoid case, inclusion of that full
   subcategory gives the source's functor into the whole morphism category. -/
def twoYonedaGroupoidPullback
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (P : PullbackChoice p) (U : C) :
    Functor.Fiber p U ⥤ twoYonedaGroupoidMorphismCategory p U :=
  twoYonedaPullback p P U ⋙ (twoYonedaPreservesCartesian p U).ι

/-- The morphism category in the groupoid version is a groupoid. -/
theorem twoYonedaGroupoidMorphismCategory_isGroupoid
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    IsGroupoid (twoYonedaGroupoidMorphismCategory p U) := by
  exact twoYonedaMorphismCategory_isGroupoid
    (Over.forget U) p (inferInstance : p.IsFibredInGroupoids)

/-- The source's second 2-Yoneda lemma for categories fibred in groupoids.
Evaluation at `id_U` is an equivalence from `Cat/C` morphisms to the fibre. -/
theorem twoYoneda_groupoid_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    (twoYonedaEvaluationCore p U).IsEquivalence := by
  sorry

/-! ## The alternative presheaf construction -/

/- These proposition-valued interfaces express that precomposition with the
   canonical map of over-categories remains a strict functor over `C`. -/
theorem twoYonedaGroupoidRestriction_obj_isOver
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {U V : C} (f : U ⟶ V)
    (G : twoYonedaGroupoidMorphismCategory p V) :
    (Over.map f ⋙ G.1) ⋙ p = Over.forget U := by
  have hG : G.1 ⋙ p = Over.forget V := G.2
  rw [Functor.assoc, hG]
  rfl

theorem twoYonedaGroupoidRestriction_map_isOver
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {U V : C} (f : U ⟶ V)
    {G H : twoYonedaGroupoidMorphismCategory p V} (η : G ⟶ H) :
    (twoYonedaPostcomposition p U).IsHomLift (𝟙 (Over.forget U))
      (Functor.whiskerLeft (Over.map f) η.1) := by
  apply IsHomLift.of_fac'
    (twoYonedaPostcomposition p U)
    (𝟙 (Over.forget U))
    (Functor.whiskerLeft (Over.map f) η.1)
    (twoYonedaGroupoidRestriction_obj_isOver p f G)
    (twoYonedaGroupoidRestriction_obj_isOver p f H)
  ext X
  change p.map (η.1.app ((Over.map f).obj X)) = _
  let : (twoYonedaPostcomposition p V).IsHomLift
      (𝟙 (Over.forget V)) η.1 := η.2
  have hfac := IsHomLift.fac' (twoYonedaPostcomposition p V)
    (𝟙 (Over.forget V)) η.1
  have hfacX := congrArg (fun t => t.app ((Over.map f).obj X)) hfac
  simpa [twoYonedaPostcomposition, Formalization.Books.Categories.Unit28.postcompositionFunctor]
    using hfacX

def twoYonedaGroupoidRestrictionObj
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {U V : C} (f : U ⟶ V)
    (G : twoYonedaGroupoidMorphismCategory p V) :
    twoYonedaGroupoidMorphismCategory p U :=
  ⟨Over.map f ⋙ G.1, twoYonedaGroupoidRestriction_obj_isOver p f G⟩

def twoYonedaGroupoidRestrictionMap
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {U V : C} (f : U ⟶ V)
    {G H : twoYonedaGroupoidMorphismCategory p V} (η : G ⟶ H) :
    twoYonedaGroupoidRestrictionObj p f G ⟶
      twoYonedaGroupoidRestrictionObj p f H :=
  ⟨Functor.whiskerLeft (Over.map f) η.1,
    twoYonedaGroupoidRestriction_map_isOver p f η⟩

theorem twoYonedaGroupoidRestrictionMap_map_id
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {U V : C} (f : U ⟶ V)
    (G : twoYonedaGroupoidMorphismCategory p V) :
    twoYonedaGroupoidRestrictionMap p f (𝟙 G) =
      𝟙 (twoYonedaGroupoidRestrictionObj p f G) := by
  apply Functor.Fiber.hom_ext
  rfl

theorem twoYonedaGroupoidRestrictionMap_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {U V : C} (f : U ⟶ V)
    {G H K : twoYonedaGroupoidMorphismCategory p V}
    (η : G ⟶ H) (θ : H ⟶ K) :
    twoYonedaGroupoidRestrictionMap p f (η ≫ θ) =
      twoYonedaGroupoidRestrictionMap p f η ≫
        twoYonedaGroupoidRestrictionMap p f θ := by
  apply Functor.Fiber.hom_ext
  exact Functor.whiskerLeft_comp (Over.map f) η.1 θ.1

/- For `f : U ⟶ V`, precomposition with `Over.map f` gives the restriction
   from the morphism category over `V` to the one over `U`. -/
def twoYonedaGroupoidRestriction
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {U V : C} (f : U ⟶ V) :
    twoYonedaGroupoidMorphismCategory p V ⥤
      twoYonedaGroupoidMorphismCategory p U where
  obj G := twoYonedaGroupoidRestrictionObj p f G
  map η := twoYonedaGroupoidRestrictionMap p f η
  map_id := by
    intro G
    exact twoYonedaGroupoidRestrictionMap_map_id p f G
  map_comp := by
    intro G H K η θ
    exact twoYonedaGroupoidRestrictionMap_map_comp p f η θ

theorem twoYonedaHomPresheaf_map_id
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) (U : C) :
    (twoYonedaGroupoidRestriction p (𝟙 U)).toCatHom =
      𝟙 (Cat.of (twoYonedaGroupoidMorphismCategory p U)) := by
  sorry

theorem twoYonedaHomPresheaf_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (twoYonedaGroupoidRestriction p (f ≫ g).unop).toCatHom =
      (twoYonedaGroupoidRestriction p f.unop).toCatHom ≫
        (twoYonedaGroupoidRestriction p g.unop).toCatHom := by
  sorry

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
    intro U
    exact twoYonedaHomPresheaf_map_id p U.unop
  map_comp := by
    intro X Y Z f g
    exact twoYonedaHomPresheaf_map_comp p f g

theorem twoYonedaHomPresheaf_obj_isGroupoid
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    IsGroupoid ((twoYonedaHomPresheaf p).obj (Opposite.op U)) := by
  change IsGroupoid (twoYonedaGroupoidMorphismCategory p U)
  exact twoYonedaGroupoidMorphismCategory_isGroupoid p U

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
  exact groupoidPresheafProjection_isFibredInGroupoids
    (twoYonedaHomPresheaf p) (twoYonedaHomPresheaf_obj_isGroupoid p)

/- The functor `G` of the source evaluates the fiber component at the
   identity object and then uses the arrow in the slice to reach the target
   identity. -/
def twoYonedaAssociatedFunctorObj
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    twoYonedaAssociatedCategory p → S :=
  fun X =>
    Functor.Fiber.fiberInclusion.obj
      ((twoYonedaEvaluationCore p X.base).obj X.fiber)

def twoYonedaAssociatedFunctorMap
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {X Y : twoYonedaAssociatedCategory p} (f : X ⟶ Y) :
    twoYonedaAssociatedFunctorObj p X ⟶ twoYonedaAssociatedFunctorObj p Y :=
    ((Functor.Fiber.fiberInclusion.map
        ((twoYonedaEvaluationCore p X.base).map f.fiber)) ≫
        (show twoYonedaGroupoidMorphismCategory p Y.base from Y.fiber).1.map
        (Over.homMk (X := Y.base)
          (U := (Over.map f.base).obj (Over.mk (𝟙 X.base)))
          (V := Over.mk (𝟙 Y.base)) f.base (by simp)))

theorem twoYonedaAssociatedFunctorMap_map_id
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    (X : twoYonedaAssociatedCategory p) :
    twoYonedaAssociatedFunctorMap p (𝟙 X) =
      𝟙 (twoYonedaAssociatedFunctorObj p X) := by
  sorry

theorem twoYonedaAssociatedFunctorMap_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {X Y Z : twoYonedaAssociatedCategory p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    twoYonedaAssociatedFunctorMap p (f ≫ g) =
      twoYonedaAssociatedFunctorMap p f ≫
        twoYonedaAssociatedFunctorMap p g := by
  sorry

def twoYonedaAssociatedFunctor
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    twoYonedaAssociatedCategory p ⥤ S where
  obj X := twoYonedaAssociatedFunctorObj p X
  map f := twoYonedaAssociatedFunctorMap p f
  map_id := by
    intro X
    exact twoYonedaAssociatedFunctorMap_map_id p X
  map_comp := by
    intro X Y Z f g
    exact twoYonedaAssociatedFunctorMap_map_comp p f g

private theorem twoYonedaAssociatedFunctorMap_isHomLift
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {X Y : twoYonedaAssociatedCategory p} (f : X ⟶ Y) :
    p.IsHomLift f.base (twoYonedaAssociatedFunctorMap p f) := by
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
   chosen value of the presheaf.  In the CoGrothendieck construction this is
   the `HasFibers.Fib` category, namely the value of the presheaf itself. -/
def twoYonedaAssociatedFiberFunctor
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    twoYonedaGroupoidMorphismCategory p U ⥤ Functor.Fiber p U :=
  twoYonedaEvaluationCore p U

/-- The fiberwise functor in the alternative proof is an equivalence. -/
theorem twoYonedaAssociatedFiberFunctor_isEquivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] (U : C) :
    (twoYonedaAssociatedFiberFunctor p U).IsEquivalence := by
  exact twoYoneda_groupoid_equivalence p U

/-- The final equivalence in the alternative proof. -/
theorem twoYonedaAssociatedFunctor_isEquivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    (twoYonedaAssociatedFunctor p).IsEquivalence := by
  sorry

/- The source's final appeal to the equivalence lemma is an equivalence in
   the 2-category of categories fibred in groupoids, not only an equivalence
   of the underlying categories. -/
theorem twoYonedaAssociatedFunctor_isFibredEquivalenceOver
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    IsFibredEquivalenceOver p (twoYonedaAssociatedProjection p) := by
  sorry

end

end Formalization.Books.Categories.Unit41
