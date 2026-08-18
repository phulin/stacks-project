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
  dsimp [twoYonedaPullbackFunctorMap]
  letI : p.IsHomLift (𝟙 f.left)
      ((Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
        (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm))) := by
    infer_instance
  letI : p.IsHomLift (𝟙 f.left)
      ((Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
        ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x)) := by
    infer_instance
  letI : p.IsHomLift k.left (P.pullbackMap k.left (P.pullback g.hom x)) :=
    (P.pullbackMap_isStronglyCartesian k.left (P.pullback g.hom x)).toIsHomLift
  infer_instance

private theorem twoYonedaPullbackFunctorMap_fac
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) {f g : Over U} (k : f ⟶ g) :
    twoYonedaPullbackFunctorMap p P U x k ≫ P.pullbackMap g.hom x =
      P.pullbackMap f.hom x := by
  have htransport :
      (Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
          (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm)) ≫
        P.pullbackMap (k.left ≫ g.hom) x = P.pullbackMap f.hom x := by
    rw [← Over.w k]
    have h :
        congrArg (fun h => P.pullback h x) (Over.w k).symm =
          (rfl : P.pullback (k.left ≫ g.hom) x =
            P.pullback (k.left ≫ g.hom) x) := by
      apply Subsingleton.elim
    rw [h]
    simp
  calc
    twoYonedaPullbackFunctorMap p P U x k ≫ P.pullbackMap g.hom x =
        (Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
            (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm)) ≫
          (((Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
              ((twoYonedaPullbackCompositionIso p P k.left g.hom).hom.app x)) ≫
            P.pullbackMap k.left (P.pullback g.hom x) ≫
            P.pullbackMap g.hom x) := by
              simp [twoYonedaPullbackFunctorMap, Category.assoc]
    _ = (Functor.Fiber.fiberInclusion : Functor.Fiber p f.left ⥤ S).map
          (eqToHom (congrArg (fun h => P.pullback h x) (Over.w k).symm)) ≫
        P.pullbackMap (k.left ≫ g.hom) x := by
          rw [twoYonedaPullbackCompositionIso_hom_app p P k.left g.hom x]
    _ = P.pullbackMap f.hom x := htransport

theorem twoYonedaPullbackFunctorMap_map_id
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) (f : Over U) :
    twoYonedaPullbackFunctorMap p P U x (𝟙 f) =
      𝟙 (twoYonedaPullbackFunctorObj p P U x f) := by
  let m := twoYonedaPullbackFunctorMap p P U x (𝟙 f)
  letI : p.IsHomLift (𝟙 f.left) m := by
    dsimp [m]
    exact twoYonedaPullbackFunctorMap_isHomLift p P U x (𝟙 f)
  letI : p.IsHomLift (𝟙 f.left)
      (𝟙 (twoYonedaPullbackFunctorObj p P U x f)) := by
    exact IsHomLift.id (P.pullback f.hom x).2
  apply Functor.IsStronglyCartesian.ext p (P.pullbackMap f.hom x)
    (𝟙 f.left) m (𝟙 (twoYonedaPullbackFunctorObj p P U x f))
  · exact twoYonedaPullbackFunctorMap_fac p P U x (𝟙 f)
  · simp
  · exact P.pullbackMap_isStronglyCartesian f.hom x

theorem twoYonedaPullbackFunctorMap_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) {f g h : Over U}
    (k : f ⟶ g) (l : g ⟶ h) :
    twoYonedaPullbackFunctorMap p P U x (k ≫ l) =
      twoYonedaPullbackFunctorMap p P U x k ≫
        twoYonedaPullbackFunctorMap p P U x l := by
  let mk := twoYonedaPullbackFunctorMap p P U x k
  let ml := twoYonedaPullbackFunctorMap p P U x l
  let mcomp := twoYonedaPullbackFunctorMap p P U x (k ≫ l)
  letI : p.IsHomLift k.left mk := by
    dsimp [mk]
    exact twoYonedaPullbackFunctorMap_isHomLift p P U x k
  letI : p.IsHomLift l.left ml := by
    dsimp [ml]
    exact twoYonedaPullbackFunctorMap_isHomLift p P U x l
  letI : p.IsHomLift (k.left ≫ l.left) (mk ≫ ml) := by
    infer_instance
  letI : p.IsHomLift (k ≫ l).left mcomp := by
    dsimp [mcomp]
    exact twoYonedaPullbackFunctorMap_isHomLift p P U x (k ≫ l)
  apply Functor.IsStronglyCartesian.ext p (P.pullbackMap h.hom x)
    (k ≫ l).left mcomp (mk ≫ ml)
  · exact twoYonedaPullbackFunctorMap_fac p P U x (k ≫ l)
  · calc
      (mk ≫ ml) ≫ P.pullbackMap h.hom x =
          mk ≫ (ml ≫ P.pullbackMap h.hom x) := by simp [Category.assoc]
      _ = mk ≫ P.pullbackMap g.hom x := by
        rw [twoYonedaPullbackFunctorMap_fac p P U x l]
      _ = P.pullbackMap f.hom x :=
        twoYonedaPullbackFunctorMap_fac p P U x k
  · exact P.pullbackMap_isStronglyCartesian h.hom x

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
  refine Functor.ext (fun f => ?_) (fun f g k => ?_)
  · exact (P.pullback f.hom x).2
  · letI : p.IsHomLift k.left
        (twoYonedaPullbackFunctorMap p P U x k) :=
      twoYonedaPullbackFunctorMap_isHomLift p P U x k
    change p.map (twoYonedaPullbackFunctorMap p P U x k) =
      eqToHom (P.pullback f.hom x).2 ≫ k.left ≫
        eqToHom (P.pullback g.hom x).2.symm
    simpa using
      (IsHomLift.fac' p k.left (twoYonedaPullbackFunctorMap p P U x k))

theorem twoYonedaPullbackFunctor_mapsStronglyCartesian
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    (x : Functor.Fiber p U) :
    MapsStronglyCartesian (Over.forget U) p
      (twoYonedaPullbackFunctor p P U x) := by
  intro f g k _
  let m := twoYonedaPullbackFunctorMap p P U x k
  letI : p.IsHomLift k.left m := by
    dsimp [m]
    exact twoYonedaPullbackFunctorMap_isHomLift p P U x k
  have hfac : m ≫ P.pullbackMap g.hom x =
      P.pullbackMap f.hom x := by
    exact twoYonedaPullbackFunctorMap_fac p P U x k
  have hcomp : p.IsStronglyCartesian (k.left ≫ g.hom)
      (m ≫ P.pullbackMap g.hom x) := by
    rw [hfac, ← Over.w k]
    exact P.pullbackMap_isStronglyCartesian f.hom x
  letI : p.IsStronglyCartesian (k.left ≫ g.hom)
      (m ≫ P.pullbackMap g.hom x) := hcomp
  exact @Functor.IsStronglyCartesian.of_comp _ _ _ _ p _ _ _ _ _ _ k.left g.hom m
    (P.pullbackMap g.hom x)
    (P.pullbackMap_isStronglyCartesian g.hom x) hcomp (by infer_instance)

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
  have pullbackMap_fac {A B : C} (h : A ⟶ B)
      {x y : Functor.Fiber p B} (φ : x ⟶ y) :
      ((P.pullbackFunctor h).map φ).1 ≫ P.pullbackMap h y =
        P.pullbackMap h x ≫ φ.1 := by
    let : p.IsHomLift (𝟙 B) φ.1 := φ.2
    let : p.IsStronglyCartesian h (P.pullbackMap h y) :=
      P.pullbackMap_isStronglyCartesian h y
    let : p.IsStronglyCartesian h (P.pullbackMap h x) :=
      P.pullbackMap_isStronglyCartesian h x
    have hφ' : p.IsHomLift h (P.pullbackMap h x ≫ φ.1) := by
      exact IsHomLift.comp_lift_id_right' p h (P.pullbackMap h x) B φ.1
    change
      (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ h
        (P.pullbackMap h y) _ _ _ (𝟙 A) h (by simp)
        (P.pullbackMap h x ≫ φ.1) hφ') ≫ P.pullbackMap h y =
        P.pullbackMap h x ≫ φ.1
    exact Functor.IsStronglyCartesian.fac p h (P.pullbackMap h y)
      (f' := h) (g := 𝟙 A) (by simp) (P.pullbackMap h x ≫ φ.1)
  let mx := twoYonedaPullbackFunctorMap p P U x k
  let my := twoYonedaPullbackFunctorMap p P U y k
  let af := twoYonedaPullbackNatTransApp p P U η f
  let ag := twoYonedaPullbackNatTransApp p P U η g
  have hmx : p.IsHomLift k.left mx := by
    dsimp [mx]
    exact twoYonedaPullbackFunctorMap_isHomLift p P U x k
  have hmy : p.IsHomLift k.left my := by
    dsimp [my]
    exact twoYonedaPullbackFunctorMap_isHomLift p P U y k
  have haf : p.IsHomLift (𝟙 f.left) af := by
    dsimp [af, twoYonedaPullbackNatTransApp]
    exact ((P.pullbackFunctor f.hom).map η).2
  have hag : p.IsHomLift (𝟙 g.left) ag := by
    dsimp [ag, twoYonedaPullbackNatTransApp]
    exact ((P.pullbackFunctor g.hom).map η).2
  letI : p.IsHomLift k.left mx := hmx
  letI : p.IsHomLift k.left my := hmy
  letI : p.IsHomLift (𝟙 f.left) af := haf
  letI : p.IsHomLift (𝟙 g.left) ag := hag
  change mx ≫ ag = af ≫ my
  apply Functor.IsStronglyCartesian.ext p (P.pullbackMap g.hom y)
    k.left (mx ≫ ag) (af ≫ my)
  calc
    (mx ≫ ag) ≫ P.pullbackMap g.hom y =
        mx ≫ (ag ≫ P.pullbackMap g.hom y) := by simp [Category.assoc]
    _ = mx ≫ (P.pullbackMap g.hom x ≫ η.1) := by
      rw [pullbackMap_fac g.hom η]
    _ = P.pullbackMap f.hom x ≫ η.1 := by
      rw [twoYonedaPullbackFunctorMap_fac p P U x k]
    _ = af ≫ P.pullbackMap f.hom y :=
      (pullbackMap_fac f.hom η).symm
    _ = af ≫ (my ≫ P.pullbackMap g.hom y) := by
      rw [twoYonedaPullbackFunctorMap_fac p P U y k]
    _ = (af ≫ my) ≫ P.pullbackMap g.hom y := by simp [Category.assoc]

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
  apply IsHomLift.of_fac'
    (twoYonedaPostcomposition p U)
    (𝟙 (Over.forget U)) (twoYonedaPullbackNatTrans p P U η)
    (twoYonedaPullbackFunctor_isOver p P U x)
    (twoYonedaPullbackFunctor_isOver p P U y)
  ext f
  change p.map (twoYonedaPullbackNatTransApp p P U η f) = _
  letI : p.IsHomLift (𝟙 f.left)
      (twoYonedaPullbackNatTransApp p P U η f) := by
    dsimp [twoYonedaPullbackNatTransApp]
    exact ((P.pullbackFunctor f.hom).map η).2
  simpa using
    (IsHomLift.fac' p (𝟙 f.left)
      (twoYonedaPullbackNatTransApp p P U η f))

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
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  intro f
  dsimp [twoYonedaPullbackMorphismMap, twoYonedaPullbackNatTrans,
    twoYonedaPullbackNatTransApp]
  simp

theorem twoYonedaPullbackMorphismMap_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C)
    {x y z : Functor.Fiber p U} (η : x ⟶ y) (θ : y ⟶ z) :
    twoYonedaPullbackMorphismMap p P U (η ≫ θ) =
      twoYonedaPullbackMorphismMap p P U η ≫
        twoYonedaPullbackMorphismMap p P U θ := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  intro f
  dsimp [twoYonedaPullbackMorphismMap, twoYonedaPullbackNatTrans,
    twoYonedaPullbackNatTransApp]
  simp

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
  letI : (twoYonedaPostcompositionGeneral q).IsHomLift (𝟙 p) η.1 := η.2
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
  let hgroup : ∀ V : C, IsGroupoid (Functor.Fiber q V) :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.1
  constructor
  intro G H η
  have hηiso : IsIso η.1 := by
    apply NatTrans.isIso_of_isIso_app
    intro X
    let hηX := twoYonedaMorphismCategory_map_isHomLift p q η X
    letI : q.IsHomLift (𝟙 (p.obj X)) (η.1.app X) := hηX
    let k := Functor.Fiber.homMk q (p.obj X) (η.1.app X)
    letI : IsIso k := (hgroup (p.obj X)).all_isIso k
    change IsIso (Functor.Fiber.fiberInclusion.map k)
    exact (Functor.Fiber.fiberInclusion.mapIso (asIso k)).isIso_hom
  letI : IsIso η.1 := hηiso
  letI : (twoYonedaPostcompositionGeneral q).IsHomLift (𝟙 p) (inv η.1) :=
    IsHomLift.lift_id_inv_isIso (twoYonedaPostcompositionGeneral q) p η.1
  let ηinv : H ⟶ G := ⟨inv η.1, inferInstance⟩
  refine ⟨ηinv, ?_, ?_⟩
  · apply Functor.Fiber.hom_ext
    change η.1 ≫ inv η.1 = 𝟙 _
    simp
  · apply Functor.Fiber.hom_ext
    change inv η.1 ≫ η.1 = 𝟙 _
    simp

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
  let hP : ∀ G : twoYonedaOverCategory p U,
      twoYonedaPreservesCartesian p U G := by
    intro G
    exact twoYonedaGroupoidMorphism_preservesCartesian p U G
  letI : (twoYonedaPreservesCartesian p U).ι.EssSurj := by
    constructor
    intro G
    refine ⟨⟨G, hP G⟩, ?_⟩
    exact ⟨Iso.refl G⟩
  letI : (twoYonedaPreservesCartesian p U).ι.IsEquivalence := {}
  letI : (twoYonedaEvaluation p U).IsEquivalence :=
    twoYoneda_fibred_equivalence p U
  exact Functor.isEquivalence_of_comp_left
    (twoYonedaPreservesCartesian p U).ι
    (twoYonedaEvaluationCore p U)

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
  letI : (twoYonedaPostcomposition p V).IsHomLift
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
  apply Cat.ext
  apply Functor.ext
  · intro G
    apply Subtype.ext
    dsimp [twoYonedaGroupoidRestriction, twoYonedaGroupoidRestrictionObj]
    simpa only [Over.mapId_eq, Functor.id_comp]
  · intro G H η
    apply Functor.Fiber.hom_ext
    change Functor.whiskerLeft (Over.map (𝟙 U)) η.1 = η.1
    simpa only [Over.mapId_eq] using
      (Formalization.Books.Categories.Unit28.prewhisker_identity_functor η.1)

theorem twoYonedaHomPresheaf_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (twoYonedaGroupoidRestriction p (f ≫ g).unop).toCatHom =
      (twoYonedaGroupoidRestriction p f.unop).toCatHom ≫
        (twoYonedaGroupoidRestriction p g.unop).toCatHom := by
  apply Cat.ext
  apply Functor.ext
  · intro G
    apply Subtype.ext
    dsimp [twoYonedaGroupoidRestriction, twoYonedaGroupoidRestrictionObj]
    simp [unop_comp, Over.mapComp_eq, Functor.assoc]
  · intro G H η
    apply Functor.Fiber.hom_ext
    change Functor.whiskerLeft (Over.map (f ≫ g).unop) η.1 =
      Functor.whiskerLeft (Over.map g.unop)
        (Functor.whiskerLeft (Over.map f.unop) η.1)
    rw [unop_comp, Over.mapComp_eq]
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
  apply Functor.Fiber.hom_ext
  dsimp [twoYonedaAssociatedFunctorMap, twoYonedaAssociatedFunctorObj]
  simp

theorem twoYonedaAssociatedFunctorMap_map_comp
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {X Y Z : twoYonedaAssociatedCategory p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    twoYonedaAssociatedFunctorMap p (f ≫ g) =
      twoYonedaAssociatedFunctorMap p f ≫
        twoYonedaAssociatedFunctorMap p g := by
  apply Functor.Fiber.hom_ext
  dsimp [twoYonedaAssociatedFunctorMap]
  simp [groupoidPresheaf_comp_fiber, Category.assoc]

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
  let U := (Over.map f.base).obj (Over.mk (𝟙 X.base))
  let V := Over.mk (𝟙 Y.base)
  let GY : twoYonedaGroupoidMorphismCategory p Y.base :=
    show twoYonedaGroupoidMorphismCategory p Y.base from Y.fiber
  let k : U ⟶ V := Over.homMk f.base (by simp [U, V])
  have hk : p.IsHomLift f.base (GY.1.map k) := by
    apply IsHomLift.of_fac' p f.base (GY.1.map k)
      (by simpa [U, GY] using Functor.congr_obj GY.2 U)
      (by simpa [V, GY] using Functor.congr_obj GY.2 V)
    simpa [U, V, k, GY] using Functor.congr_hom GY.2 k
  letI : p.IsHomLift f.base (GY.1.map k) := hk
  letI : p.IsHomLift (𝟙 X.base)
      (Functor.Fiber.fiberInclusion.map
        ((twoYonedaEvaluationCore p X.base).map f.fiber)) := inferInstance
  simpa [twoYonedaAssociatedFunctorMap, U, V, k] using
    (inferInstance : p.IsHomLift
      (𝟙 X.base ≫ f.base)
      (Functor.Fiber.fiberInclusion.map
        ((twoYonedaEvaluationCore p X.base).map f.fiber) ≫
        GY.1.map k))

/-- The associated evaluation functor is over the base. -/
theorem twoYonedaAssociatedFunctor_over
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    twoYonedaAssociatedFunctor p ⋙ p =
      twoYonedaAssociatedProjection p := by
  refine Functor.ext (fun X => ?_) (fun X Y f => ?_)
  · change p.obj (((twoYonedaEvaluationCore p X.base).obj X.fiber).1) = X.base
    exact ((twoYonedaEvaluationCore p X.base).obj X.fiber).2
  · letI : p.IsHomLift f.base (twoYonedaAssociatedFunctorMap p f) := by
      exact twoYonedaAssociatedFunctorMap_isHomLift p f
    change p.map (twoYonedaAssociatedFunctorMap p f) = _
    simpa using IsHomLift.fac' p f.base (twoYonedaAssociatedFunctorMap p f)

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
  letI : (twoYonedaAssociatedProjection p).IsFibredInGroupoids :=
    twoYonedaAssociatedProjection_isFibredInGroupoids p
  let over := twoYonedaAssociatedFunctor_over p
  apply (fibredInGroupoids_equivalence_iff_fibrewise
    (twoYonedaAssociatedProjection p) p (twoYonedaAssociatedFunctor p)
    over (inferInstance : (twoYonedaAssociatedProjection p).IsFibredInGroupoids)
    (inferInstance : p.IsFibredInGroupoids)).mpr
  intro U
  let I := HasFibers.inducedFunctor (twoYonedaAssociatedProjection p) U
  let G := fibreFunctor (twoYonedaAssociatedProjection p) p
    (twoYonedaAssociatedFunctor p) over U
  letI : I.IsEquivalence := inferInstance
  have hcomp : I ⋙ G = twoYonedaAssociatedFiberFunctor p U := by
    refine Functor.ext (fun A => ?_) (fun A B η => ?_)
    · rfl
    · apply Functor.Fiber.hom_ext
      dsimp [I, G, twoYonedaAssociatedFiberFunctor, fibreFunctor,
        twoYonedaAssociatedFunctorMap]
      simp
  letI : (I ⋙ G).IsEquivalence := by
    rw [hcomp]
    exact twoYonedaAssociatedFiberFunctor_isEquivalence p U
  exact Functor.isEquivalence_of_comp_left I G

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
