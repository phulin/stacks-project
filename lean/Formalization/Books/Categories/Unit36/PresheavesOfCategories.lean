import Formalization.Books.Categories.Unit34.Inertia
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Category.Cat.AsSmall

/-!
# Categories, Chapter 36: Presheaves of categories

The source compares fibred categories with contravariant functors to `Cat`.
Mathlib's `Pseudofunctor.CoGrothendieck` is the canonical implementation of
the displayed construction, so the source-facing names below are thin bridges
to that construction.  The strictification category used in the proof of the
last lemma is also recorded explicitly.
-/

namespace Formalization.Books.Categories.Unit36

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open Opposite
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit33

universe vC uC vS uS vD uD

noncomputable section

/-! ## The presheaf-to-fibred-category construction -/

/-- Regard an ordinary functor into `Cat` as the pseudofunctor used by the
CoGrothendieck construction. -/
abbrev splitFibredPseudofunctor
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    PseudofunctorFromCategory Cᵒᵖ (Cat.{vS, uS}) :=
  ordinaryFunctorToPseudofunctor F

/-- The category `\mathcal S_F` associated to a presheaf of categories. -/
abbrev splitFibredCategory
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :=
  Pseudofunctor.CoGrothendieck (splitFibredPseudofunctor F)

/-- The projection `p_F : \mathcal S_F \to \mathcal C`. -/
abbrev splitFibredProjection
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    splitFibredCategory F ⥤ C :=
  Pseudofunctor.CoGrothendieck.forget (splitFibredPseudofunctor F)

/-- The restriction functor `f^*` attached to a base arrow
`f : V ⟶ U`. -/
abbrev splitRestriction
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C} (f : V ⟶ U) :
    F.obj (Opposite.op U) ⥤ F.obj (Opposite.op V) :=
  (F.map f.op).toFunctor

theorem splitRestriction_comp
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    splitRestriction F (g ≫ f) =
      splitRestriction F f ⋙ splitRestriction F g := by
  change (F.map (g ≫ f).op).toFunctor =
    (F.map f.op).toFunctor ⋙ (F.map g.op).toFunctor
  rw [op_comp, F.map_comp]
  rfl

/-- The source's object description is the canonical CoGrothendieck object.
Its fields are the base object `U` and the fibre object `x`. -/
abbrev splitFibredObject
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :=
  splitFibredCategory F

/-- The source's morphism description is the canonical CoGrothendieck hom.
Its fields are the base arrow and the arrow in the source fibre. -/
abbrev splitFibredHom
    {C : Type uC} [Category.{vC} C]
  (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {X Y : splitFibredCategory F} :=
  Pseudofunctor.CoGrothendieck.Hom
    (F := splitFibredPseudofunctor F) X Y

@[simp]
theorem splitFibredProjection_obj
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) (X : splitFibredCategory F) :
    (splitFibredProjection F).obj X = X.base :=
  rfl

@[simp]
theorem splitFibredProjection_map
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {X Y : splitFibredCategory F} (f : X ⟶ Y) :
    (splitFibredProjection F).map f = f.base :=
  rfl

@[simp]
theorem splitFibred_id_base
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) (X : splitFibredCategory F) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base :=
  rfl

@[simp]
theorem splitFibred_comp_base
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {X Y Z : splitFibredCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

/- The fibre component of composition is the source's rule: pull back the
   second fibre arrow along the first base arrow, compose with the first
   fibre arrow, and use the canonical comparison supplied by the ordinary
   functor's composition law. -/
theorem splitFibred_comp_fiber
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {X Y Z : splitFibredCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫
        ((splitFibredPseudofunctor F).map f.base.op.toLoc).toFunctor.map g.fiber ≫
        ((splitFibredPseudofunctor F).mapComp
            g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.fiber :=
  rfl

theorem splitFibredProjection_isFibered
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    (splitFibredProjection F).IsFibered := by
  infer_instance

/-- The canonical lift of `f : V ⟶ U` with codomain `(U, x)` is
`(f, id_{f^*x})`. -/
abbrev splitFibredCartesianDomain
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C}
    (f : V ⟶ U)
    (x : (splitFibredPseudofunctor F).obj ⟨Opposite.op U⟩) :
    splitFibredCategory F :=
  Pseudofunctor.CoGrothendieck.domainCartesianLift x f

abbrev splitFibredCartesianLift
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C}
    (f : V ⟶ U)
    (x : (splitFibredPseudofunctor F).obj ⟨Opposite.op U⟩) :
    splitFibredCartesianDomain F f x ⟶
      (⟨U, x⟩ : splitFibredCategory F) :=
  Pseudofunctor.CoGrothendieck.cartesianLift x f

theorem splitFibredCartesianLift_isHomLift
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C} (f : V ⟶ U)
    (x : (splitFibredPseudofunctor F).obj ⟨Opposite.op U⟩) :
    (splitFibredProjection F).IsHomLift f
      (splitFibredCartesianLift F f x) := by
  infer_instance

theorem splitFibredCartesianLift_isStronglyCartesian
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C} (f : V ⟶ U)
    (x : (splitFibredPseudofunctor F).obj ⟨Opposite.op U⟩) :
    Functor.IsStronglyCartesian (splitFibredProjection F) f
      (splitFibredCartesianLift F f x) := by
  exact Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := splitFibredPseudofunctor F) x f

/-! ## Split fibred categories -/

/-- Source-facing name for equivalence of categories over a fixed base.

The source's ``isomorphic over `C`'' is equivalence in the 2-category of
categories over `C`, so reuse the established Unit 34 interface with strict
triangles and vertical natural isomorphisms rather than requiring strict
inverse functors. -/
abbrev IsomorphicOverBase
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) : Prop :=
  Formalization.Books.Categories.Unit34.IsEquivalentOverBase p q

/-- The source's notion of being split, expressed as isomorphism over the
base category. -/
def IsSplitFibredCategory
    {C : Type uC} [Category.{vC} C]
  {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) : Prop :=
  p.IsFibered ∧
    ∃ F : Cᵒᵖ ⥤ Cat.{vS, uS},
      IsomorphicOverBase p (splitFibredProjection F)

private abbrev catLiftObj
    (D : Cat.{vS, uS}) :=
  (Cat.asSmallFunctor.{max vC uC}).obj D

private abbrev catLiftHom
    {D E : Cat.{vS, uS}} (f : D ⟶ E) :
    catLiftObj.{vC, uC, vS, uS} D ⟶
      catLiftObj.{vC, uC, vS, uS} E :=
  (Cat.asSmallFunctor.{max vC uC}).map f

private abbrev catLiftFunctor
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    Cᵒᵖ ⥤ Cat :=
  F ⋙ Cat.asSmallFunctor.{max vC uC}

private theorem catLiftMap_up
    {D E : Cat.{vS, uS}} (f : D ⟶ E)
    {x y : D} (h : x ⟶ y) :
    (catLiftHom.{vC, uC, vS, uS} f).toFunctor.map
        ((AsSmall.up.{vS, uS, max vC uC}).map h) =
      (AsSmall.up.{vS, uS, max vC uC}).map (f.toFunctor.map h) := by
  dsimp [catLiftHom, Cat.asSmallFunctor]
  simp [toCatHom_toFunctor, Functor.comp_map,
    AsSmall.down_map, AsSmall.up_map_down]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem catLiftMap_down
    {D E : Cat.{vS, uS}} (f : D ⟶ E)
    {x y : catLiftObj.{vC, uC, vS, uS} D} (h : x ⟶ y) :
    ((catLiftHom.{vC, uC, vS, uS} f).toFunctor.map h).down =
      f.toFunctor.map h.down := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def splitLiftFunctor
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    splitFibredCategory F ⥤
      splitFibredCategory (catLiftFunctor.{vC, uC, vS, uS} F) where
  obj X := {
    base := X.base
    fiber := AsSmall.up.obj X.fiber }
  map f := {
    base := f.base
    fiber := AsSmall.up.map f.fiber }
  map_id X := by
    ext1
    · dsimp
    · simp [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
        ← Category.assoc, ← Functor.map_comp, ← Cat.Hom₂.comp_app]
      apply ULift.ext
      simp [AsSmall.down_map, eqToHom_down, Category.comp_id]
  map_comp f g := by
    have hmap₂ :
        ((splitFibredPseudofunctor (catLiftFunctor F)).map f.base.op.toLoc).toFunctor.map
            ((AsSmall.up.{vS, uS, max vC uC}).map g.fiber) =
          (AsSmall.up.{vS, uS, max vC uC}).map
            (((splitFibredPseudofunctor F).map f.base.op.toLoc).toFunctor.map
              g.fiber) := by
      change
        (catLiftHom.{vC, uC, vS, uS} (F.map f.base.op)).toFunctor.map
              ((AsSmall.up.{vS, uS, max vC uC}).map g.fiber) =
          (AsSmall.up.{vS, uS, max vC uC}).map
            ((F.map f.base.op).toFunctor.map g.fiber)
      exact catLiftMap_up.{vC, uC, vS, uS} (F.map f.base.op) g.fiber
    ext
    · dsimp
    · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
        op_comp, Quiver.Hom.comp_toLoc,
        Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber,
        Cat.Hom.comp_toFunctor, map_comp, Category.assoc,
        eqToHom_refl, Category.comp_id]
      slice_lhs 2 4 =>
        simp [AsSmall.down_map, AsSmall.up_map_down, eqToHom_down,
          toCatHom_toFunctor, Cat.Hom.comp_toFunctor,
          ← Cat.Hom₂.comp_app]
      rw [hmap₂]
      dsimp [splitFibredPseudofunctor, CategoryTheory.Functor.toPseudofunctor',
        catLiftFunctor]
      simp [toCatHom_toFunctor, Functor.comp_map, AsSmall.down_map,
        AsSmall.up_map_down, eqToHom_down]
      simp [CategoryTheory.Functor.toPseudofunctor'_mapComp,
        CategoryTheory.Functor.map_comp, catLiftFunctor,
        AsSmall.down_map, AsSmall.up_map_down, eqToHom_down,
        toCatHom_toFunctor, Cat.Hom.comp_toFunctor, eqToHom_map,
        eqToHom_trans, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def splitDownFunctor
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    splitFibredCategory (catLiftFunctor.{vC, uC, vS, uS} F) ⥤
      splitFibredCategory F where
  obj X := {
    base := X.base
    fiber := (AsSmall.down.{vS, uS, max vC uC}).obj X.fiber }
  map f := {
    base := f.base
    fiber := (AsSmall.down.{vS, uS, max vC uC}).map f.fiber }
  map_id X := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ <;> simp
  map_comp f g := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _
    · simp only [AsSmall.down_map,
        Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber,
        Cat.Hom.comp_toFunctor, map_comp, Category.assoc,
        eqToHom_refl, Category.comp_id]
      rw [down_comp, down_comp]
      dsimp [splitFibredPseudofunctor, CategoryTheory.Functor.toPseudofunctor',
        catLiftFunctor]
      simp [toCatHom_toFunctor, Functor.comp_map, AsSmall.down_map,
        AsSmall.up_map_down, eqToHom_down]
      rw [catLiftMap_down]
    · simp

theorem splitFibredCategory_isSplit
  {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    IsSplitFibredCategory (splitFibredProjection F) := by
  constructor
  · exact splitFibredProjection_isFibered F
  · refine ⟨F, ?_⟩
    refine ⟨𝟭 _, 𝟭 _, Functor.id_comp _, Functor.id_comp _, ?_, ?_⟩
    · refine ⟨Iso.refl _, rfl, ?_⟩
      intro X
      simp
    · refine ⟨Iso.refl _, rfl, ?_⟩
      intro X
      simp

/-! ## The splitting criterion -/

/-- A choice of pullbacks is strict when the chosen pullback functor of a
composite is literally the composite of the chosen pullback functors. -/
def isStrictPullbackChoice
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered]
    (P : PullbackChoice p) : Prop :=
  ∀ {W V U : C} (g : W ⟶ V) (f : V ⟶ U),
    P.pullbackFunctor (g ≫ f) =
      P.pullbackFunctor f ⋙ P.pullbackFunctor g

theorem isSplitFibredCategory_iff_exists_strictPullbackChoice
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    IsSplitFibredCategory p ↔
      ∃ P : PullbackChoice p, P.IsUnital ∧ isStrictPullbackChoice P := by
  sorry

/-! ## The explicit strictification category -/

/-- An object of the category `\mathcal S'` in the proof of the strictification
lemma: an object `x` over `U`, together with an arrow `f : V ⟶ U`. -/
structure StrictificationObject
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  V : C
  U : C
  f : V ⟶ U
  x : Functor.Fiber p U

/-- The object map described in the proof of strictification sends `x` to
`(x, id_{p(x)})`. -/
def strictificationObjectOf
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    StrictificationObject p P where
  V := p.obj x
  U := p.obj x
  f := 𝟙 (p.obj x)
  x := ⟨x, rfl⟩

@[simp]
theorem strictificationObjectOf_V
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    (strictificationObjectOf P x).V = p.obj x :=
  rfl

@[simp]
theorem strictificationObjectOf_U
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    (strictificationObjectOf P x).U = p.obj x :=
  rfl

@[simp]
theorem strictificationObjectOf_f
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    (strictificationObjectOf P x).f = 𝟙 (p.obj x) :=
  rfl

/-- Reindexing a strictification object along `g : W ⟶ V` is the source's
object formula `(x, f) ↦ (x, f ∘ g)`. -/
def strictificationReindexObject
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W : C} (A : StrictificationObject p P) (g : W ⟶ A.V) :
    StrictificationObject p P where
  V := W
  U := A.U
  f := g ≫ A.f
  x := A.x

theorem strictificationReindexObject_comp
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W V : C} (h : W ⟶ V) (A : StrictificationObject p P)
    (g : V ⟶ A.V) :
    strictificationReindexObject
        (strictificationReindexObject A g) h =
      strictificationReindexObject A (h ≫ g) := by
  cases A
  simp [strictificationReindexObject, Category.assoc]

/-- The chosen pullback object occurring in a strictification object. -/
def strictificationPullback
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (A : StrictificationObject p P) : Functor.Fiber p A.V :=
  P.pullback A.f A.x

/-- A morphism in the strictification category is the underlying morphism
between the two chosen pullback objects.  Its map to the base is recovered
canonically from `p.map`; this is equivalent to the source's displayed pair
`(φ, g)` with `p(φ) = g`. -/
structure StrictificationHom
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    {A B : StrictificationObject p P} where
  hom : (strictificationPullback A).1 ⟶ (strictificationPullback B).1

namespace StrictificationHom

@[ext]
lemma ext
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : StrictificationObject p P}
    {f g : StrictificationHom (A := A) (B := B) P}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The base arrow of a strictification morphism. -/
def base
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : StrictificationObject p P}
    (f : StrictificationHom (A := A) (B := B) P) : A.V ⟶ B.V :=
  eqToHom (strictificationPullback A).2.symm ≫
    p.map f.hom ≫ eqToHom (strictificationPullback B).2

end StrictificationHom

abbrev StrictificationCategory
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) :=
  StrictificationObject p P

instance strictificationCategory
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    Category (StrictificationCategory p P) where
  Hom A B := StrictificationHom (A := A) (B := B) P
  id A := { hom := 𝟙 (strictificationPullback A).1 }
  comp f g := { hom := f.hom ≫ g.hom }
  id_comp f := by
    apply StrictificationHom.ext
    simp
  comp_id f := by
    apply StrictificationHom.ext
    simp
  assoc f g h := by
    apply StrictificationHom.ext
    simp [Category.assoc]

/-- The projection `p' : \mathcal S' \to \mathcal C`. -/
def strictificationProjection
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    StrictificationCategory p P ⥤ C where
  obj A := A.V
  map f := StrictificationHom.base f
  map_id := by
    intro A
    change eqToHom _ ≫ p.map (𝟙 _) ≫ eqToHom _ = _
    simp
  map_comp := by
    intro A B D f g
    change eqToHom _ ≫ p.map (f.hom ≫ g.hom) ≫ eqToHom _ =
      (eqToHom _ ≫ p.map f.hom ≫ eqToHom _) ≫
        (eqToHom _ ≫ p.map g.hom ≫ eqToHom _)
    simp [Functor.map_comp, Category.assoc]

theorem strictificationProjection_isFibered
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    (strictificationProjection P).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro B R f
  let A := strictificationReindexObject B f
  let hBStrong : p.IsStronglyCartesian B.f (P.pullbackMap B.f B.x) :=
    P.pullbackMap_isStronglyCartesian B.f B.x
  let : p.IsStronglyCartesian B.f (P.pullbackMap B.f B.x) := hBStrong
  let : p.IsStronglyCartesian (f ≫ B.f)
      (P.pullbackMap (f ≫ B.f) B.x) :=
    P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x
  let : p.IsHomLift (f ≫ B.f) (P.pullbackMap (f ≫ B.f) B.x) := by
    exact @Functor.IsStronglyCartesian.toIsHomLift _ _ _ _ p _ _ _ _
      (f ≫ B.f) (P.pullbackMap (f ≫ B.f) B.x)
      (P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x)
  let φ : (strictificationPullback A).1 ⟶ (strictificationPullback B).1 :=
    @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
      B.f (P.pullbackMap B.f B.x)
      (P.pullbackMap_isStronglyCartesian B.f B.x)
      _ _ f (f ≫ B.f) rfl
      (P.pullbackMap (f ≫ B.f) B.x)
      (P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x).toIsHomLift
  have hφlift : p.IsHomLift f φ := by
    dsimp [φ]
    exact Functor.IsStronglyCartesian.map_isHomLift p B.f
      (P.pullbackMap B.f B.x) (f' := f ≫ B.f) (g := f) rfl
      (P.pullbackMap (f ≫ B.f) B.x)
  let : p.IsHomLift f φ := hφlift
  have hφstrong : p.IsStronglyCartesian f φ := by
    have hfac : φ ≫ P.pullbackMap B.f B.x =
        P.pullbackMap (f ≫ B.f) B.x := by
      dsimp [φ]
      exact Functor.IsStronglyCartesian.fac p B.f
        (P.pullbackMap B.f B.x) (f' := f ≫ B.f) (g := f) rfl
        (P.pullbackMap (f ≫ B.f) B.x)
    have hcompStrong : p.IsStronglyCartesian (f ≫ B.f)
        (φ ≫ P.pullbackMap B.f B.x) := by
      rw [hfac]
      exact P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x
    let : p.IsStronglyCartesian (f ≫ B.f)
        (φ ≫ P.pullbackMap B.f B.x) := hcompStrong
    exact @Functor.IsStronglyCartesian.of_comp _ _ _ _ p _ _ _ _ _ _ f B.f φ
      (P.pullbackMap B.f B.x) hBStrong hcompStrong hφlift
  let κ : A ⟶ B := { hom := φ }
  have hκbase : (strictificationProjection P).map κ = f := by
    change eqToHom _ ≫ p.map φ ≫ eqToHom _ = f
    exact (CategoryTheory.IsHomLift.fac p f φ).symm
  have hκlift : (strictificationProjection P).IsHomLift f κ := by
    have h := (inferInstance :
      (strictificationProjection P).IsHomLift
        ((strictificationProjection P).map κ) κ)
    rw [hκbase] at h
    exact h
  let : (strictificationProjection P).IsHomLift f κ := hκlift
  have hκstrong : (strictificationProjection P).IsStronglyCartesian f κ := by
    let : p.IsStronglyCartesian f φ := hφstrong
    constructor
    intro X g τ hτ
    let eX := (strictificationPullback X).2
    let eA := (strictificationPullback A).2
    let eB := (strictificationPullback B).2
    have hτmap : g ≫ f = (strictificationProjection P).map τ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift
        (strictificationProjection P) (g ≫ f) τ
    have hτmap' : g ≫ f =
        eqToHom eX.symm ≫ p.map τ.hom ≫ eqToHom eB := by
      simpa [strictificationProjection, StrictificationHom.base] using hτmap
    let g₀ : p.obj ((strictificationPullback X).1) ⟶ R := eqToHom eX ≫ g
    have hτp : p.IsHomLift (g₀ ≫ f) τ.hom := by
      apply CategoryTheory.IsHomLift.of_fac p (g₀ ≫ f) τ.hom rfl eB
      dsimp [g₀]
      have hcancel : eqToHom eX ≫ eqToHom eX.symm =
          𝟙 (p.obj ((strictificationPullback X).1)) := by
        simp
      have hAssoc : (eqToHom eX ≫ g) ≫ f =
          eqToHom eX ≫ (g ≫ f) := Category.assoc _ _ _
      have hRewrite : eqToHom eX ≫ (g ≫ f) =
          eqToHom eX ≫
            (eqToHom eX.symm ≫ p.map τ.hom ≫ eqToHom eB) := by
        exact congrArg (fun k => eqToHom eX ≫ k) hτmap'
      rw [hAssoc, hRewrite]
      have hcancel' := congrArg
        (fun k => k ≫ p.map τ.hom ≫ eqToHom eB) hcancel
      convert hcancel' using 1
      rw [Category.assoc]
      rfl
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property p f φ
        g₀ (g₀ ≫ f) rfl τ.hom
    let : p.IsHomLift g₀ χ := hχ
    let χ' : X ⟶ A := { hom := χ }
    have hχfac' : g₀ = p.map χ ≫ eqToHom eA := by
      let d := CategoryTheory.IsHomLift.domain_eq p g₀ χ
      let c := CategoryTheory.IsHomLift.codomain_eq p g₀ χ
      have hfac : g₀ = eqToHom d.symm ≫ p.map χ ≫ eqToHom c := by
        exact CategoryTheory.IsHomLift.fac p g₀ χ
      rw [hfac]
      have hEq : c = eA := by
        apply Subsingleton.elim
      have hDom : eqToHom d.symm =
          𝟙 (p.obj ((strictificationPullback X).1)) := by
        have hd : d =
            (rfl : p.obj ((strictificationPullback X).1) =
              p.obj ((strictificationPullback X).1)) := by
          apply Subsingleton.elim
        exact congrArg
          (fun h : p.obj ((strictificationPullback X).1) =
              p.obj ((strictificationPullback X).1) => eqToHom h.symm) hd
      rw [hDom, hEq, Category.id_comp]
      rfl
    have hχbase : (strictificationProjection P).map χ' = g := by
      change eqToHom eX.symm ≫ p.map χ ≫ eqToHom eA = g
      change X.V ⟶ R at g
      rw [← hχfac']
      dsimp [g₀]
      have hcancel : eqToHom eX.symm ≫ eqToHom eX =
          𝟙 X.V := by simp
      calc
        eqToHom eX.symm ≫ eqToHom eX ≫ g =
            (eqToHom eX.symm ≫ eqToHom eX) ≫ g :=
          (Category.assoc _ _ _).symm
        _ = (𝟙 X.V) ≫ g := congrArg (fun k => k ≫ g) hcancel
        _ = g := by simp
    have hχ'lift : (strictificationProjection P).IsHomLift g χ' := by
      have h := (inferInstance :
        (strictificationProjection P).IsHomLift
          ((strictificationProjection P).map χ') χ')
      rw [hχbase] at h
      exact h
    let : (strictificationProjection P).IsHomLift g χ' := hχ'lift
    have hχcomp : χ' ≫ κ = τ := by
      apply StrictificationHom.ext
      exact hχfac
    refine ⟨χ', ⟨inferInstance, hχcomp⟩, ?_⟩
    intro χ'' hχ''
    have : (strictificationProjection P).IsHomLift g χ'' := hχ''.1
    have hχ''map : g = (strictificationProjection P).map χ'' := by
      exact @CategoryTheory.IsHomLift.eq_of_isHomLift C
        (StrictificationCategory p P) _ _
        (strictificationProjection P) X A g χ'' hχ''.1
    have hχ''p : p.IsHomLift g₀ χ''.hom := by
      apply CategoryTheory.IsHomLift.of_fac p g₀ χ''.hom rfl eA
      have hχ''map' : g =
          eqToHom eX.symm ≫ p.map χ''.hom ≫ eqToHom eA := by
        simpa [strictificationProjection, StrictificationHom.base] using hχ''map
      dsimp [g₀]
      rw [hχ''map']
      change p.obj ((strictificationPullback A).1) = R at eA
      have hcancel : eqToHom eX ≫ eqToHom eX.symm =
          𝟙 (p.obj ((strictificationPullback X).1)) := by
        simp
      have hcancel' := congrArg
        (fun k => k ≫ p.map χ''.hom ≫ eqToHom eA) hcancel
      convert hcancel' using 1
      rw [Category.assoc]
      rfl
    have hχ''comp : χ''.hom ≫ φ = τ.hom := by
      have hcomp := congrArg (fun h : X ⟶ B => h.hom) hχ''.2
      dsimp [κ] at hcomp
      exact hcomp
    have hhom : χ''.hom = χ :=
      hχuniq χ''.hom ⟨hχ''p, hχ''comp⟩
    exact StrictificationHom.ext hhom
  exact ⟨A, κ, hκstrong⟩

theorem strictificationProjection_isSplit
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    IsSplitFibredCategory (strictificationProjection P) := by
  sorry

theorem strictification_object_description
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (A : StrictificationObject p P) :
    (strictificationProjection P).obj A = A.V :=
  rfl

theorem strictification_morphism_description
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : StrictificationObject p P} (f : A ⟶ B) :
    (strictificationProjection P).map f = StrictificationHom.base f :=
  rfl

/-! ## The strictification interface -/

/-- Equivalence in the 2-category of fibred categories over a fixed base:
the comparison functors commute strictly with the base, preserve strongly
cartesian arrows, and are inverse up to vertical natural isomorphism. -/
def IsFibredEquivalenceOver
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) : Prop :=
  ∃ (F : S ⥤ T) (G : T ⥤ S),
    F ⋙ q = p ∧ G ⋙ p = q ∧
      MapsStronglyCartesian p q F ∧
      MapsStronglyCartesian q p G ∧
      (∃ (e : F ⋙ G ≅ 𝟭 S)
        (over : (F ⋙ G) ⋙ p = (𝟭 S) ⋙ p),
        Formalization.Books.Categories.Unit34.IsOverNaturalIso p over e) ∧
      (∃ (e : G ⋙ F ≅ 𝟭 T)
        (over : (G ⋙ F) ⋙ q = (𝟭 T) ⋙ q),
        Formalization.Books.Categories.Unit34.IsOverNaturalIso q over e)

/-- The source's comparison data for the strictification construction.  The
first fields are the natural functor `\mathcal S \to \mathcal S'`, its
source-prescribed object map, and its strict triangle over `\mathcal C`;
the remaining fields record preservation of strongly cartesian arrows and
equivalence over the base. -/
structure StrictificationComparison
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  functor : S ⥤ StrictificationCategory p P
  functor_obj : ∀ x : S, functor.obj x = strictificationObjectOf P x
  over : functor ⋙ strictificationProjection P = p
  preserves : MapsStronglyCartesian p (strictificationProjection P) functor
  inverse : StrictificationCategory p P ⥤ S
  inverse_over : inverse ⋙ p = strictificationProjection P
  inverse_preserves :
    MapsStronglyCartesian (strictificationProjection P) p inverse
  functor_inverse :
    ∃ (e : functor ⋙ inverse ≅ 𝟭 S)
      (over : (functor ⋙ inverse) ⋙ p = (𝟭 S) ⋙ p),
      Formalization.Books.Categories.Unit34.IsOverNaturalIso p over e
  inverse_functor :
    ∃ (e : inverse ⋙ functor ≅ 𝟭 (StrictificationCategory p P))
      (over : (inverse ⋙ functor) ⋙ strictificationProjection P =
        (𝟭 (StrictificationCategory p P)) ⋙ strictificationProjection P),
      Formalization.Books.Categories.Unit34.IsOverNaturalIso
        (strictificationProjection P) over e

theorem strictificationComparison_isFibredEquivalence
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (D : StrictificationComparison p P) :
    IsFibredEquivalenceOver p (strictificationProjection P) := by
  exact ⟨D.functor, D.inverse, D.over, D.inverse_over, D.preserves,
    D.inverse_preserves, D.functor_inverse, D.inverse_functor⟩

theorem strictification_comparison_exists
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) :
    Nonempty (StrictificationComparison p P) := by
  sorry

theorem fibred_category_equivalent_to_split
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) [p.IsFibered] :
    ∃ F : Cᵒᵖ ⥤ Cat.{vS, uS},
      IsFibredEquivalenceOver p (splitFibredProjection F) := by
  sorry

end

end Formalization.Books.Categories.Unit36
