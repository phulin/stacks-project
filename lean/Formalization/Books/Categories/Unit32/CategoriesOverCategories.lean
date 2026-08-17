import Formalization.Books.Categories.Unit31.TwoFibreProducts
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Basic

/-!
# Categories, Chapter 32: Categories over categories

The source fixes a category `C` and studies categories equipped with a functor to
`C`.  Mathlib's `Over C` is the canonical category of such objects and of
strictly commuting functors.  The extra data below records the natural
transformations over `C` and the explicit fibre-product presentation from the
source.
-/

namespace Formalization.Books.Categories.Unit32

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.ObjectProperty
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit31

universe v u

/-! ## Categories over a fixed category -/

/- The source's objects and 1-morphisms are the objects and strictly commuting
   morphisms of Mathlib's `Over C`.  The wrapper keeps one unambiguous
   `CategoryStruct` for the 2-category's 1-morphisms. -/
structure CategoryOver (C : Cat.{v, u}) where
  toOver : Over C

namespace CategoryOver

abbrev left {C : Cat.{v, u}} (X : CategoryOver C) : Cat :=
  X.toOver.left

abbrev hom {C : Cat.{v, u}} (X : CategoryOver C) : left X ⟶ C :=
  X.toOver.hom

def of {C : Cat.{v, u}} {X : Cat} (p : X ⟶ C) : CategoryOver C :=
  ⟨Over.mk p⟩

structure Hom {C : Cat.{v, u}} (X Y : CategoryOver C) where
  toOver : X.toOver ⟶ Y.toOver

namespace Hom

abbrev leftHom {C : Cat.{v, u}} {X Y : CategoryOver C} (F : Hom X Y) :
    X.left ⟶ Y.left :=
  F.toOver.left

end Hom

theorem w {C : Cat.{v, u}} {X Y : CategoryOver C} (F : Hom X Y) :
    F.leftHom ≫ Y.hom = X.hom :=
  Over.w F.toOver

def id {C : Cat.{v, u}} (X : CategoryOver C) : Hom X X :=
  ⟨𝟙 X.toOver⟩

def comp {C : Cat.{v, u}} {X Y Z : CategoryOver C}
    (F : Hom X Y) (G : Hom Y Z) : Hom X Z :=
  ⟨F.toOver ≫ G.toOver⟩

@[ext]
lemma Hom.ext {C : Cat.{v, u}} {X Y : CategoryOver C}
    {F G : Hom X Y} (h : F.toOver = G.toOver) : F = G := by
  cases F
  cases G
  cases h
  rfl

end CategoryOver

abbrev CategoryOverHom {C : Cat.{v, u}} (X Y : CategoryOver C) :=
  CategoryOver.Hom X Y

abbrev structureFunctor {C : Cat.{v, u}} (X : CategoryOver C) : X.left ⥤ C :=
  X.hom.toFunctor

abbrev overFunctor {C : Cat.{v, u}} {X Y : CategoryOver C}
    (F : CategoryOverHom X Y) : X.left ⥤ Y.left :=
  F.leftHom.toFunctor

theorem overFunctor_comm {C : Cat.{v, u}} {X Y : CategoryOver C}
    (F : CategoryOverHom X Y) :
    overFunctor F ⋙ structureFunctor Y = structureFunctor X :=
  congrArg Cat.Hom.toFunctor (CategoryOver.w F)

/- A morphism between functors over `C` has components whose image in `C` is
   the identity, transported along the strict triangle equalities. -/
def overIdentityComponent {C : Cat.{v, u}} {X Y : CategoryOver C}
    (F G : CategoryOverHom X Y) (Z : X.left) :
    (structureFunctor Y).obj ((overFunctor F).obj Z) ⟶
      (structureFunctor Y).obj ((overFunctor G).obj Z) :=
  eqToHom ((congrArg (fun K : X.left ⥤ C => K.obj Z) (overFunctor_comm F)).trans
    (congrArg (fun K : X.left ⥤ C => K.obj Z) (overFunctor_comm G)).symm)

/-- A natural transformation over the fixed base category. -/
structure OverNatTrans {C : Cat.{v, u}} {X Y : CategoryOver C}
    (F G : CategoryOverHom X Y) where
  /-- The underlying natural transformation of functors. -/
  toNatTrans : overFunctor F ⟶ overFunctor G
  /-- Every component maps to the identity in the base. -/
  over : ∀ Z, (structureFunctor Y).map (toNatTrans.app Z) = overIdentityComponent F G Z

@[ext]
lemma OverNatTrans.ext {C : Cat.{v, u}} {X Y : CategoryOver C}
    {F G : CategoryOverHom X Y} {η θ : OverNatTrans F G}
    (h : η.toNatTrans = θ.toNatTrans) : η = θ := by
  cases η
  cases θ
  cases h
  rfl

/- The vertical composition laws are the ordinary natural-transformation
   laws; the over conditions are the corresponding transported identity
   equations. -/
instance overHomCategory {C : Cat.{v, u}} (X Y : CategoryOver C) :
    Category (CategoryOverHom X Y) where
  Hom F G := OverNatTrans F G
  id F :=
    { toNatTrans := 𝟙 (overFunctor F)
      over := by
        intro Z
        simp [overIdentityComponent] }
  comp η θ :=
    { toNatTrans := η.toNatTrans ≫ θ.toNatTrans
      over := by
        intro Z
        simp [NatTrans.comp_app, overIdentityComponent, η.over, θ.over] }
  id_comp := by
    intros
    apply OverNatTrans.ext
    simp
  comp_id := by
    intros
    apply OverNatTrans.ext
    simp
  assoc := by
    intros
    apply OverNatTrans.ext
    simp [Category.assoc]

/-! ### Horizontal composition and the 2-category structure -/

def overWhiskerLeft {C : Cat.{v, u}}
    {X Y Z : CategoryOver C} (F : CategoryOverHom X Y)
    {G H : CategoryOverHom Y Z} (η : OverNatTrans G H) :
    OverNatTrans (CategoryOver.comp F G) (CategoryOver.comp F H) :=
  { toNatTrans := by
      simpa [overFunctor, CategoryOver.comp, CategoryOver.Hom.leftHom,
        Over.comp_left, Cat.Hom.comp_toFunctor] using
        Functor.whiskerLeft (overFunctor F) η.toNatTrans
    over := by
      intro W
      change (structureFunctor Z).map
        (η.toNatTrans.app ((overFunctor F).obj W)) = _
      rw [η.over]
      simp [overIdentityComponent]
      congr 1 }

def overWhiskerRight {C : Cat.{v, u}}
    {X Y Z : CategoryOver C} {F G : CategoryOverHom X Y}
    (η : OverNatTrans F G) (H : CategoryOverHom Y Z) :
    OverNatTrans (CategoryOver.comp F H) (CategoryOver.comp G H) :=
  { toNatTrans := by
      simpa [overFunctor, CategoryOver.comp, CategoryOver.Hom.leftHom,
        Over.comp_left, Cat.Hom.comp_toFunctor] using
        Functor.whiskerRight η.toNatTrans (overFunctor H)
    over := by
      intro W
      change (structureFunctor Z).map
        ((overFunctor H).map (η.toNatTrans.app W)) = _
      have hmap := Functor.congr_hom (overFunctor_comm H)
        (η.toNatTrans.app W)
      simp only [overFunctor, CategoryOver.comp, CategoryOver.Hom.leftHom] at hmap ⊢
      change ((overFunctor H ⋙ structureFunctor Z).map
        (η.toNatTrans.app W)) = _
      rw [hmap, η.over]
      simp [overIdentityComponent] }

def overHorizontalComposition {C : Cat.{v, u}}
    {X Y Z : CategoryOver C} {F₁ F₂ : CategoryOverHom X Y}
    {G₁ G₂ : CategoryOverHom Y Z}
    (η : OverNatTrans F₁ F₂) (θ : OverNatTrans G₁ G₂) :
    OverNatTrans (CategoryOver.comp F₁ G₁) (CategoryOver.comp F₂ G₂) :=
  { toNatTrans := by
      simpa [overFunctor, CategoryOver.comp, CategoryOver.Hom.leftHom,
        Over.comp_left, Cat.Hom.comp_toFunctor] using
        (Functor.whiskerRight η.toNatTrans (overFunctor G₁) ≫
          Functor.whiskerLeft (overFunctor F₂) θ.toNatTrans)
    over := by
      intro W
      change (structureFunctor Z).map
        ((overFunctor G₁).map (η.toNatTrans.app W) ≫
          θ.toNatTrans.app ((overFunctor F₂).obj W)) = _
      rw [Functor.map_comp]
      have hmap := Functor.congr_hom (overFunctor_comm G₁)
        (η.toNatTrans.app W)
      simp only [overFunctor, CategoryOver.comp, CategoryOver.Hom.leftHom] at hmap ⊢
      change ((overFunctor G₁ ⋙ structureFunctor Z).map
          (η.toNatTrans.app W)) ≫
        (structureFunctor Z).map (θ.toNatTrans.app ((overFunctor F₂).obj W)) = _
      rw [hmap, η.over, θ.over]
      simp [overIdentityComponent] }

def overNatIsoOfUnderlying {C : Cat.{v, u}}
    {X Y : CategoryOver C} {F G : CategoryOverHom X Y}
    (e : overFunctor F ≅ overFunctor G)
    (h : ∀ Z, (structureFunctor Y).map (e.hom.app Z) =
      overIdentityComponent F G Z := by sorry) : F ≅ G where
  hom :=
    { toNatTrans := e.hom
      over := h }
  inv :=
    { toNatTrans := e.inv
      over := by
        intro Z
        apply (cancel_mono ((structureFunctor Y).map (e.hom.app Z))).1
        rw [← Functor.map_comp, e.inv_hom_id_app]
        rw [h Z]
        simp [overIdentityComponent] }
  hom_inv_id := by
    apply OverNatTrans.ext
    change e.hom ≫ e.inv = 𝟙 (overFunctor F)
    exact e.hom_inv_id
  inv_hom_id := by
    apply OverNatTrans.ext
    change e.inv ≫ e.hom = 𝟙 (overFunctor G)
    exact e.inv_hom_id

/- The source's 2-category is obtained by restricting the bicategory of
   categories to the strict triangles and transformations over `C`. -/
noncomputable instance categoriesOverBicategory {C : Cat.{v, u}} :
    Bicategory (CategoryOver C) where
  Hom := CategoryOverHom
  id := CategoryOver.id
  comp := CategoryOver.comp
  homCategory := overHomCategory
  whiskerLeft := overWhiskerLeft
  whiskerRight := overWhiskerRight
  associator F G H :=
    overNatIsoOfUnderlying
      (by
        simpa only [overFunctor, CategoryOver.comp, CategoryOver.Hom.leftHom,
          Over.comp_left, Cat.Hom.comp_toFunctor] using
          Functor.associator (overFunctor F) (overFunctor G) (overFunctor H))
      (by
        intro Z
        simp [Functor.associator_hom_app, overIdentityComponent, overFunctor,
          CategoryOver.comp, CategoryOver.Hom.leftHom, Over.comp_left,
          Cat.Hom.comp_toFunctor]
        all_goals exact eq_of_heq (eqToHom_heq_id_dom _ _ _).symm)
  leftUnitor F :=
    overNatIsoOfUnderlying (Functor.leftUnitor (overFunctor F)) (by
      intro Z
      change (structureFunctor _).map
        (𝟙 ((overFunctor (CategoryOver.comp (CategoryOver.id _) F)).obj Z)) = _
      rw [(structureFunctor _).map_id]
      simp [overIdentityComponent, overFunctor,
        CategoryOver.comp, CategoryOver.Hom.leftHom, Over.comp_left,
        Cat.Hom.comp_toFunctor]
      all_goals exact eq_of_heq (eqToHom_heq_id_dom _ _ _).symm)
  rightUnitor F :=
    overNatIsoOfUnderlying (Functor.rightUnitor (overFunctor F)) (by
      intro Z
      change (structureFunctor _).map
        (𝟙 ((overFunctor (CategoryOver.comp F (CategoryOver.id _))).obj Z)) = _
      rw [(structureFunctor _).map_id]
      simp [overIdentityComponent, overFunctor,
        CategoryOver.comp, CategoryOver.Hom.leftHom, Over.comp_left,
        Cat.Hom.comp_toFunctor]
      all_goals exact eq_of_heq (eqToHom_heq_id_dom _ _ _).symm)
  whiskerLeft_id := by
    intros
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    rfl
  whiskerLeft_comp := by
    intros
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    rfl
  id_whiskerLeft := by
    intros A B f g η
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    simp [overHomCategory, overWhiskerLeft, overNatIsoOfUnderlying, overFunctor,
      CategoryOver.id, CategoryOver.comp, CategoryOver.Hom.leftHom,
      Over.comp_left, Cat.Hom.comp_toFunctor]
    change η.toNatTrans.app Z = ((𝟙 _ ≫ η.toNatTrans ≫ 𝟙 _).app Z)
    simp
  comp_whiskerLeft := by
    intros A B C D f g h h' η
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change η.toNatTrans.app ((overFunctor g).obj ((overFunctor f).obj Z)) =
      ((Functor.associator (overFunctor f) (overFunctor g) (overFunctor h)).hom ≫
        Functor.whiskerLeft (overFunctor f)
          (Functor.whiskerLeft (overFunctor g) η.toNatTrans) ≫
        (Functor.associator (overFunctor f) (overFunctor g) (overFunctor h')).inv).app Z
    simp
  id_whiskerRight := by
    intros A B C f g
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change (Functor.whiskerRight (NatTrans.id (overFunctor f)) (overFunctor g)).app Z =
      (NatTrans.id ((overFunctor f) ⋙ (overFunctor g))).app Z
    exact congrArg (fun α => α.app Z)
      (Functor.whiskerRight_id (G := overFunctor f) (overFunctor g))
  comp_whiskerRight := by
    intros A B C f g h η θ i
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change (Functor.whiskerRight (η.toNatTrans ≫ θ.toNatTrans)
        (overFunctor i)).app Z =
      ((Functor.whiskerRight η.toNatTrans (overFunctor i) ≫
        Functor.whiskerRight θ.toNatTrans (overFunctor i)).app Z)
    exact congrArg (fun α => α.app Z)
      (Functor.whiskerRight_comp η.toNatTrans θ.toNatTrans (overFunctor i))
  whiskerRight_id := by
    intros A B f g η
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change (Functor.whiskerRight η.toNatTrans (𝟭 _)).app Z =
      ((Functor.rightUnitor (overFunctor f)).hom ≫ η.toNatTrans ≫
        (Functor.rightUnitor (overFunctor g)).inv).app Z
    simp
  whiskerRight_comp := by
    intros A B C D f f' η g h
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change (Functor.whiskerRight η.toNatTrans
        ((overFunctor g) ⋙ (overFunctor h))).app Z =
      ((Functor.associator (overFunctor f) (overFunctor g) (overFunctor h)).inv ≫
        Functor.whiskerRight (Functor.whiskerRight η.toNatTrans (overFunctor g))
          (overFunctor h) ≫
        (Functor.associator (overFunctor f') (overFunctor g) (overFunctor h)).hom).app Z
    simp
  whisker_assoc := by
    intros A B C D f g g' η h
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change (Functor.whiskerRight
        (Functor.whiskerLeft (overFunctor f) η.toNatTrans)
        (overFunctor h)).app Z =
      ((Functor.associator (overFunctor f) (overFunctor g) (overFunctor h)).hom ≫
        Functor.whiskerLeft (overFunctor f)
          (Functor.whiskerRight η.toNatTrans (overFunctor h)) ≫
        (Functor.associator (overFunctor f) (overFunctor g') (overFunctor h)).inv).app Z
    simp
  whisker_exchange := by
    intros A B C f g h i η θ
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change ((Functor.whiskerLeft (overFunctor f) θ.toNatTrans ≫
        Functor.whiskerRight η.toNatTrans (overFunctor i)).app Z) =
      ((Functor.whiskerRight η.toNatTrans (overFunctor h) ≫
        Functor.whiskerLeft (overFunctor g) θ.toNatTrans).app Z)
    exact congrArg (fun α => α.app Z)
      (Functor.whiskerLeft_comp_whiskerRight η.toNatTrans θ.toNatTrans)
  pentagon := by
    intros A B C D E f g h i
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change ((Functor.whiskerRight
        (Functor.associator (overFunctor f) (overFunctor g) (overFunctor h)).hom
        (overFunctor i) ≫
      (Functor.associator (overFunctor f)
          ((overFunctor g) ⋙ (overFunctor h)) (overFunctor i)).hom ≫
      Functor.whiskerLeft (overFunctor f)
        (Functor.associator (overFunctor g) (overFunctor h) (overFunctor i)).hom).app Z) =
      (((Functor.associator ((overFunctor f) ⋙ (overFunctor g))
          (overFunctor h) (overFunctor i)).hom ≫
        (Functor.associator (overFunctor f) (overFunctor g)
          ((overFunctor h) ⋙ (overFunctor i))).hom).app Z)
    simp
  triangle := by
    intros A B C f g
    apply OverNatTrans.ext
    apply NatTrans.ext
    funext Z
    change (((Functor.associator (overFunctor f) (𝟭 _) (overFunctor g)).hom ≫
        Functor.whiskerLeft (overFunctor f)
          (Functor.leftUnitor (overFunctor g)).hom).app Z) =
      (Functor.whiskerRight (Functor.rightUnitor (overFunctor f)).hom
        (overFunctor g)).app Z
    simp

/- The source uses the strict convention for this 2-category. -/
noncomputable instance categoriesOverStrict {C : Cat.{v, u}} :
    Bicategory.Strict (CategoryOver C) := by
  refine {
    id_comp := ?_
    comp_id := ?_
    assoc := ?_
    leftUnitor_eqToIso := ?_
    rightUnitor_eqToIso := ?_
    associator_eqToIso := ?_ }
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl

theorem categoriesOver_associated_two_one_category {C : Cat.{v, u}} :
    IsTwoOneCategory (AssociatedTwoOneCategory (CategoryOver C)) := by
  infer_instance

/-! ## Fibre categories and lifts -/

/- Mathlib's `Functor.Fiber` is exactly the source's fibre category: its
   objects are pairs `(x, p.obj x = U)` and its morphisms lift `𝟙 U`. -/
abbrev FibreCategory {A C : Type*} [Category* A] [Category* C]
    (p : A ⥤ C) (U : C) := Functor.Fiber p U

/-- An object of `A` lies over `U` for the functor `p`. -/
def IsObjectLift {A C : Type*} [Category* A] [Category* C]
    (p : A ⥤ C) (U : C) (x : A) : Prop :=
  p.obj x = U

/-- A morphism of `A` lies over the specified morphism of the base. -/
def IsMorphismLift {A C : Type*} [Category* A] [Category* C]
    (p : A ⥤ C) {V U : C} (f : V ⟶ U) {y x : A} (φ : y ⟶ x) : Prop :=
  p.IsHomLift f φ

theorem fibreCategory_object_lift {A C : Type*} [Category* A] [Category* C]
    (p : A ⥤ C) (U : C) (x : FibreCategory p U) :
    IsObjectLift p U x.1 :=
  x.2

theorem fibreCategory_morphism_lift {A C : Type*} [Category* A] [Category* C]
    (p : A ⥤ C) (U : C) {x y : FibreCategory p U} (φ : x ⟶ y) :
    IsMorphismLift p (𝟙 U) φ.1 :=
  φ.2

/- A morphism over `C` induces the corresponding functor between fibres. -/
def overMorphismFiberFunctor {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) (U : C) :
    FibreCategory (structureFunctor X) U ⥤ FibreCategory (structureFunctor Y) U where
  obj x :=
    ⟨(overFunctor F).obj x.1,
      (congrArg (fun K : X.left ⥤ C => K.obj x.1) (overFunctor_comm F)).trans x.2⟩
  map := fun {x y} φ =>
    ⟨(overFunctor F).map φ.1, by
      have hx : (structureFunctor Y).obj ((overFunctor F).obj x.1) = U := by
        change (overFunctor F ⋙ structureFunctor Y).obj x.1 = U
        rw [congrArg (fun K : X.left ⥤ C => K.obj x.1)
          (overFunctor_comm F)]
        exact x.2
      have hy : (structureFunctor Y).obj ((overFunctor F).obj y.1) = U := by
        change (overFunctor F ⋙ structureFunctor Y).obj y.1 = U
        rw [congrArg (fun K : X.left ⥤ C => K.obj y.1)
          (overFunctor_comm F)]
        exact y.2
      apply IsHomLift.of_fac' (structureFunctor Y) (𝟙 U)
        ((overFunctor F).map φ.1) hx hy
      let _ : (structureFunctor X).IsHomLift (𝟙 U) φ.1 := φ.2
      have hcomm := Functor.congr_hom (overFunctor_comm F) φ.1
      rw [IsHomLift.fac' (structureFunctor X) (𝟙 U) φ.1] at hcomm
      simpa [overFunctor, Cat.Hom.comp_toFunctor] using hcomm
    ⟩
  map_id := by
    intro x
    apply Functor.Fiber.hom_ext
    change (overFunctor F).map (𝟙 x.1) = 𝟙 _
    simp
  map_comp := by
    intros X' Y' Z' f g
    apply Functor.Fiber.hom_ext
    change (overFunctor F).map (f.1 ≫ g.1) =
      (overFunctor F).map f.1 ≫ (overFunctor F).map g.1
    simp

/- The same restriction sends a natural transformation over `C` to a natural
   transformation of the induced fibre functors. -/
def overMorphismFiberNatTrans {C : Cat.{v, u}}
    {X Y : CategoryOver C} {F G : CategoryOverHom X Y}
    (η : OverNatTrans F G) (U : C) :
    overMorphismFiberFunctor F U ⟶ overMorphismFiberFunctor G U where
  app x :=
    ⟨η.toNatTrans.app x.1, by
      have hxF : (structureFunctor Y).obj ((overFunctor F).obj x.1) = U := by
        change (overFunctor F ⋙ structureFunctor Y).obj x.1 = U
        rw [congrArg (fun K : X.left ⥤ C => K.obj x.1)
          (overFunctor_comm F)]
        exact x.2
      have hxG : (structureFunctor Y).obj ((overFunctor G).obj x.1) = U := by
        change (overFunctor G ⋙ structureFunctor Y).obj x.1 = U
        rw [congrArg (fun K : X.left ⥤ C => K.obj x.1)
          (overFunctor_comm G)]
        exact x.2
      apply IsHomLift.of_fac' (structureFunctor Y) (𝟙 U)
        (η.toNatTrans.app x.1) hxF hxG
      simpa [overIdentityComponent] using η.over x.1⟩
  naturality := by
    intro x y f
    apply Functor.Fiber.hom_ext
    change (overFunctor F).map f.1 ≫ η.toNatTrans.app y.1 =
      η.toNatTrans.app x.1 ≫ (overFunctor G).map f.1
    exact η.toNatTrans.naturality f.1

/-! ## The explicit 2-fibre product over `C` -/

/- The source's quadruple `(U, x, y, f)` is equivalently an object of the
   isomorphism comma category whose two objects have a common base and whose
   comparison arrow lies over the identity of that base. -/
def TwoFibreProductOverProperty {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S) (G : CategoryOverHom Y S) :
    ObjectProperty (IsoComma (overFunctor F) (overFunctor G)) :=
  fun ξ =>
    ∃ U : C,
      IsObjectLift (structureFunctor X) U ξ.obj.left ∧
      IsObjectLift (structureFunctor Y) U ξ.obj.right ∧
      IsMorphismLift (structureFunctor S) (𝟙 U) ξ.obj.hom

/-- The category of quadruples in the explicit 2-fibre-product construction. -/
abbrev TwoFibreProductOverCategory {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) :=
  (TwoFibreProductOverProperty F G).FullSubcategory

theorem twoFibreProductOver_object_description {C : Cat.{v, u}}
    {X Y S : CategoryOver C} {F : CategoryOverHom X S}
    {G : CategoryOverHom Y S} (ξ : TwoFibreProductOverCategory F G) :
    ∃ U : C,
      IsObjectLift (structureFunctor X) U ξ.obj.obj.left ∧
      IsObjectLift (structureFunctor Y) U ξ.obj.obj.right ∧
      IsMorphismLift (structureFunctor S) (𝟙 U) ξ.obj.obj.hom :=
  ξ.property

/-- The left forgetful functor in the explicit construction. -/
def twoFibreProductOverLeft {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) :
    TwoFibreProductOverCategory F G ⥤ X.left :=
  (TwoFibreProductOverProperty F G).ι ⋙ isoCommaLeft (overFunctor F) (overFunctor G)

/-- The right forgetful functor in the explicit construction. -/
def twoFibreProductOverRight {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) :
    TwoFibreProductOverCategory F G ⥤ Y.left :=
  (TwoFibreProductOverProperty F G).ι ⋙ isoCommaRight (overFunctor F) (overFunctor G)

/-- The comparison isomorphism `F ∘ p ≅ G ∘ q`. -/
noncomputable def twoFibreProductOverComparison {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) :
    twoFibreProductOverLeft F G ⋙ overFunctor F ≅
      twoFibreProductOverRight F G ⋙ overFunctor G :=
  Functor.isoWhiskerLeft (TwoFibreProductOverProperty F G).ι
    (isoCommaComparisonIso (overFunctor F) (overFunctor G))

theorem twoFibreProductOverComparison_app {C : Cat.{v, u}}
    {X Y S : CategoryOver C} {F : CategoryOverHom X S}
    {G : CategoryOverHom Y S} (ξ : TwoFibreProductOverCategory F G) :
    (twoFibreProductOverComparison F G).hom.app ξ = ξ.obj.obj.hom := by
  rfl

theorem twoFibreProductOver_morphism_base_description {C : Cat.{v, u}}
    {X Y S : CategoryOver C} {F : CategoryOverHom X S}
    {G : CategoryOverHom Y S}
    {ξ ξ' : TwoFibreProductOverCategory F G} (h : ξ ⟶ ξ') :
    ∃ (U U' : C)
      (hx : IsObjectLift (structureFunctor X) U ξ.obj.obj.left)
      (hy : IsObjectLift (structureFunctor Y) U ξ.obj.obj.right)
      (hx' : IsObjectLift (structureFunctor X) U' ξ'.obj.obj.left)
      (hy' : IsObjectLift (structureFunctor Y) U' ξ'.obj.obj.right),
      eqToHom hx.symm ≫ (structureFunctor X).map h.hom.hom.left ≫ eqToHom hx' =
        eqToHom hy.symm ≫ (structureFunctor Y).map h.hom.hom.right ≫ eqToHom hy' := by
  rcases ξ.property with ⟨U, hx, hy, hξ⟩
  rcases ξ'.property with ⟨U', hx', hy', hξ'⟩
  refine ⟨U, U', hx, hy, hx', hy', ?_⟩
  have hFa : (structureFunctor S).obj ((overFunctor F).obj ξ.obj.obj.left) = U := by
    change (overFunctor F ⋙ structureFunctor S).obj ξ.obj.obj.left = U
    rw [congrArg (fun K : X.left ⥤ C => K.obj ξ.obj.obj.left)
      (overFunctor_comm F)]
    exact hx
  have hGa : (structureFunctor S).obj ((overFunctor G).obj ξ.obj.obj.right) = U := by
    change (overFunctor G ⋙ structureFunctor S).obj ξ.obj.obj.right = U
    rw [congrArg (fun K : Y.left ⥤ C => K.obj ξ.obj.obj.right)
      (overFunctor_comm G)]
    exact hy
  have hFa' : (structureFunctor S).obj ((overFunctor F).obj ξ'.obj.obj.left) = U' := by
    change (overFunctor F ⋙ structureFunctor S).obj ξ'.obj.obj.left = U'
    rw [congrArg (fun K : X.left ⥤ C => K.obj ξ'.obj.obj.left)
      (overFunctor_comm F)]
    exact hx'
  have hGa' : (structureFunctor S).obj ((overFunctor G).obj ξ'.obj.obj.right) = U' := by
    change (overFunctor G ⋙ structureFunctor S).obj ξ'.obj.obj.right = U'
    rw [congrArg (fun K : Y.left ⥤ C => K.obj ξ'.obj.obj.right)
      (overFunctor_comm G)]
    exact hy'
  let _ : (structureFunctor S).IsHomLift (𝟙 U) ξ.obj.obj.hom := hξ
  let _ : (structureFunctor S).IsHomLift (𝟙 U') ξ'.obj.obj.hom := hξ'
  have hs := congrArg (fun k => (structureFunctor S).map k) h.hom.hom.w
  have hF := Functor.congr_hom (overFunctor_comm F) h.hom.hom.left
  have hG := Functor.congr_hom (overFunctor_comm G) h.hom.hom.right
  change (structureFunctor S).map ((overFunctor F).map h.hom.hom.left) = _ at hF
  change (structureFunctor S).map ((overFunctor G).map h.hom.hom.right) = _ at hG
  have hFt :
      eqToHom hFa.symm ≫ (structureFunctor S).map ((overFunctor F).map h.hom.hom.left) ≫
          eqToHom hFa' =
        eqToHom hx.symm ≫ (structureFunctor X).map h.hom.hom.left ≫ eqToHom hx' := by
    rw [hF]
    simp
  have hGt :
      eqToHom hGa.symm ≫ (structureFunctor S).map ((overFunctor G).map h.hom.hom.right) ≫
          eqToHom hGa' =
        eqToHom hy.symm ≫ (structureFunctor Y).map h.hom.hom.right ≫ eqToHom hy' := by
    rw [hG]
    simp
  have hξfac := IsHomLift.fac' (structureFunctor S) (𝟙 U) ξ.obj.obj.hom
  have hξ'fac := IsHomLift.fac' (structureFunctor S) (𝟙 U') ξ'.obj.obj.hom
  have hξt :
      eqToHom hFa.symm ≫ (structureFunctor S).map ξ.obj.obj.hom ≫ eqToHom hGa =
        𝟙 U := by
    rw [hξfac]
    simp [hGa]
  have hξ't :
      eqToHom hFa'.symm ≫ (structureFunctor S).map ξ'.obj.obj.hom ≫ eqToHom hGa' =
        𝟙 U' := by
    rw [hξ'fac]
    simp [hGa']
  rw [Functor.map_comp, Functor.map_comp] at hs
  have hξleft :
      eqToHom hFa.symm ≫ (structureFunctor S).map ξ.obj.obj.hom =
        eqToHom hGa.symm := by
    calc
      eqToHom hFa.symm ≫ (structureFunctor S).map ξ.obj.obj.hom =
          (eqToHom hFa.symm ≫ (structureFunctor S).map ξ.obj.obj.hom ≫
            eqToHom hGa) ≫ eqToHom hGa.symm := by simp [Category.assoc]
      _ = 𝟙 U ≫ eqToHom hGa.symm := by rw [hξt]
      _ = eqToHom hGa.symm := by simp
  have hξ'right :
      (structureFunctor S).map ξ'.obj.obj.hom ≫ eqToHom hGa' =
        eqToHom hFa' := by
    calc
      (structureFunctor S).map ξ'.obj.obj.hom ≫ eqToHom hGa' =
          𝟙 _ ≫ (structureFunctor S).map ξ'.obj.obj.hom ≫ eqToHom hGa' := by simp
      _ = (eqToHom hFa' ≫ eqToHom hFa'.symm) ≫
          (structureFunctor S).map ξ'.obj.obj.hom ≫ eqToHom hGa' := by simp
      _ = eqToHom hFa' ≫
          (eqToHom hFa'.symm ≫ (structureFunctor S).map ξ'.obj.obj.hom ≫
            eqToHom hGa') := by simp
      _ = eqToHom hFa' ≫ 𝟙 U' := by rw [hξ't]
      _ = eqToHom hFa' := by simp
  have hsT :
      eqToHom hFa.symm ≫
          (structureFunctor S).map ((overFunctor F).map h.hom.hom.left) ≫
          eqToHom hFa' =
        eqToHom hGa.symm ≫
          (structureFunctor S).map ((overFunctor G).map h.hom.hom.right) ≫
          eqToHom hGa' := by
    calc
      eqToHom hFa.symm ≫
          (structureFunctor S).map ((overFunctor F).map h.hom.hom.left) ≫
          eqToHom hFa' =
          eqToHom hFa.symm ≫
            (structureFunctor S).map ((overFunctor F).map h.hom.hom.left) ≫
            (structureFunctor S).map ξ'.obj.obj.hom ≫ eqToHom hGa' := by
              rw [hξ'right]
      _ = eqToHom hFa.symm ≫
          ((structureFunctor S).map ((overFunctor F).map h.hom.hom.left) ≫
            (structureFunctor S).map ξ'.obj.obj.hom) ≫ eqToHom hGa' := by
              simp [Category.assoc]
      _ = eqToHom hFa.symm ≫
          ((structureFunctor S).map ξ.obj.obj.hom ≫
            (structureFunctor S).map ((overFunctor G).map h.hom.hom.right)) ≫
            eqToHom hGa' := by rw [hs]
      _ = (eqToHom hFa.symm ≫ (structureFunctor S).map ξ.obj.obj.hom) ≫
          (structureFunctor S).map ((overFunctor G).map h.hom.hom.right) ≫
          eqToHom hGa' := by simp [Category.assoc]
      _ = eqToHom hGa.symm ≫
          (structureFunctor S).map ((overFunctor G).map h.hom.hom.right) ≫
          eqToHom hGa' := by rw [hξleft]
  exact hFt.symm.trans (hsT.trans hGt)

/- The comma morphism `w` supplies the commutative square in the source's
   morphism description. -/
theorem twoFibreProductOver_morphism_description {C : Cat.{v, u}}
    {X Y S : CategoryOver C} {F : CategoryOverHom X S}
    {G : CategoryOverHom Y S}
    {ξ ξ' : TwoFibreProductOverCategory F G} (h : ξ ⟶ ξ') :
    (ξ.obj.obj.hom ≫ (overFunctor G).map h.hom.hom.right) =
      (overFunctor F).map h.hom.hom.left ≫ ξ'.obj.obj.hom := by
  exact h.hom.hom.w.symm

abbrev IsVerticalNatTrans {A B D : Type*} [Category* A] [Category* B] [Category* D]
    {P Q : A ⥤ B} (p : B ⥤ D) (η : P ⟶ Q)
    (h : ∀ Z, p.obj (P.obj Z) = p.obj (Q.obj Z)) : Prop :=
  ∀ Z, p.map (η.app Z) = eqToHom (h Z)

/- The following record keeps the displayed product data together.  The
   ambient `Cat` object used for the source's 2-category is not universe
   polymorphic, whereas this full subcategory can be larger than the input
   categories, so the record is stated directly in ordinary categories. -/
structure TwoFibreProductOverDiagram {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) where
  base : TwoFibreProductOverCategory F G ⥤ C
  left : TwoFibreProductOverCategory F G ⥤ X.left
  right : TwoFibreProductOverCategory F G ⥤ Y.left
  left_over : left ⋙ structureFunctor X = base
  right_over : right ⋙ structureFunctor Y = base
  comparison : left ⋙ overFunctor F ≅ right ⋙ overFunctor G
  comparison_base : ∀ Z,
    (structureFunctor S).obj ((left ⋙ overFunctor F).obj Z) =
      (structureFunctor S).obj ((right ⋙ overFunctor G).obj Z)
  comparison_vertical :
    IsVerticalNatTrans (structureFunctor S) comparison.hom comparison_base

structure TwoFibreProductOverCone {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) (W : Type*) [Category* W] where
  base : W ⥤ C
  left : W ⥤ X.left
  right : W ⥤ Y.left
  left_over : left ⋙ structureFunctor X = base
  right_over : right ⋙ structureFunctor Y = base
  comparison : left ⋙ overFunctor F ≅ right ⋙ overFunctor G
  comparison_base : ∀ Z,
    (structureFunctor S).obj ((left ⋙ overFunctor F).obj Z) =
      (structureFunctor S).obj ((right ⋙ overFunctor G).obj Z)
  comparison_vertical :
    IsVerticalNatTrans (structureFunctor S) comparison.hom comparison_base

structure TwoFibreProductOverLift {C : Cat.{v, u}}
    {X Y S : CategoryOver C} {F : CategoryOverHom X S}
    {G : CategoryOverHom Y S}
    {W : Type*} [Category* W]
    (D : TwoFibreProductOverDiagram F G)
    (K : TwoFibreProductOverCone F G W) where
  functor : W ⥤ TwoFibreProductOverCategory F G
  over : functor ⋙ D.base = K.base
  left : K.left ⟶ functor ⋙ D.left
  left_isIso : IsIso left
  right : K.right ⟶ functor ⋙ D.right
  right_isIso : IsIso right
  left_base : ∀ Z,
    (structureFunctor X).obj (K.left.obj Z) =
      (structureFunctor X).obj ((functor ⋙ D.left).obj Z)
  right_base : ∀ Z,
    (structureFunctor Y).obj (K.right.obj Z) =
      (structureFunctor Y).obj ((functor ⋙ D.right).obj Z)
  left_vertical : IsVerticalNatTrans (structureFunctor X) left left_base
  right_vertical : IsVerticalNatTrans (structureFunctor Y) right right_base
  commutes :
    Functor.whiskerRight left (overFunctor F) ≫
        (Functor.associator functor D.left (overFunctor F)).hom ≫
        Functor.whiskerLeft functor D.comparison.hom ≫
        (Functor.associator functor D.right (overFunctor G)).inv =
      K.comparison.hom ≫ Functor.whiskerRight right (overFunctor G)

attribute [instance] TwoFibreProductOverLift.left_isIso
attribute [instance] TwoFibreProductOverLift.right_isIso

/- This is the final-object/universal-property interface for the explicit
   construction.  Its cone and lift fields spell out strict base triangles,
   vertical 2-morphisms, the comparison square, and uniqueness up to a unique
   invertible vertical transformation. -/
abbrev IsTwoFibreProductOverDiagram {C : Cat.{v, u}}
    {X Y S : CategoryOver C} {F : CategoryOverHom X S}
    {G : CategoryOverHom Y S}
    (D : TwoFibreProductOverDiagram F G) : Prop :=
  ∀ {W : Type*} [Category* W] (K : TwoFibreProductOverCone F G W),
    Nonempty (TwoFibreProductOverLift D K) ∧
      ∀ (L₁ L₂ : TwoFibreProductOverLift D K),
        ∃! η : L₁.functor ⟶ L₂.functor,
          IsIso η ∧
            IsVerticalNatTrans D.base η (fun Z =>
              congrArg (fun H : W ⥤ C => H.obj Z) (L₁.over.trans L₂.over.symm)) ∧
            L₁.left ≫ Functor.whiskerRight η D.left = L₂.left ∧
            L₁.right ≫ Functor.whiskerRight η D.right = L₂.right

noncomputable def twoFibreProductOverDiagram {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) : TwoFibreProductOverDiagram F G where
  base := twoFibreProductOverLeft F G ⋙ structureFunctor X
  left := twoFibreProductOverLeft F G
  right := twoFibreProductOverRight F G
  left_over := rfl
  right_over := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro ξ
      rcases ξ.property with ⟨U, hx, hy, hξ⟩
      exact hy.trans hx.symm
    · intro ξ ξ' h
      rcases twoFibreProductOver_morphism_base_description (F := F) (G := G) h with
        ⟨U, U', hx, hy, hx', hy', hs⟩
      change (structureFunctor X).obj ξ.obj.obj.left = U at hx
      change (structureFunctor Y).obj ξ.obj.obj.right = U at hy
      change (structureFunctor X).obj ξ'.obj.obj.left = U' at hx'
      change (structureFunctor Y).obj ξ'.obj.obj.right = U' at hy'
      have hs' := congrArg
        (fun k => eqToHom hy ≫ k ≫ eqToHom hy'.symm) hs
      have hcancel : eqToHom hy ≫ eqToHom hy.symm = 𝟙 _ := by
        simp
      have hcancel' : eqToHom hy' ≫ eqToHom hy'.symm = 𝟙 _ := by
        simp
      simpa [twoFibreProductOverRight, twoFibreProductOverLeft,
        isoCommaRight, isoCommaLeft, structureFunctor, eqToHom_trans,
        Category.assoc, hcancel, hcancel'] using hs'.symm
  comparison := twoFibreProductOverComparison F G
  comparison_base := by
    intro ξ
    rcases ξ.property with ⟨U, hx, hy, hξ⟩
    have hF :
        (structureFunctor S).obj ((overFunctor F).obj ξ.obj.obj.left) = U := by
      change (overFunctor F ⋙ structureFunctor S).obj ξ.obj.obj.left = U
      rw [congrArg (fun K : X.left ⥤ C => K.obj ξ.obj.obj.left)
        (overFunctor_comm F)]
      exact hx
    have hG :
        (structureFunctor S).obj ((overFunctor G).obj ξ.obj.obj.right) = U := by
      change (overFunctor G ⋙ structureFunctor S).obj ξ.obj.obj.right = U
      rw [congrArg (fun K : Y.left ⥤ C => K.obj ξ.obj.obj.right)
        (overFunctor_comm G)]
      exact hy
    exact hF.trans hG.symm
  comparison_vertical := by
    intro ξ
    rcases ξ.property with ⟨U, hx, hy, hξ⟩
    have hF :
        (structureFunctor S).obj ((overFunctor F).obj ξ.obj.obj.left) = U := by
      change (overFunctor F ⋙ structureFunctor S).obj ξ.obj.obj.left = U
      rw [congrArg (fun K : X.left ⥤ C => K.obj ξ.obj.obj.left)
        (overFunctor_comm F)]
      exact hx
    have hG :
        (structureFunctor S).obj ((overFunctor G).obj ξ.obj.obj.right) = U := by
      change (overFunctor G ⋙ structureFunctor S).obj ξ.obj.obj.right = U
      rw [congrArg (fun K : Y.left ⥤ C => K.obj ξ.obj.obj.right)
        (overFunctor_comm G)]
      exact hy
    let _ : (structureFunctor S).IsHomLift (𝟙 U) ξ.obj.obj.hom := hξ
    have hfac := IsHomLift.fac' (structureFunctor S) (𝟙 U) ξ.obj.obj.hom
    change (structureFunctor S).map ξ.obj.obj.hom = eqToHom (hF.trans hG.symm)
    rw [hfac]
    simp [hG]

/-- The explicit construction is a 2-fibre product in the associated `(2,1)`-category
over `C`. -/
theorem twoFibreProductOver_is_twoFibreProduct {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) :
    IsTwoFibreProductOverDiagram (twoFibreProductOverDiagram F G) := by
  let D := twoFibreProductOverDiagram F G
  change IsTwoFibreProductOverDiagram D
  intro W _ K
  let γ : W ⥤ TwoFibreProductOverCategory F G := {
    obj := fun Z => by
      let q : IsoComma (overFunctor F) (overFunctor G) :=
        { obj :=
            { left := K.left.obj Z
              right := K.right.obj Z
              hom := K.comparison.hom.app Z }
          property := by
            change IsIso (K.comparison.hom.app Z)
            infer_instance }
      exact ⟨q, by
        refine ⟨K.base.obj Z, ?_, ?_, ?_⟩
        · change (structureFunctor X).obj (K.left.obj Z) = K.base.obj Z
          exact congrArg (fun H : W ⥤ C => H.obj Z) K.left_over
        · change (structureFunctor Y).obj (K.right.obj Z) = K.base.obj Z
          exact congrArg (fun H : W ⥤ C => H.obj Z) K.right_over
        · have hF :
              (structureFunctor S).obj ((overFunctor F).obj (K.left.obj Z)) =
                K.base.obj Z := by
            change (overFunctor F ⋙ structureFunctor S).obj (K.left.obj Z) =
              K.base.obj Z
            rw [congrArg (fun H : X.left ⥤ C => H.obj (K.left.obj Z))
              (overFunctor_comm F)]
            exact congrArg (fun H : W ⥤ C => H.obj Z) K.left_over
          have hG :
              (structureFunctor S).obj ((overFunctor G).obj (K.right.obj Z)) =
                K.base.obj Z := by
            change (overFunctor G ⋙ structureFunctor S).obj (K.right.obj Z) =
              K.base.obj Z
            rw [congrArg (fun H : Y.left ⥤ C => H.obj (K.right.obj Z))
              (overFunctor_comm G)]
            exact congrArg (fun H : W ⥤ C => H.obj Z) K.right_over
          apply IsHomLift.of_fac' (structureFunctor S) (𝟙 (K.base.obj Z))
            (K.comparison.hom.app Z) hF hG
          have hv := K.comparison_vertical Z
          change (structureFunctor S).map (K.comparison.hom.app Z) =
            eqToHom (K.comparison_base Z) at hv
          rw [hv]
          simp }
    map := fun {Z Z'} f =>
      ObjectProperty.homMk {
        left := K.left.map f
        right := K.right.map f
        w := by simpa [Functor.comp] using K.comparison.hom.naturality f }
    map_id := by
      intro Z
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext <;> simp
    map_comp := by
      intro Z Z' Z'' f g
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext <;> simp }
  let α : K.left ≅ γ ⋙ D.left :=
    NatIso.ofComponents (fun Z => eqToIso (by rfl)) (by
      intro Z Z' f
      simp [γ, D, twoFibreProductOverDiagram, twoFibreProductOverLeft])
  let β : K.right ≅ γ ⋙ D.right :=
    NatIso.ofComponents (fun Z => eqToIso (by rfl)) (by
      intro Z Z' f
      simp [γ, D, twoFibreProductOverDiagram, twoFibreProductOverRight])
  constructor
  · refine ⟨{
      functor := γ
      over := by
        apply Functor.ext
        · intro Z
          have h := congrArg (fun H : W ⥤ C => H.obj Z) K.left_over
          simpa [D, twoFibreProductOverDiagram, twoFibreProductOverLeft, γ] using h
        · intro Z Z' f
          have h := congrArg (fun H : W ⥤ C => H.map f) K.left_over
          simpa [D, twoFibreProductOverDiagram, twoFibreProductOverLeft, γ] using h
      left := α.hom
      left_isIso := by infer_instance
      right := β.hom
      right_isIso := by infer_instance
      left_base := by intro Z; rfl
      right_base := by intro Z; rfl
      left_vertical := by
        intro Z
        dsimp [α]
        simp
      right_vertical := by
        intro Z
        dsimp [β]
        simp
      commutes := by
        apply NatTrans.ext
        funext Z
        simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
          Functor.whiskerRight_app, Functor.associator_hom_app,
          Functor.whiskerLeft_app]
        have hα : α.hom.app Z = 𝟙 (K.left.obj Z) := by
          dsimp [α]
          rfl
        have hβ : β.hom.app Z = 𝟙 (K.right.obj Z) := by
          dsimp [β]
          rfl
        have hcomp : D.comparison.hom.app (γ.obj Z) = K.comparison.hom.app Z := by
          change (twoFibreProductOverComparison F G).hom.app (γ.obj Z) = _
          exact twoFibreProductOverComparison_app _
        rw [hα, hβ, hcomp]
        simp }⟩
  · intro L₁ L₂
    let e₁ : K.left ≅ L₁.functor ⋙ D.left := asIso L₁.left
    let e₂ : K.left ≅ L₂.functor ⋙ D.left := asIso L₂.left
    let f₁ : K.right ≅ L₁.functor ⋙ D.right := asIso L₁.right
    let f₂ : K.right ≅ L₂.functor ⋙ D.right := asIso L₂.right
    let δ : L₁.functor ≅ L₂.functor :=
      NatIso.ofComponents (fun Z => by
        let l : (L₁.functor.obj Z).obj.obj.left ≅
            (L₂.functor.obj Z).obj.obj.left :=
          (e₁.app Z).symm ≪≫ e₂.app Z
        let r : (L₁.functor.obj Z).obj.obj.right ≅
            (L₂.functor.obj Z).obj.obj.right :=
          (f₁.app Z).symm ≪≫ f₂.app Z
        let γ₁hom := (L₁.functor.obj Z).obj.obj.hom
        let γ₂hom := (L₂.functor.obj Z).obj.obj.hom
        have h₁X := congrArg (fun t => t.app Z) L₁.commutes
        have h₂X := congrArg (fun t => t.app Z) L₂.commutes
        simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
          Functor.whiskerRight_app, Functor.associator_hom_app,
          Functor.whiskerLeft_app] at h₁X h₂X
        have h₁X' :
            (overFunctor F).map (e₁.hom.app Z) ≫ γ₁hom =
              K.comparison.hom.app Z ≫ (overFunctor G).map (f₁.hom.app Z) := by
          simpa [e₁, f₁, D, twoFibreProductOverDiagram,
            twoFibreProductOverComparison, twoFibreProductOverComparison_app,
            Functor.comp_obj, Category.assoc] using h₁X
        have h₂X' :
            (overFunctor F).map (e₂.hom.app Z) ≫ γ₂hom =
              K.comparison.hom.app Z ≫ (overFunctor G).map (f₂.hom.app Z) := by
          simpa [e₂, f₂, D, twoFibreProductOverDiagram,
            twoFibreProductOverComparison, twoFibreProductOverComparison_app,
            Functor.comp_obj, Category.assoc] using h₂X
        have h₁' :
            (overFunctor F).map (e₁.inv.app Z) ≫ K.comparison.hom.app Z =
              γ₁hom ≫ (overFunctor G).map (f₁.inv.app Z) := by
          apply (cancel_mono ((overFunctor G).map (f₁.hom.app Z))).1
          rw [← h₁X']
          rw [← Category.assoc, ← Functor.map_comp, e₁.inv_hom_id_app, Functor.map_id,
            Category.id_comp]
          rw [← Category.assoc, ← Functor.map_comp, f₁.inv_hom_id_app, Functor.map_id,
            Category.comp_id]
        exact ObjectProperty.isoMk _
          (Comma.isoMk l r (by
            change (overFunctor F).map l.hom ≫ γ₂hom =
              γ₁hom ≫ (overFunctor G).map r.hom
            dsimp [l, r]
            simp only [Functor.map_comp, Category.assoc]
            rw [h₂X']
            rw [h₁']
            simp only [← Functor.map_comp, Category.assoc]))) (by
      intro Z Z' f
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext
      · simp only [Functor.comp_map, Category.assoc]
        rw [e₁.inv.naturality_assoc, e₂.hom.naturality]
      · simp only [Functor.comp_map, Category.assoc]
        rw [f₁.inv.naturality_assoc, f₂.hom.naturality])
    refine ⟨δ.hom, ?_, ?_⟩
    · refine ⟨inferInstance, ?_, ?_, ?_⟩
      · intro Z
        have h₁inv :
            (structureFunctor X).map (e₁.inv.app Z) =
              eqToHom (L₁.left_base Z).symm := by
          apply (cancel_mono ((structureFunctor X).map (e₁.hom.app Z))).1
          rw [← Functor.map_comp, e₁.inv_hom_id_app]
          rw [L₁.left_vertical Z]
          simp
        change (structureFunctor X).map
            (e₁.inv.app Z ≫ e₂.hom.app Z) = _
        rw [Functor.map_comp, h₁inv, L₂.left_vertical Z]
        simp [eqToHom_trans]
      · apply NatTrans.ext
        funext Z
        change e₁.hom.app Z ≫
            (e₁.inv.app Z ≫ e₂.hom.app Z) = e₂.hom.app Z
        simp [Category.assoc]
      · apply NatTrans.ext
        funext Z
        change f₁.hom.app Z ≫
            (f₁.inv.app Z ≫ f₂.hom.app Z) = f₂.hom.app Z
        simp [Category.assoc]
    · intro η hη
      apply NatTrans.ext
      funext Z
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext
      · have hx := congrArg (fun t => t.app Z) hη.2.2.1
        apply (cancel_epi (e₁.hom.app Z)).1
        dsimp [δ]
        simpa [Functor.comp_map, Category.assoc] using hx
      · have hx := congrArg (fun t => t.app Z) hη.2.2.2
        apply (cancel_epi (f₁.hom.app Z)).1
        dsimp [δ]
        simpa [Functor.comp_map, Category.assoc] using hx

theorem categoriesOver_have_twoFibreProducts {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) :
    IsTwoFibreProductOverDiagram (twoFibreProductOverDiagram F G) :=
  twoFibreProductOver_is_twoFibreProduct F G

/- The source writes the following as an equality of fibre categories.  The
   canonical Lean interface is an equivalence: the explicit presentation
   remembers a witnessing base object, whereas `Functor.Fiber` records only
   its equality proof. -/
abbrev twoFibreProductOverBaseFunctor {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) :
    TwoFibreProductOverCategory F G ⥤ C :=
  twoFibreProductOverLeft F G ⋙ structureFunctor X

abbrev twoFibreProductOverFibreCategory {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) (U : C) :=
  IsoComma (overMorphismFiberFunctor F U) (overMorphismFiberFunctor G U)

theorem twoFibreProductOver_fibre_equivalent {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) (U : C) :
    Nonempty (Functor.Fiber (twoFibreProductOverBaseFunctor F G) U ≌
      twoFibreProductOverFibreCategory F G U) := by
  let A :
      Functor.Fiber (twoFibreProductOverBaseFunctor F G) U ⥤
        twoFibreProductOverFibreCategory F G U := {
    obj := fun z => by
      have hxU := z.2
      change (structureFunctor X).obj z.1.obj.obj.left = U at hxU
      let V : C := Classical.choose z.1.property
      have hV := Classical.choose_spec z.1.property
      have hx := hV.1
      have hy := hV.2.1
      have hξ := hV.2.2
      have hVU : Classical.choose z.1.property = U := hx.symm.trans hxU
      have hyU : (structureFunctor Y).obj z.1.obj.obj.right = U :=
        hy.trans (hx.symm.trans hxU)
      have hξU : IsMorphismLift (structureFunctor S) (𝟙 U)
          z.1.obj.obj.hom := by
        rw [hVU] at hξ
        exact hξ
      let x : FibreCategory (structureFunctor X) U :=
        ⟨z.1.obj.obj.left, hxU⟩
      let y : FibreCategory (structureFunctor Y) U :=
        ⟨z.1.obj.obj.right, hyU⟩
      let k := z.1.obj.obj.hom
      let h : (overMorphismFiberFunctor F U).obj x ⟶
          (overMorphismFiberFunctor G U).obj y :=
        ⟨k, hξU⟩
      exact ⟨⟨x, y, h⟩, by
        change IsIso h
        letI hk : IsIso k := z.1.obj.property
        letI : (structureFunctor S).IsHomLift (𝟙 U) k := hξU
        let hinv : (structureFunctor S).IsHomLift (𝟙 U)
            (inv k) :=
          IsHomLift.lift_id_inv_isIso (structureFunctor S) U k
        let hInv : (overMorphismFiberFunctor G U).obj y ⟶
            (overMorphismFiberFunctor F U).obj x :=
          ⟨@CategoryTheory.inv _ _ _ _ k hk, hinv⟩
        constructor
        refine ⟨hInv, ?_, ?_⟩
        · apply Functor.Fiber.hom_ext
          change k ≫ @CategoryTheory.inv _ _ _ _ k hk = 𝟙 _
          exact IsIso.hom_inv_id k
        · apply Functor.Fiber.hom_ext
          change @CategoryTheory.inv _ _ _ _ k hk ≫ k = 𝟙 _
          exact IsIso.inv_hom_id k⟩
    map := fun {z z'} f => by
      have hxU : (structureFunctor X).obj z.1.obj.obj.left = U := z.2
      have hxU' : (structureFunctor X).obj z'.1.obj.obj.left = U := z'.2
      let _ : (twoFibreProductOverBaseFunctor F G).IsHomLift (𝟙 U) f.1 := f.2
      have hleft : IsMorphismLift (structureFunctor X) (𝟙 U) f.1.hom.hom.left := by
        apply IsHomLift.of_fac' (structureFunctor X) (𝟙 U) f.1.hom.hom.left hxU hxU'
        have hfac := IsHomLift.fac' (twoFibreProductOverBaseFunctor F G)
          (𝟙 U) f.1
        change (structureFunctor X).map f.1.hom.hom.left = _ at hfac
        exact hfac
      have hyU : (structureFunctor Y).obj z.1.obj.obj.right = U := by
        have hV := Classical.choose_spec z.1.property
        have hx := hV.1
        have hy := hV.2.1
        exact hy.trans (hx.symm.trans hxU)
      have hyU' : (structureFunctor Y).obj z'.1.obj.obj.right = U := by
        have hV := Classical.choose_spec z'.1.property
        have hx := hV.1
        have hy := hV.2.1
        exact hy.trans (hx.symm.trans hxU')
      have hright : IsMorphismLift (structureFunctor Y) (𝟙 U) f.1.hom.hom.right := by
        apply IsHomLift.of_fac' (structureFunctor Y) (𝟙 U) f.1.hom.hom.right hyU hyU'
        have hfac := IsHomLift.fac' (twoFibreProductOverBaseFunctor F G)
          (𝟙 U) f.1
        have hfac' : (twoFibreProductOverDiagram F G).base.map f.1 =
            eqToHom hxU ≫ 𝟙 U ≫ eqToHom hxU'.symm := by
          change (twoFibreProductOverBaseFunctor F G).map f.1 = _
          exact hfac
        have hro :
            Functor.congr_obj (twoFibreProductOverDiagram F G).right_over z.1 =
              hyU.trans hxU.symm := by
          apply Subsingleton.elim
        have hro' :
            Functor.congr_obj (twoFibreProductOverDiagram F G).right_over z'.1 =
              hyU'.trans hxU'.symm := by
          apply Subsingleton.elim
        have hbase := Functor.congr_hom
          (twoFibreProductOverDiagram F G).right_over f.1
        change (structureFunctor Y).map f.1.hom.hom.right = _ at hbase
        rw [hro, hro'] at hbase
        change (structureFunctor Y).map f.1.hom.hom.right = _
        rw [hbase]
        rw [hfac']
        change eqToHom (hyU.trans hxU.symm) ≫
            (eqToHom hxU ≫ 𝟙 U ≫ eqToHom hxU'.symm) ≫
              eqToHom (hyU'.trans hxU'.symm).symm =
            eqToHom hyU ≫ 𝟙 U ≫ eqToHom hyU'.symm
        simp [eqToHom_trans, Category.assoc]
      refine ⟨{
        left := ⟨f.1.hom.hom.left, hleft⟩
        right := ⟨f.1.hom.hom.right, hright⟩
        w := ?_ }⟩
      apply Functor.Fiber.hom_ext
      exact f.1.hom.hom.w
    map_id := by
      intro z
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext
      · apply Functor.Fiber.hom_ext
        change (𝟙 z : z ⟶ z).1.hom.hom.left = 𝟙 _
        rfl
      · apply Functor.Fiber.hom_ext
        change (𝟙 z : z ⟶ z).1.hom.hom.right = 𝟙 _
        rfl
    map_comp := by
      intro z z' z'' f g
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext
      · apply Functor.Fiber.hom_ext
        change (f ≫ g).1.hom.hom.left = f.1.hom.hom.left ≫ g.1.hom.hom.left
        rfl
      · apply Functor.Fiber.hom_ext
        change (f ≫ g).1.hom.hom.right = f.1.hom.hom.right ≫ g.1.hom.hom.right
        rfl }
  let R :
      twoFibreProductOverFibreCategory F G U ⥤
        Functor.Fiber (twoFibreProductOverBaseFunctor F G) U := {
    obj := fun ξ => by
      let q : IsoComma (overFunctor F) (overFunctor G) :=
        { obj :=
            { left := ξ.obj.left.1
              right := ξ.obj.right.1
              hom := ξ.obj.hom.1 }
          property := by
            letI hξ : IsIso ξ.obj.hom := ξ.property
            change IsIso (Functor.Fiber.fiberInclusion.map ξ.obj.hom)
            infer_instance }
      let z : TwoFibreProductOverCategory F G :=
        ⟨q, by
          refine ⟨U, ξ.obj.left.2, ξ.obj.right.2, ξ.obj.hom.2⟩⟩
      exact ⟨z, ξ.obj.left.2⟩
    map := fun {ξ ξ'} f => by
      refine ⟨ObjectProperty.homMk (P := TwoFibreProductOverProperty F G) {
        left := f.hom.hom.left.1
        right := f.hom.hom.right.1
        w := ?_ }, ?_⟩
      · have hw := congrArg
          (fun k => Functor.Fiber.fiberInclusion.map k) f.hom.hom.w
        simpa [overMorphismFiberFunctor] using hw
      · change IsMorphismLift (twoFibreProductOverBaseFunctor F G) (𝟙 U)
          f.hom.hom.left.1
        exact f.hom.hom.left.2
    map_id := by
      intro z
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext
      · apply Functor.Fiber.hom_ext
        change (𝟙 z : z ⟶ z).1.hom.hom.left = 𝟙 _
        rfl
      · apply Functor.Fiber.hom_ext
        change (𝟙 z : z ⟶ z).1.hom.hom.right = 𝟙 _
        rfl
    map_comp := by
      intro z z' z'' f g
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext
      · apply Functor.Fiber.hom_ext
        change (f ≫ g).1.hom.hom.left = f.1.hom.hom.left ≫ g.1.hom.hom.left
        rfl
      · apply Functor.Fiber.hom_ext
        change (f ≫ g).1.hom.hom.right = f.1.hom.hom.right ≫ g.1.hom.hom.right
        rfl }
  let unitIso : 𝟭 (Functor.Fiber (twoFibreProductOverBaseFunctor F G) U) ≅
      A ⋙ R :=
    NatIso.ofComponents (fun z => eqToIso (by rfl)) (by
      intro z z' f
      apply Functor.Fiber.hom_ext
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext <;> rfl)
  let counitIso : R ⋙ A ≅
      𝟭 (twoFibreProductOverFibreCategory F G U) :=
    NatIso.ofComponents (fun ξ => eqToIso (by rfl)) (by
      intro ξ ξ' f
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext
      · apply Functor.Fiber.hom_ext
        rfl
      · apply Functor.Fiber.hom_ext
        rfl)
  exact ⟨Equivalence.mk A R unitIso counitIso⟩

/-! ## The comparison example -/

/- `SingleObj` uses multiplication for composition, so the additive group
   `ZMod 2` is tagged multiplicatively to obtain a genuine two-arrow groupoid. -/
abbrev TwoArrowCategory := SingleObj (Multiplicative (ZMod 2))
abbrev OneObjectDiscreteCategory := Discrete Unit

def oneObjectToTwoArrowCategory : OneObjectDiscreteCategory ⥤ TwoArrowCategory where
  obj _ := SingleObj.star (Multiplicative (ZMod 2))
  map _ := 𝟙 (SingleObj.star (Multiplicative (ZMod 2)))
  map_id := by intros; simp
  map_comp := by intros; simp

abbrev ordinaryExampleTwoFibreProduct :=
  IsoComma oneObjectToTwoArrowCategory oneObjectToTwoArrowCategory

theorem ordinary_example_twoFibreProduct_is_discrete_two_objects :
    Nonempty (ordinaryExampleTwoFibreProduct ≌ Discrete (ZMod 2)) := by
  let E : ordinaryExampleTwoFibreProduct ⥤ Discrete (ZMod 2) := {
    obj := fun ξ => Discrete.mk ξ.obj.hom.toAdd
    map := fun f => Discrete.eqToHom (by
      have h := f.hom.w
      simpa [oneObjectToTwoArrowCategory] using
        congrArg Multiplicative.toAdd h.symm)
    map_id := by
      intro ξ
      simp
    map_comp := by
      intro ξ₁ ξ₂ ξ₃ f g
      simp }
  let R : Discrete (ZMod 2) ⥤ ordinaryExampleTwoFibreProduct := {
    obj := fun x => ⟨
        Comma.mk (Discrete.mk ()) (Discrete.mk ())
          (SingleObj.toEnd (Multiplicative (ZMod 2))
            (Multiplicative.ofAdd x.as)), by
          change IsIso (SingleObj.toEnd (Multiplicative (ZMod 2))
            (Multiplicative.ofAdd x.as))
          infer_instance⟩
    map := fun f => ⟨{
      left := 𝟙 _
      right := 𝟙 _
      w := by
        have h := congrArg Multiplicative.ofAdd (Discrete.eq_of_hom f)
        simpa [oneObjectToTwoArrowCategory, SingleObj.toEnd_def] using h.symm }⟩
    map_id := by
      intro x
      ext <;> simp
    map_comp := by
      intro x y z f g
      ext <;> simp }
  let unitIso : 𝟭 ordinaryExampleTwoFibreProduct ≅ E ⋙ R :=
    NatIso.ofComponents (fun ξ => eqToIso (by
      apply ObjectProperty.FullSubcategory.ext
      simp [E, R, SingleObj.toEnd_def])) (by
      intros
      apply ObjectProperty.hom_ext
      ext <;> apply Subsingleton.elim)
  let counitIso : R ⋙ E ≅ 𝟭 (Discrete (ZMod 2)) :=
    NatIso.ofComponents (fun x => eqToIso (by
      apply Discrete.ext
      simp [E, R, SingleObj.toEnd_def])) (by
        intros
        apply Subsingleton.elim)
  exact ⟨Equivalence.mk' E R unitIso counitIso (by
    intro ξ
    apply Subsingleton.elim)⟩

abbrev exampleBaseCategory : Cat := Cat.of TwoArrowCategory

def exampleSourceOver : CategoryOver exampleBaseCategory :=
  CategoryOver.of oneObjectToTwoArrowCategory.toCatHom

def exampleTargetOver : CategoryOver exampleBaseCategory :=
  CategoryOver.of (𝟙 exampleBaseCategory)

def exampleOverMorphism : CategoryOverHom exampleSourceOver exampleTargetOver :=
  ⟨Over.homMk (U := exampleSourceOver.toOver) (V := exampleTargetOver.toOver)
      oneObjectToTwoArrowCategory.toCatHom (by
        simp [exampleSourceOver, exampleTargetOver, CategoryOver.of])⟩

abbrev overExampleTwoFibreProduct :=
  TwoFibreProductOverCategory exampleOverMorphism exampleOverMorphism

theorem over_example_twoFibreProduct_is_discrete_one_object :
    Nonempty (overExampleTwoFibreProduct ≌ Discrete Unit) := by
  let E : overExampleTwoFibreProduct ⥤ Discrete Unit := {
    obj := fun _ => Discrete.mk ()
    map := fun _ => 𝟙 _
    map_id := by intros; simp
    map_comp := by intros; simp }
  let R : Discrete Unit ⥤ overExampleTwoFibreProduct := {
    obj := fun _ => ⟨
      ⟨Comma.mk (L := overFunctor exampleOverMorphism)
          (R := overFunctor exampleOverMorphism)
          (Discrete.mk ()) (Discrete.mk ()) (𝟙 _), by
            change IsIso (𝟙 _)
            infer_instance⟩, by
        refine ⟨SingleObj.star (Multiplicative (ZMod 2)), ?_, ?_, ?_⟩
        · rfl
        · rfl
        · apply IsHomLift.id
          rfl⟩
    map := fun f => ⟨⟨{
      left := 𝟙 _
      right := 𝟙 _
      w := by simp }⟩⟩
    map_id := by intro; ext <;> simp
    map_comp := by
      intros
      ext <;> change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ <;>
        exact (Category.id_comp (𝟙 _)).symm }
  let unitIso : 𝟭 overExampleTwoFibreProduct ≅ E ⋙ R :=
    NatIso.ofComponents (fun ξ => eqToIso (by
      apply ObjectProperty.FullSubcategory.ext
      apply ObjectProperty.FullSubcategory.ext
      rcases ξ with ⟨⟨⟨left, right, hom⟩, hiso⟩, hproperty⟩
      rcases left with ⟨⟨⟩⟩
      rcases right with ⟨⟨⟩⟩
      rcases hproperty with ⟨U, hx, hy, hξ⟩
      have hU : U = SingleObj.star (Multiplicative (ZMod 2)) :=
        by
          cases U
          rfl
      let _ : (structureFunctor exampleTargetOver).IsHomLift
          (𝟙 U) hom := hξ
      have hfac := IsHomLift.fac' (structureFunctor exampleTargetOver)
        (𝟙 U) hom
      have hdom := IsHomLift.domain_eq (structureFunctor exampleTargetOver)
        (𝟙 U) hom
      have hcod := IsHomLift.codomain_eq (structureFunctor exampleTargetOver)
        (𝟙 U) hom
      have hhom : hom = 𝟙 _ := by
        subst U
        cases hξ
        rfl
      cases hhom
      rfl)) (by
      intros
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      have source_hom_ext : ∀ {a b : exampleSourceOver.left} (f g : a ⟶ b), f = g := by
        intro a b f g
        dsimp [exampleSourceOver, CategoryOver.of, Cat.of] at f g ⊢
        change Discrete Unit at a b
        exact @Subsingleton.elim (a ⟶ b) (Discrete.instSubsingletonDiscreteHom a b) f g
      apply CommaMorphism.ext <;> simp [E, R, exampleSourceOver,
        exampleTargetOver, CategoryOver.of, exampleOverMorphism,
        oneObjectToTwoArrowCategory] <;> apply source_hom_ext)
  let counitIso : R ⋙ E ≅ 𝟭 (Discrete Unit) :=
    NatIso.ofComponents (fun x => eqToIso (by
      apply Discrete.ext
      simp [E, R])) (by
        intros
        apply Subsingleton.elim)
  exact ⟨Equivalence.mk' E R unitIso counitIso (by
    intro ξ
    apply Subsingleton.elim)⟩

theorem different_twoFibreProducts_example :
    ¬ Nonempty (ordinaryExampleTwoFibreProduct ≌ overExampleTwoFibreProduct) := by
  rintro ⟨e⟩
  obtain ⟨e₁⟩ := ordinary_example_twoFibreProduct_is_discrete_two_objects
  obtain ⟨e₂⟩ := over_example_twoFibreProduct_is_discrete_one_object
  let e₃ := e₁.symm.trans (e.trans e₂)
  let f :
      e₃.functor.obj (Discrete.mk (0 : ZMod 2)) ⟶
        e₃.functor.obj (Discrete.mk (1 : ZMod 2)) :=
    Discrete.eqToHom (by
      exact Subsingleton.elim _ _)
  let g := e₃.functor.preimage f
  have hz : (0 : ZMod 2) = 1 := by
    simpa using Discrete.eq_of_hom g
  exact (by decide : (0 : ZMod 2) ≠ 1) hz

end Formalization.Books.Categories.Unit32
