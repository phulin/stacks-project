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
        sorry }
  comp η θ :=
    { toNatTrans := η.toNatTrans ≫ θ.toNatTrans
      over := by
        intro Z
        sorry }
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
      sorry }

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
      sorry }

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
      sorry }

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
        sorry }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

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
        sorry)
  leftUnitor F :=
    overNatIsoOfUnderlying (Functor.leftUnitor (overFunctor F)) (by
      intro Z
      sorry)
  rightUnitor F :=
    overNatIsoOfUnderlying (Functor.rightUnitor (overFunctor F)) (by
      intro Z
      sorry)
  whiskerLeft_id := by sorry
  whiskerLeft_comp := by sorry
  id_whiskerLeft := by sorry
  comp_whiskerLeft := by sorry
  id_whiskerRight := by sorry
  comp_whiskerRight := by sorry
  whiskerRight_id := by sorry
  whiskerRight_comp := by sorry
  whisker_assoc := by sorry
  whisker_exchange := by sorry
  pentagon := by sorry
  triangle := by sorry

/- The source uses the strict convention for this 2-category. -/
noncomputable instance categoriesOverStrict {C : Cat.{v, u}} :
    Bicategory.Strict (CategoryOver C) := by
  sorry

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
  map φ :=
    ⟨(overFunctor F).map φ.1, by
      sorry⟩
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
      sorry⟩
  naturality := by
    sorry

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
  sorry

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
  sorry

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
  right_over := by sorry
  comparison := twoFibreProductOverComparison F G
  comparison_base := by sorry
  comparison_vertical := by sorry

/-- The explicit construction is a 2-fibre product in the associated `(2,1)`-category
over `C`. -/
theorem twoFibreProductOver_is_twoFibreProduct {C : Cat.{v, u}}
    {X Y S : CategoryOver C} (F : CategoryOverHom X S)
    (G : CategoryOverHom Y S) :
    IsTwoFibreProductOverDiagram (twoFibreProductOverDiagram F G) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem different_twoFibreProducts_example :
    ¬ Nonempty (ordinaryExampleTwoFibreProduct ≌ overExampleTwoFibreProduct) := by
  sorry

end Formalization.Books.Categories.Unit32
