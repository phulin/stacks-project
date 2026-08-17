import Formalization.Books.Categories.Unit32.CategoriesOverCategories
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Categories, Chapter 33: Fibred categories

The source uses the universal-property definition of a strongly cartesian
morphism.  Mathlib has that definition, its factorisation API, and the
equivalent `IsFibered` interface already in
`CategoryTheory.FiberedCategory`; this file keeps those declarations as the
mathematical primitives.  The records below package the extra source-facing
data (chosen pullbacks, morphisms over a fixed base, and the final
factorisation statement).
-/

namespace Formalization.Books.Categories.Unit33

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit32

universe u₁ v₁ u₂ v₂ w v u

noncomputable section

/-! ## Strongly cartesian morphisms -/

theorem fibred_category_iff_exists_stronglyCartesian
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    p.IsFibered ↔
      ∀ (x : X) (R : C) (f : R ⟶ p.obj x),
        ∃ (y : X) (φ : y ⟶ x), Functor.IsStronglyCartesian p f φ := by
  constructor
  · intro hp x R f
    obtain ⟨y, φ, hφ⟩ := hp.toIsPreFibered.exists_isCartesian' f
    exact ⟨y, φ, @Functor.IsFibered.isStronglyCartesian_of_isCartesian
      _ _ _ _ p hp _ _ f _ _ φ hφ⟩
  · exact Functor.IsFibered.of_exists_isStronglyCartesian

theorem stronglyCartesian_comp
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C)
    {R S T : C} {a b c : X} {f : R ⟶ S} {g : S ⟶ T}
    {φ : a ⟶ b} {ψ : b ⟶ c}
    [Functor.IsStronglyCartesian p f φ]
    [Functor.IsStronglyCartesian p g ψ] :
    Functor.IsStronglyCartesian p (f ≫ g) (φ ≫ ψ) := by
  infer_instance

theorem iso_is_stronglyCartesian
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C)
    {R S : C} {a b : X} (f : R ⟶ S) (e : a ≅ b)
    [p.IsHomLift f e.hom] :
    Functor.IsStronglyCartesian p f e.hom := by
  infer_instance

theorem stronglyCartesian_of_base_isIso
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C)
    {R S : C} {a b : X} (f : R ⟶ S) (φ : a ⟶ b)
    [Functor.IsStronglyCartesian p f φ] [IsIso f] :
    IsIso φ := by
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p f φ

theorem stronglyCartesian_over_composition
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B) (G : B ⥤ C) {a b : A} (φ : a ⟶ b)
    [Functor.IsStronglyCartesian F (F.map φ) φ]
    [Functor.IsStronglyCartesian G (G.map (F.map φ)) (F.map φ)] :
    Functor.IsStronglyCartesian (F ⋙ G) ((F ⋙ G).map φ) φ := by
  sorry

theorem stronglyCartesian_fibre_product
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) {x y z : X} (f : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map f) f]
    {P : C} {π₁ : P ⟶ p.obj x} {π₂ : P ⟶ p.obj z}
    (hP : IsPullback π₁ π₂ (p.map f) (p.map g))
    (w : X) (a : w ⟶ z)
    [Functor.IsStronglyCartesian p π₂ a] :
    ∃ b : w ⟶ x, IsPullback b a f g := by
  sorry

/-! ## Pullbacks in a fibred category -/

/- A choice of pullbacks is a choice of a strongly cartesian lift for every
   object in every fibre.  `Functor.Fiber` is Mathlib's canonical fibre
   category, so no second fibre-category construction is introduced here. -/
structure PullbackChoice
    {X : Type u₁} {C : Type u₂} [Category.{v₁} X] [Category.{v₂} C]
    (p : X ⥤ C) [p.IsFibered] where
  pullback : ∀ {R S : C} (_f : R ⟶ S) (_x : Functor.Fiber p S),
    Functor.Fiber p R
  pullbackMap : ∀ {R S : C} (f : R ⟶ S) (x : Functor.Fiber p S),
    (Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ X).obj (pullback f x) ⟶ x.1
  pullbackMap_isStronglyCartesian : ∀ {R S : C} (f : R ⟶ S)
    (x : Functor.Fiber p S),
    Functor.IsStronglyCartesian p f (pullbackMap f x)

attribute [instance] PullbackChoice.pullbackMap_isStronglyCartesian

namespace PullbackChoice

variable {X : Type u₁} {C : Type u₂} [Category.{v₁} X] [Category.{v₂} C]
variable {p : X ⥤ C} [p.IsFibered]

/- Mathlib's chosen Cartesian lift is converted to a strongly Cartesian lift
   using the canonical `IsFibered` instance. -/
noncomputable def default (p : X ⥤ C) [p.IsFibered] : PullbackChoice p where
  pullback f x := Functor.Fiber.mk (Functor.IsPreFibered.pullbackObj_proj (p := p) x.2 f)
  pullbackMap f x := Functor.IsPreFibered.pullbackMap (p := p) x.2 f
  pullbackMap_isStronglyCartesian f x := by
    exact @Functor.IsFibered.isStronglyCartesian_of_isCartesian
      _ _ _ _ p inferInstance _ _ f _ _
      (Functor.IsPreFibered.pullbackMap (p := p) x.2 f)
      (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 f)

theorem exists_choice (p : X ⥤ C) [p.IsFibered] : Nonempty (PullbackChoice p) :=
  ⟨default p⟩

def pullbackFunctor (P : PullbackChoice p) {R S : C} (f : R ⟶ S) :
    Functor.Fiber p S ⥤ Functor.Fiber p R where
  obj x := P.pullback f x
  map {x y} φ := by
    letI : Functor.IsStronglyCartesian p f (P.pullbackMap f y) :=
      P.pullbackMap_isStronglyCartesian f y
    letI : Functor.IsStronglyCartesian p f (P.pullbackMap f x) :=
      P.pullbackMap_isStronglyCartesian f x
    haveI : p.IsHomLift (𝟙 S) φ.1 := φ.2
    have hφ' : p.IsHomLift f (P.pullbackMap f x ≫ φ.1) :=
      IsHomLift.comp_lift_id_right' p f (P.pullbackMap f x) S φ.1
    have hf : f = 𝟙 R ≫ f := by simp
    refine ⟨@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ f
      (P.pullbackMap f y) _ _ _ (𝟙 R) f hf (P.pullbackMap f x ≫ φ.1)
      hφ', ?_⟩
    exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _ f
      (P.pullbackMap f y) _ _ _ (𝟙 R) f hf (P.pullbackMap f x ≫ φ.1)
      hφ'
  map_id := by
    intro x
    apply Functor.Fiber.hom_ext
    sorry
  map_comp := by
    intro x y z φ ψ
    apply Functor.Fiber.hom_ext
    sorry

def IsUnital (P : PullbackChoice p) : Prop :=
  ∀ (U : C) (x : Functor.Fiber p U), P.pullback (𝟙 U) x = x

theorem exists_unital (p : X ⥤ C) [p.IsFibered] :
    ∃ P : PullbackChoice p, P.IsUnital := by
  sorry

end PullbackChoice

theorem pullback_composition_iso
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) [p.IsFibered] (P : PullbackChoice p)
    {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    ∃! α : P.pullbackFunctor (f ≫ g) ≅
        P.pullbackFunctor g ⋙ P.pullbackFunctor f,
      ∀ x : Functor.Fiber p T,
        Functor.Fiber.fiberInclusion.map (α.hom.app x) ≫
            P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x =
          P.pullbackMap (f ≫ g) x := by
  sorry

theorem pullback_identity_iso
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C) :
    ∃! α : 𝟭 (Functor.Fiber p U) ≅ P.pullbackFunctor (𝟙 U),
      ∀ x : Functor.Fiber p U,
        Functor.Fiber.fiberInclusion.map (α.hom.app x) ≫
            P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
  sorry

/- A pseudofunctor-compatible packaging of the choice.  The object and map
   fields explicitly identify the Mathlib pseudofunctor with the fibre
   categories and the `pullbackFunctor`s above; its unit, composition, and
   coherence laws are those of Mathlib's `Pseudofunctor`. -/
structure PullbackPseudofunctorData
    {X : Type u₁} [Category.{v₁} X] {C : Type u₂} [Category.{v₂} C]
    (p : X ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  value : PseudofunctorFromCategory Cᵒᵖ
    (AssociatedTwoOneCategory (Cat.{v₁, u₁}))
  object_fibre : ∀ (U : C),
    pseudofunctorObject value (Opposite.op U) =
      Bicategory.Pith.mk (Cat.of (Functor.Fiber p U))
  map_pullback : ∀ {R S : C} (f : R ⟶ S),
    Nonempty
      (eqToHom (congrArg Bicategory.Pith.as (object_fibre S).symm) ≫
          (pseudofunctorMap value f.op).of ≫
          eqToHom (congrArg Bicategory.Pith.as (object_fibre R)) ≅
        (P.pullbackFunctor f).toCatHom)

theorem pullback_pseudofunctor_exists
    {X : Type u₁} [Category.{v₁} X] {C : Type u₂} [Category.{v₂} C]
    (p : X ⥤ C) [p.IsFibered] (P : PullbackChoice p) :
    Nonempty (PullbackPseudofunctorData p P) := by
  sorry

/-! ## Fibred categories over a fixed category -/

def MapsStronglyCartesian
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ C) (q : B ⥤ C) (F : A ⥤ B) : Prop :=
  ∀ {a b : A} (φ : a ⟶ b),
    Functor.IsStronglyCartesian p (p.map φ) φ →
      Functor.IsStronglyCartesian q (q.map (F.map φ)) (F.map φ)

/- The source's objects are fibred categories over `C`. -/
structure FibredCategoryOver (C : Cat.{v, u}) where
  underlying : CategoryOver C
  isFibred : (structureFunctor underlying).IsFibered

attribute [instance] FibredCategoryOver.isFibred

/- A source 1-morphism is a functor over `C` which preserves strongly
   cartesian arrows.  The base morphism in the target is written using the
   target structure functor; the strict triangle in `CategoryOver` identifies
   it with the source base morphism. -/
structure FibredCategoryOverHom {C : Cat.{v, u}}
    (X Y : FibredCategoryOver C) where
  underlying : CategoryOverHom X.underlying Y.underlying
  preserves : MapsStronglyCartesian
    (structureFunctor X.underlying) (structureFunctor Y.underlying)
    (overFunctor underlying)

namespace FibredCategoryOverHom

@[ext]
lemma ext {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    {F G : FibredCategoryOverHom X Y} (h : F.underlying = G.underlying) : F = G := by
  cases F
  cases G
  cases h
  rfl

def id {C : Cat.{v, u}} (X : FibredCategoryOver C) :
    FibredCategoryOverHom X X where
  underlying := CategoryOver.id X.underlying
  preserves := by
    intro a b φ hφ
    sorry

def comp {C : Cat.{v, u}} {X Y Z : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) (G : FibredCategoryOverHom Y Z) :
    FibredCategoryOverHom X Z where
  underlying := CategoryOver.comp F.underlying G.underlying
  preserves := by
    intro a b φ hφ
    sorry

end FibredCategoryOverHom

def fibredOverNatTransId {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    OverNatTrans F.underlying F.underlying :=
  { toNatTrans := 𝟙 (overFunctor F.underlying)
    over := by
      intro Z
      sorry }

def fibredOverNatTransComp {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C}
    {F G H : FibredCategoryOverHom X Y}
    (η : OverNatTrans F.underlying G.underlying)
    (θ : OverNatTrans G.underlying H.underlying) :
    OverNatTrans F.underlying H.underlying :=
  { toNatTrans := η.toNatTrans ≫ θ.toNatTrans
    over := by
      intro Z
      sorry }

instance fibredCategoryOverHomCategory {C : Cat.{v, u}}
    (X Y : FibredCategoryOver C) : Category (FibredCategoryOverHom X Y) where
  Hom F G := OverNatTrans F.underlying G.underlying
  id F := fibredOverNatTransId F
  comp η θ := fibredOverNatTransComp η θ
  id_comp := by
    intros
    apply OverNatTrans.ext
    simp [fibredOverNatTransId, fibredOverNatTransComp]
  comp_id := by
    intros
    apply OverNatTrans.ext
    simp [fibredOverNatTransId, fibredOverNatTransComp]
  assoc := by
    intros
    apply OverNatTrans.ext
    simp [fibredOverNatTransComp, Category.assoc]

/- The fixed-base 2-category is made usable as a bicategory.  The preservation
   proofs are proposition-valued and are left to the proof stage; the carrier,
   composition, whiskering, and coherence maps are the canonical ones from
   `CategoryOver`. -/
def fibredHomIsoOfUnderlying {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} {F G : FibredCategoryOverHom X Y}
  (e : F.underlying ≅ G.underlying) : F ≅ G where
  hom :=
    { toNatTrans := e.hom.toNatTrans
      over := e.hom.over }
  inv :=
    { toNatTrans := e.inv.toNatTrans
      over := e.inv.over }
  hom_inv_id := by
    apply OverNatTrans.ext
    change e.hom.toNatTrans ≫ e.inv.toNatTrans = 𝟙 (overFunctor F.underlying)
    exact congrArg (fun η : OverNatTrans F.underlying F.underlying => η.toNatTrans)
      e.hom_inv_id
  inv_hom_id := by
    apply OverNatTrans.ext
    change e.inv.toNatTrans ≫ e.hom.toNatTrans = 𝟙 (overFunctor G.underlying)
    exact congrArg (fun η : OverNatTrans G.underlying G.underlying => η.toNatTrans)
      e.inv_hom_id

def fibredWhiskerLeft {C : Cat.{v, u}}
    {X Y Z : FibredCategoryOver C} (F : FibredCategoryOverHom X Y)
    {G H : FibredCategoryOverHom Y Z}
    (η : OverNatTrans G.underlying H.underlying) :
    OverNatTrans (FibredCategoryOverHom.comp F G).underlying
      (FibredCategoryOverHom.comp F H).underlying :=
  overWhiskerLeft F.underlying η

def fibredWhiskerRight {C : Cat.{v, u}}
    {X Y Z : FibredCategoryOver C}
    {F G : FibredCategoryOverHom X Y} (η : OverNatTrans F.underlying G.underlying)
    (H : FibredCategoryOverHom Y Z) :
    OverNatTrans (FibredCategoryOverHom.comp F H).underlying
      (FibredCategoryOverHom.comp G H).underlying :=
  overWhiskerRight η H.underlying

noncomputable instance fibredCategoriesOverBicategory {C : Cat.{v, u}} :
    Bicategory (FibredCategoryOver C) where
  Hom := FibredCategoryOverHom
  id := FibredCategoryOverHom.id
  comp := FibredCategoryOverHom.comp
  homCategory := fibredCategoryOverHomCategory
  whiskerLeft := fibredWhiskerLeft
  whiskerRight := fibredWhiskerRight
  associator F G H :=
    fibredHomIsoOfUnderlying
      (overNatIsoOfUnderlying
        (by
          simpa only [overFunctor, FibredCategoryOverHom.comp, CategoryOver.comp,
            CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor] using
            Functor.associator (overFunctor F.underlying)
              (overFunctor G.underlying) (overFunctor H.underlying)))
  leftUnitor F :=
    fibredHomIsoOfUnderlying
      (overNatIsoOfUnderlying
        (Functor.leftUnitor (overFunctor F.underlying)))
  rightUnitor F :=
    fibredHomIsoOfUnderlying
      (overNatIsoOfUnderlying
        (Functor.rightUnitor (overFunctor F.underlying)))
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

noncomputable instance fibredCategoriesOverStrict {C : Cat.{v, u}} :
    Bicategory.Strict (FibredCategoryOver C) := by
  sorry

theorem fibredCategoriesOver_associated_two_one_category
    (C : Cat.{v, u}) :
    IsTwoOneCategory
      (AssociatedTwoOneCategory (FibredCategoryOver C)) := by
  infer_instance

/- Equivalence over `C`: the functors and the comparison isomorphisms are all
   morphisms in the already constructed category of categories over `C`. -/
def IsEquivalentOver {C : Cat.{v, u}}
    (X Y : CategoryOver C) : Prop :=
  ∃ (F : CategoryOverHom X Y) (G : CategoryOverHom Y X),
    Nonempty (CategoryOver.comp F G ≅ CategoryOver.id X) ∧
      Nonempty (CategoryOver.comp G F ≅ CategoryOver.id Y)

theorem equivalence_over_preserves_stronglyCartesian
    {C : Cat.{v, u}} {X Y : CategoryOver C}
    (F : CategoryOverHom X Y)
    (hF : ∃ G : CategoryOverHom Y X,
      Nonempty (CategoryOver.comp F G ≅ CategoryOver.id X) ∧
        Nonempty (CategoryOver.comp G F ≅ CategoryOver.id Y))
    {a b : X.left} (φ : a ⟶ b)
    (hφ : Functor.IsStronglyCartesian (structureFunctor X) 
      ((structureFunctor X).map φ) φ) :
    Functor.IsStronglyCartesian (structureFunctor Y)
      ((structureFunctor Y).map ((overFunctor F).map φ)) ((overFunctor F).map φ) := by
  sorry

theorem fibred_iff_equivalent_over
    {C : Cat.{v, u}} {X Y : CategoryOver C}
    (h : IsEquivalentOver X Y) :
    (structureFunctor X).IsFibered ↔ (structureFunctor Y).IsFibered := by
  sorry

/-! ## The 2-fibre product statement -/

structure FibredTwoFibreProduct {C : Cat.{v, u}}
    {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) where
  diagram : TwoFibreProductOverDiagram F.underlying G.underlying
  apex_fibred : (diagram.base).IsFibered
  left_preserves : MapsStronglyCartesian diagram.base
    (structureFunctor X.underlying) diagram.left
  right_preserves : MapsStronglyCartesian diagram.base
    (structureFunctor Y.underlying) diagram.right
  is_two_fibre_product :
    IsTwoFibreProductOverDiagram.{v, u, u₁, v₁}
      (F := F.underlying) (G := G.underlying) diagram

theorem fibred_categories_have_two_fibre_products
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredTwoFibreProduct F G) := by
  sorry

/-! ## Slices, composites, and fibre products -/

theorem fibred_over_slice
    {X C : Type*} [Category* X] [Category* C]
    (U : C) (p : X ⥤ C) (p' : X ⥤ Over U)
    (factor : p' ⋙ Over.forget U = p) [p.IsFibered] :
    p'.IsFibered := by
  sorry

theorem fibred_over_fibred
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ B) (q : B ⥤ C) [p.IsFibered] [q.IsFibered] :
    (p ⋙ q).IsFibered := by
  sorry

theorem fibred_fibre_product_goes_up
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) [p.IsFibered]
    {x y z : X} (f : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map f) f]
    [HasPullback (p.map f) (p.map g)] :
    ∃ (w : X) (a : w ⟶ z) (b : w ⟶ x),
      p.obj w = pullback (p.map f) (p.map g) ∧
        Functor.IsStronglyCartesian p (pullback.snd (p.map f) (p.map g)) a ∧
        IsPullback b a f g := by
  sorry

/-! ## The amelioration factorisation -/

/- The explicit category in the source is the full subcategory of the comma
   category `Comma (𝟭 Y) F` on arrows in a common fibre.  This reuses
   Mathlib's comma and full-subcategory constructors. -/
def ameliorationProperty {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    ObjectProperty (Comma (𝟭 Y.underlying.left) (overFunctor F.underlying)) :=
  fun ξ => ∃ U : C,
    IsObjectLift (structureFunctor Y.underlying) U ξ.left ∧
      IsObjectLift (structureFunctor X.underlying) U ξ.right ∧
        IsMorphismLift (structureFunctor Y.underlying) (𝟙 U) ξ.hom

abbrev AmeliorationCategory {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :=
  (ameliorationProperty F).FullSubcategory

/- The source's fully faithful functor `u : X ⥤ X'` sends an object to the
   identity arrow `F(x) ⟶ F(x)` in the comma presentation. -/
def ameliorationFromX {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    X.underlying.left ⥤ AmeliorationCategory F where
  obj x :=
    { obj :=
        { left := (overFunctor F.underlying).obj x
          right := x
          hom := 𝟙 ((overFunctor F.underlying).obj x) }
      property := by
        refine ⟨(structureFunctor X.underlying).obj x, ?_, rfl, ?_⟩
        · exact congrArg (fun K : X.underlying.left ⥤ C => K.obj x)
            (overFunctor_comm F.underlying)
        · exact IsHomLift.id
            (congrArg (fun K : X.underlying.left ⥤ C => K.obj x)
              (overFunctor_comm F.underlying)) }
  map f :=
    ObjectProperty.homMk
      { left := (overFunctor F.underlying).map f
        right := f
        w := by simp }
  map_id := by
    intro x
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp
  map_comp := by
    intro x y z f g
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp

theorem amelioration_object_description
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) (ξ : AmeliorationCategory F) :
    ∃ U : C,
      IsObjectLift (structureFunctor Y.underlying) U ξ.obj.left ∧
        IsObjectLift (structureFunctor X.underlying) U ξ.obj.right ∧
          IsMorphismLift (structureFunctor Y.underlying) (𝟙 U) ξ.obj.hom :=
  ξ.property

theorem amelioration_morphism_description
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y)
    {ξ ξ' : AmeliorationCategory F} (h : ξ ⟶ ξ') :
    h.hom.left ≫ ξ'.obj.hom =
      ξ.obj.hom ≫ (overFunctor F.underlying).map h.hom.right := by
  exact h.hom.w

def ameliorationToX {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    AmeliorationCategory F ⥤ X.underlying.left :=
  (ameliorationProperty F).ι ⋙ Comma.snd (𝟭 Y.underlying.left)
    (overFunctor F.underlying)

def ameliorationToY {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    AmeliorationCategory F ⥤ Y.underlying.left :=
  (ameliorationProperty F).ι ⋙ Comma.fst (𝟭 Y.underlying.left)
    (overFunctor F.underlying)

/- The explicit comma presentation carries a canonical functor to the fixed
   base via its `Y`-projection.  The source proof shows that this functor is
   fibred, even though the comma category can live in a larger universe than
   the bundled `CategoryOver` carrier. -/
def ameliorationBase {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    AmeliorationCategory F ⥤ C :=
  ameliorationToY F ⋙ structureFunctor Y.underlying

theorem ameliorationBase_isFibred {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    (ameliorationBase F).IsFibered := by
  sorry

/- The three projections and their comparison maps are packaged as a theorem
   interface.  The final field records the source's necessary correction: the
   functor `v : X' ⥤ Y` is itself a fibred functor over `Y`. -/
structure AmeliorationFactorization
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) where
  middle : FibredCategoryOver C
  u : FibredCategoryOverHom X middle
  v : FibredCategoryOverHom middle Y
  w : FibredCategoryOverHom middle X
  factorization : F = FibredCategoryOverHom.comp u v
  u_fully_faithful : Nonempty (overFunctor u.underlying).FullyFaithful
  w_left_adjoint_u : Nonempty (overFunctor w.underlying ⊣ overFunctor u.underlying)
  v_fibred_over_Y : (overFunctor v.underlying).IsFibered

theorem ameliorate_fibred_morphism
    {C : Cat.{v, u}} (X Y : FibredCategoryOver C)
    (F : FibredCategoryOverHom X Y) :
    Nonempty (AmeliorationFactorization F) := by
  sorry

end

end Formalization.Books.Categories.Unit33
