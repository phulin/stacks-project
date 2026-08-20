import Formalization.Books.Categories.Unit38.CategoriesFibredInSets
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Skeletal

/-!
# Categories, Chapter 39: Categories fibred in setoids

The source's setoids are groupoids with trivial automorphism groups.  The
fixed-base 2-category, its two-fibre products, the passage to isomorphism
classes, the inertia criterion, and the product formula are stated using the
category-over and presheaf interfaces developed in Units 32--38.
-/

namespace Formalization.Books.Categories.Unit39

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open Opposite
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit32
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit34
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit36
open Formalization.Books.Categories.Unit37
open Formalization.Books.Categories.Unit38

universe vC uC vS uS vS' uS' v u v' u' u₁ v₁

noncomputable section

/-! ## Setoids -/

/- A setoid category is a groupoid whose endomorphism monoids are trivial.
   This is the literal categorical form of the source definition; the
   equivalent thin-groupoid formulation is recorded below for use with
   Mathlib's skeleton and quotient APIs. -/
def IsSetoid (C : Type* ) [Category* C] : Prop :=
  IsGroupoid C ∧ ∀ X : C, ∀ f : X ⟶ X, f = 𝟙 X

theorem isSetoid_iff_isGroupoid_and_hom_subsingleton
    {C : Type*} [Category* C] :
    IsSetoid C ↔
      IsGroupoid C ∧ ∀ X Y : C, Subsingleton (X ⟶ Y) := by
  constructor
  · rintro ⟨hgroup, hid⟩
    refine ⟨hgroup, ?_⟩
    intro X Y
    constructor
    intro f g
    let _ : IsIso g := hgroup.all_isIso g
    have hcomp : f ≫ inv g = g ≫ inv g := by
      rw [hid X (f ≫ inv g)]
      simp
    exact (cancel_mono (inv g)).1 hcomp
  · rintro ⟨hgroup, hhom⟩
    exact ⟨hgroup, fun X f => Subsingleton.elim _ _⟩

theorem isSetoid_of_isDiscrete
    {C : Type*} [Category* C] [IsDiscrete C] : IsSetoid C := by
  exact ⟨inferInstance, fun X f => Subsingleton.elim _ _⟩

theorem isSetoid_of_groupoid_of_hom_subsingleton
    {C : Type*} [Category* C] (hC : IsGroupoid C)
    (hhom : ∀ X Y : C, Subsingleton (X ⟶ Y)) : IsSetoid C := by
  exact ⟨hC, fun X f => Subsingleton.elim _ _⟩

/- The source's concrete construction from a set with an equivalence relation.
   `PLift` makes each related hom-set a proposition with one inhabitant. -/
structure SetoidCategoryObject (X : Type*) (r : Setoid X) where
  as : X

abbrev SetoidCategory (X : Type*) (r : Setoid X) :=
  SetoidCategoryObject X r

def setoidCategoryObjectEquiv (X : Type*) (r : Setoid X) :
    SetoidCategory X r ≃ X where
  toFun A := A.as
  invFun x := ⟨x⟩
  left_inv A := by cases A; rfl
  right_inv x := rfl

instance setoidCategoryCategory (X : Type*) (r : Setoid X) :
    Category (SetoidCategory X r) where
  Hom A B := PLift (r.r A.as B.as)
  id A := ⟨r.iseqv.refl A.as⟩
  comp f g := ⟨r.iseqv.trans f.down g.down⟩
  id_comp := by
    intros A B f
    cases f
    rfl
  comp_id := by
    intros A B f
    cases f
    rfl
  assoc := by
    intros A B D E f g h
    cases f
    cases g
    cases h
    simp

instance setoidCategoryGroupoid (X : Type*) (r : Setoid X) :
    Groupoid (SetoidCategory X r) where
  inv f := ⟨r.iseqv.symm f.down⟩
  inv_comp := by
    intros A B f
    cases f
    rfl
  comp_inv := by
    intros A B f
    cases f
    rfl

theorem setoidCategory_isSetoid (X : Type*) (r : Setoid X) :
    IsSetoid (SetoidCategory X r) := by
  exact ⟨inferInstance, fun A f => by cases f; rfl⟩

theorem setoidCategory_hom_nonempty_iff
    (X : Type*) (r : Setoid X)
    (A B : SetoidCategory X r) :
    Nonempty (A ⟶ B) ↔ r.r A.as B.as := by
  constructor
  · rintro ⟨f⟩
    exact f.down
  · intro h
    exact ⟨⟨h⟩⟩

/- The object quotient used by Mathlib is the source's set of isomorphism
   classes.  `ThinSkeleton` additionally supplies the canonical thin category
   structure on that quotient. -/
abbrev SetoidObjectClasses (C : Type*) [Category* C] :=
  ThinSkeleton C

theorem setoidObjectClasses_eq_iff
    {C : Type*} [Category* C] {X Y : C} :
    (ThinSkeleton.mk X : SetoidObjectClasses C) = ThinSkeleton.mk Y ↔
      Nonempty (X ≅ Y) := by
  exact Quotient.eq

theorem isSetoid_object_classes_are_discrete
    {C : Type*} [Category* C] (hC : IsSetoid C) :
    IsDiscrete (SetoidObjectClasses C) := by
  refine ⟨?_, ?_⟩
  · intro X Y
    constructor
    intro f g
    exact Subsingleton.elim f g
  · intro X Y f
    revert f
    refine Quotient.inductionOn X ?_
    intro X
    refine Quotient.inductionOn Y ?_
    intro Y f
    apply setoidObjectClasses_eq_iff.mpr
    have hXY : Nonempty (X ⟶ Y) := by
      exact leOfHom f
    let f := Classical.choice hXY
    exact ⟨@asIso _ _ _ _ f (hC.1.all_isIso f)⟩

theorem isSetoid_skeleton_equivalence
    {C : Type*} [Category* C] (hC : IsSetoid C) :
    Nonempty (Skeleton C ≌ C) ∧
      IsDiscrete (Skeleton C) := by
  have hhom : ∀ X Y : C, Subsingleton (X ⟶ Y) :=
    (isSetoid_iff_isGroupoid_and_hom_subsingleton.mp hC).2
  refine ⟨⟨skeletonEquivalence C⟩, ?_⟩
  apply (isDiscrete_iff_every_morphism_is_eqToHom).mpr
  intro X Y f
  let e : (fromSkeleton C).obj X ≅ (fromSkeleton C).obj Y :=
    @asIso _ _ _ _ ((fromSkeleton C).map f) (hC.1.all_isIso _)
  have hXY : X = Y := skeleton_skeletal C
    ⟨(fromSkeleton C).preimageIso e⟩
  refine ⟨hXY, ?_⟩
  apply (fromSkeleton C).map_injective
  exact Subsingleton.elim _ _

theorem isSetoid_objectClasses_equivalence
    {C : Type*} [Category* C] (hC : IsSetoid C) :
    Nonempty (SetoidObjectClasses C ≌ C) ∧
      IsDiscrete (SetoidObjectClasses C) := by
  have hhom : ∀ X Y : C, Subsingleton (X ⟶ Y) :=
    (isSetoid_iff_isGroupoid_and_hom_subsingleton.mp hC).2
  let F : SetoidObjectClasses C ⥤ C :=
    { obj := Quotient.out
      map := fun {X Y} f => by
        let f' : ThinSkeleton.mk (Quotient.out X) ⟶
            ThinSkeleton.mk (Quotient.out Y) :=
          eqToHom (Quotient.out_eq X) ≫ f ≫
            eqToHom (Quotient.out_eq Y).symm
        have hXY : Nonempty (Quotient.out X ⟶ Quotient.out Y) := by
          have hle := f'.le
          change Nonempty (Quotient.out X ⟶ Quotient.out Y) at hle
          exact hle
        exact Classical.choice hXY
      map_id := by
        intro X
        exact (hhom _ _).elim _ _
      map_comp := by
        intro X Y Z f g
        exact (hhom _ _).elim _ _ }
  let unitIso : 𝟭 (SetoidObjectClasses C) ≅ F ⋙ toThinSkeleton C :=
    NatIso.ofComponents
      (fun X => eqToIso (Quotient.out_eq X).symm)
      (by
        intro X Y f
        apply Subsingleton.elim)
  let counitIso : toThinSkeleton C ⋙ F ≅ 𝟭 C :=
    NatIso.ofComponents
      (fun X => Nonempty.some (Quotient.exact (Quotient.out_eq (ThinSkeleton.mk X))))
      (by
        intro X Y f
        exact (hhom _ _).elim _ _)
  let hF : F.IsEquivalence :=
    Functor.IsEquivalence.mk' (toThinSkeleton C) unitIso counitIso
  exact ⟨⟨@Functor.asEquivalence _ _ _ _ F hF⟩,
    isSetoid_object_classes_are_discrete hC⟩

/-! ## Categories fibred in setoids -/

def IsCategoryFibredInSetoids
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) : Prop :=
  p.IsFibredInGroupoids ∧
    ∀ U : C, IsSetoid (Functor.Fiber p U)

theorem isCategoryFibredInSetoids_iff_isFibered_and_setoidFibres
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) :
    IsCategoryFibredInSetoids p ↔
      p.IsFibered ∧ ∀ U : C, IsSetoid (Functor.Fiber p U) := by
  constructor
  · rintro ⟨hp, hsetoid⟩
    have h := (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp
    exact ⟨h.2, hsetoid⟩
  · rintro ⟨hfibred, hsetoid⟩
    refine ⟨(fibredInGroupoids_iff_fibred_groupoid_fibres p).mpr ?_, hsetoid⟩
    exact ⟨fun U => (hsetoid U).1, hfibred⟩

/-! ## The fixed-base 2-category -/

def IsSetoidFibredCategoryOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) : Prop :=
  ∀ U : C, IsSetoid (Functor.Fiber (structureFunctor X.underlying) U)

def categoriesFibredInSetoidsObjectProperty {C : Cat.{v, u}} :
    ObjectProperty (FibredCategoryOver C) :=
  fun X => IsSetoidFibredCategoryOver X

abbrev CategoriesFibredInSetoidsOver (C : Cat.{v, u}) :=
  FullSubTwoCategory (FibredCategoryOver C)
    (categoriesFibredInSetoidsObjectProperty (C := C))

theorem setoidFibredCategoryOver_isCategoryFibredInSetoids
    {C : Cat.{v, u}} (X : FibredCategoryOver C)
    (hX : IsSetoidFibredCategoryOver X) :
    IsCategoryFibredInSetoids (structureFunctor X.underlying) := by
  exact (isCategoryFibredInSetoids_iff_isFibered_and_setoidFibres _).mpr
    ⟨inferInstance, hX⟩

theorem mapsStronglyCartesian_to_setoidFibred
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsSetoidFibredCategoryOver Y)
    (F : CategoryOverHom X.underlying Y.underlying) :
    MapsStronglyCartesian
      (structureFunctor X.underlying) (structureFunctor Y.underlying)
      (overFunctor F) := by
  intro a b φ _hφ
  have hY' := setoidFibredCategoryOver_isCategoryFibredInSetoids Y hY
  exact fibredInGroupoids_all_morphisms_stronglyCartesian
    (structureFunctor Y.underlying) hY'.1 ((overFunctor F).map φ)

def fibredCategoryOverHomOfSetoid
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsSetoidFibredCategoryOver Y)
    (F : CategoryOverHom X.underlying Y.underlying) :
    FibredCategoryOverHom X Y where
  underlying := F
  preserves := mapsStronglyCartesian_to_setoidFibred hY F

theorem setoidFibredCategoryOver_two_morphism_isIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsSetoidFibredCategoryOver Y)
    {F G : FibredCategoryOverHom X Y} (η : F ⟶ G) : IsIso η := by
  exact fibredInGroupoids_two_morphism_isIso
    (X := X) (Y := Y) (fun U => (hY U).1) η

theorem categoriesFibredInSetoidsOver_is_two_one_category
    (C : Cat.{v, u}) :
    IsTwoOneCategory (CategoriesFibredInSetoidsOver C) := by
  intro X Y
  refine ⟨fun {F G} η => ?_⟩
  let _ : IsIso η.hom := setoidFibredCategoryOver_two_morphism_isIso
    (X := X.obj) (Y := Y.obj) Y.property η.hom
  refine ⟨⟨inv η.hom⟩, ?_, ?_⟩
  · apply Bicategory.InducedBicategory.hom₂_ext
    change η.hom ≫ inv η.hom = 𝟙 F.hom
    simp
  · apply Bicategory.InducedBicategory.hom₂_ext
    change inv η.hom ≫ η.hom = 𝟙 G.hom
    simp

/-! ## Two-fibre products -/

structure FibredInSetoidsTwoFibreProduct
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) where
  product : FibredTwoFibreProduct.{u₁, v₁, v, u} F G
  product_diagram_is_canonical :
    product.diagram = twoFibreProductOverDiagram F.underlying G.underlying
  fibres_are_setoids : ∀ U : C,
    IsSetoid (Functor.Fiber product.diagram.base U)

theorem fibredInSetoidsTwoFibreProduct_apex_isCategoryFibredInSetoids
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    {F : FibredCategoryOverHom X S} {G : FibredCategoryOverHom Y S}
    (P : FibredInSetoidsTwoFibreProduct F G) :
    IsCategoryFibredInSetoids P.product.diagram.base := by
  exact (isCategoryFibredInSetoids_iff_isFibered_and_setoidFibres
    P.product.diagram.base).mpr
    ⟨P.product.apex_fibred, P.fibres_are_setoids⟩

/- Unit 33 exposes existence of an arbitrary fibred two-fibre product, while
   the fixed-base construction used here is the canonical diagram.  Record
   the needed canonical assertion at this boundary so the setoid product is
   built from the same diagram as the fibre comparison theorem. -/
theorem canonical_twoFibreProductOverBase_isCategoryFibredInSetoids
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (hX : IsSetoidFibredCategoryOver X)
    (hY : IsSetoidFibredCategoryOver Y)
    (_hS : IsSetoidFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    IsCategoryFibredInSetoids
      (twoFibreProductOverBaseFunctor F.underlying G.underlying) := by
  apply (isCategoryFibredInSetoids_iff_isFibered_and_setoidFibres _).mpr
  refine ⟨?_, ?_⟩
  · exact (canonicalFibredTwoFibreProduct.{v, u, u, v} X Y S F G).apex_fibred
  · intro U
    obtain ⟨e⟩ := twoFibreProductOver_fibre_equivalent
      F.underlying G.underlying U
    let _ : IsGroupoid
        (twoFibreProductOverFibreCategory F.underlying G.underlying U) := by
      constructor
      intro a b f
      let _ : IsIso f.hom.left := (hX U).1.all_isIso _
      let _ : IsIso f.hom.right := (hY U).1.all_isIso _
      let g : b ⟶ a := by
        refine { hom :=
          { left := inv f.hom.left, right := inv f.hom.right, w := ?_ } }
        calc
          (overMorphismFiberFunctor F.underlying U).map (inv f.hom.left) ≫
              a.obj.hom =
            (overMorphismFiberFunctor F.underlying U).map (inv f.hom.left) ≫
              (a.obj.hom ≫
                (overMorphismFiberFunctor G.underlying U).map f.hom.right) ≫
              (overMorphismFiberFunctor G.underlying U).map
                (inv f.hom.right) := by simp [Category.assoc]
          _ = (overMorphismFiberFunctor F.underlying U).map
                (inv f.hom.left) ≫
              ((overMorphismFiberFunctor F.underlying U).map f.hom.left ≫
                b.obj.hom) ≫
              (overMorphismFiberFunctor G.underlying U).map
                (inv f.hom.right) := by rw [f.hom.w]
          _ = b.obj.hom ≫
              (overMorphismFiberFunctor G.underlying U).map
                (inv f.hom.right) := by simp [Category.assoc]
      refine ⟨⟨g, ?_, ?_⟩⟩
      · apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp [g]
      · apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp [g]
    let hcomma : ∀ A B :
        twoFibreProductOverFibreCategory F.underlying G.underlying U,
        Subsingleton (A ⟶ B) := by
      intro A B
      constructor
      intro f g
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact ((isSetoid_iff_isGroupoid_and_hom_subsingleton.mp (hX U)).2
          _ _).elim f.hom.left g.hom.left
      · exact ((isSetoid_iff_isGroupoid_and_hom_subsingleton.mp (hY U)).2
          _ _).elim f.hom.right g.hom.right
    let _ : IsGroupoid
        (Functor.Fiber (twoFibreProductOverBaseFunctor
          F.underlying G.underlying) U) := by
      refine { all_isIso := ?_ }
      intro a b f
      let _ : IsIso (e.functor.map f) :=
        (inferInstance : IsGroupoid
          (twoFibreProductOverFibreCategory F.underlying G.underlying U)).all_isIso _
      exact e.fullyFaithfulFunctor.isIso_of_isIso_map f
    exact isSetoid_of_groupoid_of_hom_subsingleton
      inferInstance (by
        intro A B
        constructor
        intro f g
        apply e.fullyFaithfulFunctor.map_injective
        exact (hcomma (e.functor.obj A) (e.functor.obj B)).elim _ _)

theorem categoriesFibredInSetoids_have_twoFibreProducts
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (hX : IsSetoidFibredCategoryOver X)
    (hY : IsSetoidFibredCategoryOver Y)
    (hS : IsSetoidFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredInSetoidsTwoFibreProduct F G) := by
  have hcanonical := canonical_twoFibreProductOverBase_isCategoryFibredInSetoids
    hX hY hS F G
  let D := twoFibreProductOverDiagram F.underlying G.underlying
  let product : FibredTwoFibreProduct F G :=
    { diagram := D
      apex_fibred :=
        (fibredInGroupoids_iff_fibred_groupoid_fibres D.base).mp
          hcanonical.1 |>.2
      is_two_fibre_product :=
        twoFibreProductOver_is_twoFibreProduct F.underlying G.underlying }
  refine ⟨{
    product := product
    product_diagram_is_canonical := rfl
    fibres_are_setoids := ?_ }⟩
  exact hcanonical.2

/-! ## Equivalences with fibred-in-sets categories -/

theorem equivalence_to_fibredInSets_gives_setoidFibres
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hG : IsEquivalenceOverFunctor p p' G)
    (hp' : IsCategoryFibredInSets p') :
    IsCategoryFibredInSetoids p ∧
      ∀ U : C,
        Function.Surjective (fibreFunctor p p' G over U).obj ∧
          ∀ x y : Functor.Fiber p U,
            ((fibreFunctor p p' G over U).obj x =
              (fibreFunctor p p' G over U).obj y) ↔
              Nonempty (x ≅ y) := by
  have htransport := fibredInGroupoids_of_isEquivalenceOverFunctor
    p p' G over hG hp'.1
  refine ⟨?_, ?_⟩
  · refine ⟨htransport.1, ?_⟩
    intro U
    apply isSetoid_of_groupoid_of_hom_subsingleton
      (((fibredInGroupoids_iff_fibred_groupoid_fibres p).mp htransport.1).1 U)
    intro x y
    constructor
    intro f g
    let F := fibreFunctor p p' G over U
    let _ : F.IsEquivalence := htransport.2 U
    apply (Functor.FullyFaithful.ofFullyFaithful F).faithful.map_injective
    exact @Subsingleton.elim _ ((hp'.2 U).subsingleton _ _) _ _
  · intro U
    let F := fibreFunctor p p' G over U
    let _ : F.IsEquivalence := htransport.2 U
    let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
    let hdiscrete := hp'.2 U
    change Function.Surjective F.obj ∧
      ∀ x y : Functor.Fiber p U,
        (F.obj x = F.obj y) ↔ Nonempty (x ≅ y)
    constructor
    · intro y
      obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage F y
      exact ⟨x, hdiscrete.eq_of_hom e.hom⟩
    · intro x y
      constructor
      · intro hxy
        let e : F.obj x ≅ F.obj y := eqToIso hxy
        obtain ⟨f, hf⟩ := hF.full.map_surjective e.hom
        obtain ⟨g, hg⟩ := hF.full.map_surjective e.inv
        refine ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
        · apply hF.faithful.map_injective
          simp [Functor.map_comp, hf, hg]
        · apply hF.faithful.map_injective
          simp [Functor.map_comp, hf, hg]
      · rintro ⟨e⟩
        exact hdiscrete.eq_of_hom (F.map e.hom)

/- The objectwise part of the source's quotient construction is exposed
   through a set-valued presheaf whose values are the object classes in
   each fibre.  The existential theorem records both the objectwise class
   equivalences and the coherent equivalence to its set-presheaf category. -/
theorem fibredSetoid_object_presheaf_exists
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    ∃ F : Cᵒᵖ ⥤ Type uS,
      IsFibredEquivalenceOver p (setPresheafProjection F) ∧
        ∀ U : C,
          Nonempty (F.obj (Opposite.op U) ≃
            SetoidObjectClasses (Functor.Fiber p U)) := by
  /- Proof plan: choose pullbacks for `p`, let reindexing act on thin-skeleton
  object classes, and form the resulting set presheaf; the quotient functor on
  each fibre assembles into the required fibred equivalence. -/
  sorry

noncomputable def fibredSetoidObjectPresheaf
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    Cᵒᵖ ⥤ Type uS :=
  Classical.choose (fibredSetoid_object_presheaf_exists p hp)

theorem fibredSetoidObjectPresheaf_obj_equiv
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) (U : C) :
    Nonempty
      ((fibredSetoidObjectPresheaf p hp).obj (Opposite.op U) ≃
      SetoidObjectClasses (Functor.Fiber p U)) := by
  exact (Classical.choose_spec
    (fibredSetoid_object_presheaf_exists p hp)).2 U

theorem fibredSetoidObjectPresheaf_isFibredEquivalentToSetPresheaf
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    IsFibredEquivalenceOver p
      (setPresheafProjection (fibredSetoidObjectPresheaf p hp)) := by
  exact (Classical.choose_spec
    (fibredSetoid_object_presheaf_exists p hp)).1

private theorem representable_of_setPresheaf_equivalence_over_slice
    {C : Type uC} [Category.{vC} C]
    {F : Cᵒᵖ ⥤ Type uS} {X : C}
    (A : setPresheafCategory F ⥤ Over X)
    (B : Over X ⥤ setPresheafCategory F)
    (hA : A ⋙ Over.forget X = setPresheafProjection F)
    (hB : B ⋙ setPresheafProjection F = Over.forget X) :
    (∃ e, ∃ (over :
      (A ⋙ B) ⋙ setPresheafProjection F =
        (𝟭 (setPresheafCategory F)) ⋙ setPresheafProjection F),
      Formalization.Books.Categories.Unit34.IsOverNaturalIso
        (setPresheafProjection F) over e) →
    (∃ e, ∃ (over :
      (B ⋙ A) ⋙ Over.forget X =
        (𝟭 (Over X)) ⋙ Over.forget X),
      Formalization.Books.Categories.Unit34.IsOverNaturalIso
        (Over.forget X) over e) → F.IsRepresentable := by
  intro hAB hBA
  refine Exists.elim hAB (fun eAB hAB' => ?_)
  refine Exists.elim hAB' (fun overAB heAB => ?_)
  refine Exists.elim hBA (fun eBA hBA' => ?_)
  refine Exists.elim hBA' (fun overBA heBA => ?_)
  have eqToHom_comp {Y Z W : C} (p : Y = Z) (q : Z = W) :
      eqToHom p ≫ eqToHom q = eqToHom (p.trans q) :=
    CategoryTheory.eqToHom_trans p q
  have hA_base {U : C} (x : F.obj (Opposite.op U)) :
      (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F)).left = U := by
    have hh := congrArg
      (fun K : setPresheafCategory F ⥤ C =>
        K.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F)) hA
    change (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F)).left = U at hh
    exact hh
  have hB_base {U : C} (g : U ⟶ X) :
      (B.obj (Over.mk g)).base = U := by
    have hh := congrArg
      (fun K : Over X ⥤ C => K.obj (Over.mk g)) hB
    change (B.obj (Over.mk g)).base = U at hh
    exact hh
  have hBA_base {U : C} (x : F.obj (Opposite.op U)) :
      (B.obj (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F))).base = U := by
    have hh := congrArg
      (fun K : Over X ⥤ C => K.obj
        (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F))) hB
    have hh' :
        (B.obj (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F))).base =
          (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F)).left := by
      change (B.obj (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F))).base =
        (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F)).left at hh
      exact hh
    exact hh'.trans (hA_base x)
  have hB_map_base {Y Z : Over X} (i : Y ⟶ Z)
      (hY : (B.obj Y).base = Y.left) (hZ : (B.obj Z).base = Z.left) :
      (B.map i).base = eqToHom hY ≫ i.left ≫ eqToHom hZ.symm := by
    have hh := Functor.congr_hom hB i
    change (B.map i).base = eqToHom hY ≫ i.left ≫ eqToHom hZ.symm at hh
    exact hh
  have hA_map_base {Y Z : setPresheafCategory F} (i : Y ⟶ Z) :
      (A.map i).left =
        eqToHom (congrArg (fun K : setPresheafCategory F ⥤ C => K.obj Y) hA) ≫
          (setPresheafProjection F).map i ≫
            eqToHom (congrArg (fun K : setPresheafCategory F ⥤ C => K.obj Z) hA).symm := by
    have hh := Functor.congr_hom hA i
    change (A.map i).left =
      eqToHom (congrArg (fun K : setPresheafCategory F ⥤ C => K.obj Y) hA) ≫
        (setPresheafProjection F).map i ≫
          eqToHom (congrArg (fun K : setPresheafCategory F ⥤ C => K.obj Z) hA).symm at hh
    exact hh
  have hP_eqToHom {Y Z : setPresheafCategory F} (h : Y = Z) :
      (setPresheafProjection F).map (eqToHom h) =
        eqToHom (congrArg (fun K : setPresheafCategory F =>
          (setPresheafProjection F).obj K) h) := by
    cases h
    symm
    apply CategoryTheory.eqToHom_refl
  have hunit_base {U : C} (x : F.obj (Opposite.op U)) :
      (eAB.hom.app (⟨U, Discrete.mk x⟩ : setPresheafCategory F)).base =
        eqToHom (hBA_base x) := by
    have hh := heAB (⟨U, Discrete.mk x⟩ : setPresheafCategory F)
    change (eAB.hom.app (⟨U, Discrete.mk x⟩ : setPresheafCategory F)).base =
      eqToHom (congrArg (fun K : setPresheafCategory F ⥤ C => K.obj
        (⟨U, Discrete.mk x⟩ : setPresheafCategory F)) overAB) at hh
    have hproof :
        congrArg (fun K : setPresheafCategory F ⥤ C => K.obj
          (⟨U, Discrete.mk x⟩ : setPresheafCategory F)) overAB = hBA_base x :=
      Subsingleton.elim _ _
    rw [hproof] at hh
    exact hh
  let toHom {U : C} (x : F.obj (Opposite.op U)) : U ⟶ X :=
    eqToHom (hA_base x).symm ≫
      (A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F)).hom
  let fromHom {U : C} (g : U ⟶ X) : F.obj (Opposite.op U) :=
    cast (congrArg (fun V : C => F.obj (Opposite.op V)) (hB_base g))
      (setPresheafObjectValue F (B.obj (Over.mk g)))
  have setObject_eq {U : C} (Y : setPresheafCategory F)
      (x : F.obj (Opposite.op U)) (hbase : Y.base = U)
      (hvalue : cast (congrArg (fun V : C => F.obj (Opposite.op V)) hbase)
        (setPresheafObjectValue F Y) = x) :
      Y = (⟨U, Discrete.mk x⟩ : setPresheafCategory F) := by
    cases Y with
    | mk Y Yfiber =>
      cases Yfiber with
      | mk y =>
        subst U
        have hyx : y = x := by
          simpa only [setPresheafObjectValue, cast_eq] using hvalue
        subst x
        rfl
  have hB_obj {U : C} (g : U ⟶ X) :
      B.obj (Over.mk g) =
        (⟨U, Discrete.mk (fromHom g)⟩ : setPresheafCategory F) := by
    apply setObject_eq (B.obj (Over.mk g)) (fromHom g) (hB_base g)
    rfl
  let hA_iso {U : C} (x : F.obj (Opposite.op U)) :
      A.obj (⟨U, Discrete.mk x⟩ : setPresheafCategory F) ≅
        Over.mk (toHom x) := by
    refine Over.isoMk (eqToIso (hA_base x)) ?_
    dsimp [toHom]
    simp
  have F_map_eqToHom {V U : C} (h : V = U) (x : F.obj (Opposite.op U)) :
      F.map (eqToHom h).op x =
        cast (congrArg (fun W : C => F.obj (Opposite.op W)) h.symm) x := by
    cases h
    simp
  have fromHom_map {U V : C} (f : U ⟶ V) (g : V ⟶ X) :
      fromHom (f ≫ g) = F.map f.op (fromHom g) := by
    let j : Over.mk (f ≫ g) ⟶ Over.mk g := by
      refine Over.homMk f ?_
      simp
    have hY : (B.obj (Over.mk (f ≫ g))).base =
        (Over.mk (f ≫ g)).left := by
      change (B.obj (Over.mk (f ≫ g))).base = U
      exact hB_base (f ≫ g)
    have hZ : (B.obj (Over.mk g)).base = (Over.mk g).left := by
      change (B.obj (Over.mk g)).base = V
      exact hB_base g
    have hj := hB_map_base j hY hZ
    have hvalue := setPresheafHom_fibre_condition F (B.map j)
    rw [hj] at hvalue
    dsimp [j] at hvalue
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hvalue
    rw [F_map_eqToHom hZ.symm, F_map_eqToHom hY] at hvalue
    have hvalue' := congrArg
      (fun y => cast (congrArg (fun W : C => F.obj (Opposite.op W)) hY) y)
      hvalue
    simpa [fromHom] using hvalue'.symm
  let e {U : C} : (U ⟶ X) ≃ F.obj (Opposite.op U) :=
    { toFun := fromHom
      invFun := toHom
      left_inv := by
        intro g
        have hobj := hB_obj g
        have hk := heBA (Over.mk g)
        change (eBA.hom.app (Over.mk g)).left =
          eqToHom (congrArg (fun K : Over X ⥤ C => K.obj (Over.mk g)) overBA) at hk
        let k :
            A.obj (⟨U, Discrete.mk (fromHom g)⟩ : setPresheafCategory F) ⟶
              Over.mk g :=
          A.map (eqToHom hobj.symm) ≫ eBA.hom.app (Over.mk g)
        have hkbase : k.left = eqToHom (hA_base (fromHom g)) := by
          dsimp [k]
          rw [hA_map_base (eqToHom hobj.symm)]
          rw [hP_eqToHom hobj.symm]
          rw [hk]
          simp only [eqToHom_comp]
          exact eqToHom_comp _ _
        have hw := Over.w k
        dsimp [toHom]
        rw [← hw, hkbase]
        change eqToHom (hA_base (fromHom g)).symm ≫
          eqToHom (hA_base (fromHom g)) ≫ g = g
        rw [← Category.assoc, eqToHom_trans]
        have hproof :
            (hA_base (fromHom g)).symm.trans (hA_base (fromHom g)) = rfl :=
          Subsingleton.elim _ _
        rw [hproof]
        simp
      right_inv := by
        intro x
        let Y : setPresheafCategory F := ⟨U, Discrete.mk x⟩
        have hAY : (A.obj Y).left = U := by
          dsimp [Y]
          exact hA_base x
        let i : A.obj Y ⟶
            Over.mk (toHom x) := by
          refine Over.homMk (eqToHom hAY) ?_
          dsimp [Y, toHom]
          simp
        let hsource :
            (B.obj (A.obj Y)).base = (A.obj Y).left :=
          by
            have hh := congrArg (fun K : Over X ⥤ C => K.obj
              (A.obj Y)) hB
            change (B.obj (A.obj Y)).base =
              (Over.forget X).obj (A.obj Y) at hh
            simpa only [Over.forget_obj] using hh
        let htarget :
            (B.obj (Over.mk (toHom x))).base = U := hB_base (toHom x)
        let hmapEq : (B.obj (A.obj Y)).base =
              (B.obj (Over.mk (toHom x))).base :=
          hsource.trans (hAY.trans htarget.symm)
        have htargetB : (B.obj (Over.mk (toHom x))).base =
            (Over.mk (toHom x)).left := by
          change (B.obj (Over.mk (toHom x))).base = U
          exact htarget
        have hm_base0 : (B.map i).base =
            eqToHom (hsource.trans (hAY.trans htarget.symm)) := by
          rw [hB_map_base i hsource htargetB]
          have hi0 : i.left = eqToHom hAY := by
            rfl
          rw [hi0]
          simp only [eqToHom_comp]
        have hm_base : (B.map i).base = eqToHom hmapEq := by
          calc
            _ = eqToHom (hsource.trans (hAY.trans htarget.symm)) := hm_base0
            _ = eqToHom hmapEq :=
              congrArg (fun h => eqToHom h) (Subsingleton.elim _ _)
        have hvalueB := setPresheafHom_fibre_condition F (B.map i)
        rw [hm_base, F_map_eqToHom hmapEq] at hvalueB
        have hvalueAB := setPresheafHom_fibre_condition F
          (eAB.hom.app Y)
        rw [hunit_base x, F_map_eqToHom (hBA_base x)] at hvalueAB
        have hvalue :
            cast (congrArg (fun V : C => F.obj (Opposite.op V)) hmapEq.symm)
                (setPresheafObjectValue F (B.obj (Over.mk (toHom x)))) =
              cast (congrArg (fun V : C => F.obj (Opposite.op V)) (hBA_base x).symm) x :=
          hvalueB.trans hvalueAB.symm
        have hproof : hmapEq.symm.trans (hBA_base x) = htarget :=
          Subsingleton.elim _ _
        have hvalue' := congrArg
          (fun y => cast
            (congrArg (fun V : C => F.obj (Opposite.op V)) (hBA_base x)) y)
          hvalue
        simpa [fromHom, hproof] using hvalue' }
  refine Functor.RepresentableBy.isRepresentable (Y := X)
    { homEquiv := e
      homEquiv_comp := by
        intro U V f g
        apply (e.symm).injective
        change toHom (e (f ≫ g)) = toHom (F.map f.op (e g))
        dsimp [toHom, e]
        rw [fromHom_map f g] }

theorem fibredSetoidObjectPresheaf_isRepresentable_of_exists_slice
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p)
    (h : ∃ X : C, IsFibredEquivalenceOver p (Over.forget X)) :
    Functor.IsRepresentable (fibredSetoidObjectPresheaf p hp) := by
  rcases h with ⟨X, hX⟩
  have hF := fibredSetoidObjectPresheaf_isFibredEquivalentToSetPresheaf p hp
  have hFX := isFibredEquivalenceOver_trans
    (isFibredEquivalenceOver_symm hF) hX
  let A := Classical.choose hFX
  have hFX' := Classical.choose_spec hFX
  let B := Classical.choose hFX'
  have hFX'' := Classical.choose_spec hFX'
  have hrest :
      B ⋙ setPresheafProjection (fibredSetoidObjectPresheaf p hp) =
          Over.forget X ∧
        MapsStronglyCartesian
          (setPresheafProjection (fibredSetoidObjectPresheaf p hp))
          (Over.forget X) A ∧
        MapsStronglyCartesian
          (Over.forget X)
          (setPresheafProjection (fibredSetoidObjectPresheaf p hp)) B ∧
        (∃ e, ∃ (over :
          (A ⋙ B) ⋙ setPresheafProjection (fibredSetoidObjectPresheaf p hp) =
            (𝟭 (setPresheafCategory (fibredSetoidObjectPresheaf p hp))) ⋙
              setPresheafProjection (fibredSetoidObjectPresheaf p hp)),
          Formalization.Books.Categories.Unit34.IsOverNaturalIso
            (setPresheafProjection (fibredSetoidObjectPresheaf p hp))
            over e) ∧
        (∃ e, ∃ (over :
          (B ⋙ A) ⋙ Over.forget X =
            (𝟭 (Over X)) ⋙ Over.forget X),
          Formalization.Books.Categories.Unit34.IsOverNaturalIso
            (Over.forget X) over e) := by
    exact hFX''.2
  have hA : A ⋙ Over.forget X =
      setPresheafProjection (fibredSetoidObjectPresheaf p hp) := by
    simpa only [] using hFX''.1
  have hB : B ⋙ setPresheafProjection
      (fibredSetoidObjectPresheaf p hp) = Over.forget X := by
    simpa only [] using hrest.1
  have hAB : ∃ e, ∃ (over :
      (A ⋙ B) ⋙ setPresheafProjection (fibredSetoidObjectPresheaf p hp) =
        (𝟭 (setPresheafCategory (fibredSetoidObjectPresheaf p hp))) ⋙
          setPresheafProjection (fibredSetoidObjectPresheaf p hp)),
      Formalization.Books.Categories.Unit34.IsOverNaturalIso
        (setPresheafProjection (fibredSetoidObjectPresheaf p hp)) over e := by
    simpa only [] using hrest.2.2.2.1
  have hBA : ∃ e, ∃ (over :
      (B ⋙ A) ⋙ Over.forget X =
        (𝟭 (Over X)) ⋙ Over.forget X),
      Formalization.Books.Categories.Unit34.IsOverNaturalIso
        (Over.forget X) over e := by
    simpa only [] using hrest.2.2.2.2
  exact representable_of_setPresheaf_equivalence_over_slice A B hA hB hAB hBA

theorem fibredSetoidObjectPresheaf_exists_slice_of_isRepresentable
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p)
    (h : Functor.IsRepresentable (fibredSetoidObjectPresheaf p hp)) :
    ∃ X : C, IsFibredEquivalenceOver p (Over.forget X) := by
  /- Proof plan: unpack `h` as a representable-presheaf isomorphism, lift it
  to an equivalence of Grothendieck constructions, and compose it with the
  chosen equivalence from `p` and the representable slice comparison. -/
  rcases (Formalization.Books.Categories.Unit03.isRepresentable_iff_exists_yoneda_iso
    (fibredSetoidObjectPresheaf p hp)).mp h with ⟨X, ⟨e⟩⟩
  have hF : IsFibredEquivalenceOver p
      (setPresheafProjection (fibredSetoidObjectPresheaf p hp)) :=
    fibredSetoidObjectPresheaf_isFibredEquivalentToSetPresheaf p hp
  have hFG : IsFibredEquivalenceOver
      (setPresheafProjection (fibredSetoidObjectPresheaf p hp))
      (setPresheafProjection (representablePresheaf X)) :=
    setPresheafProjection_isFibredEquivalenceOver_of_iso e
  have hGX : IsFibredEquivalenceOver
      (setPresheafProjection (representablePresheaf X)) (Over.forget X) :=
    isFibredEquivalenceOver_symm (representable_presheaf_slice_equivalence X)
  exact ⟨X, isFibredEquivalenceOver_trans hF
    (isFibredEquivalenceOver_trans hFG hGX)⟩

theorem fibredSetoidObjectPresheaf_isRepresentable_iff_exists_slice
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    Functor.IsRepresentable (fibredSetoidObjectPresheaf p hp) ↔
      ∃ X : C, IsFibredEquivalenceOver p (Over.forget X) := by
  constructor
  · exact fibredSetoidObjectPresheaf_exists_slice_of_isRepresentable p hp
  · exact fibredSetoidObjectPresheaf_isRepresentable_of_exists_slice p hp

abbrev setoidificationCategory
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :=
  setPresheafCategory (fibredSetoidObjectPresheaf p hp)

abbrev setoidificationProjection
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    setoidificationCategory p hp ⥤ C :=
  setPresheafProjection (fibredSetoidObjectPresheaf p hp)

theorem setoidificationCategory_isFibredInSets
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    IsCategoryFibredInSets (setoidificationProjection p hp) := by
  exact setPresheaf_category_isFibredInSets _

theorem fibredSetoids_equivalent_to_fibredInSets
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    ∃ F : Cᵒᵖ ⥤ Type uS,
      IsFibredEquivalenceOver p (setPresheafProjection F) := by
  /- Proof plan: take `fibredSetoidObjectPresheaf p hp` and return the
  equivalence recorded by
  `fibredSetoidObjectPresheaf_isFibredEquivalentToSetPresheaf`. -/
  exact ⟨fibredSetoidObjectPresheaf p hp,
    fibredSetoidObjectPresheaf_isFibredEquivalentToSetPresheaf p hp⟩

/- The source packages the preceding construction as a functor from the
   fixed-base 2-category to the ordinary category of fibred-in-sets objects. -/
structure SetoidificationFunctorProperties
    {C : Cat.{v, u}}
    (F : CategoriesFibredInSetoidsOver C ⥤
      CategoriesFibredInSetsOverCategory (Cat.of (C : Type u))) : Prop where
  unique_two_iso :
    ∀ {X Y : CategoriesFibredInSetoidsOver C}
      {f g : X ⟶ Y}, F.map f = F.map g →
        ∃! η : f ⟶ g, IsIso η
  two_isomorphic_morphisms_have_equal_images :
    ∀ {X Y : CategoriesFibredInSetoidsOver C}
      {f g : X ⟶ Y}, (∃ η : f ⟶ g, IsIso η) → F.map f = F.map g
  lifts_morphisms :
    ∀ {X Y : CategoriesFibredInSetoidsOver C}
      (h : F.obj X ⟶ F.obj Y),
      ∃ f : X ⟶ Y, F.map f = h
  fibredInSets_objects_are_fixed :
    ∀ Z : CategoriesFibredInSetsOverCategory (Cat.of (C : Type u)),
      ∃ X : CategoriesFibredInSetoidsOver C, F.obj X = Z

theorem setoidificationFunctor_exists (C : Cat.{v, u}) :
    ∃ F : CategoriesFibredInSetoidsOver C ⥤
      CategoriesFibredInSetsOverCategory (Cat.of (C : Type u)),
      SetoidificationFunctorProperties F := by
  /- Proof plan: use fibrewise thin-skeleton quotients on objects and induced
  maps on object classes on morphisms; quotient functoriality proves the laws,
  while thin target fibres give lifting and uniqueness up to a unique 2-iso. -/
  sorry

noncomputable def setoidificationFunctor (C : Cat.{v, u}) :
    CategoriesFibredInSetoidsOver C ⥤
      CategoriesFibredInSetsOverCategory (Cat.of (C : Type u)) :=
  Classical.choose (setoidificationFunctor_exists C)

theorem setoidificationFunctor_properties (C : Cat.{v, u}) :
    SetoidificationFunctorProperties (setoidificationFunctor C) := by
  exact Classical.choose_spec (setoidificationFunctor_exists C)

theorem setoidificationFunctor_lift_unique_up_to_unique_two_iso
    {C : Cat.{v, u}}
    (F : CategoriesFibredInSetoidsOver C ⥤
      CategoriesFibredInSetsOverCategory (Cat.of (C : Type u)))
    (hF : SetoidificationFunctorProperties F)
    {X Y : CategoriesFibredInSetoidsOver C}
    (h : F.obj X ⟶ F.obj Y) :
    ∃ f : X ⟶ Y, F.map f = h ∧
      ∀ g : X ⟶ Y, F.map g = h →
        ∃! η : f ⟶ g, IsIso η := by
  rcases hF.lifts_morphisms h with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact hF.unique_two_iso (hf.trans hg.symm)

/-! ## Inertia -/

theorem inertiaStructureMap_over_base
    {C : Cat.{v, u}} (X : FibredCategoryOver C) :
    inertiaStructureMap X ⋙ structureFunctor X.underlying =
      relativeInertiaBase (toBaseFibredHom X).underlying := by
  rfl

theorem setoidFibred_iff_inertia_isEquivalentOverBase
    {C : Cat.{v, u}} (X : FibredCategoryOver C) :
    IsSetoidFibredCategoryOver X ↔
      IsEquivalentOverBase
        (relativeInertiaBase (toBaseFibredHom X).underlying)
        (structureFunctor X.underlying) := by
  /- Proof plan: identify each inertia fibre with pairs `(x, automorphism x)`;
  the projection is an equivalence exactly when every automorphism is unique,
  which is the hom-subsingleton condition for setoid fibres. -/
  sorry

theorem setoidFibred_iff_inertia_structureMap_isEquivalence
    {C : Cat.{v, u}} (X : FibredCategoryOver C) :
    IsSetoidFibredCategoryOver X ↔
      Nonempty (inertiaStructureMap X).IsEquivalence := by
  /- Proof plan: rewrite the inertia map as a functor over the base using
  `inertiaStructureMap_over_base`, then apply the preceding over-base
  equivalence criterion and forget the base structure. -/
  sorry

/-! ## Morphisms modulo 2-isomorphism -/

def TwoIsomorphismRelation
    {C : Cat.{v, u}}
    {X Y : CategoriesFibredInSetoidsOver C}
    (f g : X ⟶ Y) : Prop :=
  ∃ η : f ⟶ g, IsIso η

abbrev MorphismsModuloTwoIsomorphism
    {C : Cat.{v, u}}
    (X Y : CategoriesFibredInSetoidsOver C) :=
  Quot (TwoIsomorphismRelation (X := X) (Y := Y))

theorem twoIsomorphismRelation_isEquivalence
    {C : Cat.{v, u}}
    (X Y : CategoriesFibredInSetoidsOver C) :
    Equivalence (TwoIsomorphismRelation (X := X) (Y := Y)) := by
  /- Proof plan: use identity 2-morphisms for reflexivity, inverses of
  componentwise isomorphisms for symmetry, and vertical composition for
  transitivity. -/
  sorry

theorem setoidification_morphism_classes_equiv_presheaf_morphisms
    {C : Cat.{v, u}}
    (F : CategoriesFibredInSetoidsOver C ⥤
      CategoriesFibredInSetsOverCategory (Cat.of (C : Type u)))
    (hF : SetoidificationFunctorProperties F)
    (X Y : CategoriesFibredInSetoidsOver C) :
    Nonempty
      (MorphismsModuloTwoIsomorphism X Y ≃
        ((categoriesFibredInSetsOverEquivalence (C := (C : Type u))).inverse.obj
            (F.obj X) ⟶
          (categoriesFibredInSetsOverEquivalence (C := (C : Type u))).inverse.obj
            (F.obj Y))) := by
  /- Proof plan: descend `F.map` to the 2-isomorphism quotient; the uniqueness
  and lifting fields of `hF` make this map bijective, then transport the hom
  type through `categoriesFibredInSetsOverEquivalence`. -/
  sorry

/-! ## Compatibility with two-fibre products -/

def TypeFiberProduct {A B D : Type*} (f : A → D) (g : B → D) :=
  {x : A × B // f x.1 = g x.2}

noncomputable def objectIsoClassMap
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) : SetoidObjectClasses A → SetoidObjectClasses B :=
  (ThinSkeleton.map F).obj

theorem fibredSetoid_twoFibreProduct_object_classes_equiv
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    {F : FibredCategoryOverHom X S} {G : FibredCategoryOverHom Y S}
    (hS : IsSetoidFibredCategoryOver S)
    (P : FibredInSetoidsTwoFibreProduct F G) (U : C) :
    Nonempty
      (SetoidObjectClasses (Functor.Fiber P.product.diagram.base U) ≃
        TypeFiberProduct
          (objectIsoClassMap
            (fibreFunctor
              (structureFunctor X.underlying)
              (structureFunctor S.underlying)
              (overFunctor F.underlying)
              (overFunctor_comm F.underlying) U))
          (objectIsoClassMap
            (fibreFunctor
              (structureFunctor Y.underlying)
              (structureFunctor S.underlying)
              (overFunctor G.underlying)
              (overFunctor_comm G.underlying) U))) := by
  /- Proof plan: use the canonical fibre equivalence with the iso-comma of
  the two fibre functors; because the target fibre is a setoid, taking
  thin-skeleton classes identifies its objects with the displayed type fibre product. -/
  sorry

/-! ## The fibred 2-Yoneda comparison

The following reconstruction is the strict-over-base part of the fibred
2-Yoneda argument.  It is kept here, before the representability chapter,
because it only uses `Over` and the universe-polymorphic vertical-isomorphism
interface from Unit 35.  In particular, it does not identify the two
categories involved by choosing representatives of their objects.
-/

theorem slice_functor_over_base_isomorphic_to_map
    {C : Type uC} [Category.{vC} C] {X Y : C}
    (F : Over X ⥤ Over Y)
    (hF : F ⋙ Over.forget Y = Over.forget X) :
    ∃ f : X ⟶ Y, ∃ e : F ≅ Over.map f,
      ∃ over : F ⋙ Over.forget Y = (Over.map f) ⋙ Over.forget Y,
        IsNatIsoOver (Over.forget Y) e over := by
  let hobj : ∀ U : Over X, (F.obj U).left = U.left := fun U =>
    Functor.congr_obj hF U
  let f : X ⟶ Y :=
    eqToHom (hobj (Over.mk (𝟙 X))).symm ≫
      (F.obj (Over.mk (𝟙 X))).hom
  let eapp : ∀ U : Over X, F.obj U ≅ (Over.map f).obj U := fun U => by
    refine Over.isoMk (eqToIso (hobj U)) ?_
    let u : U ⟶ Over.mk (𝟙 X) := Over.homMk U.hom
    have hu := Functor.congr_hom hF u
    change (F.map u).left =
      eqToHom (hobj U) ≫ u.left ≫
        eqToHom (hobj (Over.mk (𝟙 X))).symm at hu
    rw [← Over.w (F.map u), hu]
    dsimp [f, u]
    simp [Category.assoc]
  let e : F ≅ Over.map f := NatIso.ofComponents eapp (by
    intro U V k
    apply (Over.forget Y).map_injective
    have hk := Functor.congr_hom hF k
    change (F.map k).left =
      eqToHom (hobj U) ≫ k.left ≫ eqToHom (hobj V).symm at hk
    change (F.map k).left ≫ eqToHom (hobj V) =
      eqToHom (hobj U) ≫ k.left
    rw [hk]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id])
  let over : F ⋙ Over.forget Y = (Over.map f) ⋙ Over.forget Y :=
    hF.trans (Over.mapForget_eq f).symm
  refine ⟨f, e, over, ?_⟩
  intro U
  change (eapp U).hom.left =
    eqToHom (congrArg (fun L : Over X ⥤ C => L.obj U) over)
  dsimp [e, eapp, over, hobj]
  simp

/- A presentation stores both directions of an equivalence with a slice.  The
   equations are retained explicitly: this is what lets the comparison below
   remain universe-polymorphic and lets its verticality be checked rather than
   inferred from an untyped equivalence. -/
structure FibredSlicePresentation
    {S : Type*} [Category* S] {C : Type*} [Category* C]
    (p : S ⥤ C) where
  representingObject : C
  forward : S ⥤ Over representingObject
  forward_over : forward ⋙ Over.forget representingObject = p
  inverse : Over representingObject ⥤ S
  inverse_over : inverse ⋙ p = Over.forget representingObject
  unit : forward ⋙ inverse ≅ 𝟭 S
  unit_over : (forward ⋙ inverse) ⋙ p = (𝟭 S) ⋙ p
  unit_isOver : IsNatIsoOver p unit unit_over
  counit : inverse ⋙ forward ≅ 𝟭 (Over representingObject)
  counit_over : (inverse ⋙ forward) ⋙ Over.forget representingObject =
    (𝟭 (Over representingObject)) ⋙ Over.forget representingObject
  counit_isOver : IsNatIsoOver (Over.forget representingObject)
    counit counit_over

def fibredSlicePresentation_of_isEquivalenceOverFunctor
    {S : Type*} [Category* S] {C : Type*} [Category* C]
    {p : S ⥤ C} (X : C) (F : S ⥤ Over X)
    (hF : IsEquivalenceOverFunctor p (Over.forget X) F) :
    FibredSlicePresentation p := by
  let G := Classical.choose hF
  have hG := Classical.choose_spec hF
  let unit := Classical.choose hG.2.2.1
  have hunit := Classical.choose_spec hG.2.2.1
  let unitOver := Classical.choose hunit
  have hunitOver := Classical.choose_spec hunit
  let counit := Classical.choose hG.2.2.2
  have hcounit := Classical.choose_spec hG.2.2.2
  let counitOver := Classical.choose hcounit
  have hcounitOver := Classical.choose_spec hcounit
  exact {
    representingObject := X
    forward := F
    forward_over := hG.1
    inverse := G
    inverse_over := hG.2.1
    unit := unit
    unit_over := unitOver
    unit_isOver := hunitOver
    counit := counit
    counit_over := counitOver
    counit_isOver := hcounitOver }

def fibredSliceLift
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) : S ⥤ T :=
  P.forward ⋙ Over.map φ ⋙ Q.inverse

theorem fibredSliceLift_over
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) :
    fibredSliceLift P Q φ ⋙ q = p := by
  calc
    fibredSliceLift P Q φ ⋙ q =
        P.forward ⋙ Over.map φ ⋙ (Q.inverse ⋙ q) := by
      simp [fibredSliceLift, Functor.assoc]
    _ = P.forward ⋙ Over.map φ ⋙ Over.forget Q.representingObject := by
      rw [Q.inverse_over]
    _ = P.forward ⋙ Over.forget P.representingObject := by
      simpa [Functor.assoc] using congrArg
        (fun K : Over P.representingObject ⥤ C => P.forward ⋙ K)
        (Over.mapForget_eq φ)
    _ = p := P.forward_over

theorem fibredSliceLift_mapsStronglyCartesian
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (hq : q.IsFibredInGroupoids)
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) :
    MapsStronglyCartesian p q (fibredSliceLift P Q φ) := by
  intro a b ψ _hψ
  exact fibredInGroupoids_all_morphisms_stronglyCartesian q hq
    ((fibredSliceLift P Q φ).map ψ)

def FibredMorphismVerticalNatTrans
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G : S ⥤ T} (F_over : F ⋙ q = p) (G_over : G ⋙ q = p)
    (η : F ⟶ G) : Prop :=
  ∀ Z : S,
    q.map (η.app Z) =
      eqToHom (congrArg (fun H : S ⥤ C => H.obj Z)
        (F_over.trans G_over.symm))

def FibredMorphismVerticalIsomorphismRelation
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G : S ⥤ T} (F_over : F ⋙ q = p) (G_over : G ⋙ q = p) : Prop :=
  ∃ η : F ⟶ G, FibredMorphismVerticalNatTrans F_over G_over η ∧ IsIso η

theorem fibredMorphismVerticalNatTrans_comp
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G H : S ⥤ T}
    {F_over : F ⋙ q = p} {G_over : G ⋙ q = p} {H_over : H ⋙ q = p}
    (η : F ⟶ G) (θ : G ⟶ H)
    (hη : FibredMorphismVerticalNatTrans F_over G_over η)
    (hθ : FibredMorphismVerticalNatTrans G_over H_over θ) :
    FibredMorphismVerticalNatTrans F_over H_over (η ≫ θ) := by
  intro Z
  change q.map (η.app Z ≫ θ.app Z) = _
  rw [Functor.map_comp, hη Z, hθ Z]
  simp

theorem fibredMorphismVerticalNatTrans_inv
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G : S ⥤ T}
    {F_over : F ⋙ q = p} {G_over : G ⋙ q = p}
    (η : F ⟶ G) (hη : FibredMorphismVerticalNatTrans F_over G_over η)
    [IsIso η] :
    FibredMorphismVerticalNatTrans G_over F_over (inv η) := by
  intro Z
  apply (cancel_mono (q.map (η.app Z))).1
  rw [← q.map_comp]
  have hinv : (inv η).app Z ≫ η.app Z = 𝟙 _ := by
    exact congrArg (fun τ => τ.app Z) (IsIso.inv_hom_id η)
  rw [hinv, q.map_id, hη Z]
  simp

theorem fibred_isNatIsoOver_comp
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : B ⥤ D) {F G K : A ⥤ B}
    (e : F ≅ G) (over : F ⋙ q = G ⋙ q)
    (h : IsNatIsoOver q e over)
    (e' : G ≅ K) (over' : G ⋙ q = K ⋙ q)
    (h' : IsNatIsoOver q e' over') :
    IsNatIsoOver q (e ≪≫ e') (over.trans over') := by
  intro Z
  change q.map (e.hom.app Z ≫ e'.hom.app Z) = _
  rw [Functor.map_comp, h Z, h' Z]
  simp only [eqToHom_trans]

theorem fibred_isNatIsoOver_whiskerLeft
    {A B D E : Type*} [Category* A] [Category* B]
      [Category* D] [Category* E]
    (q : B ⥤ D) {F G : A ⥤ B} (e : F ≅ G)
    (over : F ⋙ q = G ⋙ q) (h : IsNatIsoOver q e over)
    (L : E ⥤ A) :
    IsNatIsoOver q (Functor.isoWhiskerLeft L e)
      ((Functor.assoc L F q).trans
        ((congrArg (fun K : A ⥤ D => L ⋙ K) over).trans
          (Functor.assoc L G q).symm)) := by
  intro Z
  change q.map (e.hom.app (L.obj Z)) = _
  simpa only [eqToHom_trans] using h (L.obj Z)

theorem fibred_isNatIsoOver_whiskerRight
    {A B D E : Type*} [Category* A] [Category* B]
      [Category* D] [Category* E]
    (q : B ⥤ D) {F G : A ⥤ B} (e : F ≅ G)
    (over : F ⋙ q = G ⋙ q) (h : IsNatIsoOver q e over)
    (L : B ⥤ E) (r : E ⥤ D) (L_over : L ⋙ r = q) :
    IsNatIsoOver r (Functor.isoWhiskerRight e L)
      ((Functor.assoc F L r).trans
        (((congrArg (fun K : B ⥤ D => F ⋙ K) L_over).trans
          (over.trans
            (congrArg (fun K : B ⥤ D => G ⋙ K) L_over.symm))).trans
          (Functor.assoc G L r).symm)) := by
  intro Z
  change r.map (L.map (e.hom.app Z)) = _
  have hL := Functor.congr_hom L_over (e.hom.app Z)
  change (L ⋙ r).map (e.hom.app Z) = _
  rw [hL, h Z]
  simp only [eqToHom_trans]

theorem fibred_isNatIsoOver_symm
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : B ⥤ D) {F G : A ⥤ B} (e : F ≅ G)
    (over : F ⋙ q = G ⋙ q) (h : IsNatIsoOver q e over) :
    IsNatIsoOver q e.symm over.symm := by
  intro Z
  apply (cancel_mono (q.map (e.hom.app Z))).1
  rw [← q.map_comp]
  change q.map (e.inv.app Z ≫ e.hom.app Z) = _
  have hinv : e.inv.app Z ≫ e.hom.app Z = 𝟙 _ := by
    exact congrArg (fun τ => τ.app Z) e.inv_hom_id
  rw [hinv, q.map_id, h Z]
  simp

theorem fibredSlicePresentation_lift_comparison
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (F : S ⥤ T) (F_over : F ⋙ q = p) :
    ∃ φ : P.representingObject ⟶ Q.representingObject,
      ∃ η : F ⟶ fibredSliceLift P Q φ,
        FibredMorphismVerticalNatTrans F_over
          (fibredSliceLift_over P Q φ) η ∧ IsIso η := by
  let H : Over P.representingObject ⥤ Over Q.representingObject :=
    P.inverse ⋙ F ⋙ Q.forward
  have hH : H ⋙ Over.forget Q.representingObject =
      Over.forget P.representingObject := by
    dsimp [H]
    calc
      (P.inverse ⋙ F ⋙ Q.forward) ⋙
          Over.forget Q.representingObject =
          P.inverse ⋙ F ⋙ q := by
            simpa [Functor.assoc] using congrArg
              (fun K : T ⥤ C => (P.inverse ⋙ F) ⋙ K) Q.forward_over
      _ = P.inverse ⋙ p := by
        simpa [Functor.assoc] using congrArg
          (fun K : S ⥤ C => P.inverse ⋙ K) F_over
      _ = Over.forget P.representingObject := P.inverse_over
  obtain ⟨φ, eH, _overH, heH⟩ :=
    slice_functor_over_base_isomorphic_to_map H hH
  let eP_over :
      (P.forward ⋙ H) ⋙ Over.forget Q.representingObject =
        (F ⋙ Q.forward) ⋙ Over.forget Q.representingObject := by
    calc
      (P.forward ⋙ H) ⋙ Over.forget Q.representingObject =
          P.forward ⋙ (H ⋙ Over.forget Q.representingObject) := by
            simp [Functor.assoc]
      _ = P.forward ⋙ Over.forget P.representingObject := by
            rw [hH]
      _ = p := P.forward_over
      _ = F ⋙ q := F_over.symm
      _ = F ⋙ (Q.forward ⋙ Over.forget Q.representingObject) := by
            rw [Q.forward_over]
      _ = (F ⋙ Q.forward) ⋙ Over.forget Q.representingObject := by
            simp [Functor.assoc]
  let eP : P.forward ⋙ H ≅ F ⋙ Q.forward :=
    (Functor.associator P.forward P.inverse (F ⋙ Q.forward)).symm ≪≫
      Functor.isoWhiskerRight P.unit (F ⋙ Q.forward) ≪≫
      Functor.leftUnitor (F ⋙ Q.forward)
  have heP : IsNatIsoOver (Over.forget Q.representingObject)
      eP eP_over := by
    intro Z
    dsimp [eP]
    simp only [Category.comp_id]
    have hQmap := Functor.congr_hom Q.forward_over
      (F.map (P.unit.hom.app Z))
    have hFmap := Functor.congr_hom F_over (P.unit.hom.app Z)
    calc
      _ = (Q.forward ⋙ Over.forget Q.representingObject).map
          (F.map (P.unit.hom.app Z)) := by
            simpa only [Functor.comp_map, Functor.comp_obj,
              Over.forget_map, Over.forget_obj] using
              (Category.id_comp (Over.Hom.left
                (Q.forward.map (F.map (P.unit.hom.app Z)))))
      _ = _ := hQmap
      _ = _ := by
        have hFmap' : q.map (F.map (P.unit.hom.app Z)) =
            eqToHom (congrArg (fun K : S ⥤ C => K.obj
              ((P.forward ⋙ P.inverse).obj Z)) F_over) ≫
              p.map (P.unit.hom.app Z) ≫
              eqToHom (congrArg (fun K : S ⥤ C => K.obj Z) F_over).symm := by
          simpa only [Functor.comp_map] using hFmap
        rw [hFmap', P.unit_isOver Z]
        simp only [eqToHom_trans]
        rfl
  let eFB : F ⋙ Q.forward ≅ P.forward ⋙ Over.map φ :=
    eP.symm ≪≫ Functor.isoWhiskerLeft P.forward eH
  let eFB_over :
      (F ⋙ Q.forward) ⋙ Over.forget Q.representingObject =
        (P.forward ⋙ Over.map φ) ⋙ Over.forget Q.representingObject := by
    calc
      (F ⋙ Q.forward) ⋙ Over.forget Q.representingObject = F ⋙ q := by
        simp [Functor.assoc, Q.forward_over]
      _ = p := F_over
      _ = P.forward ⋙ Over.forget P.representingObject :=
        P.forward_over.symm
      _ = (P.forward ⋙ Over.map φ) ⋙
          Over.forget Q.representingObject := by
        symm
        simpa [Functor.assoc] using congrArg
          (fun K : Over P.representingObject ⥤ C => P.forward ⋙ K)
          (Over.mapForget_eq φ)
  have hePInv : IsNatIsoOver (Over.forget Q.representingObject)
      eP.symm eP_over.symm :=
    fibred_isNatIsoOver_symm (Over.forget Q.representingObject)
      eP eP_over heP
  have heHLeft : IsNatIsoOver (Over.forget Q.representingObject)
      (Functor.isoWhiskerLeft P.forward eH) _ :=
    fibred_isNatIsoOver_whiskerLeft
      (Over.forget Q.representingObject) eH _overH heH P.forward
  have heFB' := fibred_isNatIsoOver_comp
    (Over.forget Q.representingObject) eP.symm eP_over.symm hePInv
      (Functor.isoWhiskerLeft P.forward eH) _ heHLeft
  have heFB : IsNatIsoOver (Over.forget Q.representingObject)
      eFB eFB_over := by
    simpa [eFB, eFB_over] using heFB'
  let eF : F ≅ fibredSliceLift P Q φ := by
    simpa [fibredSliceLift, Functor.assoc] using
      (((Functor.rightUnitor F).symm ≪≫
          Functor.isoWhiskerLeft F Q.unit.symm) ≪≫
        (Functor.associator F Q.forward Q.inverse).symm) ≪≫
          Functor.isoWhiskerRight eFB Q.inverse
  let eRight_over : F ⋙ q = (F ⋙ 𝟭 T) ⋙ q := by
    rw [Functor.assoc, Functor.id_comp]
  have heRight : IsNatIsoOver q (Functor.rightUnitor F).symm
      eRight_over := by
    intro Z
    simp
  have heQUnitInv : IsNatIsoOver q Q.unit.symm Q.unit_over.symm :=
    fibred_isNatIsoOver_symm q Q.unit Q.unit_over Q.unit_isOver
  let eQUnitLeft_over :
      (F ⋙ 𝟭 T) ⋙ q = (F ⋙ (Q.forward ⋙ Q.inverse)) ⋙ q :=
    (Functor.assoc F (𝟭 T) q).trans
      ((congrArg (fun K : T ⥤ C => F ⋙ K) Q.unit_over.symm).trans
        (Functor.assoc F (Q.forward ⋙ Q.inverse) q).symm)
  have heQUnitLeft : IsNatIsoOver q
      (Functor.isoWhiskerLeft F Q.unit.symm) eQUnitLeft_over :=
    fibred_isNatIsoOver_whiskerLeft q Q.unit.symm Q.unit_over.symm
      heQUnitInv F
  let eAssoc_over :
      (F ⋙ (Q.forward ⋙ Q.inverse)) ⋙ q =
        ((F ⋙ Q.forward) ⋙ Q.inverse) ⋙ q := by
    simp [Functor.assoc]
  have heAssoc : IsNatIsoOver q
      (Functor.associator F Q.forward Q.inverse).symm eAssoc_over := by
    intro Z
    simp
  have heFBRight : IsNatIsoOver q
      (Functor.isoWhiskerRight eFB Q.inverse) _ :=
    fibred_isNatIsoOver_whiskerRight
      (Over.forget Q.representingObject) eFB eFB_over heFB
      Q.inverse q Q.inverse_over
  have heF' := fibred_isNatIsoOver_comp q
    (Functor.rightUnitor F).symm eRight_over heRight
      (Functor.isoWhiskerLeft F Q.unit.symm) _ heQUnitLeft
  have heF'' := fibred_isNatIsoOver_comp q
    ((Functor.rightUnitor F).symm ≪≫
        Functor.isoWhiskerLeft F Q.unit.symm
      ) (eRight_over.trans eQUnitLeft_over) heF'
      (Functor.associator F Q.forward Q.inverse).symm eAssoc_over heAssoc
  have heF''' := fibred_isNatIsoOver_comp q
    (((Functor.rightUnitor F).symm ≪≫
        Functor.isoWhiskerLeft F Q.unit.symm) ≪≫
          (Functor.associator F Q.forward Q.inverse).symm)
      ((eRight_over.trans eQUnitLeft_over).trans eAssoc_over) heF''
      (Functor.isoWhiskerRight eFB Q.inverse) _ heFBRight
  have heF : FibredMorphismVerticalNatTrans F_over
      (fibredSliceLift_over P Q φ) eF.hom := by
    intro Z
    simpa [eF, fibredSliceLift, Functor.assoc] using heF''' Z
  exact ⟨φ, eF.hom, heF, inferInstance⟩

theorem fibredMorphismVerticalNatTrans_object_class_map_eq
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G : S ⥤ T} (F_over : F ⋙ q = p) (G_over : G ⋙ q = p)
    (η : F ⟶ G)
    (hη : FibredMorphismVerticalNatTrans F_over G_over η)
    (hq : q.IsFibredInGroupoids) (U : C) :
    objectIsoClassMap (fibreFunctor p q F F_over U) =
      objectIsoClassMap (fibreFunctor p q G G_over U) := by
  let hqgroup : IsGroupoid (Functor.Fiber q U) :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.1 U
  let _ : IsGroupoid (Functor.Fiber q U) := hqgroup
  funext x
  refine Quotient.inductionOn x ?_
  intro x
  change ThinSkeleton.mk ((fibreFunctor p q F F_over U).obj x) =
    ThinSkeleton.mk ((fibreFunctor p q G G_over U).obj x)
  apply setoidObjectClasses_eq_iff.mpr
  let hx : q.obj (F.obj x.1) = U :=
    (congrArg (fun H : S ⥤ C => H.obj x.1) F_over).trans x.2
  let hy : q.obj (G.obj x.1) = U :=
    (congrArg (fun H : S ⥤ C => H.obj x.1) G_over).trans x.2
  let k : (fibreFunctor p q F F_over U).obj x ⟶
      (fibreFunctor p q G G_over U).obj x := by
    refine ⟨η.app x.1, ?_⟩
    apply CategoryTheory.IsHomLift.of_fac' q (𝟙 U) (η.app x.1) hx hy
    simpa [hx, hy, eqToHom_trans] using hη x.1
  exact ⟨asIso k⟩

theorem slice_map_vertical_iso_unique
    {C : Type*} [Category* C] {X Y : C}
    {φ ψ : X ⟶ Y} (e : Over.map φ ≅ Over.map ψ)
    (over : (Over.map φ) ⋙ Over.forget Y =
      (Over.map ψ) ⋙ Over.forget Y)
    (h : IsNatIsoOver (Over.forget Y) e over) :
    φ = ψ := by
  let u : Over X := Over.mk (𝟙 X)
  have hleft : (e.hom.app u).left = 𝟙 X := by
    have hv := h u
    have heq : congrArg (fun L : Over X ⥤ C => L.obj u) over = rfl :=
      Subsingleton.elim _ _
    have hv' : (e.hom.app u).left =
        eqToHom (congrArg (fun L : Over X ⥤ C => L.obj u) over) := by
      simpa only [Functor.comp_obj, Over.forget_obj, Over.forget_map] using hv
    have hid : eqToHom (congrArg (fun L : Over X ⥤ C => L.obj u) over) =
        𝟙 X := by
      apply CategoryTheory.eqToHom_refl
    rw [hid] at hv'
    simpa [u] using hv'
  have hw := Over.w (e.hom.app u)
  dsimp [u] at hw
  rw [hleft] at hw
  simpa only [Category.id_comp] using hw.symm

theorem fibredSlicePresentation_isCategoryFibredInSetoids
    {S C : Type*} [Category* S] [Category* C]
    {q : S ⥤ C} (Q : FibredSlicePresentation q) :
    IsCategoryFibredInSetoids q := by
  let hQ : IsEquivalenceOverFunctor q
      (Over.forget Q.representingObject) Q.forward :=
    ⟨Q.inverse, Q.forward_over, Q.inverse_over,
      ⟨Q.unit, Q.unit_over, Q.unit_isOver⟩,
      ⟨Q.counit, Q.counit_over, Q.counit_isOver⟩⟩
  exact (equivalence_to_fibredInSets_gives_setoidFibres
    q (Over.forget Q.representingObject) Q.forward Q.forward_over hQ
      (sliceProjection_isFibredInSets Q.representingObject)).1

theorem fibredMorphismVerticalNatTrans_unique_of_setoid
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {F G : S ⥤ T}
    (F_over : F ⋙ q = p) (G_over : G ⋙ q = p)
    (hsetoid : ∀ U : C, IsSetoid (Functor.Fiber q U))
    {η θ : F ⟶ G}
    (hη : FibredMorphismVerticalNatTrans F_over G_over η)
    (hθ : FibredMorphismVerticalNatTrans F_over G_over θ) :
    η = θ := by
  apply NatTrans.ext
  funext Z
  let hx : q.obj (F.obj Z) = p.obj Z :=
    congrArg (fun H : S ⥤ C => H.obj Z) F_over
  let hy : q.obj (G.obj Z) = p.obj Z :=
    congrArg (fun H : S ⥤ C => H.obj Z) G_over
  let η' : (Functor.Fiber.mk hx) ⟶ (Functor.Fiber.mk hy) :=
    ⟨η.app Z, by
      apply CategoryTheory.IsHomLift.of_fac' q (𝟙 (p.obj Z))
        (η.app Z) hx hy
      simpa [hx, hy, eqToHom_trans] using hη Z⟩
  let θ' : (Functor.Fiber.mk hx) ⟶ (Functor.Fiber.mk hy) :=
    ⟨θ.app Z, by
      apply CategoryTheory.IsHomLift.of_fac' q (𝟙 (p.obj Z))
        (θ.app Z) hx hy
      simpa [hx, hy, eqToHom_trans] using hθ Z⟩
  have hhom : Subsingleton
      ((Functor.Fiber.mk hx) ⟶ (Functor.Fiber.mk hy)) :=
    (isSetoid_iff_isGroupoid_and_hom_subsingleton.mp
      (hsetoid (p.obj Z))).2 _ _
  have hηθ : η' = θ' := hhom.elim _ _
  exact congrArg (fun k => k.1) hηθ

theorem fibredSlicePresentation_lift_exists_and_unique
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hsetoid : ∀ U : C, IsSetoid (Functor.Fiber q U))
    (φ : P.representingObject ⟶ Q.representingObject)
    {F G : S ⥤ T} (F_over : F ⋙ q = p) (G_over : G ⋙ q = p)
    (eF : F ≅ fibredSliceLift P Q φ)
    (heF : FibredMorphismVerticalNatTrans F_over
      (fibredSliceLift_over P Q φ) eF.hom)
    (eG : G ≅ fibredSliceLift P Q φ)
    (heG : FibredMorphismVerticalNatTrans G_over
      (fibredSliceLift_over P Q φ) eG.hom) :
    ∃! η : F ⟶ G,
      FibredMorphismVerticalNatTrans F_over G_over η ∧ IsIso η := by
  have heGinv : FibredMorphismVerticalNatTrans
      (fibredSliceLift_over P Q φ) G_over eG.inv :=
    by simpa using fibredMorphismVerticalNatTrans_inv eG.hom heG
  let η : F ⟶ G := eF.hom ≫ eG.inv
  have hη : FibredMorphismVerticalNatTrans F_over G_over η :=
    fibredMorphismVerticalNatTrans_comp eF.hom eG.inv heF heGinv
  refine ⟨η, ⟨hη, inferInstance⟩, ?_⟩
  intro θ hθ
  apply fibredMorphismVerticalNatTrans_unique_of_setoid
    F_over G_over hsetoid hθ.1 hη

structure FibredMorphismOverBase
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) where
  functor : S ⥤ T
  over : functor ⋙ q = p
  preserves : MapsStronglyCartesian p q functor

def fibredSliceLiftMorphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (hq : q.IsFibredInGroupoids)
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) :
    FibredMorphismOverBase p q :=
  { functor := fibredSliceLift P Q φ
    over := fibredSliceLift_over P Q φ
    preserves := fibredSliceLift_mapsStronglyCartesian hq P Q φ }

theorem fibredSlicePresentation_representing_morphism_exists_and_unique
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (hq : q.IsFibredInGroupoids)
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hsetoid : ∀ U : C, IsSetoid (Functor.Fiber q U))
    (φ : P.representingObject ⟶ Q.representingObject) :
    ∃ F : FibredMorphismOverBase p q,
      ∀ G : FibredMorphismOverBase p q,
        (∃ e : G.functor ≅ (fibredSliceLiftMorphism hq P Q φ).functor,
          FibredMorphismVerticalNatTrans G.over
            (fibredSliceLiftMorphism hq P Q φ).over e.hom) →
          ∃! η : F.functor ⟶ G.functor,
            FibredMorphismVerticalNatTrans F.over G.over η ∧ IsIso η := by
  let F := fibredSliceLiftMorphism hq P Q φ
  refine ⟨F, ?_⟩
  intro G hG
  obtain ⟨eG, heG⟩ := hG
  let eF : F.functor ≅ (fibredSliceLiftMorphism hq P Q φ).functor :=
    Iso.refl _
  have heF : FibredMorphismVerticalNatTrans F.over F.over eF.hom := by
    intro Z
    simp [eF]
  simpa [F] using
    fibredSlicePresentation_lift_exists_and_unique P Q hsetoid φ
      F.over G.over eF heF eG heG

def FibredMorphismOverBaseVerticalIsoRelation
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (F G : FibredMorphismOverBase p q) : Prop :=
  ∃ η : F.functor ⟶ G.functor,
    FibredMorphismVerticalNatTrans F.over G.over η ∧ IsIso η

abbrev FibredMorphismOverBaseClasses
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) :=
  Quot (FibredMorphismOverBaseVerticalIsoRelation (p := p) (q := q))

theorem fibredMorphismOverBaseVerticalIsoRelation_isEquivalence
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} :
    Equivalence
      (FibredMorphismOverBaseVerticalIsoRelation (p := p) (q := q)) := by
  constructor
  · intro F
    refine ⟨𝟙 F.functor, ?_, inferInstance⟩
    intro Z
    simp
  · intro F G hFG
    rcases hFG with ⟨η, hη, hηiso⟩
    refine ⟨inv η, ?_, inferInstance⟩
    exact fibredMorphismVerticalNatTrans_inv η hη
  · intro F G H hFG hGH
    rcases hFG with ⟨η, hη, hηiso⟩
    rcases hGH with ⟨θ, hθ, hθiso⟩
    refine ⟨η ≫ θ, ?_, inferInstance⟩
    exact fibredMorphismVerticalNatTrans_comp η θ hη hθ

theorem fibredSlicePresentation_class_is_represented_by_a_slice_morphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (_hq : q.IsFibredInGroupoids)
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (F : FibredMorphismOverBase p q) :
    ∃ φ : P.representingObject ⟶ Q.representingObject,
      ∃ η : F.functor ⟶ (fibredSliceLift P Q φ),
        FibredMorphismVerticalNatTrans F.over
          (fibredSliceLift_over P Q φ) η ∧ IsIso η := by
  exact fibredSlicePresentation_lift_comparison P Q F.functor F.over

theorem fibredSlicePresentation_lift_object_class_map_eq
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hq : q.IsFibredInGroupoids)
    (φ : P.representingObject ⟶ Q.representingObject)
    {F : S ⥤ T} (F_over : F ⋙ q = p)
    (η : F ⟶ fibredSliceLift P Q φ)
    (hη : FibredMorphismVerticalNatTrans F_over
      (fibredSliceLift_over P Q φ) η) (U : C) :
    objectIsoClassMap (fibreFunctor p q F F_over U) =
      objectIsoClassMap
        (fibreFunctor p q (fibredSliceLift P Q φ)
          (fibredSliceLift_over P Q φ) U) := by
  exact fibredMorphismVerticalNatTrans_object_class_map_eq
    F_over (fibredSliceLift_over P Q φ) η hη hq U

end

end Formalization.Books.Categories.Unit39
