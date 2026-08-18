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
    rfl

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
    (hS : IsSetoidFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    IsCategoryFibredInSetoids
      (twoFibreProductOverBaseFunctor F.underlying G.underlying) := by
  sorry

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
  sorry

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

/- The objectwise equivalences above do not by themselves preserve pullback
   along arrows of `C`.  The coherent form of the quotient construction is
   the representability statement below: the chosen object-class presheaf is
   representable exactly when the original fibred category is equivalent over
   `C` to a slice.  This is the interface used by Unit 40 in place of making
   arbitrary objectwise equivalence choices.
 -/
theorem fibredSetoidObjectPresheaf_isRepresentable_iff_exists_slice
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    Functor.IsRepresentable (fibredSetoidObjectPresheaf p hp) ↔
      ∃ X : C, IsFibredEquivalenceOver p (Over.forget X) := by
  sorry

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
  sorry

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
  sorry

theorem setoidFibred_iff_inertia_structureMap_isEquivalence
    {C : Cat.{v, u}} (X : FibredCategoryOver C) :
    IsSetoidFibredCategoryOver X ↔
      Nonempty (inertiaStructureMap X).IsEquivalence := by
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
  sorry

end

end Formalization.Books.Categories.Unit39
